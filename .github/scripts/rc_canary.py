#!/usr/bin/env python3
"""Build this package on the newest Lean release candidate or release.

The script changes the working tree of the runner only. It moves `lean-toolchain`, moves every
git dependency that has a tag of the same name as the toolchain, regenerates the manifest and
builds every tracked module of the package's libraries. A dependency without such a tag stays
at its pinned revision.

Exit status: 0 when the build succeeds, when no newer Lean exists, or when only dependencies
fail; 1 when a module of this package fails or the failure cannot be attributed to a dependency.
`--plan` prints what would change and stops.
"""
import os
import re
import subprocess
import sys
from pathlib import Path

LEAN = "https://github.com/leanprover/lean4"
VERSION = re.compile(r"v(\d+)\.(\d+)\.(\d+)(?:-rc(\d+))?$")


def version_key(tag):
    m = VERSION.match(tag)
    if not m:
        return None
    major, minor, patch, rc = m.groups()
    return (int(major), int(minor), int(patch), 0 if rc else 1, int(rc or 0))


def tags(url):
    out = subprocess.run(["git", "ls-remote", "--tags", "--refs", url],
                         capture_output=True, text=True, check=True).stdout
    return {line.split("refs/tags/")[-1] for line in out.splitlines()}


def summary(text):
    print(text, flush=True)
    path = os.environ.get("GITHUB_STEP_SUMMARY")
    if path:
        with open(path, "a") as f:
            f.write(text + "\n\n")


def blocked(text):
    """Report that this package was not tested, as a warning on a successful job."""
    print(f"::warning title=Lean RC canary::{text.splitlines()[0]}", flush=True)
    summary(text)
    return 0


def tracked_lean():
    out = subprocess.run(["git", "ls-files", "*.lean"],
                         capture_output=True, text=True, check=True).stdout
    return set(out.split())


def library_targets(lakefile, files):
    if lakefile.suffix == ".toml":
        blocks = re.split(r"(?m)^\[\[", lakefile.read_text())
        libs = [m.group(1) for b in blocks if b.startswith("lean_lib]]")
                for m in [re.search(r'(?m)^name *= *"([^"]+)"', b)] if m]
    else:
        libs = re.findall(r"(?m)^(?:@\[default_target\] *)?lean_lib +«?([\w-]+)", lakefile.read_text())
    modules = [f[:-5].replace("/", ".") for f in sorted(files)
               if any(f == f"{lib}.lean" or f.startswith(f"{lib}/") for lib in libs)]
    return modules


def move_pins(text, target, is_toml):
    moved, kept = [], []
    cache = {}

    def choose(url, rev):
        if url not in cache:
            cache[url] = tags(url)
        name = url.rstrip("/").split("/")[-1].removesuffix(".git")
        if target in cache[url]:
            moved.append(name)
            return target
        kept.append(name)
        return rev

    if is_toml:
        blocks = re.split(r"(?m)^(?=\[\[)", text)
        for i, block in enumerate(blocks):
            url = re.search(r'(?m)^git *= *"([^"]+)"', block)
            rev = re.search(r'(?m)^rev *= *"([^"]+)"', block)
            if block.startswith("[[require]]") and url and rev:
                new = choose(url.group(1), rev.group(1))
                blocks[i] = block[:rev.start(1)] + new + block[rev.end(1):]
        text = "".join(blocks)
    else:
        pattern = re.compile(r'(from\s+git\s+"([^"]+)"\s*@\s*")([^"]+)(")')
        text = pattern.sub(
            lambda m: m.group(1) + choose(m.group(2), m.group(3)) + m.group(4), text)
    return text, moved, kept


def classify(log, files):
    own, other = set(), set()
    for m in re.finditer(r"(?m)^error: ([^\s:]+\.lean):\d+:\d+:", log):
        (own if m.group(1) in files else other).add(m.group(1))
    for m in re.finditer(r"(?m)^✖ \[\d+/\d+\] Building ([\w.«»]+)", log):
        path = m.group(1).replace(".", "/") + ".lean"
        (own if path in files else other).add(path)
    return sorted(own), sorted(other)


def main():
    plan_only = "--plan" in sys.argv
    toolchain = Path("lean-toolchain")
    current = toolchain.read_text().strip().split(":")[-1]
    candidates = [t for t in tags(LEAN) if version_key(t)]
    target = os.environ.get("LEAN_TARGET") or max(candidates, key=version_key)
    if not version_key(target):
        summary(f"`{target}` is not a Lean version tag.")
        return 1
    if version_key(target) <= (version_key(current) or (0,)):
        summary(f"No Lean version newer than `{current}`.")
        return 0

    lakefile = Path("lakefile.toml") if Path("lakefile.toml").exists() else Path("lakefile.lean")
    text, moved, kept = move_pins(lakefile.read_text(), target, lakefile.suffix == ".toml")
    files = tracked_lean()
    targets = library_targets(lakefile, files)
    summary(f"Lean `{current}` to `{target}`: {len(targets)} modules. "
            f"Dependencies moved: {', '.join(moved) or 'none'}. "
            f"Kept at their pins: {', '.join(kept) or 'none'}.")
    if not targets:
        summary("No module found to build.")
        return 1
    if plan_only:
        return 0

    lakefile.write_text(text)
    toolchain.write_text(f"leanprover/lean4:{target}\n")
    Path("lake-manifest.json").unlink(missing_ok=True)
    update = subprocess.run(["lake", "update"], capture_output=True, text=True)
    print(update.stdout, update.stderr, flush=True)
    if update.returncode:
        text = "`lake update` failed on this Lean version; the log has the error."
        if kept:
            return blocked(text)
        summary(text)
        return 1
    # A dependency's update hook may move the toolchain back to its own.
    toolchain.write_text(f"leanprover/lean4:{target}\n")

    has_mathlib = Path(".lake/packages/mathlib").is_dir()
    if has_mathlib and subprocess.run(["lake", "exe", "cache", "get"]).returncode:
        return blocked(f"No Mathlib cache for `{target}`; the package was not built.")

    lines = []
    with subprocess.Popen(["lake", "build", *targets], text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT) as build:
        for line in build.stdout:
            print(line, end="", flush=True)
            lines.append(line)
            # Compiling Mathlib exceeds the job's time limit, and means the pins do not match.
            if has_mathlib and re.search(r" (?:Built|Building) Mathlib\.[\w.]+(?:\s|$)", line):
                build.terminate()
                return blocked(f"The pins do not match Mathlib's cache on `{target}`; "
                               "the build was stopped before it compiled Mathlib.")
    if build.returncode == 0:
        summary(f"All modules build on `{target}`.")
        return 0

    own, other = classify("".join(lines), files)
    if own:
        summary(f"Failing on `{target}`:\n\n" + "\n".join(f"- `{p}`" for p in own))
        return 1
    if other:
        return blocked(f"Only dependencies fail on `{target}`:\n\n"
                       + "\n".join(f"- `{p}`" for p in other))
    summary(f"The build failed on `{target}` outside any module; the log has the error.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
