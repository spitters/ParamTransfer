import Lake
open Lake DSL

-- Documentation package — SEPARATE from the `paramTransfer` library package so the
-- verso toolchain is NOT a transitive dependency of consumers of the library
-- (e.g. CatCrypt requires `paramTransfer`, and must not be made to resolve verso).
-- Build the manual locally with:  cd docs && lake build && lake exe transfer-manual --output _out
require verso from git
  "https://github.com/leanprover/verso.git" @ "v4.30.0"

package paramTransferDocs where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

@[default_target]
lean_lib TransferManual where

lean_exe «transfer-manual» where
  root := `ManualMain
