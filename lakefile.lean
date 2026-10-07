import Lake
open Lake DSL

package «lollipop_end_to_end_formalization» where
  -- Standalone trimmed package for the final manuscript formalization surface.
  -- `lake build` builds only the verified library; the archive is built on request.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib Lollipop where

lean_lib old_lean_folder where

lean_lib JordanCurveTheorem where
