import Lake
open Lake DSL

package "PaulinIntroToAbstractAlgebra" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
-- -- just for visualizations (kinda breaks tho)
-- require Paperproof from git "https://github.com/Paper-Proof/paperproof.git"@"main"/"lean"
@[default_target]
lean_lib «PaulinIntroToAbstractAlgebra» where
  -- add any library configuration options here
