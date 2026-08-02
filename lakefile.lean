import Lake
open Lake DSL

package "StableMatching" where
  version := v!"0.1.0"

@[default_target]
lean_lib «StableMatching» where
  -- add library configuration options here

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.22.0"
