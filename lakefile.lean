import Lake
open Lake DSL

package "local-rings" where
  leanOptions := #[
    ⟨`autoImplicit, false⟩, -- prevents typos to be interpreted as new free variables
    ⟨`relaxedAutoImplicit, false⟩, -- prevents typos to be interpreted as new free variables
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`linter.docPrime, false⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.13.0"

@[default_target]
lean_lib "LocalRings"
