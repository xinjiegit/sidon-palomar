# Migration to the Palomar submission toolchain

The original research formalization used Lean 4.31.0 and Mathlib revision `db127794c79fdeb86f6b0cf6ff2c804026fbaff1`. It remains preserved outside this package. The submission project uses Lean 4.35.0-rc2 and the canonical Mathlib release commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

Changes to the local Sidon proof:

- All 19 proof modules now use Lean's `module` system, public imports, and exposed public declarations. No theorem assumption or conclusion was weakened.
- In `SingerLibrary.finrank_ker_trace`, a local instance explicitly selects the additive group structure induced by the field structure of `ZMod p`. This resolves an instance ambiguity in the newer Mathlib while retaining the same rank-nullity proof.
- The internal quotient-group instance `instIsCyclicQ_KL` in `SingerPrimePowerLibrary` is private, consistently with its private quotient abbreviation. Its proof and mathematical content are unchanged.
- In `Transfer.exists_polynomial_embedding`, the newly bundled `AddMonoidAlgebra` is traversed using `coeffAddEquiv`. The embedding still sends basis coefficients to an integer polynomial; injectivity follows from the same sequence of injective maps.
- The asymptotic proof imports a trimmed and ported public upstream PNT proof instead of the older external fork. Its source selection and Apache-2.0 license are recorded in `vendor/PNT`. The locally proved prime selection and limiting calculation are unchanged.

The independent challenge and solution wrappers are new submission interfaces. They use the same strict Sidon definition, both integer ceilings, and the same compression parameters as the existing formalization. See `statement-audit.txt` for the separate statement audit and the verification record for the checks completed on this package.

The PNT source migration adds module headers, public imports, and exposed public declarations. It trims unused material after `WeakPNT` in `Wiener`, an unrelated block containing unfinished results, and material after `chebyshev_asymptotic` in `Consequences`. The retained proof bodies needed for the dependency compiled without additional mathematical API changes. No new axiom replaces deleted or ported material.
