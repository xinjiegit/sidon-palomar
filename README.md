# A universal lower bound for strict Sidon subsets

This repository is a Palomar submission project for the bound

\[
H(n) \ge \left(\frac{2}{3\sqrt 3}+o(1)\right)\sqrt n.
\]

Here `H(n)` is the minimum, over all `n`-element subsets of the integers, of the maximum cardinality of a strict Sidon subset. Repeated summands are allowed. The theorem has no diameter or additive-structure hypothesis. It does not resolve the conjectural asymptotic constant `1`.

## Submission surface

`Challenge.lean` states the five submitted claims independently, using only Mathlib. `Solution.lean` proves identically named claims from the local proof modules. The only deliberate `sorry` terms belong to the independent challenge; the solution must pass the permitted-axiom check. `comparator.json` is the comparison manifest.

| Declaration in namespace `PalomarSidon` | Content |
| --- | --- |
| `universal_integer_bound` | For every positive epsilon, all sufficiently large finite integer sets have a strict Sidon subset of size at least `(2/(3√3) − epsilon) √n`. |
| `finite_prime_power_bound` | For every prime power `q`, with `m = q²+q+1`, the lower bound is `ceil((q+1)/m * ceil(n/2 − n(n−1)/(8m)))`. |
| `affine_compression` | For every positive integer `m` and `0 ≤ delta ≤ 1/2`, an injective forward Freiman 2-map from a subset of size at least `ceil(delta n − delta² n(n−1)/(2m))` into `ZMod m`. |
| `universal_real_bound` | The same asymptotic constant for finite subsets of every real coordinate space, with a threshold uniform in the dimension. |
| `universal_torsion_free_bound` | The same asymptotic constant for finite subsets of every torsion-free abelian group. |

`IsSidon` and `Freiman2On` are explicitly defined in the challenge. Freiman maps preserve existing equalities; they are not assumed to reflect equalities. Injectivity is asserted separately. Both predicates include diagonal additive relations.

## Proof structure

1. Haar measure on the two-dimensional circle gives independent uniform images of any two distinct integers under a common random affine map.
2. Disjoint short circular cells label the selected points by `ZMod m`. Their width forces all existing additive two-sum equalities to preserve labels.
3. The deterministic inequality “occupied cells ≥ selected points − colliding pairs” gives the compression estimate, with exact pair-collision probability `delta²/m`.
4. A complete finite-field proof of Singer's construction supplies a strict Sidon set of size `q+1` in `ZMod (q²+q+1)`. Translation averaging and injective pullback give the finite theorem.
5. A proved prime-number-theorem consequence supplies prime parameters asymptotic to `sqrt(3n)/2`. A checked real limit gives the optimized constant.
6. Finite subsets of torsion-free abelian groups admit an injective forward Freiman map into the integers. This transfers the result without loss.

## Scope and provenance

See `PROVENANCE.md` for upstream proof sources and modifications, and `formalization.yaml` for formalization provenance, source correspondence, automation, and review status. The supporting research report contains additional claims that are **not submitted as formalized results** here; only the five declarations listed above form this submission.

The mathematical argument and Lean code were developed with AI assistance. No human mathematical review or publication-priority certification is claimed. Registration of this formalization would not establish novelty or settle Erdős's conjecture.

The project is distributed under GPL-3.0-only, retaining the notices of the adapted Singer proof and the licenses of any included third-party sources. Git dependencies retain their own licenses.

## Build and validation

The Lean 4.35.0-rc2 build and local Comparator run passed on 4 October 2026. All five claims were accepted by Lean, NanoDa, and con-ron; their transitive axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. The [verification record](docs/comparator-local-verification.json) includes source hashes and the complete checked scope. The macOS run used the documented option without a sandbox; the configured Linux workflow supplies the isolation required for submission verification.

Use the exact toolchain in `lean-toolchain`, the pinned dependencies in `lake-manifest.json`, and the verification commands supplied in `PALOMAR_PREPARATION.md`. That file records the checks actually completed and any outstanding submission requirements. A successful local build alone is not an acceptance or registration by Palomar.
