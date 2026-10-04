# Proof-source provenance

This document separates mathematical sources, reused formal proofs, and this project's adaptations. The exact submitted declarations and source correspondence are in `formalization.yaml`.

## Affine compression and extraction

`Basic`, `CellGeometry`, `Affine`, `Occupancy`, `Extraction`, `RelationExtraction`, `Translation`, `Compression`, `GeneralCellGeometry`, `GeneralOccupancy`, and `GeneralCompression` were developed in the user-directed Codex research and formalization sessions. The proof uses Mathlib's Haar measure, finite sets, circle groups, and elementary combinatorics. There is no assumed compression axiom.

The starting paper is Alexandre Bailleul and Robin Riblet, *On the largest Sidon subset in a finite subset of R^N*, arXiv:2605.03181v1. Affine randomization also appears in Imre Z. Ruzsa, *Solving a linear equation in a set of integers II*, Acta Arith. 72 (1995), 385–397, Definition 4.3 and Theorem 4.4. This project does not claim that affine randomization itself is new. Publication priority for the exact resulting bound has not been certified.

The prior informal report is included verbatim as `docs/research-report.tex`. It contains more material than the five results submitted here. In particular, its weighted claims and structural obstructions are not represented as formally verified by this package.

## Singer's construction

The mathematical construction originates in James Singer, *A theorem in finite projective geometry and some applications to number theory*, Trans. Amer. Math. Soc. 43 (1938), 377–385.

The Lean proof is adapted from:

- Repository: <https://github.com/d0d1/singer-theorem-lean>
- Immutable revision: `0c890589afc58e8955a5d7c3a609daff6447da31`
- Authors: David B. Hulak, Arthur F. Ramos, Ruy J. G. B. de Queiroz
- Associated paper: <https://arxiv.org/abs/2605.03274v2>
- License: GPL-3.0-only

`SingerLibrary.lean` consolidates the original prime-field modules, retaining the strict modular Sidon definition and removing unused interval and asymptotic-family imports. `SingerPrimePowerLibrary.lean` consolidates the six prime-power modules and omits the final asymptotic-family wrapper. The new adapters `Singer.lean` and `SingerPrimePower.lean` express the construction as a finite subset of `ZMod (q*q+q+1)` satisfying this project's strict Sidon predicate. All reused proof bodies are compiled; no Singer axiom is introduced.

The first local adaptation targeted Lean 4.31. The Palomar copy additionally adopts Lean's module system and explicit public interfaces. An internal quotient-group instance is private because its type uses a private abbreviation. Any further API changes made for the submission toolchain are proof migrations, not assumptions. Original notices remain in the adapted source.

The complete GPL-3.0 license is at the repository root. Historical unmodified upstream Lean files remain in the parent research archive and are intentionally not duplicated as unused `.lean` files in the submitted repository. The pinned public repository supplies the original source.

## Asymptotic and ambient transfer

`Finite`, `Asymptotic`, `Transfer`, and `Main` were developed in the Codex formalization session. The prime-density input is a proved Chebyshev asymptotic from the community Prime Number Theorem And project, vendored from upstream revision `c39a751132c88b6e8080b74c74023fd95b3d8be0`. The nine selected source modules and their truncations are documented in `vendor/PNT/PROVENANCE.txt`, with the Apache-2.0 license retained at `vendor/PNT/APACHE-2.0.txt`. Prime selection, convergence to the optimized constant, and the epsilon/cardinality quantifiers are proved locally. No prime-gap or prime-number-theorem axiom is declared.

`Transfer` proves an additive embedding of a finitely generated torsion-free group into integer polynomials, then chooses an integer evaluation that separates the given finite set. It provides a forward Freiman map without a bound on the integer image's diameter; no such bound is required in the integer theorem.

## Statement and verification infrastructure

`Challenge.lean` is an independent, Mathlib-only statement file. Its five `sorry` terms are expected specification holes. Its two fixed definitions are repeated in `Solution.lean` and checked transitively by Comparator. `Solution.lean` proves the five claims from the local development. Its permitted transitive axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.

The original research and formalization were AI-assisted, and this submission preparation is agent-developed. Human authorship and responsible maintenance must be supplied by the project owner; no identity is inferred from local account information. Agent review is not described as human peer review.
