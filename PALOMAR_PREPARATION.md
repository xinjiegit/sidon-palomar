# Palomar preparation record

This directory contains preparation material, not a submitted or registered
Palomar record. The research result is the universal strict Sidon bound with
coefficient `2 / (3 * sqrt 3)`, not a solution of Erdős's conjectural coefficient
`1`. Publication novelty remains unestablished.

## Requirements checked against immutable official sources

The official sources were fetched on 2026-10-04 UTC (2026-10-03 in the user's
America/Los_Angeles timezone):

| Source | Exact revision |
| --- | --- |
| [PalomarPolicy](https://github.com/PalomarRegistry/PalomarPolicy/tree/96b034cc31a72a63d4f4041911dce337a85c9a04) | `96b034cc31a72a63d4f4041911dce337a85c9a04` |
| [PalomarSubmission](https://github.com/PalomarRegistry/PalomarSubmission/tree/65f0154ed776cd26c224254aa57b379137f28b0d) | `65f0154ed776cd26c224254aa57b379137f28b0d` |
| [formalization.yaml standard](https://github.com/mathlib-initiative/formalization.yaml/tree/99c678e569c7c4c0772db297c5ddd5e4c9b6322e) | `99c678e569c7c4c0772db297c5ddd5e4c9b6322e` |
| [PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate/tree/2891de4c48955af824969a263d31b25e7a9a1406) | `2891de4c48955af824969a263d31b25e7a9a1406` |

Pinned schemas, taxonomies, and their source manifest are included under
`scripts/metadata/policy/` for portable metadata validation. Bulky downloaded
policy and verifier source snapshots are preserved in the parent research
workspace under `../palomar_audit/policy/`, outside the submission package.
Their repository identities and exact revisions above suffice to retrieve
them independently. In this audit,
search-engine copies of the unpinned policy and the website's introductory
checklist differed from the current Git source. The pinned Git policy takes
precedence in this preparation record. Requirements may change again before
actual submission, so recheck the official minimum and contract at that time.

## Toolchain compatibility and completed port

The original proof was checked on Lean `v4.31.0`. The fetched official
`toolchains.json` requires at least **`v4.35.0-rc2`**. Lean 4.31 is therefore
not currently submission-eligible. The submission package has been ported to
Lean **`v4.35.0-rc2`**, with canonical mathlib revision
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. All 19 core modules and the nine
vendored PNT modules have rebuilt on this toolchain. The proof-side API changes
were repaired and checked; changing only the toolchain file would not have
established compatibility. Local Comparator verification then passed for all
five selected statements at 2026-10-04 07:04:04 UTC. Its con-ron pass processed
80,778 declarations, and both Lean and NanoDa accepted. The Mac run used
Comparator's no-sandbox option. The supplied Linux sandbox CI is configured
but has not been run; Palomar's own verification is also a later separate step.

The PNT library may be a Solution-only dependency. Palomar allows arbitrary
pinned public GitHub dependencies on that side. It cannot be imported by
Challenge, even transitively: Challenge's closure is restricted to Lean core
and the canonical authenticated mathlib, Tau Ceti, and CSLib closures.

The package port instead vendors the needed nine PNT modules from community
upstream revision `c39a751132c88b6e8080b74c74023fd95b3d8be0` and preserves their
Apache-2.0 attribution in `vendor/PNT`. Vendoring does not exempt these files
from module headers or source-size limits. Historical checks of the prior
4.31 external dependency do not certify the ported source. The new build and
the compared theorem axiom closures have now been checked, as recorded above.

## Package checklist

- [x] Every theorem advertised as a recorded principal result appears in the
  Comparator selection, with the same name and type in Challenge and Solution.
- [x] Challenge is mathematically explicit, imports only allowed libraries,
  includes repeated summands in the Sidon condition, and is no more than
  1,000 lines and 100 KiB (prefer at most 300 lines and 32 KiB).
- [x] Every regular `.lean` file in the *prepared submission directory* uses
  `module` and has at most 10,000 physical lines. This includes unused vendor
  sources and certificates. Only `lakefile.lean` is exempt from the module
  header. `.lean` symlinks are forbidden. Adding headers alone is insufficient:
  public declarations, imports, and exposed definition bodies must be ported.
- [x] There is exactly one Lakefile and a generated, pinned manifest.
  Every Git dependency uses a credential-free public GitHub HTTPS URL and a
  full lowercase 40-character commit. Do not submit the larger research
  workspace merely to avoid packaging the substantive proof cleanly.
- [x] There is exactly one conventional repository-root license file, and its
  detected SPDX identifier agrees with `project.license`. The retained Singer
  source is GPL-3.0-only; preserve its notices and attribution. The package
  uses GPL version 3 only. Its metadata spells the detector identifier
  `GPL-3.0`, because Palomar's pinned Licensee 10.0.0 database uses that
  legacy SPDX spelling for the GPLv3 text. This does not grant permission
  to use a later GPL version. The unmodified official detector was run using
  Licensee 10.0.0 and an existing Ruby 3.4.8 runtime. It returned one matching
  identifier, `GPL-3.0`, agreeing exactly with the metadata.
- [x] The prepared source files contain no compiled outputs (`.olean`, `.ilean`,
  native objects, and other forbidden suffixes) outside `.lake`, and contain
  no Git LFS pointers or submodules.
  The prepared source is below the 500 MiB snapshot limit. Preserve these
  properties when selecting files for the future public commit.
- [ ] Replace the two human-identity placeholders in `formalization.yaml` with
  explicitly supplied author and responsible-maintainer names. Do not infer
  public authorship from filesystem usernames or Git account names. AI systems
  belong in `automation`, not in the human-author or human-maintainer fields.
- [x] Update the metadata's toolchain-port and dependency-provenance notes to
  match the final package. Preserve the distinction between automated review,
  human review, mechanical correctness, and mathematical novelty.
- [x] Perform a fresh Lake build; inspect the complete compared theorem axiom
  closures; run Comparator and its independent kernel checker. The permitted
  axioms are precisely `propext`, `Classical.choice`, and `Quot.sound`.
  Deliberate Challenge `sorry` holes are permitted; proof dependencies on
  `sorryAx`, `Lean.ofReduceBool`, or custom axioms are not.
  Local verification passed as described above; the future Linux CI and
  Palomar verification runs remain unperformed.
- [ ] Publish only the approved package to a public GitHub repository, commit
  all intended source, and record the full immutable commit SHA. Local files,
  branches, and tags alone cannot be submitted.

## Metadata choices

`formalization.yaml` is a v0.4 draft. It intentionally contains unmistakable
pending human identities rather than inventing attribution. The pending values
can satisfy the upstream schema's string requirements, but are not acceptable
final provenance and must be rejected by the preparation check.

The declared origin is **source-based**, derived from the `formalizes` and
`adapts` source relationships. The informal report preceded Lean, and the proof
adapts the compression strategy in Bailleul--Riblet and prior affine
randomization in Ruzsa. This does not deny that the precise bound may be new;
it avoids using the metadata's `original-proof` category as an unsupported
novelty claim. The current Palomar contract forbids mixing `original-proof`
with a substantive `formalizes` or `adapts` relationship.

Mathematical sources and prior Lean developments are separately credited.
Singer's 1938 paper is a mathematical source. The Hulak--Ramos--de Queiroz
Singer repository and the community PNT project are prior formalizations.
The pinned PNT fork is identified without treating its owner as sole author of
the underlying community proof. No author endorsement is claimed.

The selected subject codes are valid in the pinned Palomar taxonomies:
`math.NT`, `math.CO`, `11B30` (arithmetic combinatorics), `11B75` (other
combinatorial number theory), and `05B10` (difference sets).

The included validator can be run from a fresh extraction:

```sh
python3 -m venv .lake/metadata-venv
.lake/metadata-venv/bin/python -m pip install -r scripts/metadata/requirements.txt
.lake/metadata-venv/bin/python scripts/metadata/check.py --strict
```

The validator uses the included exact upstream v0.4 JSON schema and the pinned
Palomar taxonomies, and checks duplicate YAML keys, selected hard field rules,
and source-origin consistency. Strict mode intentionally fails while pending
identity markers remain. This is a preparation check, not the full Palomar
verifier or an assertion that the recorded names are accurate. Keep the local
virtual environment out of the public source snapshot.

## Submission and registration are separate later actions

No external submission, push, gist, tag, or registration has been performed by
this policy-preparation task. Actual submission requires a responsible author
or maintainer, or their approval, and evidence of repository write access.
If an agent later submits, it must read the then-current
[submission-host protocol](https://submit.palomar-registry.org/llms.txt) and
use that protocol rather than driving the human form.

Palomar first performs public mechanical verification and a private automated
editorial review. A result is not registered merely because those checks find
no blocking problem: the submitter separately elects to register. Ordinary
registration history is append-only. This is a record of checked statements,
not a human peer-review endorsement or a novelty certificate.

## Authoritative policy sections

- [Source layout, toolchain, Comparator, dependencies, and license: sections 2.1--2.5](https://github.com/PalomarRegistry/PalomarPolicy/blob/96b034cc31a72a63d4f4041911dce337a85c9a04/CONTRIBUTING.md).
- [Metadata, human authorship, source provenance, and review disclosure: section 3](https://github.com/PalomarRegistry/PalomarPolicy/blob/96b034cc31a72a63d4f4041911dce337a85c9a04/CONTRIBUTING.md).
- [Binding protocol specification](https://github.com/PalomarRegistry/PalomarPolicy/blob/96b034cc31a72a63d4f4041911dce337a85c9a04/docs/specification.md).
- [Exact minimum Lean version used in this audit](https://github.com/PalomarRegistry/PalomarSubmission/blob/65f0154ed776cd26c224254aa57b379137f28b0d/toolchains.json).

The bundled metadata schemas and taxonomy resources retain their upstream
licenses and attribution; see `scripts/metadata/policy/NOTICE.md`. The
package GPL notice does not relicense the third-party taxonomy data.
