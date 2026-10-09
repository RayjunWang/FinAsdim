# Verification record

Verified on 9 October 2026 using Lean 4.30.0 and mathlib commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

## Formal result

`lake build` completed successfully: **2973 jobs**. Every project module,
including `FiniteAsdim.Theorem` and the root library target, was compiled.
The library contains the complete theorem for arbitrary finitely generated
commutative monoids and bounded-to-one actions, with no additional
freeness, cancellation, or local geometric hypotheses.

`lake env lean AxiomAudit.lean` completed successfully. Its 22 dependency
reports are retained in [axiom-audit.log](axiom-audit.log). The four final
declarations (`theorem1_1`, `theorem1_1_closed`, `theorem1_1_statement`,
`lattice_bound`) depend only on:

```text
propext
Classical.choice
Quot.sound
```

`python scripts/audit.py --axiom-log docs/axiom-audit.log` passed:

```text
PASS: scanned 32 Lean source files; no forbidden executable tokens.
PASS: checked 22 axiom reports; only standard Lean logical axioms occur.
```

The source check rejects `sorry`, `admit`, custom `axiom` declarations,
`unsafe`, and `native_decide` in executable Lean source. The actual theorem
dependency reports are the stronger check for proof gaps.

## Reproduction and limits

The local build reused compiled caches for the pinned dependencies. A fresh
GitHub runner was not executed during this task; the included CI workflow
downloads dependencies and repeats the build and audits after upload.
The source archive includes no dependency checkouts or binary build products.

All nine dependency repositories have clean Git status and match the
revisions in `lake-manifest.json`. A separate comparison of 9,274 tracked
Lean/configuration files against their committed Git blobs found no changes
or missing files (allowing checkout line-ending normalization). Lake's
"local changes" warnings in the logs came from restricted Git access in
the sandbox; a read-only Git check with filesystem access resolved them.

Kernel verification establishes the Lean statements under Lean's standard
foundations. Mathematical correspondence with the paper is a separate
review obligation, recorded in [proof-map.md](proof-map.md) and
[proof-review.md](proof-review.md). No numerical computation, finite test,
or external unproved theorem substitutes for the rank induction.
