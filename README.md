# Finite asymptotic dimension of commutative monoid actions

A complete Lean 4 formalization of **Theorem 1.1** in Ruijun Wang,
[Finite Borel asymptotic dimension of bounded-to-one commutative monoid actions,
arXiv:2609.17177v1](https://arxiv.org/html/2609.17177v1) (15 September 2026).

For a finitely generated commutative monoid `M` of rational rank `r`, every
bounded-to-one action has ordinary asymptotic dimension at most

```text
3 + 3² + ⋯ + 3ʳ = (3^(r+1) - 3) / 2.
```

The proof includes the algebraic reductions, finite-window lattice construction,
finite unions, and the rank induction. There are no `sorry` placeholders,
additional axioms, or unproved geometric inputs in the final theorem.
The Borel strengthening (Corollary 1.2) is outside this repository's scope.

## Main declarations

In [FiniteAsdim/Theorem.lean](FiniteAsdim/Theorem.lean):

- `FiniteAsdim.theorem1_1`: the recursive bound `rankBound (monoidRank M)`.
- `FiniteAsdim.theorem1_1_closed`: the bound `(3^(monoidRank M + 1) - 3) / 2`.
- `FiniteAsdim.theorem1_1_statement`: proves the complete assertion specified
  by `theorem11Statement` in `Rank.lean`, for arbitrary carrier universes.

The code uses additive notation for monoids. `monoidRank M` is the dimension
over `ℚ` of `ℚ ⊗[ℤ] GrothendieckAddGroup M`. `BoundedToOneAction` requires a
finite uniform fiber bound for each action map; the bound may depend on the
monoid element. A finite generating set is explicit and arbitrary.

`Schreier.natMetric` records all integer-radius balls of the undirected
Schreier graph, including disconnected components. `AsdimLE d n` says that
at every positive integer scale there is a partition into uniformly bounded
fibers such that every ball meets at most `n+1` fibers. Integer scales suffice
for this integer-valued graph metric. See [the proof map](docs/proof-map.md)
for the correspondence with the paper.

## Build and audit

Install [elan](https://github.com/leanprover/elan), then run from the repository root:

```sh
lake exe cache get
lake build
lake env lean AxiomAudit.lean > axiom-audit.txt
python3 scripts/audit.py --axiom-log axiom-audit.txt
```

Use `python` instead of `python3` on Windows if needed. The toolchain is
**Lean 4.30.0**, and mathlib is pinned to
`c5ea00351c28e24afc9f0f84379aa41082b1188f`. All transitive dependency revisions
are recorded in `lake-manifest.json`. The first build requires internet access
to retrieve the dependencies and their compiled cache.

The source audit rejects proof placeholders and custom axiom declarations.
The Lean axiom audit checks the actual dependencies of the final theorem.
Its only foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The repository includes a GitHub Actions workflow to repeat these checks.
The recorded local results are in [docs/verification.md](docs/verification.md).

## Upload to GitHub

Extract the supplied ZIP and upload its contents to a new GitHub repository,
including `.github/workflows/lean.yml`. Keep `lake-manifest.json` and
`lean-toolchain`. Build products and dependency caches are excluded from the
archive. No machine-specific paths are needed for the normal build.

## Proof review and attribution

The formalization found no mathematical defect in the proof of Theorem 1.1.
Several arguments were made explicit or strengthened during formalization;
[docs/proof-review.md](docs/proof-review.md) explains these changes and the
scope of the review. A kernel-checked theorem also depends on the fidelity of
its definitions to the paper; that correspondence is documented separately.

Code is under Apache-2.0; see [LICENSE](LICENSE) and [NOTICE.md](NOTICE.md).
One Grothendieck-group module is vendored verbatim from the pinned mathlib
revision with its original attribution preserved. The paper is cited as the
source of the mathematics and is not bundled in the archive.

`task.md` and `computation-record.json` retain the requested scope,
environment, verification evidence, and hashes of the delivered sources.
