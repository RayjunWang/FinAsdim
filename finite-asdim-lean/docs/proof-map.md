# Proof map

The reference throughout is Wang, [arXiv:2609.17177v1](https://arxiv.org/abs/2609.17177v1), Theorem 1.1. The entry points are in [Theorem.lean](../FiniteAsdim/Theorem.lean):

- `FiniteAsdim.theorem1_1` proves the bound expressed by `rankBound`.
- `FiniteAsdim.theorem1_1_closed` gives `(3 ^ (monoidRank M + 1) - 3) / 2`.
- `FiniteAsdim.theorem1_1_statement` proves the complete proposition specified by `theorem11Statement`.
- `FiniteAsdim.lattice_bound` performs induction simultaneously for all generating submonoids of a rank-`r` integer lattice and all action carriers.

## Correspondence with the paper

| Paper argument | Formal modules and representative declarations |
| --- | --- |
| Definition 2.1: extended metrics and partition dimension | [Metric.lean](../FiniteAsdim/Metric.lean): `NatMetric`, `ScalePartition`, `AsdimLE` |
| Lemmas 2.2–2.4: colored covers, finite unions, coarse invariance | [ColoredCover.lean](../FiniteAsdim/ColoredCover.lean), [FiniteUnion.lean](../FiniteAsdim/FiniteUnion.lean), [Coarse.lean](../FiniteAsdim/Coarse.lean) |
| Lemma 3.1: common futures and forward images | [Schreier.lean](../FiniteAsdim/Schreier.lean): `near_iff_common_future`; [Reductions.lean](../FiniteAsdim/Reductions.lean) |
| Lemma 3.2: invariant equivalence quotients | [Quotient.lean](../FiniteAsdim/Quotient.lean): `quotient_near_reflects`, `quotient_boundedToOneAction` |
| Generator independence and change of scalars | [Generators.lean](../FiniteAsdim/Generators.lean), [ScalarQuotient.lean](../FiniteAsdim/ScalarQuotient.lean): `asdimLE_generators_iff`, `scalar_metric_eq` |
| Lemmas 4.1–4.2: uniform cancellation | [Algebra.lean](../FiniteAsdim/Algebra.lean): `annihilatorPowers_stabilize`, `uniform_cancellation`; [Completion.lean](../FiniteAsdim/Completion.lean): `cancellativeQuotientEquivImage` |
| Lemma 4.4: collision action and rank decrease | [CollisionReduction.lean](../FiniteAsdim/CollisionReduction.lean), [CollisionRank.lean](../FiniteAsdim/CollisionRank.lean), [CollisionModel.lean](../FiniteAsdim/CollisionModel.lean): `collision_reduction_data` |
| Lemma 5.1 and Proposition 5.2: positive translates and torsion | [Algebra.lean](../FiniteAsdim/Algebra.lean): `finite_translates`; [Torsion.lean](../FiniteAsdim/Torsion.lean), [TorsionReduction.lean](../FiniteAsdim/TorsionReduction.lean): `torsion_reduction_coarse` |
| Corollary 5.3: lattice reduction with rank preserved | [GeneratingCompletion.lean](../FiniteAsdim/GeneratingCompletion.lean), [LatticeClassification.lean](../FiniteAsdim/LatticeClassification.lean), [LatticeReduction.lean](../FiniteAsdim/LatticeReduction.lean): `reduction_to_lattice` |
| Section 6: finite-scale control at locally free points | [GraphColoring.lean](../FiniteAsdim/GraphColoring.lean), [LatticePacking.lean](../FiniteAsdim/LatticePacking.lean), [FiniteWindow.lean](../FiniteAsdim/FiniteWindow.lean), [Compression.lean](../FiniteAsdim/Compression.lean), [LocalWitness.lean](../FiniteAsdim/LocalWitness.lean): `local_freeness_witness` |
| Section 7: collision decomposition and recombination | [Main.lean](../FiniteAsdim/Main.lean): `rank_step`; [Recombination.lean](../FiniteAsdim/Recombination.lean) |
| The induction and closed bound | [Theorem.lean](../FiniteAsdim/Theorem.lean), [Bounds.lean](../FiniteAsdim/Bounds.lean): `rankBound_closed` |

The proof reduces the original action to a lattice monoid, separates a finite collision union from its locally free complement at each scale, and uses the lower-rank induction hypothesis on each collision model. Recombination gives `N_(r+1) = 3 N_r + 3`, with `N_0 = 0`.

The supporting group-completion source [Grothendieck.lean](../FiniteAsdim/Grothendieck.lean) is vendored from mathlib; see [NOTICE.md](../NOTICE.md). The definitions and presentation differences are explained in [proof-review.md](proof-review.md).
