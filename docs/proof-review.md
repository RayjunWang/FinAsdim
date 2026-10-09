# Proof review

The source is Ruijun Wang, *Finite Borel asymptotic dimension of bounded-to-one commutative monoid actions*, [arXiv:2609.17177v1](https://arxiv.org/abs/2609.17177v1), submitted 15 September 2026. This review concerns the ordinary asymptotic dimension argument for Theorem 1.1, including its supporting arguments in Sections 2–7.

## Statement and scope

For a finitely generated commutative monoid `M`, let

\[
r=\dim_{\mathbb Q}(M^{\mathrm{gp}}\otimes_{\mathbb Z}\mathbb Q).
\]

Every bounded-to-one action of `M` has ordinary asymptotic dimension at most

\[
N_r=\sum_{j=1}^{r}3^j=\frac{3^{r+1}-3}{2}.
\]

The Lean statement permits arbitrary carriers and an arbitrary explicit finite generating set. Each action map has its own finite uniform fiber bound. It assumes neither injectivity nor freeness.

The Borel conclusion in Corollary 1.2 and the hyperfiniteness conclusion in Corollary 1.3 are outside this formalization. In particular, it does not formalize the external theorem identifying Borel and ordinary asymptotic dimensions.

## Mathematical review

No mathematical defect was identified in the Theorem 1.1 argument reviewed here. The formalization makes the following dependencies explicit:

- Common-future paths use commutativity without cancelling action maps. Forward-invariant subspaces retain their ambient metric.
- Uniform cancellation uses finite generation and a Noetherian monoid algebra. It is proved, rather than supplied as a hypothesis.
- The torsion relation has uniformly bounded classes. Its quotient action and the subsequent forward-image action are constructed, with bounded fibers preserved.
- Collision rank decreases only after passing to a torsion-free group. The induction reduces each collision quotient to a lattice again, since cyclic quotients can acquire torsion.
- The finite auxiliary coloring and its markers depend on the scale and action. Their number of colors does not enter the dimension bound.

## Formal proof refinements

1. **Coefficient ring.** Uniform cancellation uses `ℤ[P/θ]` instead of the paper's `ℚ[P/θ]`. Both rings are Noetherian in this setting, and monoid basis elements remain distinct.
2. **Torsion chains.** The invariant is strengthened to `∃ t, ∀ u, F u x = F (u + t) y`. Its simultaneous quantifier makes symmetry and composition explicit; setting `u = 0` gives the paper's common-future equation.
3. **Quotient distance.** Commutativity gives the stronger bound `d_X(x,y) ≤ d_Z(πx,πy) + D`. The paper's `(D+1)d_Z + D` estimate also follows.
4. **Finite windows.** Marker counting is proved assuming proper colors only on the cube containing the outputs. This avoids needing a globally proper extension of a local pattern in the application; the paper's extension argument is valid with its degree bound.
5. **Cyclic relations.** Membership in the cyclic subgroup is handled by both signs of the integer multiple. A positive multiple is absorbed by a positive translation; a negative multiple reverses the relation. This explicitly establishes the kernel relations needed for scalar descent.

These are changes to the proof presentation, not counterexamples or repairs to the stated theorem. Intermediate lemmas with explicit local hypotheses are discharged in the final theorem.

## Meaning of the formal definitions

`NatMetric.near s x y` represents distance at most the natural number `s`. Points in different graph components are never near at any finite radius. Thus the model includes infinite distances without doing arithmetic with infinity.

`ScalePartition` supplies a label function on the whole carrier. Its nonempty fibers are the partition parts; equal labels imply a uniform diameter bound. The extended cardinal `encard` of the label image of each ball counts the parts that ball meets, not the points in those parts. An infinite label image has infinite cardinality. The total label type need not be finite. `AsdimLE` requests these partitions at every positive integer scale.

`monoidRank` uses `ℚ ⊗_ℤ Mᵍᵖ`, with the rational factor first to carry the natural `ℚ`-module structure. Tensor symmetry identifies this rank with the paper's convention. Finite dimensionality follows from finite generation.
