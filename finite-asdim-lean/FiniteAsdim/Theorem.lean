import FiniteAsdim.LatticeReduction
import FiniteAsdim.CollisionModel
import FiniteAsdim.CollisionRank
import FiniteAsdim.LocalWitness

/-!
# Theorem 1.1 of arXiv:2609.17177v1

The induction first treats generating submonoids of integer lattices.
Collision quotients may have torsion, so each quotient is reduced back to
a lattice model before the induction hypothesis is applied.
-/

namespace FiniteAsdim

universe u v

/-- The desired bound for all generating submonoids of the rank `r` lattice. -/
def LatticeBound (r : ℕ) : Prop :=
  ∀ (P : AddSubmonoid (Fin r → ℤ)) [AddMonoid.FG P],
    AddSubgroup.closure (P : Set (Fin r → ℤ)) = ⊤ →
    ∀ (X : Type v) [AddAction P X], Schreier.BoundedToOneAction P X →
      ∀ S : Finset P, AddSubmonoid.closure (S : Set P) = ⊤ →
        AsdimLE (Schreier.natMetric (X := X) (S : Set P)) (rankBound r)

/-- The rank induction, with all local and collision inputs discharged. -/
theorem lattice_bound (r : ℕ) : LatticeBound.{v} r := by
  induction r with
  | zero =>
    intro P _ hgen X _ hb S hS
    have hz : ∀ p : P, p = 0 := by
      intro p
      apply Subtype.ext
      funext i
      exact Fin.elim0 i
    apply asdimLE_zero_of_discrete
    intro s x y hxy
    obtain ⟨l, k, a, b, ha, hb, hn, hab⟩ := Schreier.near_iff_common_future.mp hxy
    simpa only [hz a, hz b, zero_vadd] using hab
  | succ r ih =>
    intro P _ hgen X _ hb S hS
    apply rank_step (S : Set P) r
    · intro t ht
      exact local_freeness_witness P hgen hb S hS t
    · intro p q hpq
      let Q := AddMonoidHom.mrange (collisionGroupMap P p q)
      letI : AddMonoid.FG Q := collisionImage_finitely_generated P p q
      have hrank : monoidRank Q = r := collisionImage_rank P hgen p q hpq
      obtain ⟨Y, I, T, hbQ, hT, hdim⟩ := collision_reduction_data P hb S hS p q
      letI : AddAction Q Y := I
      obtain ⟨P', Y', J, U, hFG, hgen', hb', hU, hdim'⟩ := reduction_to_lattice hbQ T hT
      letI : AddMonoid.FG P' := hFG
      letI : AddAction P' Y' := J
      have hi : LatticeBound.{v} (monoidRank Q) := hrank.symm ▸ ih
      have hY' := hi P' hgen' Y' hb' U hU
      have hY'r : AsdimLE (Schreier.natMetric (X := Y') (U : Set P')) (rankBound r) := by
        simpa only [hrank] using hY'
      exact (hdim (rankBound r)).mpr ((hdim' (rankBound r)).mpr hY'r)

/-- Theorem 1.1: a bounded-to-one action of a finitely generated commutative
monoid of rational rank `r` has asymptotic dimension at most `∑ j=1..r, 3^j`.
The finite generating set is arbitrary. -/
theorem theorem1_1 {M : Type u} [AddCommMonoid M] [AddMonoid.FG M]
    {X : Type v} [AddAction M X]
    (hbounded : Schreier.BoundedToOneAction M X)
    (S : Finset M) (hS : AddSubmonoid.closure (S : Set M) = ⊤) :
    AsdimLE (Schreier.natMetric (X := X) (S : Set M)) (rankBound (monoidRank M)) := by
  obtain ⟨P, Y, I, T, hFG, hgen, hb, hT, hdim⟩ := reduction_to_lattice hbounded S hS
  letI : AddMonoid.FG P := hFG
  letI : AddAction P Y := I
  exact (hdim _).mpr (lattice_bound (monoidRank M) P hgen Y hb T hT)

/-- The same theorem with the paper's closed form of the bound. -/
theorem theorem1_1_closed {M : Type u} [AddCommMonoid M] [AddMonoid.FG M]
    {X : Type v} [AddAction M X]
    (hbounded : Schreier.BoundedToOneAction M X)
    (S : Finset M) (hS : AddSubmonoid.closure (S : Set M) = ⊤) :
    AsdimLE (Schreier.natMetric (X := X) (S : Set M))
      ((3 ^ (monoidRank M + 1) - 3) / 2) := by
  simpa only [rankBound_closed] using theorem1_1 hbounded S hS

/-- The complete assertion previously specified in `Rank.lean` is proved. -/
theorem theorem1_1_statement : theorem11Statement.{u,v} := by
  intro M _ _ X _ hb S hS
  exact theorem1_1 hb S hS

end FiniteAsdim
