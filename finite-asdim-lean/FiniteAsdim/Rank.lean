import FiniteAsdim.Grothendieck
import FiniteAsdim.Quotient
import FiniteAsdim.Bounds
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.GroupTheory.Finiteness
import Mathlib.RingTheory.Finiteness.Basic

/-!
# The exact target of Theorem 1.1

This module defines the rational rank of the group completion and states
the mathematical conclusion requested from arXiv:2609.17177. The target
is a proposition, not a proved theorem. In particular, no unproved
classification or rank-reduction claim is hidden in its hypotheses.
-/

namespace FiniteAsdim

universe u v

/-- Rationalization of the additive group completion. Reversing the
tensor factors from the paper gives the canonical rational action on
the first factor. -/
abbrev RationalCompletion (M : Type u) [AddCommMonoid M] :=
  TensorProduct ℤ ℚ (Algebra.GrothendieckAddGroup M)

/-- The rational dimension of the monoid's group completion.
For a finitely generated monoid this is a finite natural number. -/
noncomputable def monoidRank (M : Type u) [AddCommMonoid M] : ℕ :=
  Module.finrank ℚ (RationalCompletion M)

section FiniteRank

variable {M : Type u} [AddCommMonoid M]

theorem groupCompletion_exists_difference (g : Algebra.GrothendieckAddGroup M) :
    ∃ a b : M, g = Algebra.GrothendieckAddGroup.of a - Algebra.GrothendieckAddGroup.of b := by
  refine AddLocalization.ind (p := fun g => ∃ a b : M,
    g = Algebra.GrothendieckAddGroup.of a - Algebra.GrothendieckAddGroup.of b) ?_ g
  rintro ⟨a, b⟩
  refine ⟨a, b.val, ?_⟩
  change AddLocalization.mk a b = AddLocalization.addMonoidOf ⊤ a -
    AddLocalization.addMonoidOf ⊤ b.val
  rw [← AddLocalization.mk_zero_eq_addMonoidOf_mk,
    ← AddLocalization.mk_zero_eq_addMonoidOf_mk,
    Algebra.GrothendieckAddGroup.mk_sub_mk]
  simp

theorem groupCompletion_fg [AddMonoid.FG M] :
    AddGroup.FG (Algebra.GrothendieckAddGroup M) := by
  obtain ⟨S, hS⟩ := AddMonoid.FG.fg_top (M := M)
  let T := Algebra.GrothendieckAddGroup.of '' (S : Set M)
  let H := AddSubgroup.closure T
  have hm : ∀ m : M, Algebra.GrothendieckAddGroup.of m ∈ H := by
    intro m
    have hmem : m ∈ AddSubmonoid.closure (S : Set M) := by rw [hS]; trivial
    induction hmem using AddSubmonoid.closure_induction with
    | mem x hx => exact AddSubgroup.subset_closure ⟨x, hx, rfl⟩
    | zero => simp
    | add a b ha hb iha ihb => simpa using H.add_mem iha ihb
  have hH : H = ⊤ := by
    apply le_antisymm le_top
    intro g hg
    obtain ⟨a, b, rfl⟩ := groupCompletion_exists_difference g
    exact H.sub_mem (hm a) (hm b)
  exact AddGroup.fg_iff.mpr ⟨T, hH, S.finite_toSet.image _⟩

/-- The canonical map from the monoid to its rationalized completion. -/
noncomputable def rationalOf : M →+ RationalCompletion M where
  toFun m := TensorProduct.tmul ℤ (1 : ℚ) (Algebra.GrothendieckAddGroup.of m)
  map_zero' := by simp
  map_add' a b := by simp [TensorProduct.tmul_add]

theorem rational_span_eq_top (S : Finset M)
    (hS : AddSubmonoid.closure (S : Set M) = ⊤) :
    Submodule.span ℚ (rationalOf (M := M) '' (S : Set M)) = ⊤ := by
  let V := Submodule.span ℚ (rationalOf (M := M) '' (S : Set M))
  have hm : ∀ m : M, rationalOf m ∈ V := by
    intro m
    have hmem : m ∈ AddSubmonoid.closure (S : Set M) := by rw [hS]; trivial
    induction hmem using AddSubmonoid.closure_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add a b ha hb iha ihb => simpa using V.add_mem iha ihb
  apply le_antisymm le_top
  intro t ht
  clear ht
  change t ∈ V
  induction t using TensorProduct.induction_on with
  | zero => exact V.zero_mem
  | tmul q g =>
      obtain ⟨a, b, rfl⟩ := groupCompletion_exists_difference g
      rw [TensorProduct.tmul_sub]
      apply V.sub_mem
      · have h := V.smul_mem q (hm a)
        change q • TensorProduct.tmul ℤ (1 : ℚ) (Algebra.GrothendieckAddGroup.of a) ∈ V at h
        simpa [TensorProduct.smul_tmul', smul_eq_mul] using h
      · have h := V.smul_mem q (hm b)
        change q • TensorProduct.tmul ℤ (1 : ℚ) (Algebra.GrothendieckAddGroup.of b) ∈ V at h
        simpa [TensorProduct.smul_tmul', smul_eq_mul] using h
  | add a b ha hb => exact V.add_mem ha hb

theorem rationalCompletion_finite [AddMonoid.FG M] : Module.Finite ℚ (RationalCompletion M) := by
  obtain ⟨S, hS⟩ := AddMonoid.FG.fg_top (M := M)
  have hspan := rational_span_eq_top S hS
  apply Module.finite_def.mpr
  rw [← hspan]
  exact Submodule.fg_span (S.finite_toSet.image rationalOf)

end FiniteRank

/-- The exact assertion of Theorem 1.1 for arbitrary universes. A finite
generating set is explicit, and its word metric is `Schreier.natMetric`.
The proof is `theorem1_1_statement` in `Theorem.lean`. -/
def theorem11Statement : Prop :=
  ∀ (M : Type u) [AddCommMonoid M] [AddMonoid.FG M]
    (X : Type v) [AddAction M X],
    Schreier.BoundedToOneAction M X →
    ∀ S : Finset M, AddSubmonoid.closure (S : Set M) = ⊤ →
      AsdimLE (Schreier.natMetric (X := X) (S : Set M)) (rankBound (monoidRank M))

end FiniteAsdim
