import FiniteAsdim.Rank
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.LinearAlgebra.InvariantBasisNumber
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Module.Rat
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.GroupTheory.Torsion
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Algebra.Group.Pointwise.Set.Finite
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Lattices associated with finitely generated abelian groups

The rational rank fixes the number of integer coordinates in the
classification of a finitely generated torsion-free abelian group.
-/

namespace FiniteAsdim

universe u

noncomputable def groupRationalRank (Γ : Type u) [AddCommGroup Γ] : ℕ :=
  Module.finrank ℚ (TensorProduct ℤ ℚ Γ)

theorem torsionFree_rank_eq (Γ : Type u) [AddCommGroup Γ]
    [AddGroup.FG Γ] [IsAddTorsionFree Γ] :
    groupRationalRank Γ = Module.finrank ℤ Γ := by
  letI : Module.Finite ℤ Γ := Module.Finite.iff_addGroup_fg.mpr inferInstance
  unfold groupRationalRank
  exact Module.finrank_baseChange

theorem groupRationalRank_congr {Γ Δ : Type u} [AddCommGroup Γ] [AddCommGroup Δ]
    (e : Γ ≃+ Δ) : groupRationalRank Γ = groupRationalRank Δ :=
  (e.toIntLinearEquiv.baseChange ℤ ℚ Γ Δ).finrank_eq

/-- A finitely generated torsion-free abelian group of rational rank `r`
is additively isomorphic to the integer lattice with `r` coordinates. -/
theorem torsionFree_equiv_lattice (Γ : Type u) [AddCommGroup Γ]
    [AddGroup.FG Γ] [IsAddTorsionFree Γ] :
    Nonempty (Γ ≃+ (Fin (groupRationalRank Γ) → ℤ)) := by
  letI : Module.Finite ℤ Γ := Module.Finite.iff_addGroup_fg.mpr inferInstance
  rw [torsionFree_rank_eq Γ]
  exact ⟨(Module.finBasis ℤ Γ).equivFun.toAddEquiv⟩

/-- Rationalization commutes with an additive quotient. -/
noncomputable def rationalQuotientEquiv (Γ : Type u) [AddCommGroup Γ]
    (N : Submodule ℤ Γ) :
    TensorProduct ℤ ℚ (Γ ⧸ N) ≃ₗ[ℚ]
      (TensorProduct ℤ ℚ Γ) ⧸ N.baseChange ℚ := by
  let e := TensorProduct.tensorQuotientEquiv ℚ N
  have hN : LinearMap.range (TensorProduct.map (LinearMap.id : ℚ →ₗ[ℤ] ℚ) N.subtype) =
      (N.baseChange ℚ).restrictScalars ℤ := by
    ext t
    rfl
  let e' := e.trans (Submodule.quotEquivOfEq _ _ hN)
  let ea : TensorProduct ℤ ℚ (Γ ⧸ N) ≃+
      (TensorProduct ℤ ℚ Γ) ⧸ N.baseChange ℚ := e'.toAddEquiv
  exact { ea with map_smul' := map_rat_smul ea.toAddMonoidHom }

theorem rational_span_quotient_rank_drop {V : Type u} [AddCommGroup V]
    [Module ℚ V] [Module.Finite ℚ V] {v : V} (hv : v ≠ 0) :
    Module.finrank ℚ (V ⧸ Submodule.span ℚ {v}) + 1 = Module.finrank ℚ V := by
  have h := (Submodule.span ℚ {v}).finrank_quotient_add_finrank
  rw [finrank_span_singleton hv] at h
  exact h

theorem rational_tmul_ne_zero (Γ : Type u) [AddCommGroup Γ]
    [AddGroup.FG Γ] [IsAddTorsionFree Γ] {g : Γ} (hg : g ≠ 0) :
    TensorProduct.tmul ℤ (1 : ℚ) g ≠ 0 := by
  letI : Module.Finite ℤ Γ := Module.Finite.iff_addGroup_fg.mpr inferInstance
  let b := Module.finBasis ℤ Γ
  intro h
  apply hg
  apply b.repr.injective
  ext i
  let φ : Γ →ₗ[ℤ] ℤ := (Finsupp.lapply i).comp b.repr.toLinearMap
  have hφ := congrArg (fun t => TensorProduct.rid ℤ ℚ
    (TensorProduct.map (LinearMap.id : ℚ →ₗ[ℤ] ℚ) φ t)) h
  have hi : ((b.repr g i : ℤ) : ℚ) = 0 := by
    simpa [φ, TensorProduct.map_tmul, TensorProduct.rid_tmul, zsmul_eq_mul] using hφ
  have hiz : b.repr g i = 0 := by exact_mod_cast hi
  simpa using hiz

/-- Imposing one nonzero relation on a torsion-free finitely generated
abelian group lowers its rational rank by exactly one. -/
theorem cyclic_quotient_rank_drop (Γ : Type u) [AddCommGroup Γ]
    [AddGroup.FG Γ] [IsAddTorsionFree Γ] {g : Γ} (hg : g ≠ 0) :
    groupRationalRank (Γ ⧸ Submodule.span ℤ {g}) + 1 = groupRationalRank Γ := by
  letI : Module.Finite ℤ Γ := Module.Finite.iff_addGroup_fg.mpr inferInstance
  letI : Module.Free ℤ Γ := inferInstance
  letI : Module.Finite ℚ (TensorProduct ℤ ℚ Γ) :=
    Module.Finite.of_basis ((Module.finBasis ℤ Γ).baseChange ℚ)
  let e := rationalQuotientEquiv Γ (Submodule.span ℤ {g})
  have hspan : (Submodule.span ℤ {g}).baseChange ℚ =
      Submodule.span ℚ {TensorProduct.tmul ℤ (1 : ℚ) g} := by
    rw [Submodule.baseChange_span]
    simp
  unfold groupRationalRank
  rw [e.finrank_eq, hspan]
  exact rational_span_quotient_rank_drop (rational_tmul_ne_zero Γ hg)

theorem cyclic_group_quotient_rank_drop (Γ : Type u) [AddCommGroup Γ]
    [AddGroup.FG Γ] [IsAddTorsionFree Γ] {g : Γ} (hg : g ≠ 0) :
    groupRationalRank (Γ ⧸ AddSubgroup.zmultiples g) + 1 = groupRationalRank Γ := by
  have hN : (Submodule.span ℤ {g}).toAddSubgroup = AddSubgroup.zmultiples g := by
    rw [Submodule.span_int_eq_addSubgroupClosure, AddSubgroup.zmultiples_eq_closure]
  let e := QuotientAddGroup.quotientAddEquivOfEq hN
  rw [← groupRationalRank_congr e]
  exact cyclic_quotient_rank_drop Γ hg

theorem torsion_baseChange_eq_bot (Γ : Type u) [AddCommGroup Γ] :
    (AddCommGroup.torsion Γ).toIntSubmodule.baseChange ℚ = ⊥ := by
  rw [Submodule.baseChange_eq_span]
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro t ⟨g, hg, rfl⟩
  change TensorProduct.tmul ℤ (1 : ℚ) g = 0
  obtain ⟨n, hn, hng⟩ := IsOfFinAddOrder.exists_nsmul_eq_zero
    ((AddCommGroup.mem_torsion Γ g).mp hg)
  have hnat : n • TensorProduct.tmul ℤ (1 : ℚ) g = 0 := by
    have hmap := congrArg (TensorProduct.mk ℤ ℚ Γ 1) hng
    simpa only [map_nsmul, map_zero] using hmap
  have hrat : (n : ℚ) • TensorProduct.tmul ℤ (1 : ℚ) g = 0 := by
    simpa [Nat.cast_smul_eq_nsmul] using hnat
  exact (smul_eq_zero.mp hrat).resolve_left (by exact_mod_cast (Nat.ne_of_gt hn))

/-- Removing the torsion subgroup preserves rational rank; finite
generation is unnecessary for this linear equivalence. -/
theorem torsion_quotient_rank (Γ : Type u) [AddCommGroup Γ] :
    groupRationalRank (Γ ⧸ AddCommGroup.torsion Γ) = groupRationalRank Γ := by
  let N := (AddCommGroup.torsion Γ).toIntSubmodule
  let e := (rationalQuotientEquiv Γ N).trans
    (Submodule.quotEquivOfEqBot _ (torsion_baseChange_eq_bot Γ))
  have he := e.finrank_eq
  let e' := QuotientAddGroup.quotientAddEquivOfEq
    (show N.toAddSubgroup = AddCommGroup.torsion Γ by rfl)
  rw [← groupRationalRank_congr e']
  exact he

theorem finite_torsion_generated_closure {Γ : Type u} [AddCommGroup Γ]
    (S : Set Γ) (hS : S.Finite) (ht : ∀ g ∈ S, IsOfFinAddOrder g) :
    (AddSubgroup.closure S : Set Γ).Finite := by
  induction S, hS using Set.Finite.induction_on with
  | empty => simp
  | @insert g S hg hS ih =>
      have hgfin := (ht g (Set.mem_insert g S)).finite_zmultiples
      have hSfin := ih (fun x hx => ht x (Set.mem_insert_of_mem g hx))
      have heq : (AddSubgroup.closure (insert g S) : Set Γ) =
          Set.image2 (fun x y : Γ => x + y) (AddSubgroup.zmultiples g) (AddSubgroup.closure S) := by
        ext x
        rw [← Set.singleton_union, AddSubgroup.closure_union,
          ← AddSubgroup.zmultiples_eq_closure]
        change x ∈ AddSubgroup.zmultiples g ⊔ AddSubgroup.closure S ↔
          ∃ a ∈ AddSubgroup.zmultiples g, ∃ b ∈ AddSubgroup.closure S, a + b = x
        exact AddSubgroup.mem_sup
      rw [heq]
      exact hgfin.image2 (fun x y : Γ => x + y) hSfin

/-- The torsion subgroup of a finitely generated abelian group is finite.
The proof uses Noetherianity over `ℤ` and finite sums of finite cyclic
subgroups rather than a classification of finite abelian groups. -/
theorem torsion_subgroup_finite (Γ : Type u) [AddCommGroup Γ] [AddGroup.FG Γ] :
    Finite (AddCommGroup.torsion Γ) := by
  letI : Module.Finite ℤ Γ := Module.Finite.iff_addGroup_fg.mpr inferInstance
  let N := (AddCommGroup.torsion Γ).toIntSubmodule
  have hFG : N.FG := IsNoetherian.noetherian N
  obtain ⟨S, hS⟩ := hFG
  have hclosure : AddSubgroup.closure (S : Set Γ) = AddCommGroup.torsion Γ := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, hS]
    rfl
  have ht : ∀ g ∈ (S : Set Γ), IsOfFinAddOrder g := by
    intro g hg
    apply (AddCommGroup.mem_torsion Γ g).mp
    rw [← hclosure]
    exact AddSubgroup.subset_closure hg
  have hfinite := finite_torsion_generated_closure (S : Set Γ) S.finite_toSet ht
  rw [hclosure] at hfinite
  exact hfinite.to_subtype

end FiniteAsdim
