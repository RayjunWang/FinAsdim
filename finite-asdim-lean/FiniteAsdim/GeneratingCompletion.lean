import FiniteAsdim.Completion
import FiniteAsdim.LatticeClassification
import FiniteAsdim.Torsion

/-!
# Group completions of generating submonoids

A submonoid generating an abelian group has that group as its completion.
In particular its rational rank agrees with the group's rational rank.
Images under surjective group homomorphisms continue to generate.
-/

namespace FiniteAsdim

section MonoidEquivalences

variable {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]

/-- A scalar homomorphism induces a homomorphism of group completions. -/
noncomputable def completionHom (f : M →+ N) :
    Algebra.GrothendieckAddGroup M →+ Algebra.GrothendieckAddGroup N :=
  Algebra.GrothendieckAddGroup.lift (Algebra.GrothendieckAddGroup.of.comp f)

@[simp] theorem completionHom_of (f : M →+ N) (m : M) :
    completionHom f (Algebra.GrothendieckAddGroup.of m) =
      Algebra.GrothendieckAddGroup.of (f m) := by
  exact DFunLike.congr_fun
    (Algebra.GrothendieckAddGroup.lift.left_inv (Algebra.GrothendieckAddGroup.of.comp f)) m

/-- Additive monoid equivalences induce equivalences of group completions. -/
noncomputable def completionEquiv (e : M ≃+ N) :
    Algebra.GrothendieckAddGroup M ≃+ Algebra.GrothendieckAddGroup N where
  toFun := completionHom e.toAddMonoidHom
  invFun := completionHom e.symm.toAddMonoidHom
  left_inv g := by
    obtain ⟨a, b, rfl⟩ := groupCompletion_exists_difference g
    rw [map_sub, completionHom_of, completionHom_of,
      map_sub, completionHom_of, completionHom_of]
    simp
  right_inv g := by
    obtain ⟨a, b, rfl⟩ := groupCompletion_exists_difference g
    rw [map_sub, completionHom_of, completionHom_of,
      map_sub, completionHom_of, completionHom_of]
    simp
  map_add' := (completionHom e.toAddMonoidHom).map_add

theorem monoidRank_eq_of_addEquiv (e : M ≃+ N) : monoidRank M = monoidRank N :=
  (LinearEquiv.baseChange ℤ ℚ _ _ (completionEquiv e).toIntLinearEquiv).finrank_eq

/-- The image of a monoid in its completion generates the completion. -/
theorem groupCompletionImage_generates (M : Type*) [AddCommMonoid M] :
    AddSubgroup.closure
      (AddMonoidHom.mrange (Algebra.GrothendieckAddGroup.of (M := M)) :
        Set (Algebra.GrothendieckAddGroup M)) = ⊤ := by
  apply eq_top_iff.mpr
  intro g hg
  obtain ⟨a, b, rfl⟩ := groupCompletion_exists_difference g
  apply AddSubgroup.sub_mem
  · exact AddSubgroup.subset_closure ⟨a, rfl⟩
  · exact AddSubgroup.subset_closure ⟨b, rfl⟩

end MonoidEquivalences

variable {Γ Λ : Type*} [AddCommGroup Γ] [AddCommGroup Λ]

/-- The group-completion homomorphism extending a submonoid inclusion. -/
noncomputable def completionToGroup (P : AddSubmonoid Γ) :
    Algebra.GrothendieckAddGroup P →+ Γ :=
  Algebra.GrothendieckAddGroup.lift P.subtype

@[simp] theorem completionToGroup_of (P : AddSubmonoid Γ) (p : P) :
    completionToGroup P (Algebra.GrothendieckAddGroup.of p) = (p : Γ) := by
  have h := Algebra.GrothendieckAddGroup.lift.left_inv P.subtype
  exact DFunLike.congr_fun h p

theorem completionToGroup_injective (P : AddSubmonoid Γ) :
    Function.Injective (completionToGroup P) := by
  intro x y hxy
  obtain ⟨a, b, hab⟩ := groupCompletion_exists_difference (x - y)
  have hv : completionToGroup P (x - y) = 0 := by simp [map_sub, hxy]
  rw [hab, map_sub, completionToGroup_of, completionToGroup_of] at hv
  have hab' : a = b := Subtype.ext (sub_eq_zero.mp hv)
  apply sub_eq_zero.mp
  rw [hab, hab', sub_self]

theorem completionToGroup_surjective (P : AddSubmonoid Γ)
    (hgen : AddSubgroup.closure (P : Set Γ) = ⊤) :
    Function.Surjective (completionToGroup P) := by
  intro y
  obtain ⟨a, ha, c, hc, hy⟩ := exists_positive_difference P hgen y
  refine ⟨Algebra.GrothendieckAddGroup.of (⟨a, ha⟩ : P) -
    Algebra.GrothendieckAddGroup.of (⟨c, hc⟩ : P), ?_⟩
  rw [map_sub, completionToGroup_of, completionToGroup_of]
  exact hy.symm

/-- A generating submonoid has the given ambient group as its group completion. -/
noncomputable def generatingCompletionEquiv (P : AddSubmonoid Γ)
    (hgen : AddSubgroup.closure (P : Set Γ) = ⊤) :
    Algebra.GrothendieckAddGroup P ≃+ Γ :=
  AddEquiv.ofBijective (completionToGroup P)
    ⟨completionToGroup_injective P, completionToGroup_surjective P hgen⟩

/-- The monoid rank is the rational rank of its generated ambient group. -/
theorem monoidRank_eq_groupRationalRank (P : AddSubmonoid Γ)
    (hgen : AddSubgroup.closure (P : Set Γ) = ⊤) :
    monoidRank P = groupRationalRank Γ := by
  exact (LinearEquiv.baseChange ℤ ℚ _ _
    (generatingCompletionEquiv P hgen).toIntLinearEquiv).finrank_eq

/-- A finitely generated generating submonoid makes its ambient group
finitely generated. -/
theorem generatingAmbient_finitely_generated (P : AddSubmonoid Γ) [AddMonoid.FG P]
    (hgen : AddSubgroup.closure (P : Set Γ) = ⊤) : AddGroup.FG Γ := by
  classical
  obtain ⟨S, hS⟩ := AddMonoid.FG.fg_top (M := P)
  let H := AddSubgroup.closure (P.subtype '' (S : Set P))
  have hpH : ∀ p : P, (p : Γ) ∈ H := by
    intro p
    have hp : p ∈ AddSubmonoid.closure (S : Set P) := by rw [hS]; trivial
    induction hp using AddSubmonoid.closure_induction with
    | mem p hp => exact AddSubgroup.subset_closure ⟨p, hp, rfl⟩
    | zero => exact H.zero_mem
    | add p q hp hq ihp ihq => exact H.add_mem ihp ihq
  have hH : H = ⊤ := by
    apply eq_top_iff.mpr
    intro g hg
    obtain ⟨a, ha, c, hc, hgc⟩ := exists_positive_difference P hgen g
    rw [hgc]
    exact H.sub_mem (hpH ⟨a, ha⟩) (hpH ⟨c, hc⟩)
  exact AddGroup.fg_iff.mpr ⟨P.subtype '' (S : Set P), hH, S.finite_toSet.image _⟩

/-- The group completion of a finitely generated monoid is finitely generated. -/
theorem groupCompletion_finitely_generated (M : Type*) [AddCommMonoid M] [AddMonoid.FG M] :
    AddGroup.FG (Algebra.GrothendieckAddGroup M) :=
  generatingAmbient_finitely_generated _ (groupCompletionImage_generates M)

/-- Cancellation reduction preserves the original monoid's rational rank. -/
theorem groupCompletionImage_rank (M : Type*) [AddCommMonoid M] :
    monoidRank (AddMonoidHom.mrange (Algebra.GrothendieckAddGroup.of (M := M))) =
      monoidRank M :=
  monoidRank_eq_groupRationalRank _ (groupCompletionImage_generates M)

theorem completionMapImage_generates {M : Type*} [AddCommMonoid M] (θ : AddCon M) :
    AddSubgroup.closure (AddMonoidHom.mrange (completionMap θ) :
      Set (Algebra.GrothendieckAddGroup θ.Quotient)) = ⊤ := by
  apply eq_top_iff.mpr
  intro g hg
  obtain ⟨a, b, rfl⟩ := groupCompletion_exists_difference g
  obtain ⟨p, hp⟩ := θ.mk'_surjective a
  obtain ⟨q, hq⟩ := θ.mk'_surjective b
  apply AddSubgroup.sub_mem
  · apply AddSubgroup.subset_closure
    exact ⟨p, congrArg Algebra.GrothendieckAddGroup.of hp⟩
  · apply AddSubgroup.subset_closure
    exact ⟨q, congrArg Algebra.GrothendieckAddGroup.of hq⟩

/-- Passing from a congruence to its cancellative closure preserves rank. -/
theorem cancellativeClosure_quotient_rank {M : Type*} [AddCommMonoid M] (θ : AddCon M) :
    monoidRank (cancellativeClosure θ).Quotient = monoidRank θ.Quotient :=
  (monoidRank_eq_of_addEquiv (cancellativeQuotientEquivImage θ)).trans
    (monoidRank_eq_groupRationalRank _ (completionMapImage_generates θ))

/-- Images of generating submonoids under surjective homomorphisms generate
the target group. -/
theorem image_generates_of_surjective (P : AddSubmonoid Γ)
    (hgen : AddSubgroup.closure (P : Set Γ) = ⊤)
    (f : Γ →+ Λ) (hf : Function.Surjective f) :
    AddSubgroup.closure (AddMonoidHom.mrange (f.comp P.subtype) : Set Λ) = ⊤ := by
  apply eq_top_iff.mpr
  intro y hy
  obtain ⟨g, rfl⟩ := hf y
  obtain ⟨a, ha, c, hc, hg⟩ := exists_positive_difference P hgen g
  rw [hg, map_sub]
  apply AddSubgroup.sub_mem
  · exact AddSubgroup.subset_closure ⟨(⟨a, ha⟩ : P), rfl⟩
  · exact AddSubgroup.subset_closure ⟨(⟨c, hc⟩ : P), rfl⟩

/-- The scalar image used by torsion reduction generates `Γ/T`. -/
theorem torsionScalarImage_generates (P : AddSubmonoid Γ) (T : AddSubgroup Γ)
    (hgen : AddSubgroup.closure (P : Set Γ) = ⊤) :
    AddSubgroup.closure (AddMonoidHom.mrange (torsionScalarHom P T) : Set (Γ ⧸ T)) = ⊤ := by
  apply image_generates_of_surjective P hgen (QuotientAddGroup.mk' T)
  exact Quotient.mk_surjective

/-- Rank of the scalar monoid after torsion reduction, before invoking
the torsion quotient's rank-preservation theorem. -/
theorem torsionScalarImage_rank (P : AddSubmonoid Γ) (T : AddSubgroup Γ)
    (hgen : AddSubgroup.closure (P : Set Γ) = ⊤) :
    monoidRank (AddMonoidHom.mrange (torsionScalarHom P T)) = groupRationalRank (Γ ⧸ T) :=
  monoidRank_eq_groupRationalRank _ (torsionScalarImage_generates P T hgen)

end FiniteAsdim
