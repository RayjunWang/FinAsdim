import FiniteAsdim.GeneratingCompletion
import FiniteAsdim.TorsionReduction

/-!
# Reduction to an integer lattice monoid

This module assembles the algebraic, torsion, and metric reductions.
The new action carriers are quotients and subspaces of the original
carrier, so they stay in its universe.
-/

namespace FiniteAsdim

universe u v

theorem completion_image_reduction {M : Type u} [AddCommMonoid M] [AddMonoid.FG M]
    {X : Type v} [AddAction M X]
    (hbounded : Schreier.BoundedToOneAction M X)
    (S : Finset M) (hS : AddSubmonoid.closure (S : Set M) = ⊤) :
    ∃ c : M, ∃ I : AddAction
      (AddMonoidHom.mrange (Algebra.GrothendieckAddGroup.of (M := M)))
      (ForwardImage (X := X) c),
      letI := I
      Schreier.BoundedToOneAction
        (AddMonoidHom.mrange (Algebra.GrothendieckAddGroup.of (M := M)))
        (ForwardImage (X := X) c) ∧
      ∀ n : ℕ, AsdimLE (Schreier.natMetric (X := X) (S : Set M)) n ↔
        AsdimLE (Schreier.natMetric (X := ForwardImage (X := X) c)
          (Algebra.GrothendieckAddGroup.of.mrangeRestrict '' (S : Set M))) n := by
  obtain ⟨c, hc⟩ := uniform_add_cancellation (P := M)
  letI : AddAction M (ForwardImage (X := X) c) := forwardImageAction c
  have hker : ∀ a b : M,
      Algebra.GrothendieckAddGroup.of a = Algebra.GrothendieckAddGroup.of b →
      ∀ y : ForwardImage (X := X) c, a +ᵥ y = b +ᵥ y := by
    intro a b hab y
    have hlocal : (AddLocalization.addMonoidOf (⊤ : AddSubmonoid M)) a =
        (AddLocalization.addMonoidOf (⊤ : AddSubmonoid M)) b := hab
    obtain ⟨w, hw⟩ := AddSubmonoid.LocalizationMap.eq_iff_exists _ |>.mp hlocal
    have hac : a + c = b + c := hc a b ⟨w.val, by simpa [add_comm] using hw⟩
    obtain ⟨x, hx⟩ := y.prop
    apply Subtype.ext
    change a +ᵥ y.val = b +ᵥ y.val
    rw [← hx, ← add_vadd, ← add_vadd, hac]
  let I := imageAction Algebra.GrothendieckAddGroup.of hker
  refine ⟨c, I, ?_⟩
  exact image_reduction_coarse c I Algebra.GrothendieckAddGroup.of.mrangeRestrict
    Algebra.GrothendieckAddGroup.of.mrangeRestrict_surjective
    (imageAction_apply Algebra.GrothendieckAddGroup.of hker) hbounded S hS

/-- A finitely generated generating submonoid, after removing finite
torsion, has a lattice model of the same rational rank. -/
theorem generating_reduction_to_lattice {Γ : Type u} [AddCommGroup Γ]
    (P : AddSubmonoid Γ) [AddMonoid.FG P]
    [Finite (AddCommGroup.torsion Γ)]
    (hgen : AddSubgroup.closure (P : Set Γ) = ⊤)
    {X : Type v} [AddAction P X]
    (hbounded : Schreier.BoundedToOneAction P X)
    (S : Finset P) (hS : AddSubmonoid.closure (S : Set P) = ⊤) :
    ∃ P' : AddSubmonoid (Fin (groupRationalRank Γ) → ℤ),
    ∃ Y : Type v, ∃ I : AddAction P' Y, ∃ U : Finset P',
      AddMonoid.FG P' ∧
      AddSubgroup.closure (P' : Set (Fin (groupRationalRank Γ) → ℤ)) = ⊤ ∧
      letI := I
      Schreier.BoundedToOneAction P' Y ∧
      AddSubmonoid.closure (U : Set P') = ⊤ ∧
      ∀ n : ℕ, AsdimLE (Schreier.natMetric (X := X) (S : Set P)) n ↔
        AsdimLE (Schreier.natMetric (X := Y) (U : Set P')) n := by
  classical
  letI : AddGroup.FG Γ := generatingAmbient_finitely_generated P hgen
  let T := AddCommGroup.torsion Γ
  letI : Fintype T := Fintype.ofFinite T
  obtain ⟨b, hb, B, hB⟩ := exists_positive_translate_family P T hgen
  let E := positiveTranslateSetoid (X := X) P T B
  letI : AddAction P (Quotient E) :=
    quotientAddAction E (positiveTranslateSetoid_invariant P T B)
  let Q := AddMonoidHom.mrange (torsionScalarHom P T)
  let φ : P →+ Q := (torsionScalarHom P T).mrangeRestrict
  let Y := ForwardImage (X := Quotient E) (B 0)
  obtain ⟨I, hboundedQ, hdimQ⟩ := torsion_reduction_coarse P T b B hB hbounded S hS
  letI : AddAction Q Y := I
  letI : AddMonoid.FG Q := AddMonoid.fg_of_surjective φ (torsionScalarHom P T).mrangeRestrict_surjective
  let S_Q := S.image φ
  have hSQ : AddSubmonoid.closure (S_Q : Set Q) = ⊤ :=
    scalar_finset_generators φ (torsionScalarHom P T).mrangeRestrict_surjective S hS
  have hgenQ : AddSubgroup.closure (Q : Set (Γ ⧸ T)) = ⊤ :=
    torsionScalarImage_generates P T hgen
  obtain ⟨e⟩ := torsionFree_equiv_lattice (Γ ⧸ T)
  have hrank : groupRationalRank (Γ ⧸ T) = groupRationalRank Γ := torsion_quotient_rank Γ
  rw [hrank] at e
  let f : Q →+ (Fin (groupRationalRank Γ) → ℤ) := e.toAddMonoidHom.comp Q.subtype
  let P' := AddMonoidHom.mrange f
  let ψ : Q →+ P' := f.mrangeRestrict
  have hf : Function.Injective f := e.injective.comp Subtype.val_injective
  have hker : ∀ a b : Q, f a = f b → ∀ y : Y, a +ᵥ y = b +ᵥ y := by
    intro a b hab y
    rw [hf hab]
  let I' := imageAction f hker
  letI : AddAction P' Y := I'
  have hcompat : ∀ q : Q, ∀ y : Y, ψ q +ᵥ y = q +ᵥ y := imageAction_apply f hker
  have hboundP' : Schreier.BoundedToOneAction P' Y :=
    Schreier.scalar_boundedToOneAction ψ f.mrangeRestrict_surjective hcompat hboundedQ
  let U := S_Q.image ψ
  refine ⟨P', Y, I', U, inferInstance, ?_, hboundP', ?_, ?_⟩
  · exact image_generates_of_surjective Q hgenQ e.toAddMonoidHom e.surjective
  · exact scalar_finset_generators ψ f.mrangeRestrict_surjective S_Q hSQ
  · intro n
    have hleft := hdimQ n
    rw [← Finset.coe_image] at hleft
    rw [Finset.coe_image, Schreier.scalar_metric_eq ψ hcompat]
    exact hleft

/-- Corollary 5.3, with actual actions, bounded fibers, finite generators,
and equality of every asymptotic dimension bound. -/
theorem reduction_to_lattice {M : Type u} [AddCommMonoid M] [AddMonoid.FG M]
    {X : Type v} [AddAction M X]
    (hbounded : Schreier.BoundedToOneAction M X)
    (S : Finset M) (hS : AddSubmonoid.closure (S : Set M) = ⊤) :
    ∃ P : AddSubmonoid (Fin (monoidRank M) → ℤ),
    ∃ Y : Type v, ∃ I : AddAction P Y, ∃ T : Finset P,
      AddMonoid.FG P ∧
      AddSubgroup.closure (P : Set (Fin (monoidRank M) → ℤ)) = ⊤ ∧
      letI := I
      Schreier.BoundedToOneAction P Y ∧
      AddSubmonoid.closure (T : Set P) = ⊤ ∧
      ∀ n : ℕ, AsdimLE (Schreier.natMetric (X := X) (S : Set M)) n ↔
        AsdimLE (Schreier.natMetric (X := Y) (T : Set P)) n := by
  classical
  let Γ := Algebra.GrothendieckAddGroup M
  let P := AddMonoidHom.mrange (Algebra.GrothendieckAddGroup.of (M := M))
  let φ : M →+ P := Algebra.GrothendieckAddGroup.of.mrangeRestrict
  letI : AddGroup.FG Γ := groupCompletion_finitely_generated M
  letI : Finite (AddCommGroup.torsion Γ) := torsion_subgroup_finite Γ
  obtain ⟨c, I, hb, hdim⟩ := completion_image_reduction hbounded S hS
  letI : AddAction P (ForwardImage (X := X) c) := I
  let S_P := S.image φ
  have hSP : AddSubmonoid.closure (S_P : Set P) = ⊤ :=
    scalar_finset_generators φ Algebra.GrothendieckAddGroup.of.mrangeRestrict_surjective S hS
  obtain ⟨P', Y, J, U, hFG, hgen, hbound, hU, hdim'⟩ :=
    generating_reduction_to_lattice P (groupCompletionImage_generates M) hb S_P hSP
  refine ⟨P', Y, J, U, hFG, hgen, hbound, hU, ?_⟩
  intro n
  have hleft := hdim n
  rw [← Finset.coe_image] at hleft
  exact hleft.trans (hdim' n)

end FiniteAsdim
