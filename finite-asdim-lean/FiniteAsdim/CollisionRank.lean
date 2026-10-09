import FiniteAsdim.CollisionReduction
import FiniteAsdim.GeneratingCompletion

namespace FiniteAsdim

theorem lattice_group_rank (r : ℕ) : groupRationalRank (Fin r → ℤ) = r := by
  rw [torsionFree_rank_eq]
  simp

theorem collisionImage_generates {Γ : Type*} [AddCommGroup Γ]
    (P : AddSubmonoid Γ) (hgen : AddSubgroup.closure (P : Set Γ) = ⊤) (p q : P) :
    AddSubgroup.closure (AddMonoidHom.mrange (collisionGroupMap P p q) :
      Set (Γ ⧸ AddSubgroup.zmultiples (p.val - q.val))) = ⊤ := by
  exact image_generates_of_surjective P hgen
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (p.val - q.val))) Quotient.mk_surjective

theorem collisionImage_finitely_generated {Γ : Type*} [AddCommGroup Γ]
    (P : AddSubmonoid Γ) [AddMonoid.FG P] (p q : P) :
    AddMonoid.FG (AddMonoidHom.mrange (collisionGroupMap P p q)) :=
  AddMonoid.fg_of_surjective (collisionGroupMap P p q).mrangeRestrict
    (collisionGroupMap P p q).mrangeRestrict_surjective

/-- The exact rank calculation in the last sentence of Lemma 4.4. -/
theorem collisionImage_rank {r : ℕ} (P : AddSubmonoid (Fin (r + 1) → ℤ))
    (hgen : AddSubgroup.closure (P : Set (Fin (r + 1) → ℤ)) = ⊤)
    (p q : P) (hpq : p ≠ q) :
    monoidRank (AddMonoidHom.mrange (collisionGroupMap P p q)) = r := by
  have hn : p.val - q.val ≠ 0 := fun hz => hpq (Subtype.ext (sub_eq_zero.mp hz))
  have h := cyclic_group_quotient_rank_drop (Fin (r + 1) → ℤ) hn
  rw [lattice_group_rank] at h
  rw [monoidRank_eq_groupRationalRank _ (collisionImage_generates P hgen p q)]
  omega

end FiniteAsdim
