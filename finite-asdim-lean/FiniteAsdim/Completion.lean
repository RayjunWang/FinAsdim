import FiniteAsdim.Algebra
import FiniteAsdim.Grothendieck

/-!
# Cancellative closure and group completion

The cancellative closure of a monoid congruence is exactly the kernel
of the map into the group completion of the congruence quotient.
Consequently its quotient is the image monoid in that group completion.
This supplies the algebraic identification used in Section 4 of
arXiv:2609.17177v1.
-/

namespace FiniteAsdim

variable {P : Type*} [AddCommMonoid P]

/-- The natural map into the group completion after imposing a congruence. -/
def completionMap (θ : AddCon P) : P →+ Algebra.GrothendieckAddGroup θ.Quotient :=
  Algebra.GrothendieckAddGroup.of.comp θ.mk'

/-- Equality in the group completion is equality after a common translation. -/
theorem completionMap_eq_iff (θ : AddCon P) (a b : P) :
    completionMap θ a = completionMap θ b ↔ cancellativeClosure θ a b := by
  change (AddLocalization.addMonoidOf (⊤ : AddSubmonoid θ.Quotient)) (a : θ.Quotient) =
      (AddLocalization.addMonoidOf (⊤ : AddSubmonoid θ.Quotient)) (b : θ.Quotient) ↔ _
  rw [AddSubmonoid.LocalizationMap.eq_iff_exists]
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨v, hv⟩ := θ.mk'_surjective u.val
    refine ⟨v, Quotient.exact ?_⟩
    simpa [← hv, add_comm] using hu
  · rintro ⟨v, hv⟩
    refine ⟨⟨(v : θ.Quotient), AddSubmonoid.mem_top _⟩, ?_⟩
    simpa [add_comm] using (Quotient.sound hv :
      ((a + v : P) : θ.Quotient) = ((b + v : P) : θ.Quotient))

/-- The cancellative closure is the kernel congruence of the completion map. -/
theorem cancellativeClosure_eq_kernel (θ : AddCon P) :
    cancellativeClosure θ = AddCon.ker (completionMap θ) := by
  apply AddCon.ext
  intro a b
  exact (completionMap_eq_iff θ a b).symm

/-- The quotient by the cancellative closure is the image monoid in
the group completion. -/
noncomputable def cancellativeQuotientEquivImage (θ : AddCon P) :
    (cancellativeClosure θ).Quotient ≃+ AddMonoidHom.mrange (completionMap θ) :=
  (AddCon.congr (cancellativeClosure_eq_kernel θ)).trans
    (AddCon.quotientKerEquivRange (completionMap θ))

/-- In particular, the quotient by the cancellative closure is cancellative. -/
instance cancellativeClosure_quotient_isCancelAdd (θ : AddCon P) :
    IsCancelAdd (cancellativeClosure θ).Quotient :=
  (cancellativeQuotientEquivImage θ).injective.isCancelAdd
    (cancellativeQuotientEquivImage θ) (cancellativeQuotientEquivImage θ).map_add

end FiniteAsdim
