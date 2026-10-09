import FiniteAsdim.Algebra
import FiniteAsdim.Main
import Mathlib.GroupTheory.QuotientGroup.Defs

namespace FiniteAsdim

variable {M X : Type*} [AddCommMonoid M] [AddAction M X]

/-- The congruence of scalar maps that agree everywhere in an action. -/
def actionCongruence (M X : Type*) [AddCommMonoid M] [AddAction M X] : AddCon M where
  r a b := ∀ x : X, a +ᵥ x = b +ᵥ x
  iseqv :=
    { refl := fun a x => rfl
      symm := fun h x => (h x).symm
      trans := fun h₁ h₂ x => (h₁ x).trans (h₂ x) }
  add' := by
    intro a b c e hab hce x
    simp only [add_vadd]
    rw [hce x, hab (e +ᵥ x)]

theorem actionCongruence_nsmul {p q : M} (h : ∀ x : X, p +ᵥ x = q +ᵥ x) (n : ℕ) :
    actionCongruence M X (n • p) (n • q) := by
  induction n with
  | zero => simpa using (actionCongruence M X).refl 0
  | succ n ih => simpa [succ_nsmul] using (actionCongruence M X).add ih h

section Cyclic

variable {Γ : Type*} [AddCommGroup Γ] (P : AddSubmonoid Γ)
variable [AddAction P X]

/-- The explicit map used in Lemma 4.4. -/
def collisionGroupMap (p q : P) : P →+ Γ ⧸ AddSubgroup.zmultiples (p.val - q.val) :=
  (QuotientAddGroup.mk' (AddSubgroup.zmultiples (p.val - q.val))).comp P.subtype

private theorem positive_collision_cancellation (p q a b : P) (n : ℕ)
    (hpq : ∀ x : X, p +ᵥ x = q +ᵥ x)
    (heq : n • (p.val - q.val) = a.val - b.val) :
    cancellativeClosure (actionCongruence P X) a b := by
  have hab : a + n • q = b + n • p := by
    apply Subtype.ext
    have h := (sub_eq_sub_iff_add_eq_add.mp (by simpa [nsmul_sub] using heq)).symm
    simpa [add_comm] using h
  refine ⟨n • q, ?_⟩
  rw [hab]
  exact (actionCongruence P X).add ((actionCongruence P X).refl b)
    (actionCongruence_nsmul hpq n)

/-- Every relation in the cyclic quotient is in the cancellative closure
of the action congruence once `p` and `q` act identically. This is an
explicit alternative to computing the completion of a generated relation. -/
theorem collision_kernel_cancellation (p q : P)
    (hpq : ∀ x : X, p +ᵥ x = q +ᵥ x) (a b : P)
    (hab : collisionGroupMap P p q a = collisionGroupMap P p q b) :
    cancellativeClosure (actionCongruence P X) a b := by
  have hm : a.val - b.val ∈ AddSubgroup.zmultiples (p.val - q.val) :=
    QuotientAddGroup.eq_iff_sub_mem.mp hab
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
  cases n with
  | ofNat n =>
      exact positive_collision_cancellation P p q a b n hpq (by simpa using hn)
  | negSucc n =>
      apply (cancellativeClosure (actionCongruence P X)).symm
      apply positive_collision_cancellation P p q b a (n + 1) hpq
      have h := congrArg (fun z : Γ => -z) hn
      simpa [neg_sub] using h

/-- A single global collision gives an actual descended action of the
image in the cyclic group quotient, after one uniform forward shift. -/
theorem collision_image_action [AddMonoid.FG P] (p q : P)
    (hpq : ∀ x : X, p +ᵥ x = q +ᵥ x) :
    ∃ c : P, ∃ I : AddAction (AddMonoidHom.mrange (collisionGroupMap P p q)) (ForwardImage (X := X) c),
      ∀ a : P, ∀ y : ForwardImage (X := X) c,
        @VAdd.vadd _ _ I.toVAdd ⟨collisionGroupMap P p q a, ⟨a, rfl⟩⟩ y =
        @VAdd.vadd _ _ (forwardImageAction c).toVAdd a y := by
  obtain ⟨c, hc⟩ := uniform_cancellation (actionCongruence P X)
  letI : AddAction P (ForwardImage (X := X) c) := forwardImageAction c
  have hφ : ∀ a b : P, collisionGroupMap P p q a = collisionGroupMap P p q b →
      ∀ y : ForwardImage (X := X) c, a +ᵥ y = b +ᵥ y := by
    intro a b hab y
    obtain ⟨x, hx⟩ := y.property
    apply Subtype.ext
    change a +ᵥ y.val = b +ᵥ y.val
    rw [← hx, ← add_vadd, ← add_vadd]
    exact hc a b (collision_kernel_cancellation P p q hpq a b hab) x
  exact ⟨c, imageAction (collisionGroupMap P p q) hφ, fun a y => imageAction_apply _ _ a y⟩

end Cyclic

end FiniteAsdim
