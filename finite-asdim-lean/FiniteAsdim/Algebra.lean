import Mathlib.RingTheory.FiniteType
import Mathlib.GroupTheory.Congruence.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic

/-!
# Algebraic reductions

This file proves the uniform cancellation assertion of Lemma 4.2 of
arXiv:2609.17177v1. The coefficient ring is `ℤ` instead of `ℚ`; the
Noetherian and basis independence argument is unchanged.
-/

namespace FiniteAsdim

section Noetherian

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

private def mulLinear (z : R) : R →ₗ[R] R where
  toFun x := z * x
  map_add' x y := mul_add z x y
  map_smul' r x := by simp [smul_eq_mul, mul_left_comm]

/-- The annihilator ideals of the powers of a fixed element stabilize. -/
theorem annihilatorPowers_stabilize (z : R) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ x : R,
      z ^ n * x = 0 ↔ z ^ N * x = 0 := by
  let K : ℕ →o Submodule R R :=
    { toFun := fun n => LinearMap.ker (mulLinear (z ^ n))
      monotone' := monotone_nat_of_le_succ (fun n x hx => by
        change z ^ n * x = 0 at hx
        change z ^ (n + 1) * x = 0
        rw [pow_succ, mul_right_comm, hx, zero_mul]) }
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance K
  refine ⟨N, fun n hn x => ?_⟩
  change x ∈ K n ↔ x ∈ K N
  rw [hN n hn]

end Noetherian

section Additive

variable {P : Type*} [AddCommMonoid P]

/-- The cancellative closure of an additive congruence. -/
def cancellativeClosure (θ : AddCon P) : AddCon P where
  r a b := ∃ u : P, θ (a + u) (b + u)
  iseqv :=
    { refl := fun a => ⟨0, by simpa using θ.refl a⟩
      symm := fun ⟨u, hu⟩ => ⟨u, θ.symm hu⟩
      trans := fun {a b d} ⟨u, hu⟩ ⟨v, hv⟩ =>
        ⟨u + v, θ.trans
          (by simpa [add_assoc] using θ.add hu (θ.refl v))
          (by simpa [add_assoc, add_comm, add_left_comm] using θ.add hv (θ.refl u))⟩ }
  add' := by
    rintro a b d e ⟨u, hu⟩ ⟨v, hv⟩
    exact ⟨u + v, by simpa [add_assoc, add_comm, add_left_comm] using θ.add hu hv⟩

@[simp] theorem cancellativeClosure_iff (θ : AddCon P) (a b : P) :
    cancellativeClosure θ a b ↔ ∃ u : P, θ (a + u) (b + u) := Iff.rfl

/-- Translation cancels in the cancellative closure. -/
theorem cancellativeClosure_add_iff (θ : AddCon P) (a b d : P) :
    cancellativeClosure θ (a + d) (b + d) ↔ cancellativeClosure θ a b := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨d + u, by simpa [add_assoc] using hu⟩
  · intro hab
    simpa using (cancellativeClosure θ).add hab ((cancellativeClosure θ).refl d)

/-- A finite generating set has a cofinal positive diagonal. No cancellation
is used in this statement. -/
theorem exists_cofinal_diagonal [AddMonoid.FG P] :
    ∃ h : P, ∀ u : P, ∃ n : ℕ, ∃ v : P, u + v = n • h := by
  classical
  obtain ⟨S, hS⟩ := (AddMonoid.FG.fg_top (M := P))
  refine ⟨∑ s ∈ S, s, fun u => ?_⟩
  have hu : u ∈ AddSubmonoid.closure (S : Set P) := by rw [hS]; trivial
  induction hu using AddSubmonoid.closure_induction with
  | mem x hx =>
      refine ⟨1, ∑ s ∈ S.erase x, s, ?_⟩
      simpa using (Finset.add_sum_erase S (fun s : P => s) hx)
  | zero => exact ⟨0, 0, by simp⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨n, v, hv⟩ := ihx
      obtain ⟨m, w, hw⟩ := ihy
      refine ⟨n + m, v + w, ?_⟩
      rw [add_nsmul]
      rw [← hv, ← hw]
      ac_rfl

/-- Uniform cancellation in a finitely generated commutative monoid:
one translation witnesses every equality after some translation. -/
theorem uniform_add_cancellation [AddMonoid.FG P] :
    ∃ c : P, ∀ a b : P,
      (∃ u : P, a + u = b + u) → a + c = b + c := by
  let A := AddMonoidAlgebra ℤ P
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  let e : P → A := AddMonoidAlgebra.of' ℤ P
  have e_add (x y : P) : e (x + y) = e x * e y := by
    exact (AddMonoidAlgebra.of ℤ P).map_mul
      (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)
  have e_inj : Function.Injective e := by
    intro x y hxy
    exact Multiplicative.ofAdd.injective
      (AddMonoidAlgebra.of_injective (R := ℤ) (M := P) hxy)
  obtain ⟨h, hh⟩ := exists_cofinal_diagonal (P := P)
  let z : A := e h
  have e_nsmul (n : ℕ) : e (n • h) = z ^ n := by
    induction n with
    | zero =>
        simp only [zero_nsmul, pow_zero]
        exact (AddMonoidAlgebra.of ℤ P).map_one
    | succ n ihn => rw [succ_nsmul, e_add, ihn, pow_succ]
  obtain ⟨N, hN⟩ := annihilatorPowers_stabilize z
  refine ⟨N • h, fun a b ⟨u, hu⟩ => ?_⟩
  obtain ⟨n, v, hv⟩ := hh u
  have hlarge : a + (n + N) • h = b + (n + N) • h := by
    have ht := congrArg (fun x : P => x + v + N • h) hu
    simpa [add_assoc, hv, add_nsmul] using ht
  have hzero : z ^ (n + N) * (e a - e b) = 0 := by
    rw [mul_sub]
    apply sub_eq_zero.mpr
    rw [← e_nsmul, mul_comm _ (e a), mul_comm _ (e b), ← e_add, ← e_add]
    exact congrArg e hlarge
  have hsmall : z ^ N * (e a - e b) = 0 :=
    (hN (n + N) (Nat.le_add_left N n) (e a - e b)).mp hzero
  apply e_inj
  rw [e_add, e_add, e_nsmul]
  apply sub_eq_zero.mp
  simpa [mul_sub, mul_comm] using hsmall

/-- Lemma 4.2: a fixed translation realizes the cancellative closure of
any congruence on a finitely generated commutative monoid. -/
theorem uniform_cancellation [AddMonoid.FG P] (θ : AddCon P) :
    ∃ c : P, ∀ a b : P,
      cancellativeClosure θ a b → θ (a + c) (b + c) := by
  letI : AddMonoid.FG θ.Quotient :=
    AddMonoid.fg_of_surjective θ.mk' Quotient.mk''_surjective
  obtain ⟨c, hc⟩ := uniform_add_cancellation (P := θ.Quotient)
  obtain ⟨d, hd⟩ := Quotient.mk''_surjective c
  refine ⟨d, fun a b ⟨u, hu⟩ => ?_⟩
  have hquot : (a : θ.Quotient) + c = (b : θ.Quotient) + c := by
    apply hc
    exact ⟨(u : θ.Quotient), Quotient.sound hu⟩
  exact Quotient.exact (by simpa [← hd] using hquot)

/-- The forward image under the uniform translation satisfies all relations
of the cancellative closure. This is the action consequence of Lemma 4.2. -/
theorem uniform_cancellation_action [AddMonoid.FG P] {X : Type*} [AddAction P X]
    (θ : AddCon P)
    (hθ : ∀ a b : P, θ a b → ∀ x : X, a +ᵥ x = b +ᵥ x) :
    ∃ c : P, ∀ a b : P, cancellativeClosure θ a b →
      ∀ x : X, a +ᵥ (c +ᵥ x) = b +ᵥ (c +ᵥ x) := by
  obtain ⟨c, hc⟩ := uniform_cancellation θ
  refine ⟨c, fun a b hab x => ?_⟩
  simpa [add_vadd] using hθ (a + c) (b + c) (hc a b hab) x

/-- An action satisfying a congruence descends to its monoid quotient. -/
@[reducible] def congruenceAction {X : Type*} [AddAction P X] (θ : AddCon P)
    (hθ : ∀ a b : P, θ a b → ∀ x : X, a +ᵥ x = b +ᵥ x) :
    AddAction θ.Quotient X where
  vadd p x := Quotient.liftOn p (fun a : P => a +ᵥ x) (fun a b hab => hθ a b hab x)
  zero_vadd x := zero_vadd P x
  add_vadd := by
    intro p q x
    induction p using Quotient.inductionOn with
    | _ a =>
        induction q using Quotient.inductionOn with
        | _ b => exact add_vadd a b x

private noncomputable def imageRepresentative {Q : Type*} [AddCommMonoid Q]
    (f : P →+ Q) (q : AddMonoidHom.mrange f) : P :=
  Classical.choose q.prop

private theorem imageRepresentative_spec {Q : Type*} [AddCommMonoid Q]
    (f : P →+ Q) (q : AddMonoidHom.mrange f) : f (imageRepresentative f q) = q.val :=
  Classical.choose_spec q.prop

/-- An action descends to the image of any scalar homomorphism whose
kernel relations it satisfies. -/
@[reducible] noncomputable def imageAction {Q X : Type*} [AddCommMonoid Q]
    [AddAction P X] (f : P →+ Q)
    (hker : ∀ a b : P, f a = f b → ∀ x : X, a +ᵥ x = b +ᵥ x) :
    AddAction (AddMonoidHom.mrange f) X where
  vadd q x := imageRepresentative f q +ᵥ x
  zero_vadd x := by
    have heq : f (imageRepresentative f 0) = f 0 := by
      rw [imageRepresentative_spec, map_zero]; rfl
    exact (hker _ 0 heq x).trans (zero_vadd P x)
  add_vadd q r x := by
    have heq : f (imageRepresentative f (q + r)) =
        f (imageRepresentative f q + imageRepresentative f r) := by
      rw [imageRepresentative_spec, map_add, imageRepresentative_spec, imageRepresentative_spec]
      rfl
    exact (hker _ _ heq x).trans (add_vadd _ _ x)

/-- The descended image action agrees with the original action on every
scalar coming from the original monoid. -/
theorem imageAction_apply {Q X : Type*} [AddCommMonoid Q] [AddAction P X]
    (f : P →+ Q)
    (hker : ∀ a b : P, f a = f b → ∀ x : X, a +ᵥ x = b +ᵥ x)
    (a : P) (x : X) :
    @VAdd.vadd _ _ (imageAction f hker).toVAdd (f.mrangeRestrict a) x = a +ᵥ x :=
  hker _ a (imageRepresentative_spec f (f.mrangeRestrict a)) x

/-- The forward image of a monoid action under a single action map. -/
def ForwardImage {X : Type*} [AddAction P X] (c : P) :=
  {y : X // ∃ x : X, c +ᵥ x = y}

/-- Commutativity makes the forward image invariant. -/
@[reducible] def forwardImageAction {X : Type*} [AddAction P X] (c : P) :
    AddAction P (ForwardImage (X := X) c) where
  vadd p y := ⟨p +ᵥ y.val, by
    obtain ⟨x, hx⟩ := y.prop
    refine ⟨p +ᵥ x, ?_⟩
    calc
      c +ᵥ (p +ᵥ x) = (c + p) +ᵥ x := (add_vadd c p x).symm
      _ = (p + c) +ᵥ x := by rw [add_comm c p]
      _ = p +ᵥ (c +ᵥ x) := add_vadd p c x
      _ = p +ᵥ y.val := congrArg (fun z : X => p +ᵥ z) hx⟩
  zero_vadd y := Subtype.ext (zero_vadd P y.val)
  add_vadd p q y := Subtype.ext (add_vadd p q y.val)

/-- The action on the forward image under the uniform translation
actually descends to the cancellative-closure quotient. -/
theorem exists_cancellative_closure_action [AddMonoid.FG P] {X : Type*}
    [AddAction P X] (θ : AddCon P)
    (hθ : ∀ a b : P, θ a b → ∀ x : X, a +ᵥ x = b +ᵥ x) :
    ∃ c : P, ∃ I : AddAction (cancellativeClosure θ).Quotient (ForwardImage (X := X) c),
      ∀ a : P, ∀ y : ForwardImage (X := X) c,
        @VAdd.vadd _ _ I.toVAdd (a : (cancellativeClosure θ).Quotient) y =
        @VAdd.vadd _ _ (forwardImageAction c).toVAdd a y := by
  obtain ⟨c, hc⟩ := uniform_cancellation_action θ hθ
  letI : AddAction P (ForwardImage (X := X) c) := forwardImageAction c
  have hcan : ∀ a b : P, cancellativeClosure θ a b →
      ∀ y : ForwardImage (X := X) c, a +ᵥ y = b +ᵥ y := by
    intro a b hab y
    obtain ⟨x, hx⟩ := y.prop
    apply Subtype.ext
    change a +ᵥ y.val = b +ᵥ y.val
    rw [← hx]
    exact hc a b hab x
  exact ⟨c, congruenceAction (cancellativeClosure θ) hcan, fun a y => rfl⟩

end Additive

section FiniteTranslates

variable {Γ : Type*} [AddCommGroup Γ]

/-- A submonoid that generates an abelian group supplies a positive
numerator and denominator for every group element. -/
theorem exists_positive_difference (P : AddSubmonoid Γ)
    (hgen : AddSubgroup.closure (P : Set Γ) = ⊤) (f : Γ) :
    ∃ a ∈ P, ∃ c ∈ P, f = a - c := by
  have hf : f ∈ AddSubgroup.closure (P : Set Γ) := by rw [hgen]; trivial
  induction hf using AddSubgroup.closure_induction with
  | mem x hx => exact ⟨x, hx, 0, P.zero_mem, by simp⟩
  | zero => exact ⟨0, P.zero_mem, 0, P.zero_mem, by simp⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨a, ha, c, hc, rfl⟩ := ihx
      obtain ⟨b, hb, d, hd, rfl⟩ := ihy
      exact ⟨a + b, P.add_mem ha hb, c + d, P.add_mem hc hd, by abel⟩
  | neg x hx ihx =>
      obtain ⟨a, ha, c, hc, rfl⟩ := ihx
      exact ⟨c, hc, a, ha, by abel⟩

/-- Lemma 5.1: every finite set in the group has a positive translate
contained in a submonoid that generates the group. -/
theorem finite_translates (P : AddSubmonoid Γ)
    (hgen : AddSubgroup.closure (P : Set Γ) = ⊤) (F : Finset Γ) :
    ∃ b ∈ P, ∀ f ∈ F, b + f ∈ P := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨0, P.zero_mem, by simp⟩
  | @insert f F hf ih =>
      obtain ⟨a, ha, c, hc, hfac⟩ := exists_positive_difference P hgen f
      obtain ⟨b, hb, hbf⟩ := ih
      refine ⟨b + c, P.add_mem hb hc, ?_⟩
      intro g hg
      rcases Finset.mem_insert.mp hg with hgf | hgF
      · subst g
        have heq : b + c + f = b + a := by rw [hfac]; abel
        rw [heq]
        exact P.add_mem hb ha
      · have heq : b + c + g = c + (b + g) := by abel
        rw [heq]
        exact P.add_mem hc (hbf g hgF)

/-- The finite-set formulation of Lemma 5.1. -/
theorem finite_set_translates (P : AddSubmonoid Γ)
    (hgen : AddSubgroup.closure (P : Set Γ) = ⊤)
    (F : Set Γ) (hF : F.Finite) :
    ∃ b ∈ P, ∀ f ∈ F, b + f ∈ P := by
  obtain ⟨b, hb, hbf⟩ := finite_translates P hgen hF.toFinset
  exact ⟨b, hb, fun f hf => hbf f (hF.mem_toFinset.mpr hf)⟩

end FiniteTranslates

end FiniteAsdim
