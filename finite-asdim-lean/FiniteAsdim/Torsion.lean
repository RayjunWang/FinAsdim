import FiniteAsdim.Algebra
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.GroupTheory.QuotientGroup.Basic
import FiniteAsdim.Quotient

/-!
# The finite torsion equivalence relation

The shift invariant and the uniform fiber estimates from Proposition 5.2
of arXiv:2609.17177v1 are proved here. `FiberBound` uses finite covers of
fibers; in particular it cannot assign a finite cardinal to an infinite fiber.
-/

namespace FiniteAsdim

/-- Every fiber is contained in a finite set of cardinality at most `k`. -/
def FiberBound {X Y : Type*} (f : X → Y) (k : ℕ) : Prop :=
  ∀ y : Y, ∃ F : Finset X, F.card ≤ k ∧ ∀ x : X, f x = y → x ∈ F

/-- Every equivalence class is contained in a finite set of cardinality
at most `C`. -/
def ClassBound {X : Type*} (E : X → X → Prop) (C : ℕ) : Prop :=
  ∀ x : X, ∃ F : Finset X, F.card ≤ C ∧ ∀ y : X, E x y → y ∈ F

/-- Finite-cover fiber bounds are exactly the extended-cardinal bounds
used in the main action hypotheses. -/
theorem fiberBound_iff_encard {X Y : Type*} (f : X → Y) (k : ℕ) :
    FiberBound f k ↔ ∀ y : Y, (f ⁻¹' {y}).encard ≤ (k : ℕ∞) := by
  classical
  constructor
  · intro hf y
    obtain ⟨F, hFcard, hFmem⟩ := hf y
    calc
      (f ⁻¹' {y}).encard ≤ (F : Set X).encard :=
        Set.encard_mono (fun x hx => hFmem x hx)
      _ = (F.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard F
      _ ≤ (k : ℕ∞) := by exact_mod_cast hFcard
  · intro hf y
    have hfinite := Set.finite_of_encard_le_coe (hf y)
    refine ⟨hfinite.toFinset, ?_, fun x hx => hfinite.mem_toFinset.mpr hx⟩
    have hcard := hf y
    rw [hfinite.encard_eq_coe_toFinset_card] at hcard
    exact_mod_cast hcard

theorem boundedToOne_iff_fiberBound {X Y : Type*} (f : X → Y) :
    Schreier.BoundedToOne f ↔ ∃ k : ℕ, FiberBound f k := by
  simp only [Schreier.BoundedToOne, fiberBound_iff_encard]

/-- Class bounds imply the cardinal class bounds used for metric quotients. -/
theorem classBound_encard {X : Type*} (E : Setoid X) (C : ℕ)
    (hC : ClassBound E C) : ∀ y : X, {x : X | E x y}.encard ≤ (C : ℕ∞) := by
  intro y
  obtain ⟨F, hFcard, hFmem⟩ := hC y
  calc
    {x : X | E x y}.encard ≤ (F : Set X).encard :=
      Set.encard_mono (fun x hx => hFmem x (E.symm hx))
    _ = (F.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard F
    _ ≤ (C : ℕ∞) := by exact_mod_cast hFcard

/-- Restricting a function to an invariant subset preserves its fiber bound. -/
theorem fiberBound_restrict {X : Type*} (f : X → X) (k : ℕ)
    (hf : FiberBound f k) (S : Set X) (hS : ∀ x ∈ S, f x ∈ S) :
    FiberBound (fun x : S => (⟨f x.val, hS x.val x.prop⟩ : S)) k := by
  classical
  intro y
  obtain ⟨F, hFcard, hFmem⟩ := hf y.val
  refine ⟨F.subtype (fun x => x ∈ S), ?_, ?_⟩
  · rw [Finset.card_subtype]
    exact (Finset.card_filter_le _ _).trans hFcard
  · intro x hxy
    exact Finset.mem_subtype.mpr (hFmem x.val (congrArg Subtype.val hxy))

section Shift

variable {T X : Type*} [AddCommGroup T]

/-- An elementary torsion relation. -/
def TorsionEdge (F : T → X → X) (x y : X) : Prop :=
  ∃ z : X, ∃ t : T, x = F 0 z ∧ y = F t z

/-- The universal index shift carried along an equivalence chain. -/
def FamilyShift (F : T → X → X) (x y : X) : Prop :=
  ∃ t : T, ∀ u : T, F u x = F (u + t) y

theorem familyShift_refl (F : T → X → X) (x : X) : FamilyShift F x x :=
  ⟨0, fun u => by simp⟩

theorem familyShift_symm (F : T → X → X) {x y : X}
    (h : FamilyShift F x y) : FamilyShift F y x := by
  obtain ⟨t, ht⟩ := h
  refine ⟨-t, fun u => ?_⟩
  simpa [sub_eq_add_neg] using (ht (u - t)).symm

theorem familyShift_trans (F : T → X → X) {x y z : X}
    (hxy : FamilyShift F x y) (hyz : FamilyShift F y z) : FamilyShift F x z := by
  obtain ⟨t, ht⟩ := hxy
  obtain ⟨v, hv⟩ := hyz
  exact ⟨t + v, fun u => by rw [ht u, hv (u + t), add_assoc]⟩

/-- The strengthened form of equation (9): the index identity holds
simultaneously for every `u`, so it survives arbitrary chains. -/
theorem eqvGen_torsion_shift (F : T → X → X)
    (hF : ∀ u t : T, ∀ z : X, F u (F 0 z) = F (u - t) (F t z))
    {x y : X} (h : Relation.EqvGen (TorsionEdge F) x y) : FamilyShift F x y := by
  induction h with
  | rel x y hxy =>
      obtain ⟨z, t, rfl, rfl⟩ := hxy
      exact ⟨-t, fun u => by simpa [sub_eq_add_neg] using hF u t z⟩
  | refl x => exact familyShift_refl F x
  | symm x y hxy ih => exact familyShift_symm F ih
  | trans x y z hxy hyz ihxy ihyz => exact familyShift_trans F ihxy ihyz

/-- Equation (9) in the paper. -/
theorem eqvGen_torsion_common_future (F : T → X → X)
    (hF : ∀ u t : T, ∀ z : X, F u (F 0 z) = F (u - t) (F t z))
    {x y : X} (h : Relation.EqvGen (TorsionEdge F) x y) :
    ∃ t : T, F 0 x = F t y := by
  obtain ⟨t, ht⟩ := eqvGen_torsion_shift F hF h
  exact ⟨t, by simpa using ht 0⟩

/-- A map commuting with the entire translated family preserves the
generated equivalence relation. -/
theorem eqvGen_torsion_map (F : T → X → X) (g : X → X)
    (hg : ∀ t : T, ∀ x : X, g (F t x) = F t (g x))
    {x y : X} (h : Relation.EqvGen (TorsionEdge F) x y) :
    Relation.EqvGen (TorsionEdge F) (g x) (g y) := by
  induction h with
  | rel x y hxy =>
      obtain ⟨z, t, rfl, rfl⟩ := hxy
      apply Relation.EqvGen.rel
      exact ⟨g z, t, hg 0 z, hg t z⟩
  | refl x => exact Relation.EqvGen.refl (g x)
  | symm x y hxy ih => exact Relation.EqvGen.symm (g x) (g y) ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact Relation.EqvGen.trans (g x) (g y) (g z) ihxy ihyz

/-- Equation (10)'s cardinal estimate: a class lies in the union of
the finitely many fibers supplied by the shift invariant. -/
theorem classBound_of_shift [Fintype T] (F : T → X → X) (k : T → ℕ)
    (hF : ∀ u t : T, ∀ z : X, F u (F 0 z) = F (u - t) (F t z))
    (hk : ∀ t : T, FiberBound (F t) (k t)) :
    ClassBound (Relation.EqvGen (TorsionEdge F)) (∑ t : T, k t) := by
  classical
  intro x
  choose B hBcard hBmem using fun t => hk t (F 0 x)
  refine ⟨Finset.univ.biUnion B, ?_, ?_⟩
  · exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun t _ => hBcard t)
  · intro y hxy
    obtain ⟨t, ht⟩ := eqvGen_torsion_common_future F hF hxy
    exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ t, hBmem t y ht.symm⟩

end Shift

section Quotient

variable {X : Type*}

/-- A bounded equivalence quotient preserves bounded fibers. This is
the cardinal part of Lemma 3.2. -/
theorem quotient_fiberBound (E : Setoid X) (C k : ℕ)
    (hC : ClassBound E C) (f : X → X) (hf : FiberBound f k)
    (hrespect : ∀ a b : X, E a b → E (f a) (f b)) :
    FiberBound (Quotient.map f hrespect : Quotient E → Quotient E) (C * k) := by
  classical
  intro q
  induction q using Quotient.inductionOn with
  | _ y =>
      obtain ⟨B, hBcard, hBmem⟩ := hC y
      choose A hAcard hAmem using hf
      let U := B.biUnion A
      refine ⟨U.image (Quotient.mk E), ?_, ?_⟩
      · calc
          (U.image (Quotient.mk E)).card ≤ U.card := Finset.card_image_le
          _ ≤ B.card * k := Finset.card_biUnion_le_card_mul B A k (fun z _ => hAcard z)
          _ ≤ C * k := Nat.mul_le_mul_right k hBcard
      · intro p hp
        induction p using Quotient.inductionOn with
        | _ x =>
            have hxy : E (f x) y := Quotient.exact hp
            have hxU : x ∈ U := Finset.mem_biUnion.mpr
              ⟨f x, hBmem (f x) (E.symm hxy), hAmem (f x) x rfl⟩
            exact Finset.mem_image.mpr ⟨x, hxU, rfl⟩

end Quotient

section QuotientAction

variable {P X : Type*} [AddCommMonoid P] [AddAction P X]

/-- The action induced on an invariant equivalence quotient. -/
@[reducible] def quotientAddAction (E : Setoid X)
    (hE : ∀ p : P, ∀ x y : X, E x y → E (p +ᵥ x) (p +ᵥ y)) :
    AddAction P (Quotient E) where
  vadd p q := Quotient.map (fun x : X => p +ᵥ x) (hE p) q
  zero_vadd := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x => exact congrArg (Quotient.mk E) (zero_vadd P x)
  add_vadd := by
    intro p r q
    induction q using Quotient.inductionOn with
    | _ x => exact congrArg (Quotient.mk E) (add_vadd p r x)

/-- The induced quotient action is bounded-to-one whenever the original
action is bounded-to-one and the equivalence classes have a uniform bound. -/
theorem quotient_action_fiberBound (E : Setoid X) (C : ℕ)
    (hE : ∀ p : P, ∀ x y : X, E x y → E (p +ᵥ x) (p +ᵥ y))
    (hC : ClassBound E C) (p : P) (k : ℕ)
    (hk : FiberBound (fun x : X => p +ᵥ x) k) :
    @FiberBound (Quotient E) (Quotient E)
      (fun q => @VAdd.vadd P (Quotient E) (quotientAddAction E hE).toVAdd p q) (C * k) :=
  quotient_fiberBound E C k hC (fun x : X => p +ᵥ x) hk (hE p)

/-- Scalar descent to the image preserves bounded-to-one action maps. -/
theorem image_action_bounded_fibers {Q : Type*} [AddCommMonoid Q]
    (f : P →+ Q)
    (hker : ∀ a b : P, f a = f b → ∀ x : X, a +ᵥ x = b +ᵥ x)
    (hX : ∀ p : P, ∃ k : ℕ, FiberBound (fun x : X => p +ᵥ x) k) :
    ∀ q : AddMonoidHom.mrange f, ∃ k : ℕ,
      FiberBound (fun x : X => @VAdd.vadd _ _ (imageAction f hker).toVAdd q x) k := by
  intro q
  obtain ⟨p, hp⟩ := q.prop
  have hqp : q = f.mrangeRestrict p := Subtype.ext hp.symm
  subst q
  have heq : (fun x : X => @VAdd.vadd _ _ (imageAction f hker).toVAdd
      (f.mrangeRestrict p) x) = (fun x : X => p +ᵥ x) := by
    funext x
    exact imageAction_apply f hker p x
  simpa only [heq] using hX p

end QuotientAction

section PositiveTorsion

variable {Γ X : Type*} [AddCommGroup Γ]

/-- Finite translates supply all the positive representatives needed for
the torsion-family construction. -/
theorem exists_positive_translate_family (P : AddSubmonoid Γ) (T : AddSubgroup Γ)
    [Fintype T] (hgen : AddSubgroup.closure (P : Set Γ) = ⊤) :
    ∃ b ∈ P, ∃ B : T → P, ∀ t : T, (B t : Γ) = b + (t : Γ) := by
  classical
  obtain ⟨b, hb, hbt⟩ := finite_translates P hgen
    (Finset.univ.image (fun t : T => (t : Γ)))
  have hpos (t : T) : b + (t : Γ) ∈ P :=
    hbt (t : Γ) (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩)
  exact ⟨b, hb, fun t => ⟨b + (t : Γ), hpos t⟩, fun t => rfl⟩

/-- The maps used to remove torsion. The finite subgroup need not be
the entire torsion subgroup for this algebraic construction. -/
def positiveTranslateFamily (P : AddSubmonoid Γ) (T : AddSubgroup Γ)
    [AddAction P X] (B : T → P) : T → X → X :=
  fun t x => B t +ᵥ x

/-- Equation (8) follows directly from the identities of positive translates
in the ambient abelian group. -/
theorem positiveTranslateFamily_shift (P : AddSubmonoid Γ) (T : AddSubgroup Γ)
    [AddAction P X] (b : Γ) (B : T → P)
    (hB : ∀ t : T, (B t : Γ) = b + (t : Γ)) :
    ∀ u t : T, ∀ z : X,
      positiveTranslateFamily P T B u (positiveTranslateFamily P T B 0 z) =
      positiveTranslateFamily P T B (u - t) (positiveTranslateFamily P T B t z) := by
  intro u t z
  have heq : B u + B 0 = B (u - t) + B t := by
    apply Subtype.ext
    simp only [AddSubmonoid.coe_add, hB, AddSubgroup.coe_zero, AddSubgroup.coe_sub]
    abel
  simp only [positiveTranslateFamily, ← add_vadd, heq]

/-- Commutativity makes the torsion equivalence relation invariant under
all original action maps. -/
theorem positiveTranslateFamily_invariant (P : AddSubmonoid Γ) (T : AddSubgroup Γ)
    [AddAction P X] (B : T → P) (p : P) {x y : X}
    (h : Relation.EqvGen (TorsionEdge (positiveTranslateFamily P T B)) x y) :
    Relation.EqvGen (TorsionEdge (positiveTranslateFamily P T B)) (p +ᵥ x) (p +ᵥ y) := by
  apply eqvGen_torsion_map (positiveTranslateFamily P T B) (fun x : X => p +ᵥ x) _ h
  intro t z
  simp only [positiveTranslateFamily, ← add_vadd, add_comm]

/-- After translating by `B 0`, scalar differences in `T` become
equal in the torsion equivalence quotient. This is the factoring step
on `bZ` in Proposition 5.2. -/
theorem positiveTranslateFamily_factor (P : AddSubmonoid Γ) (T : AddSubgroup Γ)
    [AddAction P X] (b : Γ) (B : T → P)
    (hB : ∀ t : T, (B t : Γ) = b + (t : Γ))
    (p q : P) (hpq : (p : Γ) - (q : Γ) ∈ T) (x : X) :
    Relation.EqvGen (TorsionEdge (positiveTranslateFamily P T B))
      (p +ᵥ (B 0 +ᵥ x)) (q +ᵥ (B 0 +ᵥ x)) := by
  let t : T := ⟨(p : Γ) - (q : Γ), hpq⟩
  have heq : B t + q = p + B 0 := by
    apply Subtype.ext
    simp only [AddSubmonoid.coe_add, hB, AddSubgroup.coe_zero]
    change b + ((p : Γ) - (q : Γ)) + (q : Γ) = (p : Γ) + (b + 0)
    abel
  apply Relation.EqvGen.symm
  apply Relation.EqvGen.rel
  refine ⟨q +ᵥ x, t, ?_, ?_⟩
  · simp only [positiveTranslateFamily, ← add_vadd, add_comm]
  · simp only [positiveTranslateFamily, ← add_vadd, heq]

/-- The original scalar monoid's image in the quotient group. -/
def torsionScalarHom (P : AddSubmonoid Γ) (T : AddSubgroup Γ) : P →+ Γ ⧸ T :=
  (QuotientAddGroup.mk' T).comp P.subtype

def positiveTranslateSetoid (P : AddSubmonoid Γ) (T : AddSubgroup Γ)
    [AddAction P X] (B : T → P) : Setoid X :=
  Relation.EqvGen.setoid (TorsionEdge (positiveTranslateFamily P T B))

theorem positiveTranslateSetoid_invariant (P : AddSubmonoid Γ) (T : AddSubgroup Γ)
    [AddAction P X] (B : T → P) :
    ∀ p : P, ∀ x y : X, positiveTranslateSetoid P T B x y →
      positiveTranslateSetoid P T B (p +ᵥ x) (p +ᵥ y) := by
  intro p x y h
  exact positiveTranslateFamily_invariant P T B p h

/-- The forward image `bZ` in Proposition 5.2 carries an actual action
of the image of `P` in `Γ/T`, and all original scalar maps agree with
their images. -/
theorem torsion_image_action (P : AddSubmonoid Γ) (T : AddSubgroup Γ)
    [AddAction P X] (b : Γ) (B : T → P)
    (hB : ∀ t : T, (B t : Γ) = b + (t : Γ)) :
    letI : AddAction P (Quotient (positiveTranslateSetoid (X := X) P T B)) :=
      quotientAddAction (positiveTranslateSetoid (X := X) P T B) (positiveTranslateSetoid_invariant P T B)
    letI : AddAction P (ForwardImage (X := Quotient (positiveTranslateSetoid (X := X) P T B)) (B 0)) :=
      forwardImageAction (B 0)
    ∃ I : AddAction (AddMonoidHom.mrange (torsionScalarHom P T))
      (ForwardImage (X := Quotient (positiveTranslateSetoid (X := X) P T B)) (B 0)),
      ∀ p : P, ∀ y : ForwardImage (X := Quotient (positiveTranslateSetoid (X := X) P T B)) (B 0),
        @VAdd.vadd _ _ I.toVAdd ((torsionScalarHom P T).mrangeRestrict p) y = p +ᵥ y := by
  letI : AddAction P (Quotient (positiveTranslateSetoid (X := X) P T B)) :=
    quotientAddAction (positiveTranslateSetoid (X := X) P T B) (positiveTranslateSetoid_invariant P T B)
  letI : AddAction P (ForwardImage (X := Quotient (positiveTranslateSetoid (X := X) P T B)) (B 0)) :=
    forwardImageAction (B 0)
  have hker : ∀ p q : P, torsionScalarHom P T p = torsionScalarHom P T q →
      ∀ y : ForwardImage (X := Quotient (positiveTranslateSetoid (X := X) P T B)) (B 0),
        p +ᵥ y = q +ᵥ y := by
    intro p q hpq y
    have hpqT : (p : Γ) - (q : Γ) ∈ T := QuotientAddGroup.eq_iff_sub_mem.mp hpq
    obtain ⟨z, hz⟩ := y.prop
    apply Subtype.ext
    change p +ᵥ y.val = q +ᵥ y.val
    rw [← hz]
    induction z using Quotient.inductionOn with
    | _ x =>
        exact Quotient.sound (positiveTranslateFamily_factor P T b B hB p q hpqT x)
  exact ⟨imageAction (torsionScalarHom P T) hker,
    fun p y => imageAction_apply (torsionScalarHom P T) hker p y⟩

end PositiveTorsion

end FiniteAsdim
