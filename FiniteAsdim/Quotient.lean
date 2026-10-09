import FiniteAsdim.Schreier

/-!
# Quotients by invariant equivalence relations

The quotient action is constructed from the invariant relation. Its
projection preserves paths, and a uniform bound on the diameter of
equivalence classes gives a converse distance bound. No injectivity of
the monoid action is assumed.
-/

namespace FiniteAsdim
namespace Schreier

variable {M X : Type*} [AddCommMonoid M] [AddAction M X]

def SetoidInvariant (E : Setoid X) : Prop :=
  ∀ (c : M) {x y : X}, E.r x y → E.r (c +ᵥ x) (c +ᵥ y)

@[reducible] def quotientAddAction (E : Setoid X)
    (hE : SetoidInvariant (M := M) E) : AddAction M (Quotient E) where
  vadd c := Quotient.map (fun x : X => c +ᵥ x) (fun _ _ h => hE c h)
  zero_vadd := by
    intro z
    refine Quotient.inductionOn z (fun x => ?_)
    change Quotient.mk E ((0 : M) +ᵥ x) = Quotient.mk E x
    rw [zero_vadd]
  add_vadd := by
    intro c d z
    refine Quotient.inductionOn z (fun x => ?_)
    change Quotient.mk E ((c + d) +ᵥ x) = Quotient.mk E (c +ᵥ (d +ᵥ x))
    rw [add_vadd]

theorem quotient_equivariant (E : Setoid X)
    (hE : SetoidInvariant (M := M) E) :
    letI := quotientAddAction E hE
    Equivariant (M := M) (Quotient.mk E) := by
  letI := quotientAddAction E hE
  intro c x
  rfl

theorem quotient_near (E : Setoid X) (hE : SetoidInvariant (M := M) E)
    (S : Set M) {n : ℕ} {x y : X} (h : Near S n x y) :
    letI := quotientAddAction E hE
    Near S n (Quotient.mk E x) (Quotient.mk E y) := by
  letI := quotientAddAction E hE
  exact near_map (quotient_equivariant E hE) h

/-- Lemma 3.2, with the stronger additive bound afforded by commutativity. -/
theorem quotient_near_reflects (E : Setoid X)
    (hE : SetoidInvariant (M := M) E) (S : Set M) (D : ℕ)
    (hD : ∀ x y, E.r x y → Near S D x y) {n : ℕ} {x y : X} :
    letI := quotientAddAction E hE
    Near S n (Quotient.mk E x) (Quotient.mk E y) → Near S (n + D) x y := by
  letI := quotientAddAction E hE
  exact near_reflects_of_bounded_fibers (quotient_equivariant E hE) D
    (fun x y h => hD x y (Quotient.exact h))

theorem quotient_projection_surjective (E : Setoid X) :
    Function.Surjective (Quotient.mk E) := Quotient.mk_surjective

section FiberCardinality

variable {U V : Type*}

/-- A map with a uniform finite bound on all its fibers. -/
def BoundedToOne (f : U → V) : Prop :=
  ∃ k : ℕ, ∀ y : V, (f ⁻¹' {y}).encard ≤ (k : ℕ∞)

theorem encard_preimage_le (f : U → V) (k : ℕ)
    (hf : ∀ y : V, (f ⁻¹' {y}).encard ≤ (k : ℕ∞))
    (T : Set V) (hT : T.Finite) :
    (f ⁻¹' T).encard ≤ (k : ℕ∞) * T.encard := by
  induction T, hT using Set.Finite.induction_on with
  | empty => simp
  | @insert y T hy hT ih =>
      have heq : f ⁻¹' insert y T = (f ⁻¹' {y}) ∪ (f ⁻¹' T) := by
        ext x
        simp
      rw [heq, Set.encard_insert_of_notMem hy, mul_add, mul_one]
      calc
        ((f ⁻¹' {y}) ∪ (f ⁻¹' T)).encard
            ≤ (f ⁻¹' {y}).encard + (f ⁻¹' T).encard := Set.encard_union_le _ _
        _ ≤ (k : ℕ∞) + (k : ℕ∞) * T.encard := add_le_add (hf y) ih
        _ = (k : ℕ∞) * T.encard + (k : ℕ∞) := add_comm _ _

/-- Bounded-to-one actions have a separate uniform fiber bound for every
monoid element. This is exactly the hypothesis in Theorem 1.1. -/
def BoundedToOneAction (M X : Type*) [AddCommMonoid M] [AddAction M X] : Prop :=
  ∀ c : M, BoundedToOne (fun x : X => c +ᵥ x)

theorem quotient_fiber_bound (E : Setoid X)
    (hE : SetoidInvariant (M := M) E) (C k : ℕ)
    (hC : ∀ y : X, {x : X | E.r x y}.encard ≤ (C : ℕ∞)) (c : M)
    (hc : ∀ y : X, ((fun x : X => c +ᵥ x) ⁻¹' {y}).encard ≤ (k : ℕ∞)) :
    letI := quotientAddAction E hE
    ∀ z : Quotient E, ((fun w : Quotient E => c +ᵥ w) ⁻¹' {z}).encard
      ≤ ((k * C : ℕ) : ℕ∞) := by
  letI := quotientAddAction E hE
  intro z
  refine Quotient.inductionOn z (fun y => ?_)
  have heq : (fun w : Quotient E => c +ᵥ w) ⁻¹' {Quotient.mk E y} =
      Quotient.mk E '' ((fun x : X => c +ᵥ x) ⁻¹' {u : X | E.r u y}) := by
    ext w
    constructor
    · intro hw
      rcases Quotient.mk_surjective w with ⟨x, rfl⟩
      exact ⟨x, Quotient.exact hw, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact Quotient.sound hx
  rw [heq, Nat.cast_mul]
  calc
    (Quotient.mk E '' ((fun x : X => c +ᵥ x) ⁻¹' {u : X | E.r u y})).encard
      ≤ ((fun x : X => c +ᵥ x) ⁻¹' {u : X | E.r u y}).encard := Set.encard_image_le _ _
    _ ≤ (k : ℕ∞) * {u : X | E.r u y}.encard :=
      encard_preimage_le _ k hc _ (Set.finite_of_encard_le_coe (hC y))
    _ ≤ (k : ℕ∞) * (C : ℕ∞) := mul_le_mul_right (hC y) (k : ℕ∞)

theorem quotient_boundedToOneAction (E : Setoid X)
    (hE : SetoidInvariant (M := M) E) (C : ℕ)
    (hC : ∀ y : X, {x : X | E.r x y}.encard ≤ (C : ℕ∞))
    (hX : BoundedToOneAction M X) :
    letI := quotientAddAction E hE
    BoundedToOneAction M (Quotient E) := by
  letI := quotientAddAction E hE
  intro c
  obtain ⟨k, hk⟩ := hX c
  exact ⟨k * C, quotient_fiber_bound E hE C k hC c hk⟩

end FiberCardinality

end Schreier
end FiniteAsdim

