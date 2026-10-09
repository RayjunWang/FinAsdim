import FiniteAsdim.Recombination
import FiniteAsdim.FiniteUnion
import FiniteAsdim.Schreier

/-!
# The collision decomposition and the induction step

These theorems formalize the partition argument of Section 7. The local
freeness witness and the dimension estimates for collision subspaces are
explicit inputs. The latter must ultimately be supplied by the rank
reduction and the induction hypothesis; they are not asserted as axioms.
-/

namespace FiniteAsdim

variable {M X : Type*} [AddCommMonoid M] [AddAction M X]

def collisionSet (p q : M) : Set X := {x | p +ᵥ x = q +ᵥ x}

noncomputable def collisionPairs (K : Finset M) : Finset (M × M) := by
  classical
  exact (K.product K).filter (fun z => z.1 ≠ z.2)

def collisionUnion (K : Finset M) : Set X :=
  ⋃ z ∈ collisionPairs K, collisionSet z.1 z.2

theorem collisionSet_invariant (p q : M) : Schreier.Invariant (M := M) (collisionSet (X := X) p q) := by
  intro c x hx
  exact Schreier.collision_forward_invariant hx

theorem injective_outside_collisionUnion (K : Finset M) (x : X)
    (hx : x ∉ collisionUnion K) : (K : Set M).InjOn (fun p => p +ᵥ x) := by
  classical
  intro p hp q hq hpq
  by_contra hne
  apply hx
  apply Set.mem_iUnion.mpr
  refine ⟨(p, q), Set.mem_iUnion.mpr ⟨?_, hpq⟩⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hne⟩

/-- A finite collision window inherits the common bound of its collision sets. -/
theorem collisionUnion_asdimLE (S : Set M) (K : Finset M) (n : ℕ)
    (h : ∀ p ∈ K, ∀ q ∈ K, p ≠ q →
      AsdimLE ((Schreier.natMetric (X := X) S).restrict (collisionSet p q)) n) :
    AsdimLE ((Schreier.natMetric (X := X) S).restrict (collisionUnion K)) n := by
  classical
  apply asdimLE_finite_union (Schreier.natMetric S) (collisionPairs K)
    (fun z => collisionSet z.1 z.2) n
  intro z hz
  obtain ⟨hzK, hne⟩ := Finset.mem_filter.mp hz
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hzK
  exact h z.1 hp z.2 hq hne

/-- The complete finite-scale argument from Section 7, using all finitely
many collision pairs and the local witness on their complement. -/
theorem finite_collision_step (S : Set M) (K : Finset M) {r s : ℕ} (hs : 1 ≤ s)
    (f : X → X) (B : ℕ)
    (hB : ∀ y, Schreier.Near S B y (f y))
    (hlocal : ∀ x : X, (K : Set M).InjOn (fun p => p +ᵥ x) →
      (f '' (Schreier.natMetric S).ball x (2 * s)).encard ≤ (3 ^ (r + 1) : ℕ))
    (hcollision : ∀ p ∈ K, ∀ q ∈ K, p ≠ q →
      AsdimLE ((Schreier.natMetric (X := X) S).restrict (collisionSet p q)) (rankBound r)) :
    ScalePartition (Schreier.natMetric (X := X) S) s (rankBound (r + 1) + 1) := by
  have hA := collisionUnion_asdimLE S K (rankBound r) hcollision
  exact rank_step_at_scale (Schreier.natMetric S) (hA (2 * s) (by omega)) f B hB
    (fun u => hlocal u.val (injective_outside_collisionUnion K u.val u.property))

/-- The complete induction step, conditional on the two mathematical
inputs displayed in the statement. No ambient uniformity in the action,
the scale, or the collision quotient is required. -/
theorem rank_step (S : Set M) (r : ℕ)
    (hlocal : ∀ t : ℕ, 1 ≤ t → ∃ K : Finset M, ∃ B : ℕ, ∃ f : X → X,
      (∀ y, Schreier.Near S B y (f y)) ∧
      (∀ x, (K : Set M).InjOn (fun p => p +ᵥ x) →
        (f '' (Schreier.natMetric S).ball x t).encard ≤ (3 ^ (r + 1) : ℕ)))
    (hcollision : ∀ p q : M, p ≠ q →
      AsdimLE ((Schreier.natMetric (X := X) S).restrict (collisionSet p q)) (rankBound r)) :
    AsdimLE (Schreier.natMetric (X := X) S) (rankBound (r + 1)) := by
  intro s hs
  obtain ⟨K, B, f, hB, hf⟩ := hlocal (2 * s) (by omega)
  exact finite_collision_step S K hs f B hB hf (fun p hp q hq hne => hcollision p q hne)

end FiniteAsdim
