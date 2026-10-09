import FiniteAsdim.Metric
import FiniteAsdim.Bounds

/-! The scale-sensitive two-piece partition argument of Section 7. -/

namespace FiniteAsdim

universe u

variable {X : Type u} (d : NatMetric X)

/-- Recenter an ambient ball at a point of a subspace, doubling the radius. -/
theorem subspace_ball_image_bound {A : Set X} {I : Type u} (label : A → I)
    {s m : ℕ}
    (h : ∀ a : A, (label '' (d.restrict A).ball a (2 * s)).encard ≤ (m : ℕ∞))
    (x : X) :
    (label '' {a : A | d.near s x a.val}).encard ≤ (m : ℕ∞) := by
  by_cases he : ({a : A | d.near s x a.val} : Set A).Nonempty
  · obtain ⟨a, ha⟩ := he
    apply le_trans (Set.encard_mono (Set.image_mono (show
      {a : A | d.near s x a.val} ⊆ (d.restrict A).ball a (2 * s) from ?_))) (h a)
    intro b hb
    exact d.recenter ha hb
  · have hz : ({a : A | d.near s x a.val} : Set A) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp he
    simp [hz]

/-- At a fixed scale, unite partitions of a set and its complement.
The multiplicities add, and the common diameter bound is their maximum. -/
theorem recombine_scale {A : Set X} {s m k : ℕ}
    (hA : ScalePartition (d.restrict A) (2 * s) m)
    (hU : ScalePartition (d.restrict Aᶜ) (2 * s) k) :
    ScalePartition d s (m + k) := by
  classical
  obtain ⟨I, aLabel, DA, hDA, hMA⟩ := hA
  obtain ⟨J, uLabel, DU, hDU, hMU⟩ := hU
  let label : X → Sum I J := fun x =>
    if hx : x ∈ A then Sum.inl (aLabel ⟨x, hx⟩)
    else Sum.inr (uLabel ⟨x, hx⟩)
  refine ⟨Sum I J, label, max DA DU, ?_, ?_⟩
  · intro x y hxy
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ A
    · have he : aLabel ⟨x, hx⟩ = aLabel ⟨y, hy⟩ := by
        simpa [label, hx, hy] using hxy
      exact d.mono (le_max_left DA DU) (hDA ⟨x, hx⟩ ⟨y, hy⟩ he)
    · simp [label, hx, hy] at hxy
    · simp [label, hx, hy] at hxy
    · have he : uLabel ⟨x, hx⟩ = uLabel ⟨y, hy⟩ := by
        simpa [label, hx, hy] using hxy
      exact d.mono (le_max_right DA DU) (hDU ⟨x, hx⟩ ⟨y, hy⟩ he)
  · intro x
    let TA : Set I := aLabel '' {a : A | d.near s x a.val}
    let TU : Set J := uLabel '' {a : (Aᶜ : Set X) | d.near s x a.val}
    have hsub : label '' d.ball x s ⊆ Sum.inl '' TA ∪ Sum.inr '' TU := by
      rintro z ⟨y, hy, rfl⟩
      by_cases ha : y ∈ A
      · left
        exact ⟨aLabel ⟨y, ha⟩, ⟨⟨y, ha⟩, hy, rfl⟩, by simp [label, ha]⟩
      · right
        exact ⟨uLabel ⟨y, ha⟩, ⟨⟨y, ha⟩, hy, rfl⟩, by simp [label, ha]⟩
    calc
      (label '' d.ball x s).encard ≤ (Sum.inl '' TA ∪ Sum.inr '' TU).encard :=
        Set.encard_mono hsub
      _ ≤ (Sum.inl '' TA).encard + (Sum.inr '' TU).encard := Set.encard_union_le _ _
      _ ≤ TA.encard + TU.encard := add_le_add (Set.encard_image_le _ _) (Set.encard_image_le _ _)
      _ ≤ (m : ℕ∞) + (k : ℕ∞) := add_le_add
        (subspace_ball_image_bound d aLabel hMA x) (subspace_ball_image_bound d uLabel hMU x)
      _ = ((m + k : ℕ) : ℕ∞) := by simp

/-- A bounded-displacement map gives a uniformly bounded fiber partition. -/
theorem map_fiber_partition {A : Set X} {s k B : ℕ} (f : X → X)
    (hB : ∀ y, d.near B y (f y))
    (hk : ∀ a : A, (f '' d.ball a.val s).encard ≤ (k : ℕ∞)) :
    ScalePartition (d.restrict A) s k := by
  refine ⟨X, fun a => f a.val, B + B, ?_, ?_⟩
  · intro x y hxy
    change f x.val = f y.val at hxy
    have hy : d.near B (f x.val) y.val := by
      rw [hxy]
      exact d.symm (hB y.val)
    exact d.triangle (hB x.val) hy
  · intro a
    apply le_trans (Set.encard_mono (show
      (fun y : A => f y.val) '' (d.restrict A).ball a s ⊆ f '' d.ball a.val s from ?_)) (hk a)
    rintro z ⟨y, hy, rfl⟩
    exact ⟨y.val, hy, rfl⟩

/-- The actual final partition construction, given the collision partition
and the local-freeness witness at scale `2*s`. -/
theorem rank_step_at_scale {r s : ℕ} {A : Set X}
    (hA : ScalePartition (d.restrict A) (2 * s) (rankBound r + 1))
    (f : X → X) (B : ℕ) (hB : ∀ y, d.near B y (f y))
    (hU : ∀ u : (Aᶜ : Set X), (f '' d.ball u.val (2 * s)).encard ≤ (3 ^ (r + 1) : ℕ)) :
    ScalePartition d s (rankBound (r + 1) + 1) := by
  have hp := map_fiber_partition d f hB hU
  have hr := recombine_scale d hA hp
  simpa [rankBound_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr

end FiniteAsdim
