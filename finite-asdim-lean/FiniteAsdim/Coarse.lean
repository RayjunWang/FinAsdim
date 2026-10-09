import FiniteAsdim.Metric

namespace FiniteAsdim

universe u

variable {X Y : Type u} (d : NatMetric X) (e : NatMetric Y)

/-- The two coarse metric inequalities, written for finite radii. -/
structure CoarseEmbedding (f : X → Y) where
  a : ℕ
  b : ℕ
  forward : ∀ {s x y}, d.near s x y → e.near (a * s + b) (f x) (f y)
  backward : ∀ {s x y}, e.near s (f x) (f y) → d.near (a * s + b) x y

/-- Pull back a partition along a coarse embedding. -/
theorem asdimLE_of_embedding {f : X → Y} (h : CoarseEmbedding d e f)
    {n : ℕ} (he : AsdimLE e n) : AsdimLE d n := by
  intro s hs
  let t := max 1 (h.a * s + h.b)
  obtain ⟨I, label, D, hD, hm⟩ := he t (le_max_left _ _)
  refine ⟨I, label ∘ f, h.a * D + h.b, ?_, ?_⟩
  · intro x y hxy
    exact h.backward (hD (f x) (f y) hxy)
  · intro x
    apply le_trans (Set.encard_mono (show
      (label ∘ f) '' d.ball x s ⊆ label '' e.ball (f x) t from ?_)) (hm (f x))
    rintro z ⟨y, hy, rfl⟩
    exact ⟨f y, e.mono (le_max_right _ _) (h.forward hy), rfl⟩

/-- Coarse density gives the converse bound, using a chosen coarse inverse. -/
theorem asdimLE_of_dense_embedding {f : X → Y} (h : CoarseEmbedding d e f)
    (R : ℕ) (hdense : ∀ y, ∃ x, e.near R y (f x))
    {n : ℕ} (hx : AsdimLE d n) : AsdimLE e n := by
  classical
  choose g hg using hdense
  intro s hs
  let t := max 1 (h.a * (R + s + R) + h.b)
  obtain ⟨I, label, D, hD, hm⟩ := hx t (le_max_left _ _)
  refine ⟨I, label ∘ g, R + (h.a * D + h.b) + R, ?_, ?_⟩
  · intro y z hyz
    exact e.triangle (e.triangle (hg y) (h.forward (hD (g y) (g z) hyz))) (e.symm (hg z))
  · intro y
    apply le_trans (Set.encard_mono (show
      (label ∘ g) '' e.ball y s ⊆ label '' d.ball (g y) t from ?_)) (hm (g y))
    rintro z ⟨w, hw, rfl⟩
    refine ⟨g w, ?_, rfl⟩
    exact d.mono (le_max_right _ _) (h.backward
      (e.triangle (e.triangle (e.symm (hg y)) hw) (hg w)))

theorem asdimLE_iff_of_quasiIsometry {f : X → Y} (h : CoarseEmbedding d e f)
    (R : ℕ) (hdense : ∀ y, ∃ x, e.near R y (f x)) (n : ℕ) :
    AsdimLE d n ↔ AsdimLE e n :=
  ⟨asdimLE_of_dense_embedding d e h R hdense, asdimLE_of_embedding d e h⟩

/-- If every finite ball is a singleton, the asymptotic dimension is zero. -/
theorem asdimLE_zero_of_discrete
    (h : ∀ s x y, d.near s x y → x = y) : AsdimLE d 0 := by
  intro s hs
  refine ⟨X, id, 0, ?_, ?_⟩
  · intro x y hxy
    change x = y at hxy
    subst y
    exact d.refl x
  · intro x
    have hb : id '' d.ball x s ⊆ {x} := by
      rintro z ⟨y, hy, rfl⟩
      exact (h s x y hy).symm
    simpa using Set.encard_mono hb

end FiniteAsdim
