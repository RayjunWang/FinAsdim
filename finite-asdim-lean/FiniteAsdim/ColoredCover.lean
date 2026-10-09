import FiniteAsdim.Metric
import Mathlib.Logic.Relation
import Lean.Elab.Tactic.Omega

namespace FiniteAsdim

universe u

variable {X : Type u} (d : NatMetric X)

/-- A uniformly bounded cover by `n+1` families of pairwise `s`-separated sets. -/
def ColoredCover (A : Set X) (s n : ℕ) : Prop :=
  ∃ (I : Type u) (piece : I → Set X) (color : I → Fin (n + 1)) (D : ℕ),
    (∀ x ∈ A, ∃ i, x ∈ piece i) ∧
    (∀ i x y, x ∈ piece i → y ∈ piece i → d.near D x y) ∧
    (∀ i j, color i = color j → i ≠ j →
      ∀ x ∈ piece i, ∀ y ∈ piece j, ¬d.near s x y)

/-- Select a cover member for each point. Separation at radius `2*s`
ensures that a radius-`s` ball meets at most one member of each color. -/
theorem scalePartition_of_coloredCover {s n : ℕ}
    (h : ColoredCover d Set.univ (2 * s) n) : ScalePartition d s (n + 1) := by
  classical
  obtain ⟨I, piece, color, D, hc, hD, hsep⟩ := h
  have hc' : ∀ x : X, ∃ i, x ∈ piece i := fun x => hc x (Set.mem_univ x)
  choose label hl using hc'
  refine ⟨I, label, D, ?_, ?_⟩
  · intro x y hxy
    exact hD (label x) x y (hl x) (hxy.symm ▸ hl y)
  · intro x
    have hi : (label '' d.ball x s).InjOn color := by
      rintro i ⟨y, hy, rfl⟩ j ⟨z, hz, rfl⟩ hij
      by_contra hne
      exact hsep (label y) (label z) hij hne y (hl y) z (hl z) (d.recenter hy hz)
    rw [← hi.encard_image]
    calc
      (color '' (label '' d.ball x s)).encard ≤ (Set.univ : Set (Fin (n + 1))).encard :=
        Set.encard_mono (Set.subset_univ _)
      _ = ((n + 1 : ℕ) : ℕ∞) := by simp [Set.encard_univ, ENat.card_eq_coe_fintype_card]

/-- A nested sequence of nonempty finite sets with at most `n+1` elements
must stabilize at one of the first `n+1` steps. -/
theorem nested_stabilization {I : Type u} (n : ℕ) (T : ℕ → Set I)
    (hmono : Monotone T) (h0 : (T 0).Nonempty)
    (hb : (T (n + 1)).encard ≤ ((n + 1 : ℕ) : ℕ∞)) :
    ∃ i : Fin (n + 1), T i.val = T (i.val + 1) := by
  classical
  have hf : (T (n + 1)).Finite := Set.finite_of_encard_le_coe hb
  have hfinite (k : ℕ) (hk : k ≤ n + 1) : (T k).Finite := hf.subset (hmono hk)
  by_contra hnone
  have hne : ∀ i, i < n + 1 → T i ≠ T (i + 1) := by
    intro i hi heq
    exact hnone ⟨⟨i, hi⟩, heq⟩
  have lower : ∀ k, k ≤ n + 1 → k + 1 ≤ (T k).ncard := by
    intro k
    induction k with
    | zero =>
        intro hk
        exact (Set.ncard_pos (hfinite 0 hk)).mpr h0
    | succ k ih =>
        intro hk
        have hl := ih (by omega)
        have hlt := Set.ncard_lt_ncard
          (Set.ssubset_iff_subset_ne.mpr ⟨hmono (Nat.le_succ k), hne k (by omega)⟩)
          (hfinite (k + 1) hk)
        change (T k).ncard < (T (k + 1)).ncard at hlt
        change k + 2 ≤ (T (k + 1)).ncard
        omega
  have hb' : (T (n + 1)).ncard ≤ n + 1 := by
    have h := hb
    rw [← hf.cast_ncard_eq] at h
    simpa only [ENat.coe_le_coe] using h
  have hl := lower (n + 1) le_rfl
  omega

private def stableSet {I : Type u} (label : X → I) (s : ℕ) (i : ℕ) : Set X :=
  {x | label '' d.ball x (i * s) = label '' d.ball x ((i + 1) * s)}

private def stableEdge {I : Type u} (label : X → I) (s i : ℕ) (x y : X) : Prop :=
  x ∈ stableSet d label s i ∧ y ∈ stableSet d label s i ∧ d.near s x y

private theorem stable_image_eq {I : Type u} (label : X → I) {s i : ℕ} {x y : X}
    (hx : x ∈ stableSet d label s i) (hy : y ∈ stableSet d label s i)
    (hxy : d.near s x y) :
    label '' d.ball x (i * s) = label '' d.ball y (i * s) := by
  apply Set.Subset.antisymm
  · rw [hy]
    apply Set.image_mono
    intro z hz
    have h := d.triangle (d.symm hxy) hz
    simpa [Nat.add_mul, Nat.one_mul, Nat.add_comm] using h
  · rw [hx]
    apply Set.image_mono
    intro z hz
    have h := d.triangle hxy hz
    simpa [Nat.add_mul, Nat.one_mul, Nat.add_comm] using h

private theorem component_image_eq {I : Type u} (label : X → I) {s i : ℕ} {x y : X}
    (h : Relation.EqvGen (stableEdge d label s i) x y) :
    label '' d.ball x (i * s) = label '' d.ball y (i * s) := by
  induction h with
  | rel x y h => exact stable_image_eq d label h.1 h.2.1 h.2.2
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Partition-to-colored-cover direction of Lemma 2.2.
The cover members are chain components of the stabilization sets. -/
theorem coloredCover_of_scalePartition {s n : ℕ}
    (h : ScalePartition d ((n + 1) * s) (n + 1)) : ColoredCover d Set.univ s n := by
  classical
  obtain ⟨I, label, D, hD, hm⟩ := h
  let C (i : Fin (n + 1)) := Relation.EqvGen.setoid (stableEdge d label s i.val)
  let J := (i : Fin (n + 1)) × Quotient (C i)
  let piece : J → Set X := fun j =>
    {x | x ∈ stableSet d label s j.1.val ∧ Quotient.mk (C j.1) x = j.2}
  refine ⟨J, piece, fun j => j.1, D + n * s, ?_, ?_, ?_⟩
  · intro x hx
    have hmono : Monotone (fun i => label '' d.ball x (i * s)) := by
      intro a b hab
      apply Set.image_mono
      intro y hy
      exact d.mono (Nat.mul_le_mul_right s hab) hy
    obtain ⟨i, hi⟩ := nested_stabilization n (fun i => label '' d.ball x (i * s)) hmono
      ⟨label x, x, by simpa using d.mem_ball_self x 0, rfl⟩ (hm x)
    exact ⟨⟨i, Quotient.mk (C i) x⟩, hi, rfl⟩
  · intro j x y hx hy
    have hc : Relation.EqvGen (stableEdge d label s j.1.val) x y :=
      Quotient.exact (hx.2.trans hy.2.symm)
    have he := component_image_eq d label hc
    have hmem : label x ∈ label '' d.ball x (j.1.val * s) :=
      ⟨x, d.mem_ball_self x _, rfl⟩
    rw [he] at hmem
    obtain ⟨w, hw, hl⟩ := hmem
    have hnear := d.triangle (hD x w hl.symm) (d.symm hw)
    apply d.mono _ hnear
    exact Nat.add_le_add_left (Nat.mul_le_mul_right s (by omega : j.1.val ≤ n)) D
  · rintro ⟨i, ci⟩ ⟨j, cj⟩ hij hne x hx y hy hxy
    change i = j at hij
    subst j
    have hq : Quotient.mk (C i) x = Quotient.mk (C i) y :=
      Quotient.sound (Relation.EqvGen.rel x y ⟨hx.1, hy.1, hxy⟩)
    apply hne
    have he : ci = cj := hx.2.symm.trans (hq.trans hy.2)
    subst cj
    rfl

end FiniteAsdim
