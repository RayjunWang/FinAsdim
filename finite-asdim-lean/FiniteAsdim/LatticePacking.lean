import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.Ring.Abs
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.SplitIfs

namespace FiniteAsdim

/-- One of the three boxes of the interval `[-3R,3R]`. -/
def coordinateBox (R a : ℤ) : Fin 3 :=
  if a ≤ -R then 0 else if a ≤ R then 1 else 2

lemma coordinateBox_close {R a b : ℤ} (_hR : 0 ≤ R)
    (ha : -3 * R ≤ a ∧ a ≤ 3 * R) (hb : -3 * R ≤ b ∧ b ≤ 3 * R)
    (heq : coordinateBox R a = coordinateBox R b) : |a - b| ≤ 2 * R := by
  rw [abs_le]
  unfold coordinateBox at heq
  split_ifs at heq <;> simp_all <;> omega

/-- A finite independent set in the cube of radius `3R` has at most `3^r` elements.
This is the packing argument in Lemma 6.1 of arXiv:2609.17177v1. -/
theorem lattice_packing {r : ℕ} {R : ℤ} (hR : 0 ≤ R)
    (D : Finset (Fin r → ℤ))
    (hbound : ∀ v ∈ D, ∀ i, -3 * R ≤ v i ∧ v i ≤ 3 * R)
    (hindependent : ∀ v ∈ D, ∀ w ∈ D,
      (∀ i, |v i - w i| ≤ 2 * R) → v = w) :
    D.card ≤ 3 ^ r := by
  classical
  let box : (Fin r → ℤ) → (Fin r → Fin 3) := fun v i => coordinateBox R (v i)
  have hi : (D : Set (Fin r → ℤ)).InjOn box := by
    intro v hv w hw heq
    apply hindependent v hv w hw
    intro i
    exact coordinateBox_close hR (hbound v hv i) (hbound w hw i) (congrFun heq i)
  have hcard := Finset.card_le_card_of_injOn box
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _) hi
  simpa [Fintype.card_fun] using hcard

section Greedy
variable {V : Type*} {q : ℕ}

/-- Process colors `0,...,n-1` and select vertices having no selected neighbor. -/
def greedySelected (adj : V → V → Prop) (c : V → Fin q) : ℕ → Set V
  | 0 => ∅
  | n + 1 => {v | v ∈ greedySelected adj c n ∨
      ((c v).val = n ∧ ∀ w, adj v w → w ∉ greedySelected adj c n)}

lemma greedySelected_step (adj : V → V → Prop) (c : V → Fin q) (n : ℕ) :
    greedySelected adj c n ⊆ greedySelected adj c (n + 1) := by
  intro v hv
  exact Or.inl hv

lemma greedySelected_independent (adj : V → V → Prop) (c : V → Fin q)
    (hsymm : ∀ v w, adj v w → adj w v)
    (hproper : ∀ v w, adj v w → c v ≠ c w) (n : ℕ) :
    ∀ v ∈ greedySelected adj c n, ∀ w ∈ greedySelected adj c n, ¬adj v w := by
  induction n with
  | zero => simp [greedySelected]
  | succ n ih =>
    intro v hv w hw hadj
    rcases hv with hv | hv
    · rcases hw with hw | hw
      · exact ih v hv w hw hadj
      · exact hw.2 v (hsymm v w hadj) hv
    · rcases hw with hw | hw
      · exact hv.2 w hadj hw
      · apply hproper v w hadj
        apply Fin.ext
        exact hv.1.trans hw.1.symm

lemma greedySelected_dominates_processed (adj : V → V → Prop) (c : V → Fin q)
    (n : ℕ) : ∀ v, (c v).val < n →
      v ∈ greedySelected adj c n ∨ ∃ w, adj v w ∧ w ∈ greedySelected adj c n := by
  classical
  induction n with
  | zero => intro v hv; omega
  | succ n ih =>
    intro v hv
    by_cases hlt : (c v).val < n
    · rcases ih v hlt with hsel | ⟨w, hadj, hsel⟩
      · exact Or.inl (greedySelected_step adj c n hsel)
      · exact Or.inr ⟨w, hadj, greedySelected_step adj c n hsel⟩
    · have hcolor : (c v).val = n := by omega
      by_cases hneighbor : ∃ w, adj v w ∧ w ∈ greedySelected adj c n
      · rcases hneighbor with ⟨w, hadj, hsel⟩
        exact Or.inr ⟨w, hadj, greedySelected_step adj c n hsel⟩
      · left
        right
        refine ⟨hcolor, ?_⟩
        intro w hadj hsel
        exact hneighbor ⟨w, hadj, hsel⟩

/-- Finite proper colors produce an independent dominating set on an arbitrary graph.
No countability or finite vertex set is needed. -/
theorem finite_color_markers (adj : V → V → Prop) (c : V → Fin q)
    (hsymm : ∀ v w, adj v w → adj w v)
    (hproper : ∀ v w, adj v w → c v ≠ c w) :
    ∃ D : Set V,
      (∀ v ∈ D, ∀ w ∈ D, ¬adj v w) ∧
      (∀ v, v ∈ D ∨ ∃ w ∈ D, adj v w) := by
  refine ⟨greedySelected adj c q, greedySelected_independent adj c hsymm hproper q, ?_⟩
  intro v
  rcases greedySelected_dominates_processed adj c q v (c v).isLt with hv | ⟨w, hadj, hw⟩
  · exact Or.inl hv
  · exact Or.inr ⟨w, hw, hadj⟩

end Greedy

/-- Independence of the selected vertices in a region only needs proper
colors for adjacent pairs in that region. -/
lemma greedySelected_independent_on {V : Type*} {q : ℕ}
    (adj : V → V → Prop) (c : V → Fin q) (U : Set V)
    (hsymm : ∀ v w, adj v w → adj w v)
    (hproper : ∀ v ∈ U, ∀ w ∈ U, adj v w → c v ≠ c w) (n : ℕ) :
    ∀ v ∈ U, v ∈ greedySelected adj c n →
      ∀ w ∈ U, w ∈ greedySelected adj c n → ¬adj v w := by
  induction n with
  | zero => simp [greedySelected]
  | succ n ih =>
    intro v hvU hv w hwU hw hadj
    rcases hv with hv | hv
    · rcases hw with hw | hw
      · exact ih v hvU hv w hwU hw hadj
      · exact hw.2 v (hsymm v w hadj) hv
    · rcases hw with hw | hw
      · exact hv.2 w hadj hw
      · apply hproper v hvU w hwU hadj
        apply Fin.ext
        exact hv.1.trans hw.1.symm
end FiniteAsdim





