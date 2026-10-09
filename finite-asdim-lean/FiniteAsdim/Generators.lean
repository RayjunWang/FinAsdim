import FiniteAsdim.Schreier
import FiniteAsdim.Quotient
import FiniteAsdim.Coarse
import Mathlib.Algebra.Group.Submonoid.Basic

/-!
# Finite generating sets and metric comparison

Membership in a generated monoid is equivalent to the existence of a
finite word. Replacing a finite generating set gives linear bounds in
both directions for the Schreier metrics, hence preserves asymptotic
dimension.
-/

namespace FiniteAsdim
namespace Schreier

variable {M X : Type*} [AddCommMonoid M] [AddAction M X]

theorem exists_word_iff {S : Set M} {a : M} :
    (∃ n, Word S n a) ↔ a ∈ AddSubmonoid.closure S := by
  constructor
  · rintro ⟨n, h⟩
    induction h with
    | zero => exact AddSubmonoid.zero_mem _
    | cons s hs w ih => exact AddSubmonoid.add_mem _ (AddSubmonoid.subset_closure hs) ih
  · intro h
    induction h using AddSubmonoid.closure_induction with
    | mem a ha => exact ⟨1, by simpa using Word.cons a ha Word.zero⟩
    | zero => exact ⟨0, Word.zero⟩
    | add a b ha hb iha ihb =>
        obtain ⟨n, hn⟩ := iha
        obtain ⟨m, hm⟩ := ihb
        exact ⟨n + m, word_add hn hm⟩

theorem exists_word_of_generates {S : Set M}
    (hS : AddSubmonoid.closure S = ⊤) (a : M) : ∃ n, Word S n a := by
  apply exists_word_iff.mpr
  rw [hS]
  trivial

theorem word_compare {S T : Set M} (L : ℕ)
    (hST : ∀ s ∈ S, ∃ k ≤ L, Word T k s) {n : ℕ} {a : M}
    (h : Word S n a) : ∃ k ≤ L * n, Word T k a := by
  induction h with
  | zero => exact ⟨0, by simp, Word.zero⟩
  | @cons n a s hs w ih =>
      obtain ⟨k, hk, hks⟩ := hST s hs
      obtain ⟨j, hj, hja⟩ := ih
      refine ⟨k + j, ?_, word_add hks hja⟩
      calc
        k + j ≤ L + L * n := Nat.add_le_add hk hj
        _ = L * (n + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]

theorem near_compare {S T : Set M} (L : ℕ)
    (hST : ∀ s ∈ S, ∃ k ≤ L, Word T k s) {n : ℕ} {x y : X}
    (h : Near S n x y) : Near T (L * n) x y := by
  rcases near_iff_common_future.mp h with ⟨l, k, a, b, ha, hb, hn, hab⟩
  obtain ⟨i, hi, hia⟩ := word_compare L hST ha
  obtain ⟨j, hj, hjb⟩ := word_compare L hST hb
  apply near_iff_common_future.mpr
  refine ⟨i, j, a, b, hia, hjb, ?_, hab⟩
  calc
    i + j ≤ L * l + L * k := Nat.add_le_add hi hj
    _ = L * (l + k) := (Nat.mul_add _ _ _).symm
    _ ≤ L * n := Nat.mul_le_mul_left L hn

theorem finite_word_bound (S : Finset M) (T : Set M)
    (hST : ∀ s ∈ S, ∃ n, Word T n s) :
    ∃ L : ℕ, ∀ s ∈ S, ∃ k ≤ L, Word T k s := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert s S hs ih =>
      obtain ⟨n, hn⟩ := hST s (Finset.mem_insert_self s S)
      obtain ⟨L, hL⟩ := ih (fun t ht => hST t (Finset.mem_insert_of_mem ht))
      refine ⟨max n L, ?_⟩
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact ⟨n, le_max_left _ _, hn⟩
      · obtain ⟨k, hk, hkt⟩ := hL t ht
        exact ⟨k, le_trans hk (le_max_right _ _), hkt⟩

theorem finite_generators_compare (S T : Finset M)
    (hT : AddSubmonoid.closure (T : Set M) = ⊤) :
    ∃ L : ℕ, ∀ n x y, Near (S : Set M) n (x : X) y → Near (T : Set M) (L * n) x y := by
  obtain ⟨L, hL⟩ := finite_word_bound S (T : Set M)
    (fun s hs => exists_word_of_generates hT s)
  exact ⟨L, fun _ _ _ h => near_compare L hL h⟩

theorem asdimLE_generators_iff (S T : Finset M)
    (hS : AddSubmonoid.closure (S : Set M) = ⊤)
    (hT : AddSubmonoid.closure (T : Set M) = ⊤) (n : ℕ) :
    AsdimLE (natMetric (X := X) (S : Set M)) n ↔
    AsdimLE (natMetric (X := X) (T : Set M)) n := by
  obtain ⟨L, hL⟩ := finite_generators_compare (X := X) S T hT
  obtain ⟨K, hK⟩ := finite_generators_compare (X := X) T S hS
  let d := natMetric (X := X) (S : Set M)
  let e := natMetric (X := X) (T : Set M)
  have h : CoarseEmbedding d e (id : X → X) :=
    { a := max L K
      b := 0
      forward := fun {s x y} h => near_mono
        (by simpa using Nat.mul_le_mul_right s (le_max_left L K)) (hL s x y h)
      backward := fun {s x y} h => near_mono
        (by simpa using Nat.mul_le_mul_right s (le_max_right L K)) (hK s x y h) }
  exact asdimLE_iff_of_quasiIsometry d e h 0 (fun x => ⟨x, near_refl _ x⟩) n

end Schreier
end FiniteAsdim
