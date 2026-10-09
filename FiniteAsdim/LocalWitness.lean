import FiniteAsdim.Compression
import FiniteAsdim.Schreier
import FiniteAsdim.Quotient

namespace FiniteAsdim
namespace Schreier

variable {M : Type*} [AddCommMonoid M]

/-- A generating set supplies a finite word for every monoid element. -/
theorem exists_word_of_mem_closure (S : Set M) {a : M}
    (ha : a ∈ AddSubmonoid.closure S) : ∃ n, Word S n a := by
  induction ha using AddSubmonoid.closure_induction with
  | mem a ha => exact ⟨1, by simpa using Word.cons a ha (Word.zero (S := S))⟩
  | zero => exact ⟨0, Word.zero⟩
  | add a b ha hb iha ihb =>
      rcases iha with ⟨n, hn⟩
      rcases ihb with ⟨m, hm⟩
      exact ⟨n + m, word_add hn hm⟩

private noncomputable def wordValues (S : Finset M) : ℕ → Finset M
  | 0 => {0}
  | n + 1 => by
      classical
      exact S.biUnion (fun u => (wordValues S n).image (fun a => u + a))

private lemma word_mem_values (S : Finset M) {n : ℕ} {a : M}
    (ha : Word (S : Set M) n a) : a ∈ wordValues S n := by
  classical
  induction ha with
  | zero => simp [wordValues]
  | cons u hu hw ih =>
      exact Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_image.mpr ⟨_, ih, rfl⟩⟩

private lemma values_word (S : Finset M) (n : ℕ) {a : M}
    (ha : a ∈ wordValues S n) : Word (S : Set M) n a := by
  classical
  induction n generalizing a with
  | zero =>
      have hazero : a = 0 := by simpa [wordValues] using ha
      subst a
      exact Word.zero
  | succ n ih =>
      rcases Finset.mem_biUnion.mp ha with ⟨u, hu, hau⟩
      rcases Finset.mem_image.mp hau with ⟨b, hb, rfl⟩
      exact Word.cons u hu (ih hb)

private noncomputable def wordBallValues (S : Finset M) (s : ℕ) : Finset M := by
  classical
  exact (Finset.range (s + 1)).biUnion (wordValues S)

private lemma word_mem_ballValues (S : Finset M) {n s : ℕ} {a : M}
    (hn : n ≤ s) (ha : Word (S : Set M) n a) : a ∈ wordBallValues S s := by
  classical
  exact Finset.mem_biUnion.mpr ⟨n, Finset.mem_range.mpr (by omega), word_mem_values S ha⟩

private lemma ballValues_word (S : Finset M) (s : ℕ) {a : M}
    (ha : a ∈ wordBallValues S s) : ∃ n ≤ s, Word (S : Set M) n a := by
  classical
  rcases Finset.mem_biUnion.mp ha with ⟨n, hn, ha⟩
  exact ⟨n, by have := Finset.mem_range.mp hn; omega, values_word S n ha⟩

end Schreier

private lemma diagonal_complement {r : ℕ} (P : AddSubmonoid (Lattice r))
    (S : Finset P) {n : ℕ} {b : P} (hb : Schreier.Word (S : Set P) n b) :
    n • (∑ u ∈ S, u).val - b.val ∈ P := by
  classical
  induction hb with
  | zero => simp
  | @cons n b u hu hw ih =>
      have hucomp : (∑ v ∈ S, v).val - u.val ∈ P := by
        have heq : (∑ v ∈ S, v).val - u.val = (∑ v ∈ S.erase u, v).val := by
          have hh := congrArg Subtype.val (Finset.add_sum_erase S (fun v : P => v) hu)
          change u.val + (∑ v ∈ S.erase u, v).val = (∑ v ∈ S, v).val at hh
          rw [← hh]
          simp
        rw [heq]
        exact (∑ v ∈ S.erase u, v).property
      have hh := P.add_mem hucomp ih
      have heq : (n + 1) • (∑ v ∈ S, v).val - (u + b).val =
          ((∑ v ∈ S, v).val - u.val) + (n • (∑ v ∈ S, v).val - b.val) := by
        simp only [AddSubmonoid.coe_add, succ_nsmul]
        abel
      rwa [heq]

private lemma bounded_diagonal_complement {r : ℕ} (P : AddSubmonoid (Lattice r))
    (S : Finset P) {n s : ℕ} {b : P} (hn : n ≤ s)
    (hb : Schreier.Word (S : Set P) n b) :
    s • (∑ u ∈ S, u).val - b.val ∈ P := by
  have hh := P.add_mem (P.nsmul_mem (∑ u ∈ S, u).property (s - n))
    (diagonal_complement P S hb)
  have heq : (s - n) • (∑ u ∈ S, u).val +
      (n • (∑ u ∈ S, u).val - b.val) = s • (∑ u ∈ S, u).val - b.val := by
    rw [← add_sub_assoc, ← add_nsmul, Nat.sub_add_cancel hn]
  rwa [heq] at hh

/-- Corollary 6.4, as an actual bounded displacement map and finite injectivity test. -/
theorem local_freeness_witness {r : ℕ} (P : AddSubmonoid (Lattice r))
    (hgen : AddSubgroup.closure (P : Set (Lattice r)) = ⊤)
    {X : Type*} [AddAction P X] (hbounded : Schreier.BoundedToOneAction P X)
    (S : Finset P) (hS : AddSubmonoid.closure (S : Set P) = ⊤)
    (s : ℕ) :
    ∃ K : Finset P, ∃ B : ℕ, ∃ f : X → X,
      (∀ y, Schreier.Near (S : Set P) B y (f y)) ∧
      (∀ x, (K : Set P).InjOn (fun p => p +ᵥ x) →
        (f '' (Schreier.natMetric (S : Set P)).ball x s).encard ≤ (3 ^ r : ℕ∞)) := by
  classical
  let h : P := ∑ u ∈ S, u
  let sh : P := s • h
  let V : Finset P := Schreier.wordBallValues S s
  have hVcomp : ∀ b ∈ V, sh.val - b.val ∈ P := by
    intro b hb
    rcases Schreier.ballValues_word S s hb with ⟨n, hn, hword⟩
    exact bounded_diagonal_complement P S hn hword
  let complement : P → P := fun b =>
    if hb : b ∈ V then ⟨sh.val - b.val, hVcomp b hb⟩ else 0
  let F : Finset P := (V.product V).image (fun z => z.1 + complement z.2)
  have hforward : ∀ x y : X, Schreier.Near (S : Set P) s x y →
      ∃ m ∈ F, sh +ᵥ y = m +ᵥ x := by
    intro x y hxy
    rcases Schreier.near_iff_common_future.mp hxy with ⟨n, k, a, b, ha, hb, hnk, hab⟩
    have haV : a ∈ V := Schreier.word_mem_ballValues S (by omega) ha
    have hbV : b ∈ V := Schreier.word_mem_ballValues S (by omega) hb
    refine ⟨a + complement b, Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨haV, hbV⟩, rfl⟩, ?_⟩
    have hcb : complement b + b = sh := by
      apply Subtype.ext
      simp [complement, hbV]
    calc
      sh +ᵥ y = (complement b + b) +ᵥ y := by rw [hcb]
      _ = complement b +ᵥ (b +ᵥ y) := add_vadd _ _ _
      _ = complement b +ᵥ (a +ᵥ x) := by rw [hab]
      _ = (a + complement b) +ᵥ x := by rw [← add_vadd, add_comm]
  obtain ⟨K, L, lambda, hL, hcompression⟩ := finite_pattern_compression P hgen hbounded F
  have hwords : ∀ p : P, ∃ n, Schreier.Word (S : Set P) n p := by
    intro p
    apply Schreier.exists_word_of_mem_closure
    rw [hS]
    trivial
  choose len hlen using hwords
  let B := len sh + L.sup len
  let f : X → X := fun y => lambda (sh +ᵥ y) +ᵥ (sh +ᵥ y)
  refine ⟨K, B, f, ?_, ?_⟩
  · intro y
    have hh := Schreier.near_triangle (Schreier.word_near (hlen sh) y)
      (Schreier.word_near (hlen (lambda (sh +ᵥ y))) (sh +ᵥ y))
    apply Schreier.near_mono _ hh
    exact Nat.add_le_add_left (Finset.le_sup (hL (sh +ᵥ y))) _
  intro x hx
  let C : Finset P := F.image (fun m => m + lambda (m +ᵥ x))
  have hC : C.card ≤ 3 ^ r := hcompression x hx
  have hsub : f '' (Schreier.natMetric (S : Set P)).ball x s ⊆
      (fun p : P => p +ᵥ x) '' (C : Set P) := by
    rintro z ⟨y, hy, rfl⟩
    obtain ⟨m, hm, heq⟩ := hforward x y hy
    refine ⟨m + lambda (m +ᵥ x), Finset.mem_image.mpr ⟨m, hm, rfl⟩, ?_⟩
    dsimp [f]
    rw [heq, ← add_vadd, add_comm]
  calc
    _ ≤ ((fun p : P => p +ᵥ x) '' (C : Set P)).encard := Set.encard_le_encard hsub
    _ ≤ (C : Set P).encard := Set.encard_image_le _ _
    _ = (C.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _
    _ ≤ (3 ^ r : ℕ∞) := ENat.coe_le_coe.mpr hC

end FiniteAsdim

