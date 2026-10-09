import Mathlib.Algebra.Group.Action.Basic
import Lean.Elab.Tactic.Omega
import FiniteAsdim.Metric

/-!
# Paths and common futures for a commutative monoid action

This file proves the path characterization used in Lemma 3.1 of
arXiv:2609.17177. A generator edge is undirected, even when its action map
is not injective. Every finite path can be put into the form of two forward
words with a common endpoint; the sum of their lengths is the path length.
-/

namespace FiniteAsdim
namespace Schreier

variable {M X : Type*} [AddCommMonoid M] [AddAction M X]

/-- A word of exactly `n` generators, with value `a`. -/
inductive Word (S : Set M) : ℕ → M → Prop
  | zero : Word S 0 0
  | cons {n : ℕ} {a : M} (s : M) : s ∈ S → Word S n a → Word S (n + 1) (s + a)

/-- The undirected generator relation. -/
def Edge (S : Set M) (x y : X) : Prop :=
  ∃ s ∈ S, s +ᵥ x = y ∨ s +ᵥ y = x

/-- A path of exactly `n` edges in the undirected Schreier graph. -/
inductive Path (S : Set M) : ℕ → X → X → Prop
  | nil (x : X) : Path S 0 x x
  | cons {n : ℕ} {x y z : X} : Edge S x y → Path S n y z → Path S (n + 1) x z

def Near (S : Set M) (n : ℕ) (x y : X) : Prop :=
  ∃ k ≤ n, Path S k x y

/-- A common future reached with at most `n` generator letters in total. -/
def CommonFuture (S : Set M) (n : ℕ) (x y : X) : Prop :=
  ∃ l k a b, Word S l a ∧ Word S k b ∧ l + k ≤ n ∧ a +ᵥ x = b +ᵥ y

theorem edge_symm {S : Set M} {x y : X} (h : Edge S x y) : Edge S y x := by
  rcases h with ⟨s, hs, h | h⟩
  · exact ⟨s, hs, Or.inr h⟩
  · exact ⟨s, hs, Or.inl h⟩

theorem path_append {S : Set M} {n m : ℕ} {x y z : X}
    (h : Path S n x y) (k : Path S m y z) : Path S (n + m) x z := by
  induction h with
  | nil => simpa using k
  | cons e p ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Path.cons e (ih k)

theorem path_symm {S : Set M} {n : ℕ} {x y : X}
    (h : Path S n x y) : Path S n y x := by
  induction h with
  | nil x => exact Path.nil x
  | @cons n x y z e p ih =>
      simpa using path_append ih (Path.cons (edge_symm e) (Path.nil x))

theorem word_add {S : Set M} {n m : ℕ} {a b : M}
    (h : Word S n a) (k : Word S m b) : Word S (n + m) (a + b) := by
  induction h with
  | zero => simpa using k
  | cons s hs w ih =>
      simpa [add_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Word.cons s hs ih

theorem word_path {S : Set M} {n : ℕ} {a : M}
    (h : Word S n a) (x : X) : Path S n x (a +ᵥ x) := by
  induction h generalizing x with
  | zero => simpa using Path.nil (S := S) x
  | cons s hs w ih =>
      have e : Edge S x (s +ᵥ x) := ⟨s, hs, Or.inl rfl⟩
      simpa [← add_vadd, add_comm] using Path.cons e (ih (s +ᵥ x))

/-- Commutativity allows the forward and backward letters of a path to
be collected without requiring any action map to be injective. -/
theorem path_common_future {S : Set M} {n : ℕ} {x y : X}
    (h : Path S n x y) :
    ∃ l k a b, Word S l a ∧ Word S k b ∧ l + k = n ∧ a +ᵥ x = b +ᵥ y := by
  induction h with
  | nil x => exact ⟨0, 0, 0, 0, Word.zero, Word.zero, rfl, rfl⟩
  | @cons n x z y e p ih =>
      rcases ih with ⟨l, k, a, b, ha, hb, hlk, hab⟩
      rcases e with ⟨s, hs, hxs | hsx⟩
      · refine ⟨l + 1, k, s + a, b, Word.cons s hs ha, hb, by omega, ?_⟩
        calc
          (s + a) +ᵥ x = a +ᵥ (s +ᵥ x) := by rw [add_comm s a, add_vadd]
          _ = a +ᵥ z := by rw [hxs]
          _ = b +ᵥ y := hab
      · refine ⟨l, k + 1, a, s + b, ha, Word.cons s hs hb, by omega, ?_⟩
        calc
          a +ᵥ x = a +ᵥ (s +ᵥ z) := by rw [hsx]
          _ = s +ᵥ (a +ᵥ z) := by rw [← add_vadd, add_comm a s, add_vadd]
          _ = s +ᵥ (b +ᵥ y) := by rw [hab]
          _ = (s + b) +ᵥ y := by rw [add_vadd]

theorem near_iff_common_future {S : Set M} {n : ℕ} {x y : X} :
    Near S n x y ↔ CommonFuture S n x y := by
  constructor
  · rintro ⟨d, hd, hp⟩
    rcases path_common_future hp with ⟨l, k, a, b, ha, hb, heq, hab⟩
    exact ⟨l, k, a, b, ha, hb, by omega, hab⟩
  · rintro ⟨l, k, a, b, ha, hb, hlen, hab⟩
    refine ⟨l + k, hlen, ?_⟩
    have hb' : Path S k (b +ᵥ y) y := path_symm (word_path hb y)
    rw [← hab] at hb'
    exact path_append (word_path ha x) hb'

/-- A collision remains a collision at every forward image. -/
theorem collision_forward_invariant {a b c : M} {x : X}
    (h : a +ᵥ x = b +ᵥ x) : a +ᵥ (c +ᵥ x) = b +ᵥ (c +ᵥ x) := by
  calc
    a +ᵥ (c +ᵥ x) = c +ᵥ (a +ᵥ x) := by rw [← add_vadd, add_comm a c, add_vadd]
    _ = c +ᵥ (b +ᵥ x) := by rw [h]
    _ = b +ᵥ (c +ᵥ x) := by rw [← add_vadd, add_comm c b, add_vadd]

theorem common_future_forward_invariant {S : Set M} {n : ℕ} {x y : X}
    (h : CommonFuture S n x y) (c : M) :
    CommonFuture S n (c +ᵥ x) (c +ᵥ y) := by
  rcases h with ⟨l, k, a, b, ha, hb, hn, hab⟩
  refine ⟨l, k, a, b, ha, hb, hn, ?_⟩
  calc
    a +ᵥ (c +ᵥ x) = c +ᵥ (a +ᵥ x) := by rw [← add_vadd, add_comm a c, add_vadd]
    _ = c +ᵥ (b +ᵥ y) := by rw [hab]
    _ = b +ᵥ (c +ᵥ y) := by rw [← add_vadd, add_comm c b, add_vadd]

theorem near_forward_invariant {S : Set M} {n : ℕ} {x y : X}
    (h : Near S n x y) (c : M) : Near S n (c +ᵥ x) (c +ᵥ y) :=
  near_iff_common_future.mpr (common_future_forward_invariant (near_iff_common_future.mp h) c)

theorem near_refl (S : Set M) (x : X) : Near S 0 x x := ⟨0, le_rfl, Path.nil x⟩

theorem near_symm {S : Set M} {n : ℕ} {x y : X}
    (h : Near S n x y) : Near S n y x := by
  rcases h with ⟨k, hk, hp⟩
  exact ⟨k, hk, path_symm hp⟩

theorem near_mono {S : Set M} {n m : ℕ} {x y : X}
    (hnm : n ≤ m) (h : Near S n x y) : Near S m x y := by
  rcases h with ⟨k, hk, hp⟩
  exact ⟨k, le_trans hk hnm, hp⟩

theorem near_triangle {S : Set M} {n m : ℕ} {x y z : X}
    (h : Near S n x y) (k : Near S m y z) : Near S (n + m) x z := by
  rcases h with ⟨l, hl, hp⟩
  rcases k with ⟨j, hj, kp⟩
  exact ⟨l + j, Nat.add_le_add hl hj, path_append hp kp⟩

theorem path_zero {S : Set M} {x y : X} (h : Path S 0 x y) : x = y := by
  cases h
  rfl

theorem near_zero {S : Set M} {x y : X} (h : Near S 0 x y) : x = y := by
  rcases h with ⟨k, hk, hp⟩
  have hk0 : k = 0 := by omega
  subst k
  exact path_zero hp

/-- The integer-valued extended graph metric of the action. -/
def natMetric (S : Set M) : NatMetric X where
  near := Near S
  refl := near_refl S
  symm := near_symm
  mono := near_mono
  triangle := near_triangle
  separated := near_zero

/-- Forward invariance of a subset under every element of the monoid. -/
def Invariant (A : Set X) : Prop := ∀ (c : M) (x : X), x ∈ A → c +ᵥ x ∈ A

/-- The restricted action on a forward invariant subset. -/
@[reducible] def addActionOn (A : Set X) (hA : Invariant (M := M) A) : AddAction M A where
  vadd c x := ⟨c +ᵥ x.val, hA c x.val x.property⟩
  zero_vadd x := Subtype.ext (zero_vadd (M := M) x.val)
  add_vadd c d x := Subtype.ext (add_vadd c d x.val)

/-- An invariant subset's intrinsic Schreier metric equals the restricted
ambient metric. This is the second conclusion of Lemma 3.1. -/
theorem invariant_near_iff (A : Set X) (hA : Invariant (M := M) A)
    (S : Set M) (n : ℕ) (x y : A) :
    letI := addActionOn A hA
    Near S n x y ↔ Near S n x.val y.val := by
  letI := addActionOn A hA
  rw [near_iff_common_future, near_iff_common_future]
  constructor
  · rintro ⟨l, k, a, b, ha, hb, hn, hab⟩
    exact ⟨l, k, a, b, ha, hb, hn, congrArg Subtype.val hab⟩
  · rintro ⟨l, k, a, b, ha, hb, hn, hab⟩
    exact ⟨l, k, a, b, ha, hb, hn, Subtype.ext hab⟩

theorem word_near {S : Set M} {n : ℕ} {c : M}
    (hc : Word S n c) (x : X) : Near S n x (c +ᵥ x) :=
  ⟨n, le_rfl, word_path hc x⟩

/-- The forward image is uniformly dense in an invariant subset.
Combined with `invariant_near_iff`, this gives the last conclusion of
Lemma 3.1 whenever the chosen generators generate `c`. -/
theorem forward_image_dense (A : Set X) (hA : Invariant (M := M) A)
    {S : Set M} {n : ℕ} {c : M} (hc : Word S n c) (x : A) :
    ∃ y : A, (∃ z : A, c +ᵥ z.val = y.val) ∧ Near S n x.val y.val := by
  refine ⟨⟨c +ᵥ x.val, hA c x.val x.property⟩, ⟨x, rfl⟩, ?_⟩
  exact word_near hc x.val

section EquivariantMaps

variable {Y : Type*} [AddAction M Y]

def Equivariant (f : X → Y) : Prop :=
  ∀ (c : M) (x : X), f (c +ᵥ x) = c +ᵥ f x

theorem edge_map {S : Set M} {f : X → Y} (hf : Equivariant (M := M) f)
    {x y : X} (h : Edge S x y) : Edge S (f x) (f y) := by
  rcases h with ⟨s, hs, h | h⟩
  · exact ⟨s, hs, Or.inl (by rw [← hf, h])⟩
  · exact ⟨s, hs, Or.inr (by rw [← hf, h])⟩

theorem path_map {S : Set M} {f : X → Y} (hf : Equivariant (M := M) f)
    {n : ℕ} {x y : X} (h : Path S n x y) : Path S n (f x) (f y) := by
  induction h with
  | nil x => exact Path.nil (f x)
  | cons e p ih => exact Path.cons (edge_map hf e) ih

theorem near_map {S : Set M} {f : X → Y} (hf : Equivariant (M := M) f)
    {n : ℕ} {x y : X} (h : Near S n x y) : Near S n (f x) (f y) := by
  rcases h with ⟨k, hk, hp⟩
  exact ⟨k, hk, path_map hf hp⟩

/-- For equivariant quotients of commutative monoid actions, the bounded
fiber diameter gives an additive distortion bound. This is stronger than
the edge-by-edge bound `(D + 1) * n + D` in Lemma 3.2 of the paper. -/
theorem near_reflects_of_bounded_fibers {S : Set M} {f : X → Y}
    (hf : Equivariant (M := M) f) (D : ℕ)
    (hD : ∀ x y, f x = f y → Near S D x y)
    {n : ℕ} {x y : X} (h : Near S n (f x) (f y)) : Near S (n + D) x y := by
  rcases near_iff_common_future.mp h with ⟨l, k, a, b, ha, hb, hn, hab⟩
  have hfut : f (a +ᵥ x) = f (b +ᵥ y) := by rw [hf, hf]; exact hab
  have hmid := hD (a +ᵥ x) (b +ᵥ y) hfut
  have hstart := word_near ha x
  have hend := near_symm (word_near hb y)
  have hchain := near_triangle (near_triangle hstart hmid) hend
  exact near_mono (by omega) hchain

theorem near_reflects_quotient_bound {S : Set M} {f : X → Y}
    (hf : Equivariant (M := M) f) (D : ℕ)
    (hD : ∀ x y, f x = f y → Near S D x y)
    {n : ℕ} {x y : X} (h : Near S n (f x) (f y)) :
    Near S ((D + 1) * n + D) x y := by
  apply near_mono _ (near_reflects_of_bounded_fibers hf D hD h)
  have hprod : n ≤ (D + 1) * n := by
    calc
      n = 1 * n := by simp
      _ ≤ (D + 1) * n := Nat.mul_le_mul_right n (by omega)
  omega

end EquivariantMaps

end Schreier
end FiniteAsdim

