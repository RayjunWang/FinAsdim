import Mathlib.Data.Set.Card

/-!
# Integer-valued extended metrics and partition asymptotic dimension

`near s x y` means that the distance between `x` and `y` is at most the
natural number `s`. Points in different components are never near.
This relation representation avoids any convention for infinity arithmetic.

The partition is represented by an arbitrary label function. Its nonempty
fibers are exactly its parts; there is no finiteness assumption on the
total number of parts. The cardinality bound uses `encard`, which assigns
infinity to infinite sets rather than the junk value zero of `ncard`.
-/

namespace FiniteAsdim

universe u v

structure NatMetric (X : Type u) where
  near : ℕ → X → X → Prop
  refl : ∀ x, near 0 x x
  symm : ∀ {s x y}, near s x y → near s y x
  mono : ∀ {s t x y}, s ≤ t → near s x y → near t x y
  triangle : ∀ {s t x y z}, near s x y → near t y z → near (s + t) x z
  separated : ∀ {x y}, near 0 x y → x = y

namespace NatMetric

variable {X : Type u} (d : NatMetric X)

theorem ext {e : NatMetric X} (h : ∀ s x y, d.near s x y ↔ e.near s x y) : d = e := by
  cases d with
  | mk nd rd sd md td zd =>
    cases e with
    | mk ne re se me te ze =>
      have he : nd = ne := funext fun s => funext fun x => funext fun y => propext (h s x y)
      subst ne
      rfl

def ball (x : X) (s : ℕ) : Set X := {y | d.near s x y}

theorem mem_ball_self (x : X) (s : ℕ) : x ∈ d.ball x s :=
  d.mono (Nat.zero_le s) (d.refl x)

def restrict (A : Set X) : NatMetric A where
  near s x y := d.near s x.val y.val
  refl x := d.refl x.val
  symm h := d.symm h
  mono hst h := d.mono hst h
  triangle h₁ h₂ := d.triangle h₁ h₂
  separated h := Subtype.ext (d.separated h)

theorem recenter {s : ℕ} {x a y : X}
    (ha : a ∈ d.ball x s) (hy : y ∈ d.ball x s) :
    y ∈ d.ball a (2 * s) := by
  have h := d.triangle (d.symm ha) hy
  simpa [two_mul] using h

end NatMetric

/-- A uniformly bounded partition with at most `m` parts meeting each `s`-ball. -/
def ScalePartition {X : Type u} (d : NatMetric X) (s m : ℕ) : Prop :=
  ∃ (I : Type u) (label : X → I) (D : ℕ),
    (∀ x y, label x = label y → d.near D x y) ∧
    (∀ x, (label '' d.ball x s).encard ≤ (m : ℕ∞))

/-- The partition definition in Definition 2.1 of arXiv:2609.17177v1. -/
def AsdimLE {X : Type u} (d : NatMetric X) (n : ℕ) : Prop :=
  ∀ s : ℕ, 1 ≤ s → ScalePartition d s (n + 1)

end FiniteAsdim
