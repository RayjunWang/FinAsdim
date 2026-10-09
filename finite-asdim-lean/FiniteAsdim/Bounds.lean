import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace FiniteAsdim

/-- The dimension bound of Theorem 1.1. -/
def rankBound : ℕ → ℕ
  | 0 => 0
  | r + 1 => rankBound r + 3 ^ (r + 1)

@[simp] theorem rankBound_zero : rankBound 0 = 0 := rfl

@[simp] theorem rankBound_succ (r : ℕ) :
    rankBound (r + 1) = rankBound r + 3 ^ (r + 1) := rfl

/-- Division-free version of the displayed closed formula. -/
theorem rankBound_closed_mul (r : ℕ) : 2 * rankBound r + 3 = 3 ^ (r + 1) := by
  induction r with
  | zero => decide
  | succ r ih =>
    rw [rankBound_succ, Nat.mul_add, Nat.pow_succ]
    omega

theorem rankBound_closed (r : ℕ) :
    rankBound r = (3 ^ (r + 1) - 3) / 2 := by
  have h := rankBound_closed_mul r
  have hsub : 3 ^ (r + 1) - 3 = 2 * rankBound r := by omega
  rw [hsub, Nat.mul_div_right]
  decide

end FiniteAsdim
