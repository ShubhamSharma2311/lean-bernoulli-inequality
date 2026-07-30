import Mathlib

/-!
# Bernoulli's inequality

For `x ≥ -1` and `n : ℕ`, `1 + n·x ≤ (1 + x)ⁿ`.
-/

namespace Bernoulli

/-- The inductive step: `1 + (k + 1)·x ≤ (1 + k·x)(1 + x)` for `k ≥ 0`. -/
lemma step {k : ℝ} (hk : 0 ≤ k) (x : ℝ) : 1 + (k + 1) * x ≤ (1 + k * x) * (1 + x) := by
  nlinarith [mul_nonneg hk (sq_nonneg x)]

/-- **Bernoulli's inequality.** -/
theorem one_add_mul_le_pow {x : ℝ} (hx : -1 ≤ x) (n : ℕ) : 1 + n * x ≤ (1 + x) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h0 : 0 ≤ 1 + x := by linarith
    calc 1 + ((k + 1 : ℕ) : ℝ) * x = 1 + ((k : ℝ) + 1) * x := by push_cast; ring
      _ ≤ (1 + k * x) * (1 + x) := step (Nat.cast_nonneg k) x
      _ ≤ (1 + x) ^ k * (1 + x) := mul_le_mul_of_nonneg_right ih h0
      _ = (1 + x) ^ (k + 1) := (pow_succ _ _).symm

/-- The common special case `0 ≤ x`. -/
theorem one_add_mul_le_pow_of_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : 1 + n * x ≤ (1 + x) ^ n :=
  one_add_mul_le_pow (by linarith) n

/-- Natural-number form at `x = 1`: `n + 1 ≤ 2ⁿ`. -/
theorem succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  sorry

end Bernoulli
