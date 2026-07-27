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
  sorry

end Bernoulli
