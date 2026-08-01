import Bernoulli.Basic

namespace Bernoulli

example (n : ℕ) : 1 + (n : ℝ) * 2 ≤ (1 + 2) ^ n := one_add_mul_le_pow (by norm_num) n

example : 11 ≤ 2 ^ 10 := succ_le_two_pow 10

end Bernoulli
