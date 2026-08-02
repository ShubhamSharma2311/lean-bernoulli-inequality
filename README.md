# Bernoulli's Inequality

`1 + n·x ≤ (1 + x)ⁿ` for real `x ≥ -1`, by induction on `n`.

Formalised in Lean 4 with Mathlib. No `sorry`.

## Proof outline

1. `(1 + kx)(1 + x) = 1 + (k + 1)x + kx²` and `kx² ≥ 0`.
2. For `x ≥ -1` the factor `1 + x` is non-negative, so the inductive hypothesis can be multiplied by it.
3. Chaining the two inequalities closes the induction.

## Contents

- [`Bernoulli/Basic.lean`](Bernoulli/Basic.lean): the main development
- [`Bernoulli/Examples.lean`](Bernoulli/Examples.lean): small worked examples

Declarations:

- `Bernoulli.step`
- `Bernoulli.one_add_mul_le_pow`
- `Bernoulli.one_add_mul_le_pow_of_nonneg`
- `Bernoulli.succ_le_two_pow`

## Build

```
lake exe cache get
lake build
```

Toolchain: `leanprover/lean4:v4.33.0-rc1`.
