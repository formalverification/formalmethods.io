# `bind` and `pure` for Probability Distributions

## `pure`: Creating a Deterministic Distribution

`pure a` creates a probability distribution that always returns `a` with probability 1.

```lean
pure : α → PMF α
pure a = the distribution where P(X = a) = 1 and P(X = b) = 0 for all b ≠ a
```

### Example

```lean
def always_true : PMF Bool := pure true
-- This distribution gives: P(true) = 1, P(false) = 0
```

### In our code

```lean
pure (encrypt m k)
```

creates a distribution that always returns the specific ciphertext `encrypt m k` with probability 1.

---

## `bind`: Chaining Random Processes

`bind` chains two random processes together:

1. First, sample from one distribution.
2. Based on that result, sample from another distribution.

```lean
bind : PMF α → (α → PMF β) → PMF β
```

### Intuitive Explanation

Think of `bind p f` as a two-step random process:

1. Sample `x` from distribution `p`.
2. Use `x` to choose a new distribution `f x`.
3. Sample from `f x` to get the final result.

### Example

```lean
-- Roll a die, then flip that many coins and count heads
def roll_then_flip : PMF Nat :=
  bind die_roll (λ n => flip_n_coins n)
```

---

## Breaking Down Our Expression

```lean
μC = bind μMK (λ (m, k) => pure (encrypt m k))
```

This means:

1. **First step**: sample a pair `(m, k)` from the joint distribution `μMK`
2. **Second step**: Return `encrypt m k` with probability 1

Since the second step is deterministic (`pure`), this simplifies to:

Sample `(m, k)` from `μMK` and output `encrypt m k`.

---

## Why Use `bind` and `pure`?

To build complex probability distributions from simple ones:

```lean
-- Without bind/pure (conceptually):
μC c = Σ {P(M=m, K=k) : (m, k) is such that c = encrypt m k}

-- With bind/pure:
μC = bind μMK (λ (m, k) => pure (encrypt m k))
```

The `bind`/`pure` formulation is cleaner and more compositional.

## The General Pattern

```lean
bind p (λ x => pure (f x)) = map f p
```

When the second step is deterministic (using `pure`), `bind` reduces to `map`.

So we could also write:
```lean
μC = map (λ (m, k) => encrypt m k) μMK
```

## In Probability Terms

- `pure a` is the Dirac delta distribution δ_a
- `bind` is the law of total probability:
  ```
  P(Y = y) = Σ_x P(X = x) · P(Y = y | X = x)
  ```
  where `bind p f` represents the distribution of Y when:

    - X has distribution p
    - Y | X=x has distribution f(x)

## Summary

In `μC = bind μMK (λ (m, k) => pure (encrypt m k))`:

- `μMK` is the joint distribution of (message, key) pairs.
- `bind` says "sample from this distribution."
- `λ (m, k) => pure (encrypt m k)` says "then apply encryption deterministically."
- Result: `μC` is the ciphertexts distribution.

