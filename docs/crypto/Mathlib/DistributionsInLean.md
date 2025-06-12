# Deep Dive: How Lean Represents Probability Distributions

## What is a PMF Really?

In Lean/Mathlib, a `PMF α` (Probability Mass Function) is fundamentally:

```lean
/-- A probability mass function, or discrete probability measures is 
  a function `α → ℝ≥0∞` such that the values have (infinite) sum `1`. -/

def PMF.{u} (α : Type u) : Type u :=
  { f : α → ℝ≥0∞ // HasSum f 1 }
```

So a PMF is a **pair**

1. A function assigning probabilities to outcomes.

2. A proof that these probabilities form a valid distribution.

---

## Our Distributions as Mathematical Objects

### μM : PMF (Plaintext n)

- **Type**: A function `Plaintext n → ℝ≥0∞` (plus a proof).
- **Meaning**: For any n-bit message m, `μM m` is the probability that message m is sent.
- **Example**: If all messages equally likely, `μM m = 1/2^n` for all m.

### μK : PMF (Key n)  

- **Type**: A function `Key n → ℝ≥0∞`
- **Meaning**: For any n-bit key k, `μK k` is its probability
- **Definition**: `uniformOfFintype` makes `μK k = 1/2^n` for all k

### μMK : PMF (Plaintext n × Key n)

- **Type**: A function `(Plaintext n × Key n) → ℝ≥0∞`
- **Meaning**: Joint probability P(M = m ∧ K = k)
- **Value**: `μMK (m,k) = μM m * μK k` (independence!)

### μC : PMF (Ciphertext n)

- **Type**: A function `Ciphertext n → ℝ≥0∞`  
- **Meaning**: For any n-bit ciphertext c, `μC c` is probability of observing c
- **Computed**: By summing over all (m,k) pairs that produce c

### μC_M : Plaintext n → PMF (Ciphertext n)

- **Type**: A function that takes a message and returns a distribution
- **Meaning**: For fixed m, `μC_M m` is the conditional distribution P(C | M = m)
- **Value**: `(μC_M m) c = if ∃k. encrypt m k = c then 1/2^n else 0`

---

## Why `noncomputable`?

This is subtle! Even though we're dealing with finite types, these definitions are `noncomputable` because:

### 1. Real Number Arithmetic

```lean
noncomputable def μK {n : ℕ} : PMF (Key n) := uniformOfFintype (Key n)
```

The probability values are in `ℝ≥0∞` (extended non-negative reals), not rationals:

- `1/2ⁿ` is computed as real division, not rational division
- Real arithmetic is inherently noncomputable in constructive mathematics
- Even though we "know" the answer is rational, the type system uses reals


### 2. Infinite Summations

Even for finite types, PMF uses infinite summation machinery:

```lean
∑' a : α, p a  -- This is an infinite sum operator
```

- The `∑'` notation works for both finite and infinite types.
- It's defined using limits and topology.
- Even when `α` is finite, we use the general machinery.


### 3. Classical Logic

PMF operations often use classical logic (excluded middle):

```lean
open Classical  -- Needed for many probability operations
```

This makes things noncomputable in Lean's constructive logic.

---

## Why Can We Still Prove `= 1/8`?

Here's the beautiful part: **noncomputable doesn't mean we can't reason about values**!

### Proofs vs Computation

```lean
-- We can't compute this:
#eval μK ⟨[true, false, true], by decide⟩  -- Error: noncomputable

-- But we CAN prove this:
example : μK ⟨[true, false, true], by decide⟩ = 1/8 := by
  simp [μK, uniformOfFintype_apply]
  -- Proves that (card (Key 3))⁻¹ = 8⁻¹ = 1/8
```

### What's Happening?

1. **Definitional unfolding**: Even though `μK` is noncomputable, we can unfold its definition in proofs.

2. **Symbolic reasoning**: We prove `1/card(Key 3) = 1/8` symbolically, not by computation.

3. **Type class inference**: Lean knows `Fintype (Key 3)` and can reason about cardinalities.

4. **Real number lemmas**: Mathlib has lemmas about real arithmetic that we use in proofs.

---

## The Philosophical Point

This separation between computation and reasoning is fundamental:

- **Computation**: Running an algorithm to get a concrete answer.
- **Reasoning**: Proving properties about mathematical objects.

In formal mathematics, we often work with noncomputable objects (like real numbers, infinite sets, choice functions) but can still prove precise theorems about them.

### Summary

+ In Lean, probability distributions are functions from outcomes to probabilities, bundled with a proof that probabilities sum to 1.

+ Even though we work with finite spaces, these are marked `noncomputable` because they use real number arithmetic and infinite summation machinery. 

+ This doesn't limit our reasoning---we can still prove exact results like "each key has probability 1/8."

+ The distinction between computation and proof is fundamental: we reason symbolically about these mathematical objects without needing to compute their values."

+ Practical Analogy

     - **Computable**: a calculator gives you 0.125 when you type 1 ÷ 8.
     - **Noncomputable with proofs**: we can show algebraically that 1/8 = 0.125 without calculating

     PMFs in Lean are the second kind---we work with them symbolically and prove properties, rather than computing decimal expansions.

---

