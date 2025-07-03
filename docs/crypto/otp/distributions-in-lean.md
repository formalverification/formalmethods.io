# Distributions in Lean

??? info "Recall: Definition of Probability 🎲" 

    +  Ω denotes an **outcome space**

    +  ω ∈ Ω denotes an **outcome** (e.g., of an experiment, trial, etc.)

    +  An **event** 𝐸 is a set of outcomes: 𝐸 ⊆ Ω

    +  A **probability mass function** (pmf), or **probability measure**, on an outcome space is
       a function ℙ : Ω → ℝ such that, for all events 𝐸₀, 𝐸₁, …
        + ℙ ∅ = 0 and ℙ Ω = 1
        + 0 ≤ ℙ 𝐸ᵢ ≤ 1
        + 𝐸ᵢ ⊆ 𝐸ⱼ → ℙ 𝐸ᵢ ≤ ℙ 𝐸ⱼ (monotone)
        + ℙ(⋃ 𝐸ᵢ) ≤ ∑ ℙ 𝐸ᵢ (subadditive)

---

## What is a PMF?

In Lean/Mathlib, a *probability mass function* over a type `α` is denoted `PMF α`.

!!! info "Mathlib's Probability Mass Function type"

    ```lean
    /-- A probability mass function, or discrete probability measure is
      a function `α → ℝ≥0∞` such that the values have (infinite) sum `1`. -/

    def PMF.{u} (α : Type u) : Type u :=
      { f : α → ℝ≥0∞ // HasSum f 1 }
    ```

    So a PMF is a **pair**

    1. A function assigning probabilities to outcomes.

    2. A proof that these probabilities form a valid distribution.

!!! info "Syntax: `{ _ // _ }`"

    In Lean the mathematical expression `{x : P x}` is written `{ x // P x }`.

    Example: `{n : Nat // n % 2 = 0}` is the type of even natural numbers.

---


## Distributions over messages and keys

+  `μM : PMF (Plaintext n)`

    - **Type**: A function `μM : Plaintext n → ℝ≥0∞`, along with proof of `HasSum μM 1`.
    - **Meaning**: For any n-bit message `m`, `μM m = P(M = m)`, the prob message `m` is sent.
    - **Example**: If all messages equally likely, `μM m = 1/2^n` for all `m`.

+  `μK : PMF (Key n)`

    - **Type**: A function `μK : Key n → ℝ≥0∞`, along with proof of `HasSum μK 1`.
    - **Meaning**: For any n-bit key `k`, `μK k` is its probability, `P(K = k)`.
    - **Definition**: `uniformOfFintype` makes `μK k = 1/2^n` for all `k`

+  `μMK : PMF (Plaintext n × Key n)`

    - **Type**: A function `μMK : Plaintext n × Key n → ℝ≥0∞`, with proof of `HasSum μMK 1`.
    - **Meaning**: For message `m` and key `k`, `μMK (m, k)` = the joint prob `P(M = m, K = k)`.
    - **Value**: `μMK (m, k) = μM m * μK k` (independence!)

+  `μC : PMF (Ciphertext n)`

    - **Type**: A function `μC : Ciphertext n → ℝ≥0∞`,  along with proof of `HasSum μC 1`.
    - **Meaning**: For any n-bit ciphertext `c`, `μC c` is probability of observing `c`.
    - **Computed**: By summing over all `(m, k)` pairs that produce `c`

+  `μC_M : Plaintext n → PMF (Ciphertext n)`

    - **Type**: A function that takes a message and returns a distribution on `Ciphertext n`.
    - **Meaning**: For fixed message `m`, `μC_M m = P(C | M = m)`.
    - **Value**: `(μC_M m) c = if ∃k. encrypt m k = c then 1/2^n else 0`

---


## Mathlib Specifics

[`Probability/ProbabilityMassFunction/`][Probability/ProbabilityMassFunction/]

📁 [`Mathlib/Probability/ProbabilityMassFunction/Basic.lean`][Probability/ProbabilityMassFunction/Basic.lean]

+ Often imported as `PMF`.

+ It's the main tool for defining **discrete random variables** and their **distributions**.

🔑️ **Key Concepts**

+  **`PMF α`** represents a **probability mass function** (pmf) over a type `α`;
   it's a function `α → NNReal` (non-negative reals) where the sum over all `a : α` is 1.

+  **`PMF.pure (a : α)`** is a pmf with all mass at `a` (prob 1 for `a`, 0 otherwise).

+  **`PMF.bind (p : PMF α) (f : α → PMF β)`** is used for creating dependent r.v.s;
   given a r.v. `p` and function `f` mapping outcomes of `p` to new r.v.s, `bind` gives the resulting distribution on `β`.

+  `PMF.map (f : α → β) (p : PMF α)`: If we apply a function `f` to the outcomes
   of a r.v. `p`, `map` gives the pmf of the results.

---

### Conditional Probability in Mathlib

📁 [`Mathlib/Probability/ConditionalProbability.lean`][Probability/ConditionalProbability.lean]

 `Probability.ConditionalProbability`

+  [`cond`][cond] is the **conditional probability measure** of measure `μ` on set `s`

+  it is `μ` restricted to `s` and scaled by the inverse of `μ s` (to make it a
   probability measure): `(μ s)⁻¹ • μ.restrict s`

+  **`cond (p : PMF α) (E : Set α)`** gives the conditional pmf given an event `E` <<== check this!!

   we'll use it to define $P(M=m \; | \; C=c)$

**Other notable files**

+ [`Probability/ConditionalExpectation.lean`][Probability/ConditionalExpectation.lean] conditional expectation
+ [`Probability/CondVar.lean`][Probability/CondVar.lean] conditional variance
+ [`Probability/Independence/Conditional.lean`][Probability/Independence/Conditional.lean] conditional independence



---

[Probability/ConditionalExpectation.lean]: https://github.com/leanprover-community/mathlib4/blob/4459088658417ad4ec82b194da3184cbe638b7e0/Mathlib/Probability/ConditionalExpectation.lean
[Probability/ConditionalProbability.lean]: https://github.com/leanprover-community/mathlib4/blob/4459088658417ad4ec82b194da3184cbe638b7e0/Mathlib/Probability/ConditionalProbability.lean
[MeasureTheory/Function/ConditionalExpectation/Basic.lean]: https://github.com/leanprover-community/mathlib4/blob/4459088658417ad4ec82b194da3184cbe638b7e0/Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean
[Probability/Independence/Conditional.lean]: https://github.com/leanprover-community/mathlib4/blob/4459088658417ad4ec82b194da3184cbe638b7e0/Mathlib/Probability/Independence/Conditional.lean
[Probability/ProbabilityMassFunction/]: https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/Probability/ProbabilityMassFunction
[Probability/ProbabilityMassFunction/Basic.lean]: https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Probability/ProbabilityMassFunction/Basic.lean
[cond]: https://github.com/leanprover-community/mathlib4/blob/4459088658417ad4ec82b194da3184cbe638b7e0/Mathlib/Probability/ConditionalProbability.lean#L70-L71
[Probability/CondVar.lean]: https://github.com/leanprover-community/mathlib4/blob/4459088658417ad4ec82b194da3184cbe638b7e0/Mathlib/Probability/CondVar.lean

<!-- [Probability/ConditionalProbability.lean]: https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Probability/ConditionalProbability.lean -->
<!-- [Probability/Independence/Conditional.lean]: https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Probability/Independence/Conditional.lean -->

