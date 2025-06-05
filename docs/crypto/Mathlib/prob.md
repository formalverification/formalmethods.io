# Probability in L∃∀N

## 🎲 Basic Definitions of Probability Theory

+  Ω denotes an **outcome space** 

+  ω ∈ Ω denotes an **outcome** (e.g., of an experiment, trial, etc.)
   
+  An **event** 𝐸 is a set of outcomes: 𝐸 ⊆ Ω

+  A **probability mass function** (pmf), or **probability measure**, on an outcome space is
   a function ℙ : Ω → ℝ such that, for all events 𝐸₀, 𝐸₁, …
   + ℙ ∅ = 0 and ℙ Ω = 1 
   + 0 ≤ ℙ 𝐸ᵢ ≤ 1 
   + 𝐸ᵢ ⊆ 𝐸ⱼ → ℙ 𝐸ᵢ ≤ ℙ 𝐸ⱼ (monotone)
   + ℙ(⋃ 𝐸ᵢ) ≤ ∑ ℙ 𝐸ᵢ (subadditive)

!!! note "Mathlib's definition"

    It's slightly more direct: it's a function `f : α → NNReal`
    (non-negative reals) along with a proof `h : tsum f = 1` (the sum of `f a` over all
    `a : α` is 1). The other properties above (like monotonicity, probability of empty
    set being 0, etc.) can be derived from this.


---

## Basic Probability in Mathlib

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

## Conditional Probability in Mathlib

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
