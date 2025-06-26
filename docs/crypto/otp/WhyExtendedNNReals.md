# Deep Dive

## Why use [0, ∞] for the codomain of a distribution?

- Probabilities should be in [0, 1] by definition.
- If p + q > 1, then p + q isn't a probability of anything.
- A rich type system should enforce this constraint.
- Having to prove preservation of [0, 1] keeps us mathematically honest.

So why did Mathlib choose `ENNReal`?  The reasons are probably subtle, but we can
at least speculate and provide some food for thought and further discussion.


1.  **Integration with Measure Theory**. (pardon the pun)


    In measure theory, measures assign values in [0,∞] to sets.

    The measure of a set `S`, denoted `μ S`, is an extended nonnegative real.

    A measure `μ` is called a probability measure if `μ univ = 1`.

    The designers of Mathlib likely wanted PMFs that integrate seamlessly with the
    measure theory library, where `ENNReal` is standard.

    !!! info "Measures and outer measures in Mathlib"

         ```lean
         /-- An outer measure is a countably subadditive monotone function that sends `∅` to `0`.
         -/
         structure OuterMeasure (α : Type*) where
           protected measureOf : Set α → ℝ≥0∞
           protected empty : measureOf ∅ = 0
           protected mono : ∀ {s₁ s₂}, s₁ ⊆ s₂ → measureOf s₁ ≤ measureOf s₂
           protected iUnion_nat : ∀ s : ℕ → Set α, Pairwise (Disjoint on s) →
             measureOf (⋃ i, s i) ≤ ∑' i, measureOf (s i)

         /-- A measure is defined to be an outer measure that is countably additive on
         measurable sets, with the assumption that the outer measure is the canonical
         extension of the restricted measure.
         -/
         structure Measure (α : Type*) [MeasurableSpace α] extends OuterMeasure α
           where m_iUnion ⦃f : ℕ → Set α⦄ :
           (∀ i, MeasurableSet (f i)) → Pairwise (Disjoint on f) →
             toOuterMeasure (⋃ i, f i) = ∑' i, toOuterMeasure (f i)

         class IsProbabilityMeasure (μ : Measure α) : Prop where
           measure_univ : μ univ = 1
         ```


2.  **Division Conventions**

    `ENNReal` has specific conventions that make probability formulas work. These would be messier and require more special case analysis with a [0, 1] type.

    !!! info "Division in `EENReal`" 

        ```lean
        -- In ENNReal:
        0 / 0 = 0    -- Makes conditional probability P(A|B) work when P(B) = 0
        x / ∞ = 0    -- Handles certain limit cases
        x / 0 = ∞    -- for x > 0
        ```

     


---

## The Pragmatic Compromise

Philosophically, a `Probability` type should be:

```lean
def Probability := {x : ℝ // 0 ≤ x ∧ x ≤ 1}
```

And operations should return proofs:

```lean
def prob_or (p q : Probability) (h : disjoint) : Probability :=
  ⟨p.val + q.val, by proof_that_sum_le_1⟩
```

Mathlib probably chose `ENNReal` for pragmatic reasons:

1. **Compatibility** with measure theory (the bigger framework)
2. **Computational** convenience (limits and sums "just work")
3. **Mathematical** practice (probabilists often work with unnormalized measures)

But this loses "type safety." A more principled approach might have:

```lean
-- The "right" design?
structure PMF (α : Type*) where
  val : α → Probability  -- Each value is certified in [0,1]
  has_sum_one : ∑ val = 1
```

## Final Thoughts

### Honest Bottom Line

A real tension in library design:

- **Type safety** says: enforce invariants in types
- **Pragmatism** says: make it compatible with existing math
- **Mathlib chose** pragmatism over purity here

### Summary

+  Mathlib uses [0, ∞] for probability values, which might seem wrong---probabilities
   should be in [0,1]!

+  A pragmatic choice for integration with measure theory and handling limits.

+  In a perfect world, we might use a `Probability` type that restricts inhabitants
   to [0, 1].

+  Mathlib prioritizes compatibility with the broader mathematical ecosystem over type safety here.

