# Deep Dive: Why use [0, ∞] for the codomain of a distribution?

- Probabilities should be in [0, 1] by definition.
- If p + q > 1, then p + q isn't a probability of anything.
- A rich type system should enforce this constraint.
- Having to prove preservation of [0, 1] keeps us mathematically honest.

So why did Mathlib choose `ENNReal`? The reasons are probably subtle, but we can speculate.

---

## 1. **Integration with Measure Theory**

This is probably the biggest reason:

```lean
/-- In measure theory, measures assign values in [0,∞] to sets.

A measure is defined to be an outer measure that is countably additive on
measurable sets, with the assumption that the outer measure is the canonical
extension of the restricted measure.

The measure of a set `s`, denoted `μ s`, is an extended nonnegative real.

The real-valued version is written `μ.real s`.
-/
structure Measure (α : Type*) [MeasurableSpace α] extends OuterMeasure α where
  m_iUnion ⦃f : ℕ → Set α⦄ : (∀ i, MeasurableSet (f i)) → Pairwise (Disjoint on f) →
    toOuterMeasure (⋃ i, f i) = ∑' i, toOuterMeasure (f i)
  trim_le : toOuterMeasure.trim ≤ toOuterMeasure
```

```lean
/-- A measure `μ` is called a probability measure if `μ univ = 1`. -/
class IsProbabilityMeasure (μ : Measure α) : Prop where
  measure_univ : μ univ = 1
```

PMFs are designed to integrate seamlessly with measure theory, where `ENNReal` is standard.


---

## 2. **Division Conventions**

`ENNReal` has specific conventions that make probability formulas work:

```lean
-- In ENNReal:
0 / 0 = 0    -- Makes conditional probability P(A|B) work when P(B) = 0
x / ∞ = 0    -- Handles certain limit cases
x / 0 = ∞    -- for x > 0
```

These would be messier and require more special case analysis with a [0, 1] type.


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

---

## Summary

+  Mathlib uses [0, ∞] for probability values, which might seem wrong---probabilities
   should be in [0,1]!

+  A pragmatic choice for integration with measure theory and handling limits.

+  In a perfect world, we might use a `Probability` type that restricts inhabitants
   to [0, 1].
   
+  Mathlib prioritizes compatibility with the broader mathematical ecosystem over type safety here.

### Honest Bottom Line

A real tension in library design:

- **Type safety** says: enforce invariants in types
- **Pragmatism** says: make it compatible with existing math
- **Mathlib chose** pragmatism over purity here


