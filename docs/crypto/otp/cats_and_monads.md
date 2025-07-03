# A Category Theory Perspective: The Probability Monad 🔮

For those who like category theory, we can frame the concepts of `pure` and `bind` for probability mass functions in the language of monads.

Indeed, the structure formed by `PMF`, `pure`, and `bind` is a classic example of a **monad**.

In this view, `PMF` is a type constructor that wraps a type `α` in a "probabilistic context," yielding `PMF α`.

The functions `pure` and `bind` are the two fundamental operations that define the monad.

## `pure` as Monadic `unit`

+  `pure` is the standard monadic `unit` (aka `return`)

+  It takes `a : α` and *lifts* it into the monadic context with *minimal effect*.

     `pure` : α → `PMF` α

+  In the probability monad "minimal effect" means "no uncertainty."

+  `pure a` lives in the probabilistic world---it is a **Dirac delta distribution** $δ_a$, where all the probability mass is concentrated on that single value.

+  `pure` is a lens through which to view any `a : α` as a (constant) "random" variable.

+  `pure` is a thunk; i.e., a way to view `a` as the (constant) function `λ _ → a`.


## `bind` as Monadic `>>=`

The `bind` function is the cornerstone of the monad.

It is often written `>>=` and sometimes called `flatMap` (e.g. in Scala).

It defines how to compose operations within the monadic context.

`bind : PMF α → (α → PMF β) → PMF β`

This signature is revealing: `bind` takes

+  a probability distribution `p : PMF α`,
+  a "Kleisli arrow" which maps each `a : α` to a distribution on `β`,

and returns a new distribution over `β`, which represents the total probability of the combined, sequential process.

In our context, a Kleisli arrow is a family of probability distributions
over `β`, indexed by `α`.

!!! info "Monads and effects"

    The composition that `bind` manifests--combining a value with a Kleisli arrow to
    produce a distribution--is precisely how monads are able to handle *side effects
    in computational contexts*--in this case, the context is probability and the
    side effects are correlations or dependencies among random processes, that is,
    the effects that values of random variables, or "events," can have on the
    probabilities of other events.

## The Monad Laws for Probability

For (`PMF`, `bind`, `pure`) to comprise a monad, it must satisfy three laws, which guarantee that sequencing probabilistic computations behaves sensibly.

1.  **Left Identity**: `bind (pure a) f ≡ f a`
    *  *In probability terms*: given the "point mass at `a`" distribution over `α`,
       applying the family `f` simply gives the distribution `f a`.

2.  **Right Identity**: `bind p pure ≡ p`
    *  *In probability terms*: If you have a random variable with distribution `p` and your second step is to simply take its outcome and deterministically wrap it back into a `PMF`, you haven't actually changed the distribution. The final distribution is identical to the original `p`.

3.  **Associativity**: `bind (bind p f) g ≡ bind p (λx => bind (f x) g)`
    *  *In probability terms*: Thhe way in which you group the composition of a given sequence of probabilistic events doesn't matter. You can either run the first two events (`bind p f`) and then pipe the result into the third (`g`), or you can compose the second and third events (`λx => bind (f x) g)`) and pipe the result of the first event (`p`) into that composite function. Both methods yield the same final probability distribution. This is analogous to the law of total probability applied iteratively.

+  By satisfying these laws, the triple (`PMF`, `bind`, `pure`)  provides a robust compositional framework for building complex probabilistic models from simpler ones.

+  The expression `bind μMK (λ (m, k) => pure (encrypt m k))` is a clear demonstration of this principle, sequencing a random draw from `μMK` with a deterministic computation.

---

## The Category of Types

The single category we are working in is the category of types and functions (often called **Type** in programming languages like Lean, or **Set** in set theory).

* **Objects**: The objects are the types themselves (e.g., `Bool`, `Nat`, `String`).
* **Morphisms**: The morphisms are the functions between types (e.g., `is_even: Nat → Bool`).


### How `PMF` acts on the category of types

1.  **Mapping Objects**.

    The `PMF` functor takes an object (a type α) and maps it to a *new object* in the same category, the type `PMF` α. For example,

    * the object `Bool` is mapped to the object `PMF Bool`.
    * the object `Nat` is mapped to the object `PMF Nat`.

    Crucially, `PMF Bool` is still just a type---an object in the category **Type**.

2.  **Mapping Morphisms**.

    The `PMF` functor takes a morphism, `f: α → β`, and maps it to a *new morphism* in the same category (the function `map f: PMF α → PMF β`).

    * It maps the function `not: Bool → Bool` to the new function `map not: PMF Bool → PMF Bool`.
    * It maps the function `is_even: Nat → Bool` to the new function `map is_even: PMF Nat → PMF Bool`.

Because `PMF` takes any object or morphism in **Type** and produces another object or morphism right back in **Type**, it is an endofunctor on **Type**.

---

## PMF is a functor

Recall, a **functor**, `F : 𝒞 → 𝒟`, is a map from one category to another that
satisfies the functor laws.

```
  𝒞       𝒟

  α ----> Fα
  |       |              fmap : (α → β) → (Fα → Fβ)
  |       |
f |       | fmap f       Functor Laws
  |       |               i. fmap id = id
  v       v              ii. fmap (g ∘ f) = (fmap g) ∘ (fmap f)
  β ----> Fβ
```

What are the categories involved here?

Clearly the domain category of `PMF` is the category of types.

Also, PMF is a *type constructor* in the sense that, for each type `α`, the value
`PMF α` is a type.

Thus the codomain category of PMF is also `Type`.


### From Monad to Functor

For any monad, the monadic structure automatically gives rise to a functor.

The functor's `fmap` operation can be defined using `bind` and `pure`.

A type constructor is a functor if it supports an `fmap` function that *lifts* a regular function into the context of the type.

For `PMF`, this means we need a function with the following signature:

`fmap : (α → β) → (PMF α → PMF β)`

But this can be defined directly from the monadic operations, bind and pure!

`fmap f p = bind p (λ x ⇒ pure (f x))`

This composition has a clear probabilistic meaning:

1.  **`bind p ...`**: sample a value `x` from the distribution `p`.
2.  **`... λ x => pure (f x)`**: take the sampled value `x`, apply the function `f`,
    and produce a deterministic distribution that always returns the result `f x`.

The overall effect is a new probability distribution over the type `β`, which is precisely what mapping a function over `p` should produce.

### The Functor Laws

This definition of `fmap` also satisfies the two functor laws, which follow directly from the monad laws:

1.  **Identity**: `fmap id = id`
    * Mapping the identity function over a distribution doesn't change it.

2.  **Composition**: `fmap (g ∘ f) = (fmap g) ∘ (fmap f)`
    * Mapping the composition of two functions is the same as mapping the first function and then mapping the second.

+  So, while `bind` is about sequencing probabilistic computations, `fmap` is about applying a deterministic transformation to the *outcome* of a probabilistic computation.

+  The fact that every monad (like `PMF`) is also a functor is a fundamental concept in category theory that provides this useful `fmap` operation for "free".


## Application

Recall how we defined the ciphertext distribution,

`μC = bind μMK (λ (m, k) => pure (encrypt m k))`.

+ `μMK` is the joint distribution of (message, key) pairs.
+ `bind μMK` says "sample from this distribution."
+ `λ (m, k) => pure (encrypt m k)` says "apply encryption deterministically."



