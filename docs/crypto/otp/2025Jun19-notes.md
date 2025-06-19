# Lean4: a primer for paranoids and pedants

We will demonstrate not only *how* to prove properties in Lean but also *why* the
methods work, connecting the seemingly magical world of tactics to the solid ground
of **proof objects**, with which we are more familiar from Agda.

We'll start by reviewing a concrete, fundamental example from last time: computing
the probability of choosing a specific key at random.

This will allow us to *bring the ideas down to earth* and immediately dive into and
discuss the *tactic vs. proof object* dichotomy.

---

## Part 1: A Concrete First Proof

Let's start with the

**Claim**. The probability of randomly choosing a specific 3-bit key is 1/8.

In Lean, the theorem and its tactic-based proof are very concise.

```lean
import Mathlib.Probability.Distributions.Uniform

-- (Assuming a file OTP.Basic with the definition of Key)
open OTP
-- Recall, we define `Key n` as vectors of booleans.
-- This is equivalent to `Fin n → Bool` or other n-bit types.

-- Here is the uniform distribution over keys of length n.
noncomputable def μK {n : ℕ} : PMF (Key n) := PMF.uniformOfFintype (Key n)

-- Our claim: the probability of choosing key [true, false, true] is 1/8.
example : μK ⟨[true, false, true], rfl⟩ = (1/8 : ENNReal) :=
 -- and here's the tactic-based proof in Lean:
  by simp [μK, PMF.uniformOfFintype_apply]; rfl
```

This is great for a user who knows what `simp` means and does,
but it may seem like a magical incantation for the newcomer.

So, let's unpack it.

---

### Deconstructing `simp`

The `simp` tactic is an automated rewriter.

It tries to simplify the main goal by applying a list of theorems (called a
"simpset") from left to right, over and over, until no more simplifications can be
made.

When you write `simp [foo, bar]`, you are telling Lean:

"Please use your standard simpset, plus the definitions/lemmas `foo` and `bar` to the
set of tools you can use to simplify or reduce the goal."

---

### Step 1: Unfolding the Definition of `μK`

Let's break down the proof step-by-step, showing the tactic at each stage, and then
discuss the proof object it's building.

🥅 **Goal State Before the Tactic** 🥅

```lean
⊢ μK ⟨[true, false, true], rfl⟩ = 1 / 8
```

Here, `⊢` indicates the goal we are trying to prove.

**The Tactic** `simp [μK]` or `rw [μK]`

tells Lean to substitute `μK` with its definition.

🥅 **Goal State After the Tactic** 🥅

```lean
⊢ PMF.uniformOfFintype (Key 3) ⟨[true, false, true], rfl⟩ = 1 / 8
```

---

#### Why this works

Looking under the hood,

* `μK` is defined as `PMF.uniformOfFintype (Key n)`.

* `simp` (and the more targeted `rw`) can access all definitions in context.

* It sees the term `μK` in the goal and replaces it with its definition; a
  simple substitution.

---

#### The Equivalent Proof Term

In a term-based proof, the substitution is achieved using functions that show
equality is respected by function application.

If we have a proof `h : μK = PMF.uniformOfFintype (Key 3)`, we can use it to rewrite
the goal.

The definition itself provides this proof `h`. The core idea is `Eq.subst` or `Eq.rec`.

A proof term for just this step would look like this:

```lean
-- Let P be the property we are trying to prove for the definition.
-- P := λ x => x ⟨[true, false, true], _⟩ = 1/8
-- Our goal is `P (μK)`
-- The definition of μK gives us `proof_of_definition : μK = PMF.uniformOfFintype (Key 3)`

-- The new proof term is:
Eq.subst proof_of_definition (new_goal : P (PMF.uniformOfFintype (Key 3)))
```

...which is a bit clunky.

A more common term-based idiom is to simply start with the definition
already unfolded.

The tactic `rw` is essentially a mechanical way of applying `Eq.subst`.

---

### Step 2: Unfolding Definition of Uniform PMF

Now we apply the definition of what `uniformOfFintype` evaluates to for a given input.

🥅 **Goal State Before the Tactic** 🥅

```lean
⊢ PMF.uniformOfFintype (Key 3) ⟨[true, false, true], rfl⟩ = 1 / 8
```

**The Tactic** `simp [PMF.uniformOfFintype_apply]`

The lemma `PMF.uniformOfFintype_apply` states:

If `a` is an inhabitant of the finite type `α`, then

`PMF.uniformOfFintype α a` is equal to `(Fintype.card α)⁻¹`.

🥅 **Goal State After the Tactic** 🥅

```lean
⊢ (Fintype.card (Key 3))⁻¹ = 1 / 8
```

---

#### Why this works

Looking under the hood,

* `simp` finds a lemma `PMF.uniformOfFintype_apply` in the library;

* This lemma matches the pattern `PMF.uniformOfFintype (Key 3) ...` on the lhs of our goal;

* `simp` using the lemma to rewrites the lhs as `(Fintype.card (Key 3))⁻¹`.

---

#### The Equivalent Proof Term

This is a direct application of the lemma.

The proof term for the rewrite is `PMF.uniformOfFintype_apply (Key 3) ⟨...⟩`.

Applying this equality to our goal transforms it.

A proof would look like:

```lean
-- h₁ : PMF.uniformOfFintype (Key 3) ⟨...⟩ = (Fintype.card (Key 3))⁻¹
-- This comes from the lemma PMF.uniformOfFintype_apply
-- We use this to transform the goal into proving:
-- ⊢ (Fintype.card (Key 3))⁻¹ = 1 / 8
```

This is again a form of `Eq.subst`.

The `rw` tactic is the most direct parallel: `rw [PMF.uniformOfFintype_apply]`.

---

### Step 3: Computing the Cardinality and Final Simplification

This is where `simp` really shines by combining computation and proof.

🥅 **Goal State Before the Tactic** 🥅

```lean
⊢ (Fintype.card (Key 3))⁻¹ = 1 / 8
```

**The Tactic** `simp; rfl`

We don't need to provide any more lemmas. The rest is handled by Lean's built-in
capabilities.

🥅 **Goal State After the Tactic** 🥅

The goal is solved!

#### Why this works

Looking under the hood,

1.  **Typeclass Inference**. Lean needs to know the size of `Key 3`. The type `Key 3`,
    which is `Vector Bool 3`, has an instance of the `Fintype` typeclass. This
    instance provides a computable function to get the number of elements.

2.  **Computation**. The `simp` tactic (or the `norm_num` tactic it calls internally)
    executes the cardinality function, simplifying `Fintype.card (Key 3)` to `8`. The
    goal becomes `(8 : ENNReal)⁻¹ = 1/8`.

3.  **Normalization**. The `simp` engine has lemmas about `ENNReal` arithmetic.
    It knows that `8⁻¹` is the same as `1/8`.

4.  **Reflexivity**. The goal becomes `1/8 = 1/8`. `simp` reduces both sides to the
    same term, and the final `rfl` tactic confirms this equality and closes the goal.

---

#### The Equivalent Proof Term

A term-based proof must explicitly provide proofs for each of these steps.

```lean
-- A lemma that proves card (Key 3) = 8
have card_proof : Fintype.card (Key 3) = 8 := by-- ... proof using vector cardinality lemmas

-- We use this proof to rewrite the goal
-- The goal becomes ⊢ 8⁻¹ = 1/8
-- This is true by reflexivity, since 8⁻¹ is just notation for 1/8 in ENNReal.
-- The final term is:
rfl
```

The `simp` tactic automated the process of finding `card_proof`, applying it, and
then seeing that the result was definitionally equal.

 The full proof term generated by our original `by simp [...]` is effectively a
 composition of all these steps, applying congruence lemmas (`congr_arg`) and
 transitivity (`Eq.trans`) to chain all the intermediate equalities together into one
 grand proof that the starting expression equals the final one.

---

### Summary & Agda Perspective

| Tactic Proof Step | What it Does | Underlying Proof Term Concept |
| :--- | :--- | :--- |
| `by simp [μK, ...]` | A powerful, automatic rewrite sequence. | A complex, generated term chaining together multiple equalities; a function that takes no arguments and returns a proof of `LHS = RHS`. |
| `rw [μK]` | Replaces `μK` with its definition. | Application of `Eq.subst` or `Eq.rec` using definitional equality of `μK`. |
| `rw [lem]` | Rewrites goal using a proven lemma `lem : A = B`. | Application of `Eq.subst` using lemma `lem` as proof of equality. |
| `rfl` | Solves a goal of the form `A = A`. | The constructor for equality, `Eq.refl A`; it's a direct proof object. |

+  From an Agda perspective, a tactic proof is essentially a **program that writes a
   proof term**, which is why tactic writing is metaprogramming.

+  `simp` is a very high-level command, like a call to a complex library, while `rw`
   and `rfl` are more like fundamental operations.

This first example was heavy on `simp`. Next, let's tackle a proof that requires more
manual, step-by-step tactics like `intro`, `apply`, and `let`, which have even
clearer one-to-one correspondences with proof-term constructs like `fun`, function
application, and `let ... in ...`.

---

## Part 2: Deconstructing a Compositional Proof with `bind` and `pure`

For our next step, we move beyond proofs that are solved by a single `simp` command
and into a more structured proof that requires several foundational tactics.

We will prove a fundamental property about the ciphertext distribution `μC`, which we
defined last time using `bind` and `pure`.

This give us the perfect opportunity to explore tactics like `rw`, `intro`, and
`apply`, and examine their corresponding proof term constructions.

---

### Recall construction of `μC`

Last time we saw that the ciphertext distribution `μC` can be constructed by
chaining two probabilistic processes:

1.  Sample a message `m` and a key `k` from their joint distribution `μMK`.

2.  Deterministically compute the ciphertext `c = encrypt m k`.

We captured this nicely in Lean as follows:

```lean
μC = bind μMK (λ mk => pure (encrypt mk.1 mk.2))
```

Let's prove a theorem that shows what this actually *means* when we
compute the probability of a specific ciphertext `c`.

The **law of total probability** says that `P(C=c)` is the sum of probabilities of
all `(m, k)` pairs that produce `c`.

!!! note "**Theorem**"

    ```lean
    μC c = ∑' (⟨m , k⟩ : Plaintext n × Key n), if encrypt m k = c then μMK ⟨m , k⟩ else 0
    ```

Proving this will require unpacking the meaning of `bind` and `pure`.

---

### Step 0: Setup for the Proof

First we add the necessary definitions to our Lean file.

We need `Plaintext`s, an encryption function, and the distributions `μMK` and `μC`.

For simplicity, we use a simple xor for encryption and assume a uniform distribution
for messages.

```lean
/-!
## Part 2: Deconstructing `bind` and `pure`
-/

-- Assume a uniform distribution on messages for this example.
noncomputable def μM {n : ℕ} : PMF (Plaintext n) := PMF.uniformOfFintype (Plaintext n)

-- The joint distribution assumes independence of message and key.
-- This is a manual construction of the product distribution P(m, k) = P(m) * P(k).
noncomputable def μMK {n : ℕ} : PMF (Plaintext n × Key n) :=
  PMF.bind μM (λ m => PMF.map (λ k => (m, k)) μK)

-- The ciphertext distribution, built with bind and pure.
noncomputable def μC {n : ℕ} : PMF (Ciphertext n) :=
  PMF.bind μMK (λ ⟨m, k⟩ => PMF.pure (encrypt m k))
```

The **law of total probability** says that `P(C=c)` is the sum of probabilities of
all `(m, k)` pairs that produce `c`.

!!! note "**Theorem**"

    `μC c = ∑' (mk : Plaintext n × Key n), if encrypt mk.1 mk.2 = c then μMK mk else 0`

---

### The Proof Step-by-Step

Here is the complete, corrected proof in Lean:
```lean
open Classical
theorem μC_apply_eq_sum {n : ℕ} (c : Ciphertext n) :
  μC c = ∑' mk : Plaintext n × Key n, if encrypt mk.1 mk.2 = c then μMK mk else 0
  := by
  rw [μC, PMF.bind_apply]
  simp only [PMF.pure_apply, mul_boole]
  congr 1
  ext mk
  simp only [eq_comm]
```

#### Step 1: Unfold `bind`

**Tactics**. `rw [μC, PMF.bind_apply]`

+  `rw [μC]`: as before, this is a substitution.

    It replaces `μC` with its definition, `PMF.bind μMK ...`.

    The proof term equivalent is `Eq.subst`.

+  `rw [PMF.bind_apply]`: this is the core of Step 1.

    `PMF.bind_apply` is a theorem in Mathlib that states:

    ```lean
    (PMF.bind p f) y = ∑' x, p x * (f x) y
    ```

    This is a formal expression of the *law of total probability*.

    `rw` finds this lemma and mechanically rewrites the lhs of our goal to match it.


---

#### Step 1: Unfold `pure`


🥅 **Goal State** 🥅

```lean
n : ℕ
c : Ciphertext n
⊢ ∑' (a : Plaintext n × Key n),
    μMK a * (match a with | (m, k) => PMF.pure (encrypt m k)) c
= ∑' (mk : Plaintext n × Key n), if encrypt mk.1 mk.2 = c then μMK mk else 0
```

**Tactics**. `simp only [PMF.pure_apply, mul_boole]`

+  `PMF.pure_apply` says `(pure a) b` is 1 if `a = b` and 0 otherwise.

   `simp` is smart enough to apply this inside the summation.

+  `mul_boole` simplifies multiplication with the indicator function.

   It turns the `if` into a multiplication by `1` or `0`.

🥅 **Goal State After the Tactics** 🥅

```lean
⊢ (∑' mk, if c = encrypt mk.1 mk.2 then μMK mk else 0)
= (∑' mk, if encrypt mk.1 mk.2 = c then μMK mk else 0)
```

Now the only difference between the two sides is the order of the equality:

`c = ...` versus `... = c`.

---

#### Step 2: Aligning the Summations

We need to show the bodies of the two summations are equal.

**Tactics**. `congr 1; ext mk`

* `congr 1`. This "congruence" tactic focuses the proof on the first arguments of the
  equality—in this case, the functions inside the summations `∑'`.

* `ext mk`. This "extensionality" tactic then states we can prove the two functions
  are equal by proving they are equal for an arbitrary input, which it names `mk`.

🥅 **Goal State After the Tactic** 🥅

```lean
mk: Plaintext n × Key n
⊢ (if c = encrypt mk.1 mk.2 then μMK mk else 0) = (if encrypt mk.1 mk.2 = c then μMK mk else 0)
```

---

#### Step 3: Finishing with `eq_comm`

Now we just resolve the switched equality.

**Tactic**. `simp only [eq_comm]`

* The lemma `eq_comm` states that `a = b` is equivalent to `b = a`. `simp` uses this
  to rewrite the goal, making the two sides identical and closing the proof.

---

## Part 3: Proving a Cryptographic Property (One-Time Pad)

The standard way to prove the perfect secrecy of OTP is to show that for any fixed
plaintext `m`, the conditional distribution of ciphertexts is uniform.

### Step 0: Setup for the Proof

We define the conditional distribution `μC_M m` by mapping the encryption function
over the uniform key distribution.

```lean
-- The distribution of ciphertexts, conditioned on a fixed message `m`.
noncomputable def μC_M {n : ℕ} (m : Plaintext n) : PMF (Ciphertext n) :=
  PMF.map (encrypt m) μK
```

Our goal is to prove that this distribution is uniform.

**Theorem:** `∀ (m : Plaintext n), μC_M m = PMF.uniformOfFintype (Ciphertext n)`

---

### A Detour into Equivalences (`≃`)

Key mathematical insight: for a fixed `m`, the function `encrypt m` is a bijection.

In Lean, such a bijection is captured by the type `Equiv`, written `α ≃ β`.

#### What is an `Equiv`?

An `Equiv` is a structure that bundles a function, its inverse, and proofs that they
are indeed inverses of each other. It represents an isomorphism between types.

The formal definition in Mathlib is:
```lean
structure Equiv (α : Sort*) (β : Sort*) where
  toFun    : α → β        -- The forward function
  invFun   : β → α        -- The inverse function
  left_inv  : Function.LeftInverse invFun toFun   -- proof of invFun (toFun x) = x
  right_inv : Function.RightInverse invFun toFun  -- proof of toFun (invFun y) = y
```

#### How to Construct an `Equiv` (Intro)

There are two main ways to build an equivalence.

1.  **From an Involutive Function (High-Level)**

    If a function is its own inverse, like `not` or our `encrypt m`, you can use the
    constructor `Equiv.ofInvolutive`.

    ```lean
    -- Helper lemma: For a fixed message m, encryption is its own inverse.
    lemma encrypt_involutive {n : ℕ} (m : Plaintext n) :
      Function.Involutive (encrypt m) := by ...

    -- We build the Equiv directly from this property.
    def encrypt_equiv {n : ℕ} (m : Plaintext n) : Key n ≃ Ciphertext n :=
      Equiv.ofInvolutive (encrypt m) (encrypt_involutive m)
    ```

2.  **By Hand (Low-Level)**

    You can construct one by providing all four fields. This is useful for simple cases.

    ```lean
    -- An equivalence between Bool and Bool using `not`.
    def not_equiv : Bool ≃ Bool where
      toFun    := not
      invFun   := not
      left_inv  := Bool.not_not
      right_inv := Bool.not_not
    ```

#### How to Use an `Equiv` (Elim)

Once you have an `Equiv`, you can use it in several ways.

1. **As a Function**. Lean knows how to treat an `Equiv` `e` as a function. You can just write `e x`.

2. **Accessing the Inverse**. The inverse is available as `e.symm`. So you can write `e.symm y`.

3. **Using the Proofs**. The proofs `e.left_inv` and `e.right_inv` are powerful tools for rewriting.

```lean
example (e : α ≃ β) (x : α) : e.symm (e x) = x := by
  -- The goal is exactly the statement of the left_inv property.
  simp [e.left_inv]
```

+  Understanding how to construct and use equivalences is crucial for many proofs
   involving bijections.

+  The final step of our OTP theorem would be to find the right Mathlib lemma that
   uses this `encrypt_equiv` to prove that the `map` of a uniform distribution is
   still uniform.

---

