# Lean4: a primer for pedantic provers

We seek to not only demonstrate *how* to prove properties in Lean but also *why* the
methods work, connecting the seemingly magical world of tactics to the solid ground
of **proof objects**, with which we are more familiar from Agda.

Our proposed aim to bridge the gap between tactic-based proofs and their underlying
proof terms has been called "an outstanding pedagogical approach."[^1]

We'll start with a concrete, fundamental example that we touched upon in our previous
meetings: computing the probability of choosing a specific key at random.

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

**The Tactic** `simp`

We don't need to provide any more lemmas. The rest is handled by Lean's built-in capabilities.

🥅 **Goal State After the Tactic** 🥅

The goal is solved!

#### Why this works

Looking under the hood,

1.  **Typeclass Inference**. Lean needs to know the size of `Key 3`. The type `Key 3`,
    which is `Vector Bool 3`, has an instance of the `Fintype` typeclass. This
    instance provides a computable function to get the number of elements.

2.  **Computation**. The `simp` tactic (or the `norm_num` tactic it calls internally)
    executes this function. It knows `Vector Bool 3` has `2^3 = 8` elements. So it
    simplifies `Fintype.card (Key 3)` to the value `8`. The goal becomes
    `(8 : ENNReal)⁻¹ = 1/8`.

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

### Lean Code (Version 1.0)**

Here is the initial Lean file containing the setup from our first example.

Copy this into `presentation_examples.lean` in your VS Code project.

```lean
-- We need to import the necessary parts of Mathlib.
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.Vector.Basic

/-!
### Part 1: A Concrete First Proof
-/

-- To make our example concrete, we'll define Key n as vectors of booleans.
-- This is equivalent to `Fin n → Bool` or other n-bit types.
abbrev Key (n : ℕ) := Vector Bool n

-- The uniform distribution over keys, as mentioned in your notes.
noncomputable def μK {n : ℕ} : PMF (Key n) := PMF.uniformOfFintype (Key n)

-- Our theorem: The probability of the key [true, false, true] is 1/8.
example : μK ⟨[true, false, true], by simp⟩ = (1/8 : ENNReal) := by
  -- This proof works by unfolding definitions and simplifying.
  -- 1. `μK` unfolds to `PMF.uniformOfFintype (Key 3)`.
  -- 2. `PMF.uniformOfFintype_apply` rewrites the goal to `(Fintype.card (Key 3))⁻¹`.
  -- 3. The `Fintype` instance for `Vector Bool 3` computes the cardinality to `8`.
  -- 4. The goal simplifies to `8⁻¹ = 1/8`, which is true by definition (`rfl`).
  simp [μK, PMF.uniformOfFintype_apply]
```

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

-- For our example, Plaintexts are also n-bit vectors.
abbrev Plaintext (n : ℕ) := Vector Bool n
abbrev Ciphertext (n : ℕ) := Vector Bool n

-- A simple toy encryption function: pointwise XOR.
def encrypt (m : Plaintext n) (k : Key n) : Ciphertext n :=
  Vector.map₂ Bool.xor m k

-- Assume a uniform distribution on messages for this example.
noncomputable def μM {n : ℕ} : PMF (Plaintext n) := PMF.uniformOfFintype (Plaintext n)

-- The joint distribution assumes independence of message and key.
-- This is a manual construction of the product distribution P(m, k) = P(m) * P(k).
noncomputable def μMK {n : ℕ} : PMF (Plaintext n × Key n) :=
  -- This is the PMF product, which corresponds to P(m, k) = P(m) * P(k)
  PMF.prod μM μK

-- The ciphertext distribution, built with bind and pure.
noncomputable def μC {n : ℕ} : PMF (Ciphertext n) :=
  PMF.bind μMK (fun mk => PMF.pure (encrypt mk.1 mk.2))
```

---

### Step 1: Unfold Everything

The first step in many proofs is to reveal the definitions of the objects we are
reasoning about.

🥅 **Goal State Before the Tactic** 🥅

```lean
theorem μC_apply_eq_sum {n : ℕ} (c : Ciphertext n) :
    μC c = ∑' (mk : Plaintext n × Key n), if encrypt mk.1 mk.2 = c then μMK mk else 0 := by
  -- First, let's see what μC is.
  rw [μC]
  -- Now, let's apply the definition of how `bind` works on a specific output.
  -- This is the crucial lemma `PMF.bind_apply`.
  rw [PMF.bind_apply]
```

🥅 **Goal State After the Tactic** 🥅

```lean
⊢ (∑' (x : Plaintext n × Key n),
    μMK x * (PMF.pure (encrypt x.1 x.2)) c)
  =
  ∑' (mk : Plaintext n × Key n),
    if encrypt mk.1 mk.2 = c then μMK mk else 0
```

---

#### Why this works & proof term view

Looking under the hood,

1.  `rw [μC]`: as before, this is a substitution.

    It replaces `μC` with its definition, `PMF.bind μMK ...`.

    The proof term equivalent is `Eq.subst`.

2.  `rw [PMF.bind_apply]`: this is the core of Step 1.

    `PMF.bind_apply` is a theorem in Mathlib that states:

    ```lean
    (PMF.bind p f) y = ∑' x, p x * (f x) y
    ```

    This lemma is the formal expression of the "law of total probability."

    The `rw` tactic finds this lemma and mechanically rewrites the left-hand side of
    our goal to match it.

---

### Step 2: Simplify the `pure` Term

Our goal now involves a sum containing the term `(PMF.pure (encrypt x.1 x.2)) c`,

where `pure` creates a deterministic distribution.

Let's simplify that.

#### The Tactic-Based Proof (Continuing)

```lean
-- We have `... * (PMF.pure ...)` inside the sum. Let's simplify it.
-- The `PMF.pure_apply` lemma says `(pure a) b` is 1 if a=b and 0 otherwise.
-- `simp` is smart enough to apply this inside the summation.
simp [PMF.pure_apply]
```

🥅 **Goal State After the Tactic** 🥅

```lean
⊢ (∑' (x : Plaintext n × Key n),
    μMK x * if encrypt x.1 x.2 = c then 1 else 0)
  =
  ∑' (mk : Plaintext n × Key n),
    if encrypt mk.1 mk.2 = c then μMK mk else 0
```

---

#### Why this works & proof term view

+  `PMF.pure_apply` states `(PMF.pure a) b = if a = b then 1 else 0`.

+  `simp` applies this rewrite inside the summation (it "simplifies under binders").

+  For each `x` in the sum, it replaces `(PMF.pure (encrypt x.1 x.2)) c` with
   `if encrypt x.1 x.2 = c then 1 else 0`.

+  The corresponding proof term would involve a congruence lemma for summations,
   `tsum_congr_args`, which says that two sums are equal provided their bodies are
   equal for all inputs.

   The proof of equality of the bodies would then use `PMF.pure_apply`.

   `simp` does all of this.

---

### Step 3: Final Touches

The two sides of the equation look almost identical.

We just need to convince Lean that `P * (if cond then 1 else 0)` is the same as `if cond then P else 0`.

#### The Tactic-Based Proof (Finishing)

```lean
  -- The goal is now to show that `P * (if ...)` is the same as `if ... then P else ...`
  -- This is a standard algebraic simplification.
  simp
```
The goal is solved. `simp` has a lemma called `mul_boole` that proves exactly this identity.

**The Equivalent Proof Term (`rfl`)**

After the final `simp`, the left and right sides are syntactically identical.

The final step is just reflexivity, `Eq.refl`.

The genius of `simp` is that it did the `rw [mul_boole]` and `rfl` for us.

---


## The Lean Code File (Version 2.0)

Here is the complete, updated file with our new definitions and the full proof.

```lean
-- We need to import the necessary parts of Mathlib.
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.Vector.Basic

/-!
### Part 1: A Concrete First Proof
-/

-- To make our example concrete, we'll define Key n as vectors of booleans.
-- This is equivalent to `Fin n → Bool` or other n-bit types.
abbrev Key (n : ℕ) := Vector Bool n

-- The uniform distribution over keys, as mentioned in your notes.
noncomputable def μK {n : ℕ} : PMF (Key n) := PMF.uniformOfFintype (Key n)

-- Our theorem: The probability of the key [true, false, true] is 1/8.
example : μK ⟨[true, false, true], by simp⟩ = (1/8 : ENNReal) := by
  -- This proof works by unfolding definitions and simplifying.
  -- 1. `μK` unfolds to `PMF.uniformOfFintype (Key 3)`.
  -- 2. `PMF.uniformOfFintype_apply` rewrites the goal to `(Fintype.card (Key 3))⁻¹`.
  -- 3. The `Fintype` instance for `Vector Bool 3` computes the cardinality to `8`.
  -- 4. The goal simplifies to `8⁻¹ = 1/8`, which is true by definition (`rfl`).
  simp [μK, PMF.uniformOfFintype_apply]


/-!
### Part 2: Deconstructing `bind` and `pure`
-/

-- For our example, Plaintexts are also n-bit vectors.
abbrev Plaintext (n : ℕ) := Vector Bool n
abbrev Ciphertext (n : ℕ) := Vector Bool n

-- A simple toy encryption function: pointwise XOR.
def encrypt (m : Plaintext n) (k : Key n) : Ciphertext n :=
  Vector.map₂ Bool.xor m k

-- Assume a uniform distribution on messages for this example.
noncomputable def μM {n : ℕ} : PMF (Plaintext n) := PMF.uniformOfFintype (Plaintext n)

-- The joint distribution assumes independence of message and key.
noncomputable def μMK {n : ℕ} : PMF (Plaintext n × Key n) :=
  -- This is the PMF product, which corresponds to P(m, k) = P(m) * P(k)
  PMF.prod μM μK

-- The ciphertext distribution, built with bind and pure.
noncomputable def μC {n : ℕ} : PMF (Ciphertext n) :=
  PMF.bind μMK (fun mk => PMF.pure (encrypt mk.1 mk.2))


-- Theorem: The probability of a ciphertext `c` is the sum of probabilities
-- of all (message, key) pairs that produce `c`.
theorem μC_apply_eq_sum {n : ℕ} (c : Ciphertext n) :
    μC c = ∑' (mk : Plaintext n × Key n), if encrypt mk.1 mk.2 = c then μMK mk else 0 := by
  -- First, let's see what μC is.
  rw [μC]
  -- Now, let's apply the definition of how `bind` works on a specific output.
  -- This is the crucial lemma `PMF.bind_apply`.
  rw [PMF.bind_apply]
  -- We have `... * (PMF.pure ...)` inside the sum. Let's simplify it.
  -- The `PMF.pure_apply` lemma says `(pure a) b` is 1 if a=b and 0 otherwise.
  -- `simp` is smart enough to apply this inside the summation.
  simp only [PMF.pure_apply]
  -- The goal is now to show that `P * (if ...)` is the same as `if ... then P else ...`
  -- This is a standard algebraic simplification handled by `mul_boole`.
  simp
```

This second example shows how we can construct proofs by successively applying
theorems (`rw`) and simplifying (`simp`).

Next, we'll prove a more cryptographic property, namely, a simple one-time pad lemma,
which requires us to introduce assumptions with `intro` and use them with `apply`.

---

So far, we have explored how distributions are defined and how to prove basic equalities by unfolding those definitions. Now, let's use these building blocks to prove a foundational cryptographic property: a key lemma for the **perfect secrecy of the One-Time Pad (OTP)**.

This example is powerful because it's simple enough to grasp intuitively but complex enough to require new and fundamental proof tactics. It will also show how we can leverage the vast library of mathematical facts within Mathlib to our advantage.

---


## Part 3: Proving a Cryptographic Property (One-Time Pad)

The core idea of the one-time pad is that if you encrypt a message with a truly
random key, the resulting ciphertext is also completely random.

In other words, observing a ciphertext `c` gives an attacker no information
whatsoever about the plaintext `m` that was encrypted.

The standard way to prove this is to show that the conditional distribution of
ciphertexts, given a *fixed* plaintext message `m`, is uniform.

This is the conditional distribution `P(C | M=m)` we discussed previously, which we
can formalize in Lean.

---

### Step 0: Setup for the Proof

Let's define the conditional ciphertext distribution, `μC_M m`.

This represents the distribution of ciphertexts when we encrypt a *specific, known*
message `m` with a random key drawn from `μK`.

In Lean, this is a straightforward `map` operation.

```lean
/-!
### Part 3: Proving a Cryptographic Property (One-Time Pad)
-/

-- The distribution of ciphertexts, conditioned on a fixed message `m`.
-- This is created by taking the key distribution `μK` and mapping the function
-- `encrypt m` over it. For each random key `k`, we produce `encrypt m k`.
noncomputable def μC_M {n : ℕ} (m : Plaintext n) : PMF (Ciphertext n) :=
  PMF.map (encrypt m) μK
```

Our goal is to prove that this distribution is the uniform distribution.

**Theorem:** For any message `m`, `μC_M m` is the uniform distribution over
ciphertexts; that is,

```lean
∀ (m : Plaintext n), μC_M m = PMF.uniformOfFintype (Ciphertext n)
```

---

### Step 1: Introducing Hypotheses with `intro`

Our theorem starts with `∀ m...`, so we need to introduce an arbitrary `m`.

**The Tactic**. `intro m`

The `intro` tactic consumes a universal quantifier (`∀`) or implication (`→`).

It takes the quantified variable (`m`) and moves it into the local context as an hypothesis.

🥅 **Goal State Before the Tactic** 🥅

```lean
⊢ ∀ (m : Plaintext n), μC_M m = PMF.uniformOfFintype (Ciphertext n)
```

**Applying `intro m`**

```lean
theorem otp_perfect_secrecy_lemma {n : ℕ} :
    ∀ (m : Plaintext n), μC_M m = PMF.uniformOfFintype (Ciphertext n) := by
  intro m
```

🥅 **Goal State After the Tactic** 🥅

```lean
m: Plaintext n
⊢ μC_M m = PMF.uniformOfFintype (Ciphertext n)
```

#### The Equivalent Proof Term

This is the most beautiful part for Agda fans.

The `intro` tactic corresponds to creating a **lambda abstraction**.

The proof term starts

```lean
λ (m : Plaintext n) =>
  -- The rest of the proof, which must produce a proof of
  -- `μC_M m = PMF.uniformOfFintype (Ciphertext n)`
  ...
```
`intro` is the tactic equivalent of `λ (m : ...) => ...`.

---

### Step 2: Proving Function Equality with `ext`

The goal is now to prove that two `PMF`s are equal.

A `PMF` is fundamentally a function.

!!! info "The principle of **function extensionality** (funext)"

    Two functions `f` and `g` are equal iff `f x = g x` for all `x`.

**The Tactic**. `ext c`

The `ext` tactic applies the funext principle, replacing the goal `f = g` with the
goal `∀ x, f x = g x`, and automatically running `intro x`.

🥅 **Goal State Before the Tactic** 🥅

```lean
m: Plaintext n
⊢ μC_M m = PMF.uniformOfFintype (Ciphertext n)
```
**Applying `ext c`:**
```lean
  -- To prove two PMFs are equal, we show they give the same probability to every output.
  ext c
```

🥅 **Goal State After the Tactic** 🥅

```lean
m: Plaintext n
c: Ciphertext n
⊢ μC_M m c = PMF.uniformOfFintype (Ciphertext n) c
```

#### The Equivalent Proof Term

The `ext` tactic is a shortcut for applying the `funext` axiom.

The proof term would look like

```lean
fun (m : Plaintext n) =>
  funext (fun (c : Ciphertext n) =>
    -- The rest of the proof, which must produce a proof of
    -- `μC_M m c = ...`
    ...
  )
```
So,

+  `intro` builds lambdas for `∀`,
+  `ext` builds lambdas for function equality.

---

### Step 3: Using the Mathlib Machinery

We could now unfold all the definitions with `rw` and prove this from first principles.

However, Mathlib has already done the hard work for us!

There is a powerful theorem, `PMF.map_of_bijective`, that says:

*If you `map` a uniform distribution through a `bijective` function, the result is another uniform distribution.*

Our `encrypt m` function (which is `λ k => m xor k`) is a bijection from `Key n` to `Ciphertext n`.

Let's use that fact.

---

#### Tactic-Based Proof (Finishing)

```lean
  -- Unfold the definition of μC_M to expose the `map`.
  rw [μC_M]
  -- Now, apply the powerful lemma from Mathlib.
  rw [PMF.map_of_bijective (encrypt m) (λ k => encrypt_is_bijective m k)]
```

This is a bit complex:

+  The `rw` tactic here uses `PMF.map_of_bijective`.

+  This requires a proof that our encryption function is bijective.

+  We pass that as an argument: `(encrypt_is_bijective m)`.

---

#### Tactic-Based Proof (Alt Ending)

The `simp` tactic is actually smart enough to figure this out if we set it up correctly!

A cleaner proof looks like this:

```lean
-- First, we prove that encryption is a bijection. This is a helper lemma.
lemma encrypt_bijective {n : ℕ} (m : Plaintext n) : Function.Bijective (encrypt m) :=
  -- This is true because XORing with a constant is its own inverse.
  Function.Bijective.of_involutive (λ k => by simp [encrypt, Vector.map₂_map, Bool.xor_comm, Bool.xor_self])

-- Now the main proof becomes incredibly clean.
theorem otp_perfect_secrecy_lemma {n : ℕ} :
    ∀ (m : Plaintext n), μC_M m = PMF.uniformOfFintype (Ciphertext n) := by
  intro m
  rw [μC_M] -- Unfold our definition
  -- `simp` finds the `map_of_bijective` lemma and our `encrypt_bijective` lemma!
  simp [μK, PMF.map_of_bijective, encrypt_bijective m]
```

The `simp` call does all the work:

+  unfolds `μK` to see it's uniform,
+  sees the `PMF.map`,
+  finds the `map_of_bijective` lemma,
+  proves the side-condition by applying our `encrypt_bijective` helper lemma.

!!! note "Typical workflow"

    1. Identify the high-level mathematical property you need (e.g., mapping a distribution over a bijection).
    2. Prove it as a separate lemma.
    3. Use that lemma to make your main proof clean and conceptual.

---

## The Lean Code File (Version 3.0)

Here is the complete file. It now contains the proof of the OTP secrecy lemma, which
you can test and explore in VS Code.

```lean
-- We need to import the necessary parts of Mathlib.
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.Vector.Basic

/-!
### Part 1: A Concrete First Proof
-/

-- To make our example concrete, we'll define Key n as vectors of booleans.
abbrev Key (n : ℕ) := Vector Bool n

-- The uniform distribution over keys, as mentioned in your notes.
noncomputable def μK {n : ℕ} : PMF (Key n) := PMF.uniformOfFintype (Key n)

-- Our theorem: The probability of the key [true, false, true] is 1/8.
example : μK ⟨[true, false, true], by simp⟩ = (1/8 : ENNReal) := by
  simp [μK, PMF.uniformOfFintype_apply]


/-!
### Part 2: Deconstructing `bind` and `pure`
-/

-- For our example, Plaintexts are also n-bit vectors.
abbrev Plaintext (n : ℕ) := Vector Bool n
abbrev Ciphertext (n : ℕ) := Vector Bool n

-- A simple toy encryption function: pointwise XOR.
def encrypt (m : Plaintext n) (k : Key n) : Ciphertext n :=
  Vector.map₂ Bool.xor m k

-- Assume a uniform distribution on messages for this example.
noncomputable def μM {n : ℕ} : PMF (Plaintext n) := PMF.uniformOfFintype (Plaintext n)

-- The joint distribution assumes independence of message and key.
noncomputable def μMK {n : ℕ} : PMF (Plaintext n × Key n) :=
  PMF.prod μM μK

-- The ciphertext distribution, built with bind and pure.
noncomputable def μC {n : ℕ} : PMF (Ciphertext n) :=
  PMF.bind μMK (fun mk => PMF.pure (encrypt mk.1 mk.2))


-- Theorem: The probability of a ciphertext `c` is the sum of probabilities
-- of all (message, key) pairs that produce `c`.
theorem μC_apply_eq_sum {n : ℕ} (c : Ciphertext n) :
    μC c = ∑' (mk : Plaintext n × Key n), if encrypt mk.1 mk.2 = c then μMK mk else 0 := by
  rw [μC, PMF.bind_apply]
  simp only [PMF.pure_apply, mul_boole]


/-!
### Part 3: Proving a Cryptographic Property (One-Time Pad)
-/

-- The distribution of ciphertexts, conditioned on a fixed message `m`.
noncomputable def μC_M {n : ℕ} (m : Plaintext n) : PMF (Ciphertext n) :=
  PMF.map (encrypt m) μK

-- Helper lemma: For a fixed message m, encryption is a bijection from keys to ciphertexts.
lemma encrypt_bijective {n : ℕ} (m : Plaintext n) : Function.Bijective (encrypt m) :=
  -- This is true because XORing with a constant is its own inverse.
  -- The proof is to show that applying the function twice gets you back to the start.
  Function.Bijective.of_involutive (fun k => by
    -- We need to show `encrypt m (encrypt m k) = k`
    simp [encrypt, Vector.map₂_map, Bool.xor_comm, Bool.xor_assoc, Bool.xor_self, Bool.xor_false])

-- Theorem: For any message m, the distribution of ciphertexts is uniform.
-- This is a key lemma for proving the perfect secrecy of the one-time pad.
theorem otp_perfect_secrecy_lemma {n : ℕ} :
    ∀ (m : Plaintext n), μC_M m = PMF.uniformOfFintype (Ciphertext n) := by
  -- Consider an arbitrary message m.
  intro m
  -- Unfold the definition of our conditional distribution.
  rw [μC_M]
  -- The main argument: mapping a uniform distribution over a bijection yields
  -- a uniform distribution. `simp` can apply this high-level theorem for us.
  -- It uses our `encrypt_bijective` lemma to satisfy the precondition.
  simp [μK, PMF.map_of_bijective, encrypt_bijective m]
```



[1] ...by the Gemini AI Agent.
