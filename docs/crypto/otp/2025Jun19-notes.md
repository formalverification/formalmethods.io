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

In a term-based proof, this substitution is achieved using functions that show
equality is respected by function application. The `rw` tactic is essentially a
mechanical way of applying the principle of substitution (`Eq.subst` or `Eq.rec`).

---

### Step 2: Unfolding Definition of Uniform PMF

Now we apply the definition of what `uniformOfFintype` evaluates to for a given input.

🥅 **Goal State Before the Tactic** 🥅

```lean
⊢ PMF.uniformOfFintype (Key 3) ⟨[true, false, true], rfl⟩ = 1 / 8
```

**The Tactic** `simp [PMF.uniformOfFintype_apply]`

The lemma `PMF.uniformOfFintype_apply` states: If `a` is an inhabitant of the finite
type `α`, then `PMF.uniformOfFintype α a` is equal to `(Fintype.card α)⁻¹`.

🥅 **Goal State After the Tactic** 🥅

```lean
⊢ (Fintype.card (Key 3))⁻¹ = 1 / 8
```
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

1.  **Typeclass Inference**. Lean finds the `Fintype` instance for `Key 3`
    (`Vector Bool 3`) to determine its size.

2.  **Computation**. The `simp` tactic (or the `norm_num` tactic it calls internally)
    executes the cardinality function, simplifying `Fintype.card (Key 3)` to `8`. The
    goal becomes `(8 : ENNReal)⁻¹ = 1/8`.

3.  **Normalization**. The `simp` engine knows that `8⁻¹` is notation for `1/8`.

4.  **Reflexivity**. The goal becomes `1/8 = 1/8`. `simp` reduces both sides to the
    same term, and the final `rfl` tactic confirms this equality and closes the goal.

---

### Summary & Agda Perspective

| Tactic Proof Step | What it Does | Underlying Proof Term Concept |
| :--- | :--- | :--- |
| `by simp [μK, ...]` | A powerful, automatic rewrite sequence. | A complex, generated term chaining together multiple equalities; a function that takes no arguments and returns a proof of `LHS = RHS`. |
| `rw [μK]` | Replaces `μK` with its definition. | Application of `Eq.subst` or `Eq.rec` using definitional equality of `μK`. |
| `rfl` | Solves a goal of the form `A = A`. | The constructor for equality, `Eq.refl A`; it's a direct proof object. |

+  From an Agda perspective, a tactic proof is essentially a **program that writes a
   proof term**, which is why tactic writing is metaprogramming.

+  `simp` is a very high-level command, like a call to a complex library, while `rw`
   and `rfl` are more like fundamental operations.

---

## Part 2: Deconstructing a Compositional Proof with `bind` and `pure`

Now we move into a more structured proof that requires several foundational tactics,
proving a property of the ciphertext distribution `μC`.

### Step 0: Setup for the Proof

First we add the necessary definitions. For simplicity, we use XOR for encryption and
assume a uniform distribution for messages.

```lean
-- Assume a uniform distribution on messages for this example.
noncomputable def μM {n : ℕ} : PMF (Plaintext n) := PMF.uniformOfFintype (Plaintext n)

-- The joint distribution, assuming independence of message and key.
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
    μC c = ∑' mk : Plaintext n × Key n, if encrypt mk.1 mk.2 = c then μMK mk else 0 := by
  rw [μC, PMF.bind_apply]
  simp only [PMF.pure_apply, mul_boole]
  congr 1
  ext mk
  simp only [eq_comm]
```

#### Step 1: Unfold `bind` and `pure`

The tactics `rw [μC, PMF.bind_apply]` and `simp only [PMF.pure_apply, mul_boole]`
unfold the definitions as before. They apply the law of total probability
(`PMF.bind_apply`), the definition of a deterministic distribution
(`PMF.pure_apply`), and a lemma about multiplication (`mul_boole`). This leaves the
goal:

```lean
⊢ (∑' mk, if c = encrypt mk.1 mk.2 then μMK mk else 0) = (∑' mk, if encrypt mk.1 mk.2 = c then μMK mk else 0)
```

The only difference between the two sides is the order of the equality `c = ...`
versus `... = c`.

#### Step 2: Aligning the Summations

We need to show the bodies of the two summations are equal.

**The Tactic**. `congr 1; ext mk`

* `congr 1`. This "congruence" tactic focuses the proof on the first arguments of the
  equality—in this case, the functions inside the summations `∑'`.

* `ext mk`. This "extensionality" tactic then states we can prove the two functions
  are equal by proving they are equal for an arbitrary input, which it names `mk`.

🥅 **Goal State After the Tactic** 🥅

```lean
mk: Plaintext n × Key n
⊢ (if c = encrypt mk.1 mk.2 then μMK mk else 0) = (if encrypt mk.1 mk.2 = c then μMK mk else 0)
```

#### Step 3: Finishing with `eq_comm`

Now we just resolve the switched equality.

**The Tactic.** `simp only [eq_comm]`

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

To prove the theorem, the key mathematical insight is that for a fixed `m`, the
function `encrypt m` is a bijection. In Lean, a computationally useful bijection is
captured by the type `Equiv`, written `α ≃ β`. Instead of completing the proof, let's
understand this fundamental tool.

#### What is an `Equiv`?

An `Equiv` is a structure that bundles a function, its inverse, and proofs that they
are indeed inverses of each other. It represents an isomorphism between types.

The formal definition in Mathlib is:
```lean
structure Equiv (α : Sort*) (β : Sort*) where
  toFun    : α → β        -- The forward function
  invFun   : β → α        -- The inverse function
  left_inv  : Function.LeftInverse invFun toFun   -- proof that invFun (toFun x) = x
  right_inv : Function.RightInverse invFun toFun  -- proof that toFun (invFun y) = y
```

#### How to Construct an `Equiv` (Introduction)

There are two main ways to build an equivalence.

1.  **From an Involutive Function (High-Level)**

    If a function is its own inverse, like `not` or our `encrypt m`, you can use the
    constructor `Equiv.ofInvolutive`. This is what we did in our Lean code.

    ```lean
    -- Helper lemma: For a fixed message m, encryption is its own inverse.
    lemma encrypt_involutive {n : ℕ} (m : Plaintext n) : Function.Involutive (encrypt m) := ...

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

#### How to Use an `Equiv` (Elimination)

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

## Revealing Proof Objects from Tactics

Let's see how we can get Lean to reveal the proof objects that a proof generates.

**The Feature**

Lean has a tactic called `show_term`.

It executes the tactics within it and then, instead of closing the goal, it prints the raw proof term that was generated.

**How to Demonstrate It:**

1.  Pick a simple proof, like our very first one.
2.  In your VS Code, change the proof to this:

    ```lean
    -- Our theorem: The probability of the key [true, false, true] is 1/8.
    example : μK ⟨[true, false, true], rfl⟩ = (1/8 : ENNReal) := by
      show_term -- Add this tactic
        simp [μK, PMF.uniformOfFintype_apply]; rfl
    ```
3.  When you put your cursor on the `show_term` line, the "Lean Infoview" panel will display the generated proof term.
4.  **The Warning (and the point):** The term will be long, ugly, and full of machine-generated names. It will look something like `Eq.trans (PMF.uniformOfFintype_apply ... ) (congr_arg Inv.inv (Fintype.card_vector ...))`.
5.  **Your Explanation:** "For those of us from an Agda background, it's natural to ask: where is the proof object? Tactic proofs *generate* proof objects. We can ask Lean to show us the term it generated using the `show_term` tactic. As you can see, the result is incredibly verbose and not meant for human consumption. This is the fundamental trade-off: tactics let us write short, conceptual proofs at the expense of creating these complex, machine-readable proof terms under the hood."

This demonstration makes your point perfectly without the need to prepare a separate file. It respects the Agda perspective while highlighting Lean's different philosophy.




[^1]: ...by the Gemini AI Agent.

