# OTP: Perfect Secrecy in Lean

The standard way to prove the perfect secrecy of OTP is to show that for any fixed
plaintext `m`, the conditional distribution of ciphertexts is uniform.

## Proof Setup

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

## A Detour into Equivalences (`≃`)

Key mathematical insight: for a fixed `m`, the function `encrypt m` is a bijection.

In Lean, such a bijection is captured by the type `Equiv`, written `α ≃ β`.

### What is an `Equiv`?

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

### How to Construct an `Equiv` (Intro)

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

### How to Use an `Equiv` (Elim)

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

## Next

1.  A detailed Markdown explanation of our proof for `otp_perfect_secrecy_lemma`.

2.  An explanation for why `encrypt_equiv` must be `noncomputable` while `xorEquiv` is not.

Let's tackle the `noncomputable` question first, as it's a deep and important concept in Lean.

---

## Computable vs. Noncomputable Definitions

The reason one definition is `noncomputable` and the other is not comes down to **how the inverse function is provided**.

It's a classic case of being *constructive* versus *classical*.


### `def xorEquiv` (Constructive)

```lean
def xorEquiv {n : ℕ} (m : Plaintext n) : Key n ≃ Ciphertext n where
  toFun     := encrypt m
  invFun    := vec_xor m -- We explicitly provide the inverse function
  left_inv  := by ...
  right_inv := by ...
```

Here, we create the `Equiv` structure by hand. We provide all four components:

1.  `toFun`: The forward function, `encrypt m`.

2.  `invFun`: The inverse function, `vec_xor m`. **We explicitly construct and provid this function.**

3.  `left_inv`: A proof that `vec_xor m (encrypt m k) = k`.

4.  `right_inv`: A proof that `encrypt m (vec_xor m c) = c`.

Because every component is explicitly defined and computable, the entire `xorEquiv` definition is computable.

---

### `noncomputable def encrypt_equiv` (Classical)

```lean
noncomputable def encrypt_equiv {n : ℕ} (m : Plaintext n) : Key n ≃ Ciphertext n :=
  Equiv.ofBijective (encrypt m) (encrypt_bijective m)
```

Here, we use the high-level constructor `Equiv.ofBijective`. We provide it with:

1.  A function, `encrypt m`.

2.  A proof, `encrypt_bijective m`, which proves that the function is both injective and surjective.

But notice what's missing: **we never told Lean what the inverse function is!**

The `Equiv.ofBijective` constructor has to create the inverse function for us.

How does it do that?  It uses the proof of surjectivity.

A proof of `Surjective (encrypt m)` says "for every ciphertext `c`, there *exists* a key `k` such that `encrypt m k = c`."

To define an inverse function, Lean must *choose* such a `k` for each `c`.

This act of choosing an object from a proof of its existence requires the **axiom of
choice** (`Classical.choice`).

In Lean's constructive logic, any definition that depends on the axiom of choice is marked as `noncomputable`.

**In short:**

* **`xorEquiv` is computable** because we did the work of providing the inverse function constructively.

* **`encrypt_equiv` is noncomputable** because we asked Lean to conjure the inverse function out of a classical existence proof, forcing it to use the noncomputable axiom of choice.

---

## Explaining the `otp_perfect_secrecy_lemma` Proof

**Theorem to Prove:**

```lean
theorem otp_perfect_secrecy_lemma {n : ℕ} :
    ∀ (m : Plaintext n), μC_M m = PMF.uniformOfFintype (Ciphertext n)
```

**The Proof, Explained:**
```lean
theorem otp_perfect_secrecy_lemma {n : ℕ} :
    ∀ (m : Plaintext n), μC_M m = PMF.uniformOfFintype (Ciphertext n) := by
  intro m
  have hμ : μC_M m = PMF.uniformOfFintype (Ciphertext n) := by
    apply map_uniformOfFintype_equiv (xorEquiv m)
  simp [hμ, PMF.uniformOfFintype_apply]
```

* **Tactic `intro m`**
    *  **What it does:** The proof begins by addressing the "for all `m`" part of the theorem.

       The `intro` tactic introduces an arbitrary but fixed message `m` that we can work with for the rest of the proof.

    * **Goal State:**

        ```lean
        m: Plaintext n
        ⊢ μC_M m = PMF.uniformOfFintype (Ciphertext n)
        ```

* **Tactic `have hμ : ... := by ...`**

    * **What it does:** This is the main logical step. The `have` tactic lets us prove a helper fact, or lemma, which we can then use to prove our main goal. Here, we are proving a fact named `hμ`. Coincidentally, `hμ` is the exact statement of our main goal.

    * **The Sub-Proof:** The proof of `hμ` is `apply map_uniformOfFintype_equiv (xorEquiv m)`. This applies the helper lemma you proved earlier, which states that mapping a uniform distribution over an equivalence (`xorEquiv m`) results in a uniform distribution. This single line brilliantly captures the core mathematical argument.

    * **Goal State (after the `have` block is complete):**

        ```lean
        m: Plaintext n
        hμ: μC_M m = PMF.uniformOfFintype (Ciphertext n)
        ⊢ μC_M m = PMF.uniformOfFintype (Ciphertext n)
        ```

* **Tactic `simp [hμ, PMF.uniformOfFintype_apply]`**

    * **What it does:** This tactic finishes the proof using the fact `hμ` we just proved. The `simp [hμ]` part tells Lean to rewrite the goal using `hμ`.

    * **How it Works:** `simp` sees `μC_M m` on the left side of the goal `⊢` and sees the hypothesis `hμ` which states `μC_M m = ...`. It substitutes the left side with the right side of `hμ`.

    * **Goal State (after `simp [hμ]`):**

        ```lean
        ⊢ PMF.uniformOfFintype (Ciphertext n) = PMF.uniformOfFintype (Ciphertext n)
        ```

    * This goal is true by reflexivity, and `simp` is able to solve it completely. (The extra `PMF.uniformOfFintype_apply` is not strictly necessary here, as `hμ` is sufficient, but it doesn't hurt). A more direct way to finish after the `have` block would simply be `exact hμ`.
