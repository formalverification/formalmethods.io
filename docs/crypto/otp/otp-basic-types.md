# Basic Types for the OTP

<!-- markdown-toc start - Don't edit this section. Run M-x markdown-toc-refresh-toc -->
**Table of Contents**

- [Basic Types for the OTP](#basic-types-for-the-otp)
  - [Initial Considerations 🤔](#initial-considerations-)
  - [Types Aliases  🕵️](#types-aliases--)
  - [XOR Operation ⊕](#xor-operation-)
  - [Initial Definitions ✍️](#initial-definitions-)
  - [Mathlib Specifics](#mathlib-specifics)
    - [[`Data/Vector/`][Data/Vector/]](#datavectordatavector)
    - [[`Data/List/`][Data/List/]](#datalistdatalist)

<!-- markdown-toc end -->


## Initial Considerations 🤔

+ What types for messages, keys, ciphertexts?

    `Vector Bool n` is a good candidate (or `Fin n → Bool`).

+ How to represent the XOR operation on these types?

+ Which Mathlib probability definitions will you need? (e.g., `PMF`, `Pure`, `Bind` for random variables, `cond` for conditional probability).

---

## Types Aliases  🕵️

```lean
def Plaintext (n : Nat) := Vector Bool n
def Key (n : Nat) := Vector Bool n
def Ciphertext (n : Nat) := Vector Bool n
```

Using `n : Nat` so definitions are generic for any length.

---

## XOR Operation ⊕

We need a function like

```lean
xor_vector {n : Nat} (v₁ v₂ : Vector Bool n) : Vector Bool n
```

This can be defined using `Vector.map₂ Bool.xor v₁ v₂`.

---


## Initial Definitions ✍️

!!! note "*Message Distribution* `PMF (Plaintext n)`"

    Perfect secrecy definition assumes messages come from *some* probability distribution.

    In our theorem statement, we leave this arbitrary: `μ_M : PMF (Plaintext n)`.

!!! note "*Key Distribution* `PMF (Key n)`"

    This is uniform on the key space (a finite set of size 2ⁿ).

    We need to define what `is_uniform (μ_K : PMF (Key n))` means.

    For a finite type `α`, probability mass function `p` is uniform if `p a = 1 / card α` for all `a : α`.

    Mathlib has utilities for this, e.g. `PMF.uniformOfFintype`.

!!! note "*Ciphertext Distribution* `PMF (Ciphertext n)`"

    This is derived from message and key distributions using `PMF.bind` to represent the encryption process.

!!! note "*Conditional Probability* $ℙ(M=m \;| \;C=c)$"

    defined using `PMF.cond`

In `OTP/Basic.lean`,

```lean
import Mathlib.Data.Vector.Basic

namespace OTP

  def Plaintext (n : Nat) := Vector Bool n
  def Key (n : Nat) := Vector Bool n
  def Ciphertext (n : Nat) := Vector Bool n

  -- Element-wise XOR for Vectors
  def xor_vector {n : Nat} (v₁ v₂ : Vector Bool n) : Vector Bool n :=
    Vector.zipWith Bool.xor v₁ v₂
    -- Or more explicitly:
    -- Vector.ofFn (fun i => Bool.xor (v₁.get i) (v₂.get i))

  def encrypt {n : Nat} (p : Plaintext n) (k : Key n) : Ciphertext n :=
    xor_vector p k

  def decrypt {n : Nat} (c : Ciphertext n) (k : Key n) : Ciphertext n :=
    xor_vector c k

  -- Let's test with a simple example if we can construct vectors
  -- To make this evaluable, we need a concrete n and ways to make vectors.
  -- For example:
  def ex_plaintext : Plaintext 3 := ⟨#[true, false, true], by decide⟩ -- Using constructor for clarity

  -- Or using the direct constructor...
  def ex_plaintext' : Plaintext 3 := ⟨#[true, false, true], by rfl⟩ -- by rfl or by decide usually works for length proofs
  def ex_key : Key 3 := ⟨#[false, true, true], by decide⟩

  #eval encrypt ex_plaintext ex_key
  -- Expected output: vector of ![true, true, false] (or similar representation)

  def ex_ciphertext : Ciphertext 3 := encrypt ex_plaintext ex_key
  #eval decrypt ex_ciphertext ex_key
  -- Expected output: vector of ![true, false, true]

end OTP
```

---

## Mathlib Specifics

!!! note "**Tip**"

    Use the [Mathlib documentation website](https://leanprover-community.github.io/mathlib4_docs/index.html) for easy browsing of module contents and definitions.

    <center><https://leanprover-community.github.io/mathlib4_docs/index.html></center>


### [`Data/Vector/`][Data/Vector/]

📁 [`Mathlib/Data/Vector/Basic.lean`][Data/Vector/Basic.lean].

+  **`Vector α n`** represents a list of elements of type `α` that is known to have
length `n`.
   Well suited to plaintexts, keys, and ciphertexts where length is fixed and equal.


🧰 **Useful functions**

+  `Vector.map (f : α → β) : Vector α n → Vector β n`
+  `Vector.map₂ (f : α → β → γ) : Vector α n → Vector β n → Vector γ n`,
   perfect for XORing two vectors.
+  `Vector.get : Vector α n → Fin n → α` to get an element at an index.
+  `Vector.ofFn : ((i : Fin n) → α) → Vector α n` to construct a vector from a function.
+  Literals like `![a, b, c]` can often be coerced to `Vector α 3` if the type is known.

---

### [`Data/List/`][Data/List/]

+  In [`Mathlib/Data/List/Basic.lean`][Data/List/Basic.lean] and other files in [`Mathlib/Data/List/`][Data/List/].

+  While `Vector` is likely better for fixed-length crypto primitives, `List α` is
   the standard list type.

+  Good to know its API (e.g., `map`, `zipWith`, `length`) as `Vector` often mirrors
   or builds upon `List` concepts.

---


[Data/List/Basic.lean]: https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/List/Basic.lean
[Data/List/Basic.html]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/Basic.html
[Data/List/]: https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/Data/List
[Data/Vector/]: https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/Data/Vector
[Data/Vector/Basic.lean]: https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/Vector/Basic.lean
