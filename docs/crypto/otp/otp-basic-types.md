# Basic Types for the OTP

## Initial Considerations 🤔

+ What types for messages, keys, ciphertexts?

    `Vector Bool n` is a good candidate (or `Fin n → Bool`).

+ How to represent the XOR operation on these types?

+ Which Mathlib probability definitions will you need? (e.g., `PMF`, `Pure`, `Bind` for random variables, `cond` for conditional probability).

---

## Initial Definitions ✍️

### Types Aliases

```lean
def Plaintext (n : Nat) := Vector Bool n
def Key (n : Nat) := Vector Bool n
def Ciphertext (n : Nat) := Vector Bool n
```

Using `n : Nat` so definitions are generic for any length.


### The XOR Operation ⊕

To encrypt plain text messages, and decrypt ciphertext messages, we will use the "exclusive or" function, `xor`,
applied pointwise to the message and key vectors.

```lean
xor_vector {n : Nat} (v₁ v₂ : Vector Bool n) : Vector Bool n
```

As we'll see below, this operation can be defined in a number of ways---for example,
as `Vector.zipWith Bool.xor v₁ v₂` or `Vector.ofFn (λ i => Bool.xor (v₁.get i)
(v₂.get i))`, which are merely different ways of applying Boolean xor pointwise on
the input vectors.

The `encrypt` and `decrypt` functions are essentially aliases for the `xor_vector`
function:

```lean
def encrypt {n : Nat} (p : Plaintext n) (k : Key n) : Ciphertext n :=
  xor_vector p k

def decrypt {n : Nat} (c : Ciphertext n) (k : Key n) : Ciphertext n :=
  xor_vector c k
```

Notice, however, that unlike `xor_vec` which takes a pair of generic binary vectors
and returns a binary vector, `encrypt` takes a `Plaintext` message and a `Key` and
returns `Ciphertext` message, while `decrypt` takes a `Ciphertext` message and a
`Key` and returns `Plaintext` message.

Lean will complain if we try to apply `encrypt` to a `Ciphertext` message and a
`Key` or to two generic binary vectors.


---

## Initial Definitions in Lean

Let's now encode these basic definitions in Lean.

In Section [Lean Project Setup](crypto/otp/lean-project-setup.md), we created and
built a Lean project called `OTP`.  This process creates a file called
`OTP/Basic.lean` containing one line:

```lean
def hello := "world"
```

In your terminal, navigate to the `OTP` project directory and enter `code .`, which
will launch VSCode with the `OTP` project open.

In the project Explorer window on the left, click on the `OTP` directory and double
click on the `Basic.lean` file to open it.

Replace its contents (`def hello := "world"`) with the following:

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
  def ex_plaintext : Plaintext 3 := ⟨#[true, false, true], by decide⟩

  def ex_plaintext'' : Plaintext 3 := ⟨#[true, false, true], rfl⟩
  -- `rfl` is the unique constructor for the equality type

  def ex_plaintext' : Plaintext 3 := ⟨#[true, false, true], by rfl⟩
  -- `by rfl` uses the rfl tactic, which is more generic than the `rfl` above.
  -- It works for any relation that has a reflexivity lemma tagged with
  -- the attribute `@[refl]`.

  def ex_key : Key 3 := ⟨#[false, true, true], by decide⟩

  #eval encrypt ex_plaintext ex_key
  -- Expected output: vector of ![true, true, false] (or similar representation)

  def ex_ciphertext : Ciphertext 3 := encrypt ex_plaintext ex_key
  #eval decrypt ex_ciphertext ex_key
  -- Output: #[true, false, true]

end OTP
```

!!! note "Exercise"

    Can the `encrypt` function take a `Ciphertext` and a `Key` (or a `Plaintext` message and a `Ciphertext` message, or even two keys) as arguments?  (Use `#eval` to check.)

    Would you say that `encrypt` is a function from `Plaintext n` × `Key n` to `Ciphertext n`?  Or is it a binary operation on `Vector Bool n`?

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
