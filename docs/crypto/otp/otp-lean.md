# OTP in L∃∀N

## Initial Considerations

+ What types for messages, keys, ciphertexts? (`Vector Bool n` is a good candidate, or `Fin n → Bool`).
+ How to represent the XOR operation on these types?
+ Which Mathlib probability definitions will you need? (e.g., `PMF`, `Pure`, `Bind` for random variables, `cond` for conditional probability).

---

## Types

```lean
def Plaintext (n : Nat) := Vector Bool n
def Key (n : Nat) := Vector Bool n
def Ciphertext (n : Nat) := Vector Bool n
```

Using `n : Nat` so definitions are generic for any length.

---

## XOR Operation

We need a function like

```lean
xor_vector {n : Nat} (v₁ v₂ : Vector Bool n) : Vector Bool n
```

This can be defined using `Vector.map₂ Bool.xor v₁ v₂`.

---


## Mathlib Probability Definitions

* *Message Distribution (`PMF (Plaintext n)`):* The perfect secrecy definition usually assumes *some* distribution for messages. 

      We might leave this as arbitrary `(μ_M : PMF (Plaintext n))` in our theorem statement.

* **Key Distribution (`PMF (Key n)`):** must be uniform, so we need to define what
`is_uniform (μ_K : PMF (Key n))` means.

      Typically, for a finite type `α`, a `PMF p` is uniform if `p a = 1 / Fintype.card α` for all `a`.

      Mathlib should have utilities for this (e.g., `PMF.uniformOfFintype`).

* **Ciphertext Distribution:** derived from message and key distributions using `PMF.bind` or `PMF.map` to represent the encryption process.

* **Independence:** we'll likely need to state the independence of key and message PMFs as a hypothesis. 

      Can be expressed by saying the joint distribution is the product of the marginals.

      e.g., `joint_pmf m k = (μ_M m) * (μ_K k)`

      Mathlib's `PMF.indepFun` might be relevant here.

* **Conditional Probability:** `PMF.cond` will be key to defining $ℙ(M=m \;| \;C=c)$.

---

### **Lean 4 Project Setup** 셋업

1.  **Create the Project**.

    In a terminal,
    ```bash
    lake new OTP math
    cd OTP
    ```

2.  **Verfiy Mathlib Dependency**.

    The `lakefile.toml` should look something like this:

    ```toml
    name = "OTP"
    version = "0.1.0"
    keywords = ["math"]
    defaultTargets = ["OTP"]

    [leanOptions]
    pp.unicode.fun = true # pretty-prints `fun a ↦ b`
    autoImplicit = false

    [[require]]
    name = "mathlib"
    scope = "leanprover-community"

    [[lean_lib]]
    name = "OTP"
    ```

3.  **Fetch Mathlib:**
    In your terminal (in the `otp_formalization` directory):
    ```bash
    lake update
    ```
    This might take a few minutes the first time. Then build to ensure it's working:
    ```bash
    lake build
    ```

4.  **Create Main File**.

    * The `lake new` command creates `OTP.lean` and `OTP/Basic.lean`.
    * We'll start the formalization in `OTP/Basic.lean` which is imported into `OTP.lean`.


---


### **Initial Definitions** ✍️

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
