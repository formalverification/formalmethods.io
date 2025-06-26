# The Law of Total Probability in Lean

## Deconstructing a Compositional Proof with `bind` and `pure`

We now move beyond proofs that are solved by a single `simp` command
and into a more structured proof that requires several foundational tactics.

We will prove a fundamental property about the ciphertext distribution `μC`, which we
define using `bind` and `pure`.

This give us the perfect opportunity to explore tactics like `rw`, `intro`, and
`apply`, and examine their corresponding proof term constructions.

---

### Construction of `μC`

The ciphertext distribution `μC` can be constructed by
chaining two probabilistic processes:

1.  Sample a message-key pair `(m , k)` from their joint distribution `μMK`.

2.  Deterministically compute the ciphertext `c = encrypt m k`.

We capture this nicely in Lean as follows:

```lean
μC = bind μMK (λ mk => pure (encrypt mk.1 mk.2))
```

To help us understand the meaning of this definition, let's use it to prove a theorem
that computes the probability of a specific ciphertext `c`.

---

### The Law of Total Probability

`P(C=c)` is the sum of probabilities of all `(m, k)` pairs that produce `c`.

!!! info "**Theorem**"

    ```lean
    μC c = ∑' (⟨m , k⟩ : Plaintext n × Key n), if encrypt m k = c then μMK ⟨m , k⟩ else 0
    ```

Proving this will require unpacking the meaning of `bind` and `pure`.

---

### Setup for the Proof

First we add the necessary definitions to our Lean file.

We need `Plaintext`s, an encryption function, and the distributions `μMK` and `μC`.

For simplicity, we use a simple xor for encryption and assume a uniform distribution
for messages.

```lean
-- Assume a uniform distribution on messages for this example.
noncomputable def μM {n : ℕ} : PMF (Plaintext n) :=
  PMF.uniformOfFintype (Plaintext n)

-- Manual construction of the product distribution P(m, k) = P(m) * P(k).
-- (assumes independence of message and key)
noncomputable def μMK {n : ℕ} : PMF (Plaintext n × Key n) :=
  PMF.bind μM (λ m => PMF.map (λ k => (m, k)) μK)

-- The ciphertext distribution, built with bind and pure.
noncomputable def μC {n : ℕ} : PMF (Ciphertext n) :=
  PMF.bind μMK (λ ⟨m, k⟩ => PMF.pure (encrypt m k))
```

The **law of total probability** says that `P(C=c)` is the sum of probabilities of
all `(m, k)` pairs that produce `c`.

!!! info "**Theorem**"

    ```lean
    μC c = ∑' (mk : Plaintext n × Key n), if encrypt mk.1 mk.2 = c then μMK mk else 0
    ```

---

### The Proof Step-by-Step

Here is the complete, corrected proof in Lean:
```lean
open Classical
theorem μC_apply_eq_sum {n : ℕ} (c : Ciphertext n) :

  μC c = ∑' mk : Plaintext n × Key n,
           if encrypt mk.1 mk.2 = c then μMK mk else 0

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
⊢   (if c = encrypt mk.1 mk.2 then μMK mk else 0)
  = (if encrypt mk.1 mk.2 = c then μMK mk else 0)
```

---

#### Step 3: Finishing with `eq_comm`

Now we just resolve the switched equality.

**Tactic**. `simp only [eq_comm]`

* The lemma `eq_comm` states that `a = b` is equivalent to `b = a`. `simp` uses this
  to rewrite the goal, making the two sides identical and closing the proof.

---




