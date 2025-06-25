# Formalizing Discrete Probability in Lean 4: The One-Time Pad

## FM Crypto Meeting

---

## Overview

- <font color="slate">GOAL</font>

     Learn how to formalize some basic discrete probability in Lean 4.

- <font color="slate">CASE STUDY</font>

     Use Lean for formalize the statement and proof of *perfect secrecy* of the One-Time Pad.

- <font color="slate">KEY CONCEPTS</font>
    - Probability Mass Functions (PMFs)
    - Independence and joint distributions
    - Conditional probability
    - Bijections preserving uniform distributions

---

## The One-Time Pad

### Informal Definition

- **Message space**: $M = \{0,1\}^n$
- **Key space**: $K = \{0,1\}^n$
- **Ciphertext space**: $C = \{0,1\}^n$
- **Encryption**: $\text{Enc}(m, k) = m \oplus k$
- **Decryption**: $\text{Dec}(c, k) = c \oplus k$

### Key Property
$$\text{Dec}(\text{Enc}(m, k), k) = (m \oplus k) \oplus k = m$$

---

## Lean 4 Formalization: Types

```lean
import Mathlib.Data.Vector.Basic

def Plaintext  (n : Nat) := List.Vector Bool n
def Key        (n : Nat) := List.Vector Bool n
def Ciphertext (n : Nat) := List.Vector Bool n

-- Element-wise xor
def vec_xor {n : Nat} (v₁ v₂ : List.Vector Bool n) :=
  map₂ xor v₁ v₂

def encrypt {n : Nat} (m : Plaintext n) (k : Key n) : Ciphertext n :=
  vec_xor m k
```

??? info "Let me show you this in action..."

    ```lean
    -- Demo 1: Basic OTP Operations
    section BasicOTP
      open OTP

      -- Create a 4-bit message
      def demo_msg : Plaintext 4 := ⟨[true, false, true, true], by decide⟩
      def demo_key : Key 4 := ⟨[false, true, false, true], by decide⟩

      -- Show encryption
      #eval encrypt demo_msg demo_key
      -- Output: [true, true, true, false]

      -- Show decryption recovers the message
      #eval decrypt (encrypt demo_msg demo_key) demo_key
      -- Output: [true, false, true, true]

      -- Show that different keys give different ciphertexts
      def demo_key2 : Key 4 := ⟨[true, true, false, false], by decide⟩
      #eval encrypt demo_msg demo_key2
      -- Output: [false, true, true, true]
    end BasicOTP
    ```

    !!! note "Key point"

        The same message encrypted with different keys produces different ciphertexts!

---

## Correctness of Encryption/Decryption

```lean
lemma encrypt_decrypt {n : Nat} (m : Plaintext n) (k : Key n) :
  decrypt (encrypt m k) k = m := by
  unfold encrypt decrypt vec_xor
  apply ext  -- vector extensionality
  intro i    -- prove element-wise
  simp only [get_map₂]
  -- Goal: xor (xor (get m i) (get k i)) (get k i) = get m i
  simp  -- Uses xor properties automatically
```

Key insight: Reduce vector equality to element-wise boolean equality

??? info "Let's explore the xor properties that make this work..."

    ```lean
    -- Demo 2: xor Properties
    section xorProperties
      open OTP Bool

      -- Interactive proof that xor is self-inverse
      example (a b : Bool) : xor (xor a b) b = a := by
        -- Let's explore the proof interactively
        rw [xor_assoc]
        -- Goal: xor a (xor b b) = a
        rw [xor_self]
        -- Goal: xor a false = a
        rw [xor_false]
        -- Done!

      -- Another way using simp
      example (a b : Bool) : xor (xor a b) b = a := by simp
    end XORProperties
    ```

    !!! note "Teaching moment"

        Lean can automatically find these properties, but stepping through shows us exactly why decryption works!

---

## Probability Mass Functions in Lean

### Mathlib's PMF type
```lean
import Mathlib.Probability.ProbabilityMassFunction.Constructions

-- PMF α represents discrete probability distributions over α
-- (μ : PMF α) assigns probability μ a to element a : α
```

### Uniform distribution over keys
```lean
noncomputable def μK {n : ℕ} : PMF (Key n) :=
  uniformOfFintype (Key n)

-- For any key k: μK k = 1 / 2^n
```

---

## Independence and Joint Distributions

### Independent product of PMFs
```lean
noncomputable def μMK {n : ℕ} (μM : PMF (Plaintext n)) :
  PMF (Plaintext n × Key n) :=
  PMF.bind μM (fun m => PMF.map (fun k => (m, k)) μK)

-- P(M = m, K = k) = P(M = m) · P(K = k)
```

### Ciphertext distribution
```lean
noncomputable def μC {n : Nat} (μM : PMF (Plaintext n)) :
  PMF (Ciphertext n) :=
  PMF.bind (μMK μM) (fun mk =>
    PMF.pure (encrypt mk.1 mk.2))
```

---

!!! info "Lemma (xor is a Bijection)"

    For fixed $m$, the map $k ↦ m ⊕ k$ is a bijection!

    ```lean
    def xorEquiv {n : ℕ} (m : Plaintext n) : Key n ≃ Ciphertext n where
      toFun   := encrypt m     -- k ↦ m ⊕ k
      invFun  := vec_xor m     -- c ↦ m ⊕ c
      left_inv := by           -- m ⊕ (m ⊕ k) = k
        intro k
        apply ext
        simp [encrypt, vec_xor, get_map₂, xor_aab_eq_b]
      right_inv := by          -- (m ⊕ c) ⊕ m = c
        intro c
        apply ext
        simp [encrypt, vec_xor, get_map₂, xor_aab_eq_b]
    ```

??? note "Let me demonstrate why this bijection property is so important..."

    ```lean
    -- Demo 3: Bijection Property
    section BijectionDemo
      open OTP

      -- Show that encryption with a fixed message is injective
      example {n : Nat} (m : Plaintext n) (k₁ k₂ : Key n)
        (h : encrypt m k₁ = encrypt m k₂) : k₁ = k₂ := by
        -- Use the bijection property
        have bij := xorEquiv m
        -- Apply injectivity
        exact bij.injective h

      -- Show that for every ciphertext, there's a unique key
      example {n : Nat} (m : Plaintext n) (c : Ciphertext n) :
        ∃! k : Key n, encrypt m k = c := by
        use vec_xor m c
        constructor
        · -- Existence
          simp [encrypt, vec_xor, xor_aab_eq_b]
        · -- Uniqueness
          intro k hk
          exact (key_uniqueness m k c).mp hk
    end BijectionDemo
    ```

    !!! note "Key insight"

        This bijection is what guarantees that ciphertexts are uniformly distributed!

---

!!! info "Lemma (bijections preserve uniform distributions)"

    ```lean
    lemma map_uniformOfFintype_equiv
        {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
        [Nonempty α] [Nonempty β] (σ : α ≃ β) :
        PMF.map σ (uniformOfFintype α) = uniformOfFintype β
    ```

    !!! note "Intuition"

        Given a uniform distribution on $α$, if we apply a bijection $σ : α → β$, then
        we get a uniform distribution on $β$. **Crucial point**: bijections preserve cardinality!

??? note "Let's see how this applies to our probability calculations..."

    ```lean
    -- Demo 4: Probability Calculations
    section ProbabilityDemo
      open OTP PMF

      -- The probability of any specific 3-bit key is 1/8
      example : (μK (n := 3)) ⟨[true, false, true], by decide⟩ = 1/8 := by
        simp [μK, uniformOfFintype_apply]
        -- Lean knows that card (Key 3) = 2^3 = 8
        norm_num

      -- The conditional probability P(C = c | M = m) is also 1/8
      example (m : Plaintext 3) (c : Ciphertext 3) :
        (μC_M m) c = 1/8 := by
        rw [C_given_M_eq_inv_card_key]
        norm_num
    end ProbabilityDemo
    ```

    !!! note "Key Point"

        Both the key distribution and the conditional ciphertext distribution are uniform with the same probability!

---

## Perfect Secrecy: Statement

### Informal Version
For all messages $m$ and ciphertexts $c$:

$$P(M = m | C = c) = P(M = m)$$

It's easy to see this is equivalent to the assertion that $M$ and $C$ are indenpendent.

!!! info "Independence and Conditional Probability"

    By definition of conditional probability,

    $$P(M = m \;|\; C = c) · P(C = c) = P(M = m, C = c) = P(C = c \;| \; M = m) · P(M = m).$$

    $M$ and $C$ are <font color="slate">independent</font> provided

    $$P(M = m, C = c) = P(M = m) P(C = c).$$

    Therefore, assuming $P(C = c) > 0$ and $P(M = m) > 0$, the following are equivalent:

    1. $P(M = m, C = c) = P(M = m) · P(C = c)$

    2. $P(M = m \;| \; C = c) = P(M = m)$,

    3. $P(C = c \;| \; M = m) = P(C = c)$.


We will prove the third assertion.


<!-- Prove -->
<!-- ### Lean Version -->
<!-- ```lean -->
<!-- theorem perfect_secrecy {n : Nat} (μM : PMF (Plaintext n))  -->
<!--   (m₀ : Plaintext n) (c₀ : Ciphertext n) : -->
<!--   (μC_M m₀) c₀ * μM m₀ / (μC μM) c₀ = μM m₀ -->
<!-- ``` -->

<!-- Where: -->

<!-- - `μC_M m₀` is the conditional distribution $P(C | M = m_0)$ -->
<!-- - `μC μM` is the marginal distribution $P(C)$ -->

---

## Proof Strategy

1. **Show conditional distribution is uniform**:

   \\[P(C = c | M = m) = \frac{1}{2^n}\\]

2. **Show marginal distribution is uniform**:

   \\[P(C = c) = \frac{1}{2^n}\\]

---

## Perfect Secrecy Visualization

??? info "Perfect secrecy in action with a small example..."

    ```lean
    -- Demo 5: Perfect Secrecy Visualization
    section PerfectSecrecyDemo
      open OTP

      -- For a 2-bit OTP, let's verify perfect secrecy manually
      -- Message: [true, false]
      -- Key space has 4 elements: [false,false], [false,true], [true,false], [true,true]

      def msg_10 : Plaintext 2 := ⟨[true, false], by decide⟩

      -- Each key gives a different ciphertext:
      #eval encrypt msg_10 ⟨[false, false], by decide⟩  -- [true, false]
      #eval encrypt msg_10 ⟨[false, true], by decide⟩   -- [true, true]
      #eval encrypt msg_10 ⟨[true, false], by decide⟩   -- [false, false]
      #eval encrypt msg_10 ⟨[true, true], by decide⟩    -- [false, true]

      -- Key insight: Every possible ciphertext appears exactly once!
      -- This is why the OTP has perfect secrecy.
    end PerfectSecrecyDemo
    ```

    !!! note "Critical observation"

        Each of the 4 possible 2-bit ciphertexts appears exactly once. This uniform mapping is the essence of perfect secrecy!

---

## Common Pitfall: Key Reuse

??? info "Why you must never reuse a one-time pad key..."

    ```lean
    -- Demo 6: Common Pitfall - Key Reuse
    section KeyReuse
      open OTP

      def msg1 : Plaintext 4 := ⟨[true, false, true, false], by decide⟩
      def msg2 : Plaintext 4 := ⟨[false, true, false, true], by decide⟩
      def shared_key : Key 4 := ⟨[true, true, false, false], by decide⟩

      def c1 := encrypt msg1 shared_key
      def c2 := encrypt msg2 shared_key

      -- If an attacker gets both ciphertexts, they can XOR them:
      #eval vec_xor c1 c2
      -- This equals vec_xor msg1 msg2 - the key cancels out!
      #eval vec_xor msg1 msg2

      -- Lesson: NEVER reuse a one-time pad key!
    end KeyReuse
    ```

    !!! note "Security lesson"

        If we xor two ciphertexts encrypted with the same key, the key cancels out, leaving $m_1 ⊕ m_2$. This leaks information about the messages!

---

## Summary and Lessons Learned

### 1. **Type Classes Matter**

- `Fintype` for finite types
- `Nonempty` to avoid division by zero
- `DecidableEq` for computability

### 2. **Bijections are Powerful**

- xor with fixed value is a bijection
- Bijections preserve uniform distributions
- Can transform complex sums using bijections

### 3. **PMF Library is Well-Designed**

- `bind` for dependent distributions
- `map` for transforming distributions
- Uniform distributions built-in

---

## Summary and Lessons Learned

1. **What μC represents**

     The distribution of ciphertexts when we:

     - sample a message `m` from `μM`
     - sample a key `k` uniformly from all `2ⁿ` keys
     - output `encrypt m k`

2. **Why it's uniform**

     - for each `m`, the map `k ↦ m ⊕ k` is a bijection
     - so each ciphertext `c` appears exactly once for each `m`
     - since keys are uniform, each `c` has probability `1/2ⁿ`

3. **Perfect secrecy**: P(C = c | M = m) = 1/2ⁿ = P(C = c)

     - OTP achieves perfect secrecy because xor is a bijection
     - so both conditional and marginal distributions of ciphertexts are uniform
     - this is precisely independence between message and ciphertext.

---

## Challenges in Formalization

### 1. **Vector Equality**

- Must use extensionality (`ext`)
- Reduce to element-wise proofs
- `simp` is very helpful with `get_map₂`

### 2. **Infinite Sums**

- `tsum` requires careful manipulation
- Product types need `tsum_prod'`
- Conditional sums use `tsum_ite_eq`

### 3. **Real Number Arithmetic**

- Coercion between `Nat`, `NNReal`, `ENNReal`
- Division requires non-zero denominators
- Must track when values are finite

---

## Future Directions

### Extensions

1.  **Other Cryptographic Constructions**

    + Stream ciphers
    + Block ciphers (with appropriate modes)
    + Public key encryption

2.  **Advanced Probability**

    + Computational indistinguishability
    + Negligible functions
    + Probabilistic polynomial time

3.  **Security Proofs**

    + Semantic security
    + CPA/CCA security
    + Reduction proofs

---

## Takeaways

- **Lean + Mathlib** provides excellent support for probability
- **Type-driven development** helps catch errors early
- **Bijections** are a key tool in cryptographic proofs
- **Perfect secrecy** is elegantly expressible and provable


### Resources

+  **Slides** <https://formalmethods.io/crypto>
+  **Code** <https://github.com/formalverification/lean4crypto/>

+  **Lean** <https://lean-lang.org/>
+  **Mathlib docs** <https://leanprover-community.github.io/mathlib4_docs/>
+  **Mathlib source** <https://github.com/leanprover-community/mathlib4>

## Questions?

### Quick Reference

- `PMF α` - Probability mass function over type `α`
- `uniformOfFintype` - Uniform distribution
- `List.Vector` - Fixed-length vectors
- `ENNReal` - Extended non-negative reals
- `≃` - Type equivalence (bijection)

Thank you!
