# Formalizing Discrete Probability in Lean 4: The One-Time Pad

## FM Crypto Meeting

---

## Overview

- **Goal**: Formalize basic discrete probability in Lean 4
- **Case Study**: One-Time Pad (OTP) and Perfect Secrecy
- **Key Concepts**:
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

-- Element-wise XOR
def vec_xor {n : Nat} (v₁ v₂ : List.Vector Bool n) := 
  map₂ xor v₁ v₂

def encrypt {n : Nat} (m : Plaintext n) (k : Key n) : Ciphertext n :=
  vec_xor m k
```

### Let me show you this in action...

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

**Key points to emphasize**: Notice how the same message encrypted with different keys produces completely different ciphertexts!

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

### Let's explore the XOR properties that make this work...

```lean
-- Demo 2: XOR Properties
section XORProperties
  open OTP Bool
  
  -- Interactive proof that XOR is self-inverse
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

**Teaching moment**: Lean can automatically find these properties, but stepping through shows us exactly why decryption works!

---

## Probability Mass Functions in Lean 4

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

## Key Lemma 1: XOR is a Bijection

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

For fixed $m$, the map $k \mapsto m \oplus k$ is a bijection!

### Let me demonstrate why this bijection property is so important...

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

**Key insight**: This bijection is what guarantees that ciphertexts are uniformly distributed!

---

## Key Lemma 2: Bijections Preserve Uniform Distributions

```lean
lemma map_uniformOfFintype_equiv
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] 
    [Nonempty α] [Nonempty β] (e : α ≃ β) :
    PMF.map e (uniformOfFintype α) = uniformOfFintype β
```

### Intuition
- If we have a uniform distribution on $\alpha$
- And apply a bijection $e : \alpha \to \beta$  
- We get a uniform distribution on $\beta$
- Crucial: bijections preserve cardinality!

### Let's see how this applies to our probability calculations...

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

**Notice**: Both the key distribution and the conditional ciphertext distribution are uniform with the same probability!

---

## Perfect Secrecy: Statement

### Informal Version
For all messages $m$ and ciphertexts $c$:

$$P(M = m | C = c) = P(M = m)$$

### Lean 4 Version
```lean
theorem perfect_secrecy {n : Nat} (μM : PMF (Plaintext n)) 
  (m₀ : Plaintext n) (c₀ : Ciphertext n) :
  (μC_M m₀) c₀ * μM m₀ / (μC μM) c₀ = μM m₀
```

Where:

- `μC_M m₀` is the conditional distribution $P(C | M = m_0)$
- `μC μM` is the marginal distribution $P(C)$

---

## Proof Strategy

1. **Show conditional distribution is uniform**:

   \\[P(C = c | M = m) = \frac{1}{2^n}\\]

2. **Show marginal distribution is uniform**:

   \\[P(C = c) = \frac{1}{2^n}\\]

3. **Apply Bayes' theorem**:

    \begin{align*}
    P(M = m | C = c) =& \frac{P(C = c \; | \; M = m) · P(M = m)}{P(C = c)}\\[8pt]
    &= \frac{2^{-n} · P(M = m)}{2^{-n}}\\[8pt]
    &= P(M = m)
    \end{align*}

   <!-- $$P(M = m | C = c) = \frac{P(C = c | M = m) \cdot P(M = m)}{P(C = c)}$$ -->

   <!-- $$= \frac{\frac{1}{2^n} \cdot P(M = m)}{\frac{1}{2^n}} = P(M = m)$$ -->

---

## Perfect Secrecy Visualization

### Let me show you perfect secrecy in action with a small example...

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

**Critical observation**: Each of the 4 possible 2-bit ciphertexts appears exactly once. This uniform mapping is the essence of perfect secrecy!

---

## Common Pitfall: Key Reuse

### Let me demonstrate why you must NEVER reuse a one-time pad key...

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

**Security lesson**: When you XOR two ciphertexts encrypted with the same key, the key cancels out, leaving $m_1 \oplus m_2$. This leaks information about the messages!

---

## Lessons Learned

### 1. **Type Classes Matter**
- `Fintype` for finite types
- `Nonempty` to avoid division by zero
- `DecidableEq` for computability

### 2. **Bijections are Powerful**
- XOR with fixed value is a bijection
- Bijections preserve uniform distributions
- Can transform complex sums using bijections

### 3. **PMF Library is Well-Designed**
- `bind` for dependent distributions  
- `map` for transforming distributions
- Uniform distributions built-in

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
1. **Other Cryptographic Constructions**
   - Stream ciphers
   - Block ciphers (with appropriate modes)
   - Public key encryption

2. **Advanced Probability**
   - Computational indistinguishability
   - Negligible functions
   - Probabilistic polynomial time

3. **Security Proofs**
   - Semantic security
   - CPA/CCA security
   - Reduction proofs

---

## Takeaways

- **Lean 4 + Mathlib** provides excellent support for probability
- **Type-driven development** helps catch errors early
- **Bijections** are a key tool in cryptographic proofs
- **Perfect secrecy** is elegantly expressible and provable

### Resources
- Code available at: [your repository]
- Mathlib docs: https://leanprover-community.github.io/mathlib4_docs/
- Learn more: https://leanprover.github.io/

---

## Questions?

### Quick Reference
- `PMF α` - Probability mass function over type `α`
- `uniformOfFintype` - Uniform distribution
- `List.Vector` - Fixed-length vectors
- `ENNReal` - Extended non-negative reals
- `≃` - Type equivalence (bijection)

Thank you!
