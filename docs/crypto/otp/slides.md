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

---

## Perfect Secrecy: Statement

### Informal Version
For all messages $m$ and ciphertexts $c$:

$$P(M = m \; | \; C = c) = P(M = m)$$

### Lean 4 Version
```lean
theorem perfect_secrecy {n : Nat} (μM : PMF (Plaintext n)) 
  (m₀ : Plaintext n) (c₀ : Ciphertext n) :
  (μC_M m₀) c₀ * μM m₀ / (μC μM) c₀ = μM m₀
```

Where:

+ `μC_M m₀` is the conditional distribution $P(C \; | \; M = m_0)$
+ `μC μM` is the marginal distribution $P(C)$

---

## Proof Strategy

1.  **Show conditional distribution is uniform**:

    $$P(C = c \; | \; M = m) = 2^{-n}$$

2.  **Show marginal distribution is uniform**:

    $$P(C = c) = 2^{-n}$$

3.  **Apply Bayes' theorem**:

    \begin{align*}
    P(M = m | C = c) =& \frac{P(C = c \; | \; M = m) · P(M = m)}{P(C = c)}\\[8pt]
    &= \frac{2^{-n} · P(M = m)}{2^{-n}}\\[8pt]
    &= P(M = m)
    \end{align*}

---

## Step 1: Conditional Distribution is Uniform

```lean
lemma C_given_M_eq_inv_card_key {n : ℕ} 
  (m : Plaintext n) (c : Ciphertext n) :
  (μC_M m) c = 1 / card (Key n) := by
  -- μC_M m = map (encrypt m) μK
  -- encrypt m is a bijection (xorEquiv m)
  -- So map (encrypt m) μK = uniformOfFintype (Ciphertext n)
  have hμ : μC_M m = uniformOfFintype (Ciphertext n) := by
    apply map_uniformOfFintype_equiv (xorEquiv m)
  simpa [hμ, uniformOfFintype_apply]
    using card_congr (xorEquiv m)
```

---

## Step 2: Marginal Distribution is Uniform

```lean
lemma prob_C_uniform_ennreal {n : Nat} (μM : PMF (Plaintext n)) 
  (c : Ciphertext n) :
  (μC μM) c = (card (Key n) : ENNReal)⁻¹
```

### Key insight:
- For each $m$, there's exactly one $k$ such that $m \oplus k = c$
- Namely, $k = m \oplus c$
- So we can rewrite the sum over $(m,k)$ pairs as a sum over $m$ alone

---

## Working with ENNReal

### Challenge: Division in probability
- PMFs use `NNReal` (non-negative reals)
- Division requires `ENNReal` (extended non-negative reals)
- Need to handle $0$ and $\infty$ carefully

### Key properties used:
```lean
-- For x ≠ 0 and x ≠ ∞:
x * y / x = y

-- Uniform distribution has probability 1/|S|
(uniformOfFintype S) s = (card S)⁻¹
```

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

## Demo: Interactive Proof Development

Let's see how Lean 4's tactics work in practice:

```lean
example {n : Nat} (m : Plaintext n) (k : Key n) :
  encrypt m k = encrypt m k := by
  -- Lean's proof state shows current goal
  rfl  -- reflexivity
  
example {n : Nat} (m : Plaintext n) (k₁ k₂ : Key n) 
  (h : encrypt m k₁ = encrypt m k₂) : k₁ = k₂ := by
  -- Use key uniqueness
  have h_unique := key_uniqueness m k₁ (encrypt m k₂)
  rw [h_unique.mp h]
  -- Alternative: use xorEquiv directly
```

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

- **Lean 4 + Mathlib** provides excellent support for probability
- **Type-driven development** helps catch errors early
- **Bijections** are a key tool in cryptographic proofs
- **Perfect secrecy** is elegantly expressible and provable


### Resources

+  Slides: <https://formalmethods.io/crypto>
+  Code: <https://github.com/formalverification/lean4crypto/>

+  Lean site: <https://lean-lang.org/>
+  Lean docs: https://lean-lang.org/documentation/ 
+  Mathlib docs: <https://leanprover-community.github.io/mathlib4_docs/>

---

## Questions?

### Quick Reference
- `PMF α` - Probability mass function over type `α`
- `uniformOfFintype` - Uniform distribution
- `List.Vector` - Fixed-length vectors
- `ENNReal` - Extended non-negative reals
- `≃` - Type equivalence (bijection)

Thank you!

---


