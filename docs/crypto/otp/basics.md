## What is the One-Time Pad (OTP)?

A theoretically unbreakable ("perfect secrecy") encryption technique with very specific requirements.

**The Key** must be

* truly random
* at least as long as the plaintext message
* used only once
* kept **secret** between sender and receiver

---

## Encryption

* **plaintext message**. typically converted into a sequence of bits (or numbers)
* **key**. also a sequence of bits (or numbers) of the same length
* **encryption**. performed by combining plaintext with key using a simple operation, most commonly **bitwise XOR**.

If using numbers (e.g., letters A=0, B=1, ... Z=25), modular addition is used.

* `Ciphertext = Plaintext XOR Key` (for bits)
* `Ciphertext = (Plaintext + Key) mod N` (for numbers modulo N)

---

## Decryption

uses the same key and the reverse operation
* `Plaintext = Ciphertext XOR Key` (because `(P XOR K) XOR K = P`)
* `Plaintext = (Ciphertext - Key) mod N`

---

## Perfect Secrecy

The core theoretical property of OTP is 

!!! info ""

    The ciphertext provides *no information* (other than max length)
    about the plaintext content.

+  Formally, $P(\text{plaintext} = m \; | \; \text{ciphertext} = c) = P(\text{plaintext} = m)$.
   
+  Knowing $c$ doesn't change the probability distribution of the plaintext $m$.

+  This holds *only if all the conditions for the key are met* (random, same length, used once).

--- 

## Why OTP is interesting to cryptographers

+  It's the theoretical "gold standard" of secrecy.

+  It highlights the critical importance of key management (randomness, length,
   single-use, secrecy).  Most practical ciphers try to achieve similar security with
   shorter, reusable keys, which is much harder.

+  Understanding its limitations motivates study of other cryptographic systems.

--- 

## Feasibility of Formalizing OTP in Lean

Formalizing the One-Time Pad in Lean is **highly feasible** and useful as a PoC,
providing a concrete example of verifying a security property.

+  **Simple Operations**. The core operations (XOR, modular addition) are already
   well-defined or easy to define in Lean. Mathlib has `Bool.xor` and `ZMod N` for modular arithmetic.

+  **Clear Definitions:** We can define types for plaintexts, keys, and ciphertexts 
   (e.g., `List Bool`, `Vector Bool n`, or functions `Fin n → Bool`).

+  **Focus on a Key Property**. The main goal would be to formalize and prove its
   *perfect secrecy*, a non-trivial but achievable result that would be very compelling.

+  **Mathlib Support**. Mathlib has a growing library for probability theory on
   finite types (`Mathlib.Probability.ProbabilityMassFunction`), which is essential
   for proving perfect secrecy. We don't need to build from scratch! 

---

## What to Formalize

1.  **Define message space, key space, ciphertext space**. 
    For simplicity, use `Vector Bool n` (vectors of Booleans of fixed length `n`).

2.  **Define encrypt and decrypt functions**. 
    (e.g., element-wise XOR for `Vector Bool n`).

3.  **State assumptions about key**.

    + chosen uniformly at random from the key space

    + independent of plaintext

4.  **Formalize definition of perfect secrecy**.

    $$P(M=m \; | \; C=c) = P(M=m)$$

    Involves defining probability mass functions for message and key, and conditional probability.

5.  **Prove our OTP implementation satisfies perfect secrecy** under the stated assumptions.


