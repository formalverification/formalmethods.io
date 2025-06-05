# OTP: Construction

!!! info "Definition of \_⊕\_" 

    \_⊕\_ is bitwise XOR: $\quad 0 ⊕ 0 = 0, \quad 0 ⊕ 1 = 1, \quad 1 ⊕ 0 = 1, \quad 1 ⊕ 1 = 0$.

    For n-bit strings $\; a = a₁ ⋯ a_n$, $\; b = b₁ ⋯ b_n$ , let $\; a ⊕ b = a₁ ⊕ b₁ ⋯ a_n ⊕ b_n$.

??? info "Cayley table of \_⊕\_"

    ⊕ | 0 | 1
    --| --| --
    0 | 0 | 1
    1 | 1 | 0


!!! note "An important property of \_⊕\_"

    $a ⊕ b = c ⇔ a = b ⊕ c$, for all $a$, $b$, $c$. 


Fix an integer $n > 0$. 

Let $ℳ$ be the *message space* , $𝒦$ the *key space*, and $𝒞$ the *ciphertext space*.

Assume $ℳ$, $𝒦$, $𝒞$ all equal $\{0, 1\}^n$.

+  **Gen** (key-generation algorithm) choose key from *uniform distribution* over $𝒦$.

+  **Enc** (encryption algorithm) given $k ∈ 𝒦$, $m ∈ ℳ$,  output ciphertext $c = k ⊕ m$.

+  **Dec** (decryption algorithm) given $k ∈ 𝒦$, $c ∈ 𝒞$, output message $m = k ⊕ c$.

