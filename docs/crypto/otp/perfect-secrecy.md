# Perfect Secrecy of the One-time Pad

## Construction

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

## Perfect Secrecy Theorem

!!! note "Theorem 2.9 (Katz & Lindell, 2ed)"

    The one-time pad encryption scheme is perfectly secret.

??? note "Proof of Theorem 2.9 ✍️"

    + Let $C$ and $M$ be r.v.s from arbitrary, fixed distributions over $ℳ$ and $𝒞$, resp.
    + Let $K$ be a r.v. from the uniform distribution over $𝒦$.

    !!! note "**Goal** 🥅"

        If $m ∈ ℳ$, $c ∈ 𝒞$ and $ℙ(C = c) > 0$, then $ℙ (M = m \; | \; C = c) = ℙ(M = m)$.

    We first show what amounts to "$C$ is uniform if $K$ is uniform, regardless of $M$."
    
    Compute $ℙ(C = c \; | \; M = m )$ for arbitrary $c ∈ 𝒞$ and $m ∈ ℳ$:
    \\[ℙ (C = c \; | \; M = m) = ℙ (\mathrm{Enc}_k (m) = c) = ℙ(k ⊕ m = c)= ℙ(k = m ⊕ c)= 2^{-n},\\]

    since $k$ is chosen from a uniform distribution over the set $𝒦$ of $n$-bit strings.

    For $c ∈ 𝒞$,

    \\[ℙ (C = c) = ∑\_{m ∈ ℳ} ℙ (C = c \; | \; M = m) · ℙ(M = m) = 2^{-n} ∑\_{m ∈ ℳ} ℙ(M = m) = 2^{-n}.\\] 

    Finally, by Bayes' Theorem,

    \begin{align*}
    ℙ(M = m \; | \; C = c) &= \frac{ℙ(C = c \; | \; M = m) · ℙ(M = m)}{ℙ(C = c)}\\
                           &= \frac{2^{-n} · ℙ(M = m)}{2^{-n}} = ℙ(M = m).
    \end{align*}

    ∎


