# OTP: Perfect Secrecy

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


