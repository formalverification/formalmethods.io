# Vector and List in Mathlib

!!! note "**Tip**"

    Use the [Mathlib documentation website](https://leanprover-community.github.io/mathlib4_docs/index.html) for easy browsing of module contents and definitions.
    
    <center><https://leanprover-community.github.io/mathlib4_docs/index.html></center>


## [`Data/Vector/`][Data/Vector/]

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

## [`Data/List/`][Data/List/]

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
