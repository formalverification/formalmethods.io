## Revealing Proof Objects from Tactics

Let's see how we can get Lean to reveal the proof objects that a proof generates.

**The Feature**

Lean has a tactic called `show_term`.

It executes the tactics within it and then, instead of closing the goal, it prints the raw proof term that was generated.

**How to Demonstrate It:**

1.  Pick a simple proof, like our very first one.

2.  In VS Code, change the proof to

    ```lean
    -- Our theorem: The probability of the key [true, false, true] is 1/8.
    example : μK ⟨[true, false, true], rfl⟩ = (1/8 : ENNReal) := by
      show_term -- Add this tactic
        simp [μK, PMF.uniformOfFintype_apply]; rfl
    ```

3.  When the cursor is on the `show_term` line, the "Lean Infoview" panel will display the generated proof term.

4.  **Warning** (and the point)

    The term is long, ugly, and full of machine-generated names.

    It looks something like `Eq.trans (PMF.uniformOfFintype_apply ... ) (congr_arg Inv.inv (Fintype.card_vector ...))`.

5.  **Explanation**

    For Agda developers, it's natural to ask: where is the proof object?

    Tactic proofs *generate* proof objects. We can ask Lean to show us the term it
    generated using the `show_term` tactic.

    Apparently, the result is extremely verbose and not really meant for human consumption.

    This is the fundamental trade-off: tactics let us write short, conceptual proofs
    at the expense of creating these complex, machine-readable proof terms under the
    hood.




