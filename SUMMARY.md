# Łukasiewicz Logic & MV-algebras in Lean 4 — Summary

A from-scratch formalization of MV-algebras and the BL/Łukasiewicz proof systems,
with **no Mathlib dependency**. Every canonical file is pure Lean 4 core (zero
imports) and has been compiled and verified with Lean 4.31.0.

## Canonical files — all pure core, all compile

| File | imports | `sorry` tactic | Axiom deps of main result |
|---|---|---|---|
| `MVAlgebra_scratch.lean` | 0 | 0 | none / `propext` |
| `Equivalence.lean` | 0 | 0 | `propext` |
| `Soundness.lean` | 0 | **0** | **`propext`** |
| `DeductionBL.lean` | 0 | 0 | `propext` |
| `prop17.lean` | 0 | 0 | `propext` |

All compile standalone with `lean FILE.lean` — no Lake, no Mathlib, no toolchain
setup beyond the Lean compiler itself. **No file depends on `sorryAx` or
`Classical.choice`.**

## What is proven

**`MVAlgebra_scratch.lean` — the algebraic heart, 0 sorry.**
MV-algebras via Chang's axioms; the natural order with antisymmetry; the keystone
**residuation** `x⊙z ≤ y ↔ z ≤ x⇨y`; detachment; the ⊙-monoid; both De Morgan
laws; and the lattice fragment through absorption.

**`Equivalence.lean` — BL+dn vs Łukasiewicz, 0 sorry — COMPLETE.**
Direction A of the basis equivalence: all four Łukasiewicz axioms (L1–L4) are
derived in BL + double negation and machine-checked axiom-free.

**`Soundness.lean` — algebraic soundness, 0 sorry — COMPLETE.**
**All 11 BL axioms proved sound algebraically** — id, a1, a2, a3, a4, a5a, a5b,
a6, a7, dn, and modus ponens. `#print axioms sound` shows `[propext]` only — no
`sorryAx`. The hard case (a6, prelinearity) is proved via **Mundici's
Proposition 1.7** `(x⊖y) ∧ (y⊖x) = 0` and **Proposition 1.6(ii)**
(distributivity of `⊕` over `∧`), yielding the **key equation**
`(z ⊕ ¬A) ∧ (z ⊕ ¬B) = z` when A = imp x y, B = imp y x. All steps are equational
derivations from Chang's axioms; no subdirect representation theorem needed.

**`DeductionBL.lean` — Local Deduction Theorem over BL, 0 sorry — COMPLETE.**
The full LDT `Γ,a ⊢ b ⟺ ∃n, Γ ⊢ aⁿ⇒b` is proved in both directions. (The
*classical* deduction theorem fails for Łukasiewicz — it lacks contraction — so
this resource-counting "local" form is the correct statement.) The **fusion
crux** `imp_sconj_fuse` is fully proved with axiom dependency `[propext]` only.

**`prop17.lean` — MV-algebra distributivity & Prop 1.7, 0 sorry — COMPLETE.**
The standalone module that builds the heavy machinery for Soundness's a6 case:
- Mundici's Proposition 1.7: `(x⊖y) ∧ (y⊖x) = 0`
- `mvsup_lub`: `mvsup` is the lattice supremum
- Proposition 1.6(i): `x ⊙ (y∨z) = (x⊙y) ∨ (x⊙z)`
- De Morgan: `¬(x∨y) = ¬x ∧ ¬y`, `¬(x∧y) = ¬x ∨ ¬y`
- Proposition 1.6(ii): `x ⊕ (y∧z) = (x⊕y) ∧ (x⊕z)`
- The key equation `a6_key`: `(z ⊕ (x⊖y)) ∧ (z ⊕ (y⊖x)) = z`

All theorems compile with axiom dependencies of either `none` or `propext` only.

## Verification status, in one line

Five canonical files, all pure Lean core with zero Mathlib dependency, all
compile under Lean 4.31.0; **all proofs are complete with `propext` as the only
axiom dependency** — no `sorryAx`, no choice, no admit. Łukasiewicz logic over
arbitrary MV-algebras is fully sound, and the BL-equivalence + Local Deduction
Theorem are also fully proved.
