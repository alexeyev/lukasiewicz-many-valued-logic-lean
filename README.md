A from-scratch formalization of **MV-algebras** and the proof systems for
**Łukasiewicz logic** and **Hájek's Basic Logic (BL)**, in **pure Lean 4 core
with no Mathlib dependency**.

Every canonical file is a single self-contained Lean source with **zero imports**.
They compile with a bare `lean File.lean` invocation — no Lake project, no Mathlib,
no toolchain setup beyond the Lean compiler itself.

> **Headline result:** algebraic soundness of all **eleven** BL axioms over
> arbitrary MV-algebras is fully proved, including the prelinearity axiom (a6),
> which is derived *equationally* from Chang's axioms via Mundici's
> Propositions 1.6 and 1.7 — no subdirect-representation theorem required.
> The soundness theorem depends on only the standard `propext` axiom: no
> `sorryAx`, no `Classical.choice`.

---

## What's proven

| File | Lines | What it establishes | `sorry` | Axiom deps of main result |
|---|---:|---|:---:|---|
| `MVAlgebra_scratch.lean` | 301 | MV-algebras (Chang's axioms); natural order with antisymmetry; **residuation** `x⊙z ≤ y ↔ z ≤ x⇨y`; ⊙-monoid; both De Morgan laws; lattice fragment | 0 | none / `propext` |
| `prop17.lean` | 482 | Distributivity machinery: **Mundici Prop 1.7** `(x⊖y) ∧ (y⊖x) = 0`; sup is the lattice LUB; **Prop 1.6(i)/(ii)**; De Morgan for ∧/∨; the key equation `(z⊕¬A) ∧ (z⊕¬B) = z` | 0 | none / `propext` |
| `Soundness.lean` | 741 | **Algebraic soundness of BL** — all 11 axioms evaluate to `⊤` in every MV-algebra under every valuation | 0 | `propext` |
| `Equivalence.lean` | 143 | BL + double-negation ⊢ Łukasiewicz: all four Łukasiewicz axioms **L1–L4** derived | 0 | none |
| `DeductionBL.lean` | 283 | **Local Deduction Theorem** `Γ,a ⊢ b ⟺ ∃n, Γ ⊢ aⁿ⇒b`, both directions | 0 | `propext` |

The "Axiom deps" column is the output of Lean's `#print axioms`, which reports the
**full transitive closure** of axiom dependencies. The absence of `sorryAx` is what
distinguishes a complete proof from one with an unfinished `sorry`.

### A note on `propext`

`propext` (propositional extensionality, `(a ↔ b) → a = b`) is one of Lean's three
standard foundational axioms and underlies essentially all of Mathlib. It is known
to be consistent with Lean's type theory. Depending on it is normal and safe; in
this project it enters only through `rw` on `↔`-statements. Several lemmas
(e.g. `mundici_prop17`, the De Morgan laws) depend on **no axioms at all**.

---

## The mathematics, briefly

**MV-algebras** are the algebraic models of Łukasiewicz infinite-valued logic — the
many-valued / fuzzy logic whose truth values live in `[0,1]` with `x ⊕ y = min(1, x+y)`
and `¬x = 1 - x`. They are axiomatized here exactly as in Chang (1958): an abelian
monoid `(⊕, 0)` with an involution `¬` satisfying `x ⊕ ¬0 = ¬0` and the
characteristic identity `¬(¬x ⊕ y) ⊕ y = ¬(¬y ⊕ x) ⊕ x`.

**Basic Logic (BL)**, due to Hájek, is the logic of all continuous t-norms; adding the
double-negation axiom `¬¬a → a` recovers Łukasiewicz logic. The structurally hard
axioms are *divisibility* (a4) and *prelinearity* (a6). The latter,
`((a→b)→c) → (((b→a)→c) → c)`, is the crux of this development: it is **false** in a
single non-linearly-ordered MV-algebra unless one uses the specific structure of `→`.
The proof here routes through Mundici's Proposition 1.7,

```
(x ⊖ y) ∧ (y ⊖ x) = 0,
```

combined with distributivity of `⊕` over `∧` (Prop 1.6(ii)), to obtain the key
identity `(z ⊕ ¬A) ∧ (z ⊕ ¬B) = z` when `A = a→b`, `B = b→a` — entirely by
equational reasoning from Chang's axioms.

---

## Building & checking

Requires **Lean 4** (developed and verified against **v4.31.0**). The pinned version
is in `lean-toolchain`; [`elan`](https://github.com/leanprover/elan) will pick it up
automatically.

Because the files have no imports, the simplest check is to compile each one directly:

```bash
lean MVAlgebra_scratch.lean
lean prop17.lean
lean Soundness.lean
lean Equivalence.lean
lean DeductionBL.lean
```

A file that compiles silently has no errors and no `sorry`. To inspect the axiom
footprint of any result, append a `#print axioms` line, e.g.:

```lean
#print axioms Luk.MVAlgebra.sound
-- 'Luk.MVAlgebra.sound' depends on axioms: [propext]
```

There is no build step beyond invoking `lean`; a `lakefile.toml` is included only as
an optional convenience for editor/Lake integration and pulls in **no** dependencies.

---

## Repository layout

```
MVAlgebra_scratch.lean   -- MV-algebra core (namespace MV)
prop17.lean              -- distributivity + Prop 1.7 + key equation (namespace Luk)
Soundness.lean           -- BL soundness, all 11 axioms (namespace Luk)
Equivalence.lean         -- BL+dn ⊢ Łukasiewicz L1–L4 (namespace Luk)
DeductionBL.lean         -- Local Deduction Theorem (namespace LukasiewiczBL.Deduction)
SUMMARY.md               -- detailed prose walk-through of each file
LICENSE                  -- Beerware
CITATION.cff             -- machine-readable citation metadata
```

`prop17.lean` is a standalone development of the heavy lemmas; `Soundness.lean`
inlines what it needs, so the two are independently checkable.

---

## Citing this work

If you use this formalization or build on its proofs, a citation is appreciated.
GitHub renders the `CITATION.cff` metadata directly ("Cite this repository" in the
sidebar). A BibTeX entry:

```bibtex
@software{lean_lukasiewicz,
  title        = {A Mathlib-free Lean 4 Formalization of MV-algebras and the
                  Soundness of {\L}ukasiewicz / Basic Logic},
  author       = {Claude-Opus, Models Family and Alekseev, Anton},
  year         = {2026},
  version      = {1.0.0},
  license      = {Beerware},
  url          = {https://github.com/alexeyev/lukasiewicz-many-valued-logic-lean}
}
```

Please also consider citing the underlying mathematics:

- C. C. Chang, *Algebraic analysis of many valued logics*, Trans. Amer. Math. Soc.
  **88** (1958), 467–490.
- R. Cignoli, I. M. L. D'Ottaviano, D. Mundici, *Algebraic Foundations of
  Many-Valued Reasoning*, Trends in Logic vol. 7, Kluwer, 2000. (Source of
  Propositions 1.6 and 1.7 used in the a6 proof.)
- P. Hájek, *Metamathematics of Fuzzy Logic*, Trends in Logic vol. 4, Kluwer,
  1998. (Source of the BL axiomatization and the Local Deduction Theorem.)

---

## License

Released under the **Beerware License** (Revision 42) — see [`LICENSE`](LICENSE).
You may do whatever you like with this; if we ever meet and you found it useful, a
beer is welcome.

---

## A note on how this was prepared

This formalization was developed with the assistance of Anthropic's **Claude (Opus
family)** models, working interactively against the Lean 4 compiler. Every proof in
the repository was machine-checked by Lean itself — the kernel is the final arbiter
of correctness, independent of how the proof terms were produced. The numerical
sanity checks, the axiom-dependency audits, and the line-by-line compilation results
reported above were all run and verified directly against the Lean toolchain.
