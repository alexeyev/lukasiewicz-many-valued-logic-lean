# lean-lukasiewicz

[![verify](https://github.com/alexeyev/lukasiewicz-many-valued-logic-lean/actions/workflows/verify.yml/badge.svg)](https://github.com/alexeyev/lukasiewicz-many-valued-logic-lean/actions/workflows/verify.yml)

A from-scratch formalization of **MV-algebras** and the proof systems for
**Łukasiewicz logic** and **Hájek's Basic Logic (BL)**, in **pure Lean 4 core
with no Mathlib dependency**.

The MV-algebra theory is a **dependency-ordered module chain** built with Lake
(`Base → … → IdealLattice`); each module imports its predecessor, so every result
is proved exactly once — no code duplication. Four self-contained
propositional-logic modules round out the development and are checked
individually with a bare `lean` invocation. The whole project pulls in **no**
external packages.

> **Headline result:** algebraic soundness of all **eleven** BL axioms over
> arbitrary MV-algebras is fully proved, including the prelinearity axiom (a6),
> which is derived *equationally* from Chang's axioms via Mundici's
> Propositions 1.6 and 1.7 — no subdirect-representation theorem required.
> The soundness theorem depends on only the standard `propext` axiom: no
> `sorryAx`, no `Classical.choice`.

---

## What's proven

The MV-algebra theory is a **dependency-ordered module chain** under
[`Lukasiewicz/`](Lukasiewicz/): each module `import`s its predecessor, so every
result is proved exactly once (no code duplication). The four propositional-logic
modules are self-contained and checked individually. Line counts below are the
*unique* content of each module.

**The MV-algebra chain** (`Base → … → IdealLattice`, built by `lake build`):

| Module | Lines | What it adds | `sorry` | Axiom deps of main result |
|---|---:|---|:---:|---|
| `Base.lean` | 473 | MV-algebra class (Chang's axioms); `⊙`-monoid; both De Morgan laws; natural order with antisymmetry; sup/inf; **Mundici Prop 1.7** `(x⊖y) ∧ (y⊖x) = 0`; sup is the lattice LUB; **Prop 1.6(i)/(ii)** | 0 | none / `propext` |
| `Lattice.lean` | 110 | **Mundici's Fundamental Structure Theorem** (Props 1.5 + 1.6): every MV-algebra is a bounded lattice with `⊙` distributing over `∨` and `⊕` over `∧` | 0 | `propext` |
| `Distance.lean` | 340 | **Mundici Proposition 1.10**: the distance `d(x,y) := (x⊖y) ⊕ (y⊖x)` is a metric (zero iff equal, symmetric, triangle inequality, `⊕`-non-expansiveness) | 0 | **none** |
| `BooleanCenter.lean` | 277 | **Mundici Lemma 1.2** (4 equivalent characterizations of `≤`) and the **Boolean Center Theorem**: the ⊙-idempotents = ⊕-idempotents = {a : a∨¬a = 1} = {a : a∧¬a = 0} | 0 | `propext` |
| `MVLemmas.lean` | 199 | **Mundici Lemma 1.3** (uniqueness of negation) and **Lemma 1.8** (`x∧y = 0 ⟹ (n·x)∧y = 0`, propagation of disjointness) | 0 | `propext` |
| `BooleanAlgebra.lean` | 165 | **The Boolean Center is a Boolean algebra** (`a⊙b = a∧b`, `a⊕b = a∨b` on `B(A)`); plus **Mundici Lemma 1.4** (monotonicity package) | 0 | `propext` |
| `Ideals.lean` | 436 | **MV-homomorphisms and ideals** (Lemma 1.9); **Mundici Prop 1.11 (full bijection)**: ideals ↔ congruences via `x ≡_I y ⟺ d(x,y) ∈ I`; **MV-algebras form a category** | 0 | **none** |
| `Subalgebras.lean` | 221 | **Sub-MV-algebras**; **image of a homomorphism is a sub-MV-algebra**; **Boolean center is a sub-MV-algebra**; **principal ideals** `⟨a⟩ = {x : ∃n, x ≤ n·a}` and minimality; **proper ideals** | 0 | mostly axiom-free, some `[propext, Quot.sound]` (from `omega`) |
| `IdealOperations.lean` | 189 | **Lattice of ideals**: intersection `I ∩ J` (GLB) and sum `I + J` (smallest ideal containing both); **preimage of an ideal**; **Mundici Lemma 1.9(vi)**: `h` injective ⟺ `Ker(h) = {0}`; **kernel of composition** | 0 | **none** |
| `Instances.lean` | 165 | **Concrete instances**: the trivial MV-algebra `PUnit`, the **product MV-algebra** `A × B` with **projection homomorphisms**; **`nfold` arithmetic**; **`h` preserves `nfold`**; **image of a principal ideal** | 0 | mostly axiom-free, one `[propext, Quot.sound]` |
| `Quotient.lean` | 220 | **The quotient MV-algebra** `A/I` (lifted operations, all six axioms); the canonical surjection `A → A/I` with **`Ker = I`**; a **sub-MV-algebra as an MV-algebra** (`instSubMV`); and the **First Isomorphism Theorem** `A/Ker(h) ≅ Im(h)` (the canonical map is a bijective homomorphism) | 0 | `[Quot.sound]` (+`propext`); **no choice** |
| `Correspondence.lean` | 198 | **The Correspondence (Lattice) Theorem**: ideals of `A/I` ↔ ideals of `A` containing `I`, via pushforward `J ↦ J/I` and preimage `K ↦ π⁻¹(K)`; and the **Third Isomorphism Theorem**: for `I ⊆ J`, the map `A/I → A/J` is surjective with kernel `J/I`, so `(A/I)/(J/I) ≅ A/J` | 0 | `[Quot.sound]` (+`propext`); **no choice** |
| `SecondIso.lean` | 109 | **The Second Isomorphism Theorem**: for a sub-MV-algebra `S` and ideal `I`, the composite `S ↪ A → A/I` has kernel `S ∩ I` and image `(S+I)/I`, giving `S/(S∩I) ≅ (S+I)/I` (a corollary of the First Iso Theorem) | 0 | `[Quot.sound]` (+`propext`); **no choice** |
| `CRT.lean` | 161 | **The Chinese Remainder Theorem**: for comaximal ideals (`I + J = A`), the diagonal `⟦a⟧ ↦ (⟦a⟧_I, ⟦a⟧_J)` is a bijective homomorphism `A/(I∩J) ≅ A/I × A/J` (injective always; surjective from comaximality, via the witness `(y⊙i)⊕(x⊙j)`) | 0 | `[Quot.sound]` (+`propext`); **no choice** |
| `IsoBasics.lean` | 152 | **Basic isomorphism facts**: identity/composition preserve injectivity & surjectivity; `A/{0} ≅ A`; `A/A ≅ 1` (trivial); product projections are surjective; the product universal property (`pair`) | 0 | mostly axiom-free; `[Quot.sound]` for the quotients |
| `IdealLattice.lean` | 184 | **The lattice of ideals**: `⊆` is a partial order; `∩`/`+` are meet/join (GLB/LUB); bottom `{0}` & top `A`; idempotency, commutativity, absorption; order characterizations `I⊆J ⟺ I∩J=I ⟺ I+J=J`; comaximality is symmetric and `⟺ 1 ∈ I+J`; sub-MV-algebras are closed under `∩` | 0 | mostly axiom-free; `[propext]` for `↔` lemmas |

**The propositional-logic modules** (self-contained; each checked with `lean Lukasiewicz/<Name>.lean`):

| Module | Lines | What it establishes | `sorry` | Axiom deps of main result |
|---|---:|---|:---:|---|
| `Residuation.lean` | 301 | MV-algebras with the **residuation** law `x⊙z ≤ y ↔ z ≤ x⇨y`; `⊙`-monoid; De Morgan; lattice fragment (an independent core using `sup`/`inf` naming) | 0 | none / `propext` |
| `Soundness.lean` | 741 | **Algebraic soundness of BL** — all 11 axioms evaluate to `⊤` in every MV-algebra under every valuation | 0 | `propext` |
| `Equivalence.lean` | 143 | BL + double-negation ⊢ Łukasiewicz: all four Łukasiewicz axioms **L1–L4** derived | 0 | none |
| `DeductionBL.lean` | 286 | **Local Deduction Theorem** `Γ,a ⊢ b ⟺ ∃n, Γ ⊢ aⁿ⇒b`, both directions | 0 | `propext` |

The "Axiom deps" column is the output of Lean's `#print axioms`, which reports the
**full transitive closure** of axiom dependencies. The absence of `sorryAx` is what
distinguishes a complete proof from one with an unfinished `sorry`.

### A note on `propext` and `Quot.sound`

`propext` (propositional extensionality, `(a ↔ b) → a = b`) and `Quot.sound`
(equal quotient classes for related elements) are two of Lean's three standard
foundational axioms; both underlie essentially all of Mathlib and are known to
be consistent with Lean's type theory. Depending on them is normal and safe.
In this project `propext` enters only through `rw` on `↔`-statements, and
`Quot.sound` enters only through the quotient construction in `Quotient.lean`
(and transitively via the `omega` tactic on `Nat`). Several results
(e.g. `mundici_prop17`, the distance metric, the De Morgan laws) depend on
**no axioms at all**.

The **third** standard Lean axiom, `Classical.choice`, is deliberately **never
used** — every result here, including the quotient MV-algebra and the First
Isomorphism Theorem, is choice-free. (This is why the First Isomorphism Theorem
is stated as "the canonical map is a bijective homomorphism" rather than by
exhibiting an explicit inverse: inverting a map whose image membership is a
`Prop` would require choice.)

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

Requires **Lean 4** (developed and verified against **v4.31.0**) and **Lake**
(bundled with Lean). The pinned version is in `lean-toolchain`;
[`elan`](https://github.com/leanprover/elan) will pick it up automatically.

The MV-algebra chain is built with Lake (the modules import one another):

```bash
lake build
```

The four self-contained propositional-logic modules each redeclare the core
class for standalone checking, so they are checked individually:

```bash
lake env lean Lukasiewicz/Residuation.lean
lake env lean Lukasiewicz/Soundness.lean
lake env lean Lukasiewicz/Equivalence.lean
lake env lean Lukasiewicz/DeductionBL.lean
```

A module that compiles silently has no errors and no `sorry`. To inspect the axiom
footprint of any result, add a `#print axioms` line in a scratch module that
imports the library, e.g.:

```lean
import Lukasiewicz.Instances
#print axioms Luk.MVAlgebra.mundici_prop17
-- 'Luk.MVAlgebra.mundici_prop17' does not depend on any axioms
```

The project depends on **no** external packages — it is pure Lean 4 core, with
Mathlib deliberately not required.

### Continuous integration

Every push and pull request is checked by the [`verify`](.github/workflows/verify.yml)
GitHub Actions workflow, which on a fresh machine:

1. installs the pinned Lean toolchain via `elan`;
2. runs `lake build` over the entire MV-algebra chain;
3. type-checks the four standalone logic modules with `lean`;
4. audits the axiom dependencies of a representative theorem from every area and
   **fails if any depends on `sorryAx` or `Classical.choice`**; and
5. greps the sources to confirm there are no `sorry`s and no use of classical
   choice machinery.

A green badge therefore certifies not just that everything compiles, but that the
development is genuinely complete (no holes) and **choice-free** (only `propext`
and `Quot.sound` are ever used).

---

## Repository layout

```
Lukasiewicz.lean              -- library root (imports the algebra chain)
lakefile.toml                 -- Lake build config (no dependencies)
lean-toolchain                -- pinned Lean version (v4.31.0)
Lukasiewicz/
  Base.lean                   -- MV-algebra core + Prop 1.7        (chain root)
  Lattice.lean                -- Fundamental Structure Theorem
  Distance.lean               -- the metric d (Prop 1.10)
  BooleanCenter.lean          -- Lemma 1.2 + Boolean Center Theorem
  MVLemmas.lean               -- Lemma 1.3 + Lemma 1.8
  BooleanAlgebra.lean         -- B(A) is a Boolean algebra + Lemma 1.4
  Ideals.lean                 -- homomorphisms, ideals, Prop 1.11 bijection
  Subalgebras.lean            -- sub-algebras, principal/proper ideals
  IdealOperations.lean        -- ideal lattice, injectivity (Lemma 1.9(vi))
  Instances.lean              -- PUnit, product algebra, nfold
  Quotient.lean               -- quotient A/I + First Iso Theorem
  Correspondence.lean         -- Correspondence + Third Iso Theorem
  SecondIso.lean              -- Second Isomorphism Theorem
  CRT.lean                    -- Chinese Remainder Theorem
  IsoBasics.lean              -- id/comp, A/{0}≅A, A/A≅1, projections
  IdealLattice.lean           -- ideal lattice laws + comaximality      (chain tip)
  Residuation.lean            -- independent MV core (sup/inf naming) [standalone]
  Soundness.lean              -- BL soundness, all 11 axioms          [standalone]
  Equivalence.lean            -- BL+dn ⊢ Łukasiewicz L1–L4            [standalone]
  DeductionBL.lean            -- Local Deduction Theorem              [standalone]
FORMALIZATION.md              -- in-depth mathematical walk-through
SUMMARY.md                    -- prose walk-through of each module
LICENSE                       -- Beerware
CITATION.cff                  -- machine-readable citation metadata
```

The algebra chain (`Base → … → IdealLattice`) is strictly dependency-ordered, so
each theorem is proved exactly once. The four `[standalone]` logic modules are
independent developments that each redeclare the `MVAlgebra` class; they are
excluded from the library root to avoid class-redeclaration clashes but remain
individually checkable.

---

## Citing this work

If you use this formalization or build on its proofs, a citation is appreciated.
GitHub renders the `CITATION.cff` metadata directly ("Cite this repository" in the
sidebar). A BibTeX entry:

```bibtex
@software{lean_lukasiewicz,
  title        = {A Mathlib-free Lean 4 Formalization of MV-algebras and the
                  Soundness of {\L}ukasiewicz / Basic Logic},
  author       = {The lean-lukasiewicz contributors},
  year         = {2026},
  version      = {1.0.0},
  license      = {Beerware},
  url          = {https://github.com/USERNAME/lean-lukasiewicz}
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
