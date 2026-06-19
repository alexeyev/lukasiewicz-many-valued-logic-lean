# Łukasiewicz Logic & MV-algebras in Lean 4 — Summary

A from-scratch formalization of MV-algebras and the BL/Łukasiewicz proof systems,
with **no Mathlib dependency**. The development is pure Lean 4 core (no external
packages) and has been compiled and verified with Lean 4.31.0.

The MV-algebra theory is organized as a **dependency-ordered module chain** under
`Lukasiewicz/` (`Base → … → IdealLattice`); each module imports its predecessor, so
every result is proved exactly once. The four propositional-logic modules are
self-contained (each redeclares the core class) and are checked individually.

## Modules — all pure core, all compile clean

**The MV-algebra chain** (built by `lake build`):

| Module | imports | `sorry` tactic | Axiom deps of main result |
|---|---|---|---|
| `Base.lean` | (chain root) | 0 | none / `propext` |
| `Lattice.lean` | Base | **0** | **`propext`** |
| `Distance.lean` | Lattice | **0** | **none** (axiom-free!) |
| `BooleanCenter.lean` | Distance | **0** | **`propext`** |
| `MVLemmas.lean` | BooleanCenter | **0** | **`propext`** (Lemma 1.3 axiom-free; Lemma 1.8 needs `propext`) |
| `BooleanAlgebra.lean` | MVLemmas | **0** | **`propext`** (the structural theorem is axiom-free) |
| `Ideals.lean` | BooleanAlgebra | **0** | **none** (entire module axiom-free!) |
| `Subalgebras.lean` | Ideals | **0** | mixed (axiom-free + `[propext]` + `[Quot.sound]` from `omega`) |
| `IdealOperations.lean` | Subalgebras | **0** | **none** (entire module axiom-free!) |
| `Instances.lean` | IdealOperations | **0** | mostly axiom-free, one inherits `[propext, Quot.sound]` |
| `Quotient.lean` | Instances | **0** | `[Quot.sound]` / `[propext, Quot.sound]`; **no `Classical.choice`** |
| `Correspondence.lean` | Quotient | **0** | `[Quot.sound]` / `[propext, Quot.sound]`; **no `Classical.choice`** |
| `SecondIso.lean` | Correspondence | **0** | `[Quot.sound]` / `[propext, Quot.sound]`; **no `Classical.choice`** |
| `CRT.lean` | SecondIso | **0** | `[Quot.sound]` / `[propext, Quot.sound]`; **no `Classical.choice`** |
| `IsoBasics.lean` | CRT | **0** | axiom-free / `[Quot.sound]`; **no `Classical.choice`** |
| `IdealLattice.lean` | IsoBasics | **0** | axiom-free / `[propext]`; **no `Classical.choice`** |

**The propositional-logic modules** (self-contained; checked with `lean Lukasiewicz/<Name>.lean`):

| Module | imports | `sorry` tactic | Axiom deps of main result |
|---|---|---|---|
| `Residuation.lean` | 0 | 0 | none / `propext` |
| `Soundness.lean` | 0 | **0** | **`propext`** |
| `Equivalence.lean` | 0 | 0 | `propext` |
| `DeductionBL.lean` | 0 | 0 | `propext` |

The algebra chain is built with `lake build`; the standalone modules compile with
`lean Lukasiewicz/<Name>.lean`. No Mathlib, no external packages. **No module
depends on `sorryAx` or `Classical.choice`.**

## What is proven

**`Residuation.lean` — the algebraic heart, 0 sorry.**
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

**`Lattice.lean` — Mundici's Fundamental Structure Theorem, 0 sorry — COMPLETE.**
The most-cited foundational result in MV-algebra theory: every MV-algebra is a
bounded lattice under its natural order, with the monoid operations distributing
over the lattice operations. Bundles Mundici's Propositions 1.5 (lattice
structure) and 1.6 (distributivities `x ⊙ (y∨z) = (x⊙y) ∨ (x⊙z)` and
`x ⊕ (y∧z) = (x⊕y) ∧ (x⊕z)`) into a single statement with all eight conjuncts
proved constructively from Chang's axioms — no subdirect representation, no
choice. Axiom dependency: `propext`.

**`Distance.lean` — Mundici Proposition 1.10: the MV-algebra metric, 0 sorry — COMPLETE.**
The distance function `d(x,y) := (x ⊙ ¬y) ⊕ (y ⊙ ¬x)` makes every MV-algebra into
a metric structure. On the standard `[0,1]` algebra it computes `|x − y|`; on a
Boolean algebra it is symmetric difference. All five metric properties are
proved: `d(x,y) = 0 ↔ x = y` (identity of indiscernibles), `d(x,y) = d(y,x)`
(symmetry), `d(x,z) ≤ d(x,y) ⊕ d(y,z)` (triangle inequality), `d(x,y) = d(¬x,¬y)`
(negation-invariance), and `d(x⊕s, y⊕t) ≤ d(x,y) ⊕ d(s,t)` (non-expansiveness of
`⊕`). All seven results are fully **axiom-free** — `#print axioms` reports "does
not depend on any axioms" for each. This is the metric foundation of MV-algebra
theory: it is the machinery via which congruences are characterized in Mundici
Proposition 1.11 (`x ~ y ⟺ d(x,y) ∈ I` for some ideal `I`), and the basis for
the uniform-continuity arguments used in the analytic theory of Łukasiewicz
logic.

**`BooleanCenter.lean` — Mundici Lemma 1.2 + Boolean Center Theorem, 0 sorry — COMPLETE.**
Two foundational characterizations of MV-algebra structure:

1. **Mundici Lemma 1.2** — the four equivalent characterizations of the natural
   order: `x ≤ y ⟺ ¬x⊕y = 1 ⟺ x⊙¬y = 0 ⟺ y = x⊕(y⊖x) ⟺ ∃z, x⊕z = y`. The
   forward implications are axiom-free; the bundled `iff` uses `propext`.

2. **The Boolean Center Theorem** — the set `B(A) := {a : a⊙a = a}` (the
   `⊙`-idempotents) coincides with the `⊕`-idempotents, with `{a : a∨¬a = 1}`
   (excluded middle), and with `{a : a∧¬a = 0}` (non-contradiction). The four
   characterizations are proved equivalent and `B(A)` is shown closed under `⊙`,
   `⊕`, and `¬`, making it a Boolean subalgebra of `A`. Cignoli's "Boolean
   Skeletons of MV-algebras" (2011) and Mundici's "Advanced Łukasiewicz
   Calculus" §3 study `B(A)` as a primary object — it is exactly the "classical
   part" of a many-valued algebra. On the standard `[0,1]` algebra,
   `B([0,1]) = {0, 1}` is the original Boolean algebra of classical logic.

**`MVLemmas.lean` — Mundici Lemmas 1.3 and 1.8, 0 sorry — COMPLETE.**
Two short but foundational lemmas:

1. **Lemma 1.3** — *Uniqueness of negation*: `¬a` is the unique element `x`
   satisfying both `a ⊕ x = 1` and `a ⊙ x = 0`. The proof is exactly the
   antisymmetric pinch — these two equations express `¬a ≤ x` and `x ≤ ¬a`
   respectively. This says: negation in an MV-algebra is algebraically
   determined; there's no choice of which "complement" to pick. **Axiom-free.**

2. **Lemma 1.8** — *Propagation of disjointness*: if `x ∧ y = 0` then
   `(nfold n x) ∧ y = 0` for every `n`, where `nfold n x` is the `n`-fold sum
   `x ⊕ x ⊕ ⋯ ⊕ x`. This is the engine that powers Mundici's Proposition 1.19
   (existence of prime ideals), which in turn drives Chang's Subdirect
   Representation Theorem and the completeness of Łukasiewicz logic with
   respect to `[0,1]`. We prove the structural single-step version, the
   helper `mvinf_oplus_eq_of_left_mvinf_zero` (if `a ∧ y = 0` then
   `(a⊕b) ∧ y = b ∧ y`), and the full inductive version. The bundle uses only
   `propext`; the structural lemma itself is axiom-free.

**`BooleanAlgebra.lean` — Boolean center is a Boolean algebra + Lemma 1.4, 0 sorry — COMPLETE.**
Closes the Boolean-center story with the structural theorem that, restricted
to `B(A)`, the MV-operations match the lattice operations: `a ⊙ b = a ∧ b`
and `a ⊕ b = a ∨ b` whenever both `a, b ∈ B(A)`. Combined with the closure
results from `BooleanCenter.lean`, this gives a complete Boolean-algebra
structure on `B(A)`. The proof of `⊙ = ∧` is the elegant chain
`a ∧ b = mvinf b a = b ⊙ (¬b ⊕ a) = (b ⊙ b) ⊙ (¬b ⊕ a) = b ⊙ (b ∧ a) ≤ b ⊙ a`
using only `b`'s idempotence; `⊕ = ∨` then follows via De Morgan. The headline
`odot_eq_mvinf_of_isBoolean` is **axiom-free**.

Also formalizes **Mundici Lemma 1.4** — the monotonicity bundle: `x ≤ y ⟺ ¬y ≤ ¬x`
(contraposition, axiom-free), monotonicity of `⊕` and `⊙` (axiom-free), and the
residuation transfer law `x ⊙ y ≤ z ⟺ x ≤ ¬y ⊕ z` (axiom-free).

**`Ideals.lean` — MV-homomorphisms, ideals, congruences + Prop 1.11 full bijection + category structure, 0 sorry — COMPLETE.**
The category-theoretic foundation of MV-algebra theory:

1. **MVHom**: a function preserving 0, ⊕, ¬. Mundici Lemma 1.9 is formalized in
   full: every MV-homomorphism *automatically* preserves 1, ⊙, ≤, ∨, ∧, and the
   distance function d.

2. **Ideal**: a downward-closed submonoid containing 0. The zero ideal `{0}` and the
   improper ideal `A` are constructed. **The kernel `Ker(h) := {x : h(x) = 0}` is
   shown to be an ideal** (Lemma 1.9 (v)).

3. **MVCongruence**: equivalences compatible with ⊕ and ¬. ⊙-, ∧-, and ∨-compatibility
   are derived (since these operations are definable from ⊕, ¬).

4. **The Ideal–Congruence Bijection (Mundici Proposition 1.11, both directions)** —
   the central theorem. Forward: every ideal `I` induces a congruence via
   `x ≡_I y ⟺ d(x,y) ∈ I`. Reverse: every congruence `R` has a kernel ideal
   `R.kernel := {x : x R 0}`, and the congruence induced by this kernel equals `R`.
   The reverse direction uses the key identity `x ⊕ (y ⊖ x) = mvsup x y` — when
   `(y ⊖ x) R 0`, we get `x R (x ∨ y)` and symmetrically `y R (x ∨ y)`, so `x R y`
   by transitivity. The bundled theorem `ideal_congruence_bijection` is **axiom-free**.

5. **MV-algebras form a category**: the identity function `MVHom.id` is an
   MV-homomorphism, composition `MVHom.comp` is an MV-homomorphism, and the
   category laws (`id_comp`, `comp_id`, `comp_assoc`) all hold by `rfl`. **Axiom-free.**

The **entire file is fully axiom-free** — `#print axioms` reports "does not depend
on any axioms" for all 20+ theorems, including the full bijection.

**`Subalgebras.lean` — Sub-MV-algebras, principal ideals, Boolean center as subalgebra, 0 sorry — COMPLETE.**
The structural sub-algebra theory:

1. **SubMVAlgebra**: subsets closed under `0`, `⊕`, `¬`. Closure under `1`, `⊙`, `∧`,
   `∨` follows *automatically* — each derived `_mem` lemma is axiom-free.

2. **Image of an MV-homomorphism is a sub-MV-algebra** (`MVHom.image`). The image
   `{y : ∃ x, h(x) = y}` inherits all closure properties from `h`'s preservation laws.
   Axiom-free.

3. **The Boolean center `B(A)` is a sub-MV-algebra of `A`** (`booleanCenter`).
   Pulls together the closure results from `BooleanCenter.lean` into the
   `SubMVAlgebra` structure: every Boolean element under `⊕`, `¬`, etc., is still Boolean.

4. **Principal ideals**: `⟨a⟩ := {x : ∃n, x ≤ n·a}` where `n·a := nfold n a`. Proved:
   - It IS an ideal (uses the helper `nfold_add : nfold (n+m) x = nfold n x ⊕ nfold m x`).
   - `a ∈ ⟨a⟩` (take `n=1`).
   - It's the **smallest** ideal containing `a`: any ideal `J` with `a ∈ J` contains all of `⟨a⟩`.

5. **Proper ideals**: `Ideal.IsProper I := ¬ I.carrier 1`. Proved:
   - `1 ∈ I ⟹ ∀x, x ∈ I` (the canonical "improper iff contains 1" characterization).
   - The zero ideal is proper iff the MV-algebra is nontrivial.
   - The top ideal is never proper.

**`IdealOperations.lean` — Lattice operations on ideals, preimages, injectivity, 0 sorry — COMPLETE.**
The fully-developed structural theory of ideals and homomorphisms:

1. **Lattice of ideals**: `Ideal.inter` (intersection, the GLB) and `Ideal.sum`
   (the smallest ideal containing both — note the `≤`-closure required to make it
   downward-closed: `I + J := {z : ∃ x∈I, y∈J, z ≤ x ⊕ y}`). Bundled with
   `Ideal.le_inter` (GLB property of intersection) and `Ideal.sum_le` (LUB property
   of sum). All axiom-free.

2. **Preimage of an ideal**: `MVHom.preimage h J := {x : h x ∈ J}`. The kernel
   `MVHom.ker h` is exactly `h.preimage (zeroIdeal B)` — recorded as
   `ker_eq_preimage_zero`. Axiom-free.

3. **Mundici Lemma 1.9(vi)**: an MV-homomorphism is injective iff its kernel is
   `{0}`. The proof is the beautiful distance argument: `h x = h y ⟹ h(d x y) = 0 ⟹ 
   d(x,y) ∈ Ker h = {0} ⟹ d(x,y) = 0 ⟹ x = y`. Axiom-free.

4. **Kernel of composition**: `Ker h ⊆ Ker (g ∘ h)`. Axiom-free.

The entire file is **fully axiom-free** — every single theorem reports "does not
depend on any axioms".

**`Instances.lean` — Concrete MV-algebra instances + nfold/homomorphism properties, 0 sorry — COMPLETE.**
The first concrete MV-algebra instances and arithmetic properties:

1. **The trivial MV-algebra on `PUnit`**: a one-element type with all operations
   constant. Acts as the terminal object in the category of MV-algebras.
   `0 = 1` holds trivially. Axiom-free.

2. **The product MV-algebra `A × B`**: componentwise operations make any product
   of MV-algebras an MV-algebra. All 6 Chang axioms hold component-by-component.
   The **projection homomorphisms** `ProdMV.fst : A × B → A` and
   `ProdMV.snd : A × B → B` are MV-homomorphisms. Their kernels are the natural
   "axis-aligned" ideals. Axiom-free.

3. **Properties of `nfold`** (the n-fold ⊕ already used in principal ideals and
   Mundici Lemma 1.8):
   - `nfold_one : nfold 1 a = a`
   - `nfold_of_zero : nfold n 0 = 0`
   - `nfold_of_one : nfold n 1 = 1` for `n ≥ 1`
   - `nfold_mono_arg : a ≤ b → nfold n a ≤ nfold n b`
   - `nfold_le_one : nfold n a ≤ 1`
   All axiom-free.

4. **Homomorphisms preserve `nfold`**: `MVHom.map_nfold : h(n·a) = n·(h a)`. The
   workhorse for image-of-principal-ideal computations.

5. **Image of a principal ideal**: `image_principalIdeal_le : h "(⟨a⟩) ⊆ ⟨h a⟩`.
   The proof uses `map_nfold` plus `map_le`.

The file gives the project its first concrete MV-algebra instances besides the
abstract typeclass: `PUnit` (trivial) and `A × B` (product). Together with the
homomorphism preservation properties, they make the category-theoretic theory
concrete.

**`Base.lean` — MV-algebra core + distributivity & Prop 1.7, 0 sorry — COMPLETE.**
The root of the algebra chain. It declares the `MVAlgebra` class (Chang's six
axioms), builds the `⊙`-monoid, both De Morgan laws, the natural order with
antisymmetry, and `sup`/`inf`; then the heavy machinery that powers Soundness's
a6 case:
- Mundici's Proposition 1.7: `(x⊖y) ∧ (y⊖x) = 0`
- `mvsup_lub`: `mvsup` is the lattice supremum
- Proposition 1.6(i): `x ⊙ (y∨z) = (x⊙y) ∨ (x⊙z)`
- De Morgan: `¬(x∨y) = ¬x ∧ ¬y`, `¬(x∧y) = ¬x ∨ ¬y`
- Proposition 1.6(ii): `x ⊕ (y∧z) = (x⊕y) ∧ (x⊕z)`
- The key equation `a6_key`: `(z ⊕ (x⊖y)) ∧ (z ⊕ (y⊖x)) = z`

Every module in the chain imports `Base` (directly or transitively). All theorems
compile with axiom dependencies of either `none` or `propext` only.

**`Quotient.lean` — quotient MV-algebras + First Isomorphism Theorem, 0 sorry — COMPLETE.**
The capstone of the homomorphism/ideal theory:

1. **The quotient MV-algebra `A/I`.** For an ideal `I`, the relation
   `x ≈ y ⟺ d(x,y) ∈ I` (the congruence from `Ideals.lean`) is packaged as a
   `Setoid`, and `QuotientByIdeal I := Quotient I.setoid` is given a full
   `MVAlgebra` instance. The operations are lifted via `Quotient.lift₂`/`lift`;
   well-definedness is exactly the congruence's `⊕`/`¬` compatibility, and all
   six Chang axioms transfer through `Quotient.inductionOn` from `A`.

2. **The canonical surjection `A → A/I` with `Ker = I`.** `Ideal.mkHom I` sends
   `x ↦ ⟦x⟧`; every preservation law holds by `rfl`. `ker_mkHom` proves its
   kernel is exactly `I` — completing "every ideal is a kernel" (the converse to
   "every kernel is an ideal" from `Ideals.lean`), using the identity
   `d(x,0) = x`. `mkHom_surjective` records surjectivity.

3. **A sub-MV-algebra as an MV-algebra.** `SubMVAlgebra.Subtype` carves out the
   subtype `{x // S.carrier x}`, and `instSubMV` makes it an MV-algebra with the
   ambient operations and `Subtype.ext`-transferred axioms. This is what lets
   `Im(h)` be spoken of as a type. **Axiom-free.**

4. **The First Isomorphism Theorem** `A / Ker(h) ≅ Im(h)`. The canonical map
   `firstIso h : A/Ker(h) → Im(h)`, `⟦x⟧ ↦ h x`, is well-defined because
   `⟦x⟧ = ⟦y⟧ ⟹ d(x,y) ∈ Ker(h) ⟹ d(h x, h y) = 0 ⟹ h x = h y`. It is proved
   **injective** (`firstIso_injective`) and **surjective** (`firstIso_surjective`),
   hence a bijective homomorphism — i.e. an isomorphism. Bundled as
   `firstIsomorphismTheorem`.

The construction is entirely **choice-free**: its only axiom is `Quot.sound`
(plus `propext` where `↔` is rewritten). An isomorphism is recorded as a
bijective homomorphism rather than by exhibiting an inverse, because inverting a
map whose image-membership witness is a `Prop` would require `Classical.choice`.

**`Correspondence.lean` — Correspondence Theorem + Third Isomorphism Theorem, 0 sorry — COMPLETE.**
Completes the standard isomorphism-theorem suite:

1. **The Correspondence (Lattice) Theorem.** For an ideal `I`, the ideals of the
   quotient `A/I` are in bijection with the ideals of `A` that contain `I`. The
   two maps are pushforward `J ↦ J/I := {⟦x⟧ : x ∈ J}` (`corrImage`) and preimage
   `K ↦ π⁻¹(K)` (`corrPreimage`). Both round-trips are proved
   (`corr_left_inv`, `corr_right_inv`), bundled as `correspondenceTheorem`. The
   forward round-trip leans on the key lemma `mem_of_dist_mem` — an ideal's
   membership is closed under its induced congruence.

2. **The Third Isomorphism Theorem.** For `I ⊆ J`, the canonical map
   `A/I → A/J`, `⟦x⟧_I ↦ ⟦x⟧_J` (`thirdIsoMap`), is well-defined (since `I ⊆ J`
   refines the congruences), **surjective** (`thirdIsoMap_surjective`), and its
   **kernel is exactly `J/I`** (`ker_thirdIsoMap`: `⟦x⟧_I ∈ Ker ⟺ x ∈ J`).
   Composed with the First Isomorphism Theorem this gives `(A/I)/(J/I) ≅ A/J`.
   Bundled as `thirdIsomorphismTheorem`.

Like the quotient module, everything here is **choice-free** — only `Quot.sound`
and `propext` appear. `mem_of_dist_mem` itself is fully axiom-free.

**`SecondIso.lean` — the Second Isomorphism Theorem, 0 sorry — COMPLETE.**
Completes the isomorphism-theorem suite (First, Second, Third, Correspondence):

For a sub-MV-algebra `S` and an ideal `I`, consider the **composite**
`φ : S ↪ A → A/I`, `s ↦ ⟦s⟧` (`subQuotientHom`). Its kernel is exactly
`S ∩ I` (`ker_subQuotientHom`, where `subInterIdeal` is `S ∩ I` viewed as an
ideal of `S`), and its image is `(S+I)/I = {⟦s⟧ : s ∈ S}`
(`mem_image_subQuotientHom`). Feeding `φ` into the First Isomorphism Theorem
yields the **Second Isomorphism Theorem** `S/(S∩I) ≅ (S+I)/I`, bundled as
`secondIsomorphismTheorem`.

This is the cleanest possible proof: the Second Iso Theorem is a one-line
corollary of the First applied to the inclusion-then-quotient composite. As with
the rest of the quotient theory it is **choice-free** (`Quot.sound`/`propext`
only); `subInterIdeal` is fully axiom-free.

**`CRT.lean` — the Chinese Remainder Theorem, 0 sorry — COMPLETE.**
A famous isomorphism theorem beyond the standard three. For **comaximal** ideals
`I, J` (i.e. `I + J = A`, witnessed by `i ∈ I`, `j ∈ J` with `i ⊕ j = 1`):

`A / (I ∩ J) ≅ A/I × A/J`.

The induced diagonal `crtMap`, `⟦a⟧ ↦ (⟦a⟧_I, ⟦a⟧_J)`, is **always injective**
(`crtMap_injective`: its construction collapses exactly `I ∩ J`) and is
**surjective exactly under comaximality** (`crtMap_surjective`). The surjectivity
witness is the MV analogue of the classical CRT solution: for target
`(⟦x⟧_I, ⟦y⟧_J)`, the element `a = (y ⊙ i) ⊕ (x ⊙ j)` satisfies `a ≡ x (mod I)`
and `a ≡ y (mod J)`. The proof is pure congruence algebra — from `i ⊕ j = 1` we
get `i ≈_I 0`, `j ≈_I 1`, `j ≈_J 0`, `i ≈_J 1`, and the congruence's `⊙`/`⊕`
compatibility collapses `a` appropriately. Bundled as `chineseRemainderTheorem`,
and (like the rest) **choice-free**.

**`IsoBasics.lean` — basic isomorphism facts, 0 sorry — COMPLETE.**
Short choice-free results rounding out the homomorphism/quotient theory: the
identity is injective and surjective (`id_injective`, `id_surjective`);
composition preserves both (`comp_injective`, `comp_surjective`), so bijective
homomorphisms compose; `A/{0} ≅ A` (`quotZero_iso`); `A/A ≅ 1`, the trivial
algebra (`quotTop_iso`); the product projections are surjective (`fst_surjective`,
`snd_surjective`); and the product universal property — a pair of homs induces a
hom into the product (`MVHom.pair`, with the projection laws). Most of these are
fully axiom-free.

**`IdealLattice.lean` — the lattice of ideals, 0 sorry — COMPLETE.**
The ideals of an MV-algebra form a bounded lattice; this records it as
carrier-level lemmas (`Ideal.Sub` for `⊆`, `Ideal.Equiv` for `=`). `Sub` is a
partial order (reflexive, transitive, antisymmetric); intersection is the GLB and
sum the LUB (`inter_sub_left/right`, `sub_inter`, `left/right_sub_sum`, `sum_sub`);
the zero ideal is bottom and the improper ideal is top; idempotency, commutativity,
and absorption hold; and the order characterizations `I⊆J ⟺ I∩J=I ⟺ I+J=J`. The
comaximality theory: it is symmetric (`comaximal_symm`) and equivalent to
`1 ∈ I+J`, equivalently `I+J = A` (`comaximal_iff_one_mem_sum`,
`comaximal_iff_top_sub_sum`). Sub-MV-algebras are likewise closed under
intersection. Most results are fully axiom-free; the rest use only `propext`.

## Verification status, in one line

Sixteen chained algebra modules (`Base → … → IdealLattice`, built with `lake build`)
plus four self-contained logic modules (`Residuation`, `Soundness`,
`Equivalence`, `DeductionBL`) — all pure Lean core with zero Mathlib dependency,
all compile cleanly under Lean 4.31.0 with **no `sorry`, no `sorryAx`, no
`Classical.choice`**. The algebra chain proves every result exactly once (no code
duplication); axiom footprints are `none`, `propext`, or `[propext, Quot.sound]`
(`Quot.sound` enters through the quotient construction and through `omega` on
`Nat`). Łukasiewicz logic
over arbitrary MV-algebras is fully sound, and the BL-equivalence + Local
Deduction Theorem are also fully proved.
