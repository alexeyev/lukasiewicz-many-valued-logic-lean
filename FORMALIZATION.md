# How the formalization is structured

A self-contained tour of what this project does, written for someone who has
not seen many-valued logic before. We start from "why would anyone want a logic
where statements can be more than just true or false?" and build up to the main
theorem. All file references are clickable.

> **TL;DR.** We give a Lean 4 proof that *every theorem of Basic Logic
> evaluates to "fully true" under every many-valued interpretation*. The
> structurally hard step is the **prelinearity axiom** $\text{a}6$, which we
> close equationally via Mundici's Proposition 1.7 — no representation
> theorem, no choice axiom.

---

## 1. What is many-valued logic, and what is BL?

Classical logic has two truth values: **true** ($1$) and **false** ($0$). That
is enough for mathematics, but it is awkward for statements that are
*partially* true: "John is tall", "the patient is healthy", "this image is a
cat". These have a degree of truth, not a yes/no answer.

**Many-valued logic** replaces the two-element set $\{0, 1\}$ with a richer
space of truth values, typically the unit interval $[0,1]$.
**Łukasiewicz logic** is the oldest and most studied such logic; its standard
semantics on $[0,1]$ is

$$
\neg x = 1 - x, \qquad x \oplus y = \min(1, x+y).
$$

Implication is then $x \Rightarrow y = \min(1,\, 1 - x + y)$ — equal to $1$
exactly when $x \le y$. So "if $x$ then $y$" is fully true iff $y$ is at least
as true as $x$, and otherwise has a graded truth value measuring how much
truth would be lost in the implication.

**Hájek's Basic Logic (BL)** is the weakest logic of this whole family — it
captures the common laws true for *every* continuous t-norm based fuzzy
logic, including Łukasiewicz, Gödel, and Product logic as special cases. Its
axioms are listed in §4 below.

The choice of BL as a target is deliberate: it is general (everything proved
sound for BL is automatically sound for Łukasiewicz), but the structural axioms
$\text{a}4$ (*divisibility*) and $\text{a}6$ (*prelinearity*) are the
mathematically interesting cases. Most existing formalizations of Łukasiewicz
logic axiomatize it directly with L1–L4 instead, sidestepping these axioms; we
do not.

---

## 2. What is the project's goal, in one sentence?

We want to prove, *inside Lean*, the following:

> **Soundness theorem.** If a formula $\varphi$ is provable in BL — that is,
> derivable from the eleven BL axioms by modus ponens — then $\varphi$
> evaluates to $1$ under **every** valuation in **every** MV-algebra.

The clause "in every MV-algebra" is the strong part. It says the syntactic
proof system does not accidentally prove anything that fails in some
many-valued model. This is the standard *algebraic semantic completeness*
property; here we prove the soundness half (the easier but still substantial
direction).

---

## 3. What is an MV-algebra?

An **MV-algebra** is the algebraic structure that captures all the equations
that hold in $[0,1]$ for $\oplus$ and $\neg$. Concretely, it is a 4-tuple
$(A,\,\oplus,\,\neg,\,0)$ where $A$ is a set, $\oplus: A \times A \to A$ is a
binary operation, $\neg: A \to A$ is unary, and $0 \in A$ is a constant,
satisfying six equations:

| Name | Equation | Meaning |
|---|---|---|
| `oplus_assoc` | $(x \oplus y) \oplus z = x \oplus (y \oplus z)$ | $\oplus$ is associative |
| `oplus_comm` | $x \oplus y = y \oplus x$ | $\oplus$ is commutative |
| `oplus_zero` | $x \oplus 0 = x$ | $0$ is the unit |
| `neg_neg` | $\neg \neg x = x$ | $\neg$ is an involution |
| `oplus_negzero` | $x \oplus \neg 0 = \neg 0$ | $\neg 0$ ("top") is absorbing |
| `mv_axiom` | $\neg(\neg x \oplus y) \oplus y = \neg(\neg y \oplus x) \oplus x$ | the Łukasiewicz / "join-symmetry" axiom |

The first three say $(A, \oplus, 0)$ is an abelian monoid. `neg_neg` says
$\neg$ is its own inverse. `oplus_negzero` defines what "$1$" should look
like. The last one — the only non-monoid equation — is what makes everything
specifically about Łukasiewicz logic; it is sometimes called Chang's MV9.

This is the entire axiomatization. In Lean ([`Lukasiewicz/Soundness.lean`](Lukasiewicz/Soundness.lean)):

```lean
class MVAlgebra (A : Type _) where
  oplus         : A → A → A
  neg           : A → A
  zero          : A
  oplus_assoc   : ∀ x y z, oplus (oplus x y) z = oplus x (oplus y z)
  oplus_comm    : ∀ x y, oplus x y = oplus y x
  oplus_zero    : ∀ x, oplus x zero = x
  neg_neg       : ∀ x, neg (neg x) = x
  oplus_negzero : ∀ x, oplus x (neg zero) = neg zero
  mv_axiom      : ∀ x y, oplus (neg (oplus (neg x) y)) y
                       = oplus (neg (oplus (neg y) x)) x
```

A `class` in Lean is a *parameterized* structure: whenever the type checker
sees `[MVAlgebra A]`, it knows it can use these six axioms about that
particular `A`. The variables $x, y, z$ are *universally quantified over $A$*
— they are placeholders that stand for arbitrary elements.

### A concrete example: the two-element MV-algebra

Take $A = \{0, 1\}$, $\oplus = \mathrm{or}$, $\neg = \mathrm{not}$. All six
axioms are checked by truth table — this is *classical* propositional logic.
In Lean we can build this instance with a one-line `by decide`. So
MV-algebras strictly generalize Booleans.

### The richer example: the real interval

$A = [0,1]$, $\oplus(x,y) = \min(1, x+y)$, $\neg x = 1-x$, $0$ = the real
number $0$. This is the **standard MV-algebra**. Every theorem we prove for
abstract $A$ specializes to a fact about $[0,1]$.

### Derived operators

From the six primitives we define:

$$
\begin{aligned}
1 &:= \neg 0 \qquad &&\text{(top)} \\
x \Rightarrow y &:= \neg x \oplus y \qquad &&\text{(implication, "residuum")}\\
x \odot y &:= \neg(\neg x \oplus \neg y) \qquad &&\text{(strong conjunction)} \\
x \le y &:\Longleftrightarrow (x \Rightarrow y) = 1 \qquad &&\text{(natural order)}
\end{aligned}
$$

Each of these has the right meaning on $[0,1]$:

- $x \Rightarrow y = \min(1, 1 - x + y)$, which is $1$ exactly when $x \le y$.
- $x \odot y = \max(0, x + y - 1)$ — "Łukasiewicz t-norm".
- $x \le y$ as defined unfolds to the usual $\le$ on reals.

There are also two lattice operations (proved to behave like
$\min$ and $\max$ on $[0,1]$):

$$
x \vee y := (x \odot \neg y) \oplus y, \qquad
x \wedge y := x \odot (x \Rightarrow y).
$$

The single most useful identity proved in this layer is **residuation**:

$$x \odot z \le y \;\Longleftrightarrow\; z \le x \Rightarrow y.$$

This says $\odot$ and $\Rightarrow$ are *adjoint* — and that property is what
makes the algebra a "residuated lattice", which is the structure underlying
every substructural and fuzzy logic. In Lean:

```lean
theorem residuation (x y z : A) : le (odot x z) y ↔ le z (imp x y)
```

It lives in [`Lukasiewicz/Residuation.lean`](Lukasiewicz/Residuation.lean) (axiom-free)
and is re-proved in [`Lukasiewicz/Soundness.lean`](Lukasiewicz/Soundness.lean).

---

## 4. What is BL, formally?

BL has a syntax (formulas) and a proof system (which formulas are theorems).

### Syntax — what formulas look like

We use the most parsimonious possible language: just propositional variables,
the constant **false** ($\bot$), and the connective **implies** ($\Rightarrow$).
Everything else is *defined*:

$$
\sim a \;:=\; a \Rightarrow \bot, \qquad a \otimes b \;:=\; \sim(a \Rightarrow \sim b).
$$

So $\sim a$ ("not $a$") is sugar for "$a$ implies false", and $a \otimes b$
("strong conjunction") is sugar for "it is not the case that $a$ implies not
$b$". This makes the formal syntax tiny.

In Lean ([`Lukasiewicz/Soundness.lean`](Lukasiewicz/Soundness.lean)):

```lean
inductive Formula where
  | var : Nat → Formula     -- propositional variables, indexed by ℕ
  | bot : Formula           -- ⊥
  | imp : Formula → Formula → Formula    -- implication
```

The `var n` constructor uses natural numbers just to give the variables
names; we never actually do arithmetic on them.

> **Why ⊥ primitive and ∼ derived?** Making $\sim$ a primitive constructor
> instead of defining it as $a \Rightarrow \bot$ silently *weakens* the
> system — double-negation introduction stops being derivable. This was a
> real bug caught and fixed during development; see the comment block at
> the top of [`Lukasiewicz/Equivalence.lean`](Lukasiewicz/Equivalence.lean).

### Proof system — what counts as a theorem

A BL theorem is anything that can be obtained from the eleven axiom schemes
below by **modus ponens** (from $a$ and $a \Rightarrow b$, conclude $b$).
Throughout, $a, b, c$ are *arbitrary* formulas — each axiom is a scheme that
gives a theorem for every choice of formulas to plug in.

| Rule | Statement | Name |
|---|---|---|
| $\mathsf{id}$ | $a \Rightarrow a$ | identity |
| $\mathsf{a1}$ | $(a \Rightarrow b) \Rightarrow ((b \Rightarrow c) \Rightarrow (a \Rightarrow c))$ | transitivity / prefixing |
| $\mathsf{a2}$ | $(a \otimes b) \Rightarrow a$ | weakening for $\otimes$ |
| $\mathsf{a3}$ | $(a \otimes b) \Rightarrow (b \otimes a)$ | $\otimes$ is commutative |
| $\mathsf{a4}$ | $(a \otimes (a \Rightarrow b)) \Rightarrow (b \otimes (b \Rightarrow a))$ | **divisibility** |
| $\mathsf{a5a}$ | $(a \Rightarrow (b \Rightarrow c)) \Rightarrow ((a \otimes b) \Rightarrow c)$ | currying — one half of residuation |
| $\mathsf{a5b}$ | $((a \otimes b) \Rightarrow c) \Rightarrow (a \Rightarrow (b \Rightarrow c))$ | uncurrying — the other half |
| $\mathsf{a6}$ | $((a \Rightarrow b) \Rightarrow c) \Rightarrow (((b \Rightarrow a) \Rightarrow c) \Rightarrow c)$ | **prelinearity** |
| $\mathsf{a7}$ | $\bot \Rightarrow a$ | ex falso quodlibet |
| $\mathsf{dn}$ | $\sim\sim a \Rightarrow a$ | **double negation** (this is what makes BL into Łukasiewicz) |
| $\mathsf{mp}$ | from $a$ and $a \Rightarrow b$, conclude $b$ | modus ponens |

The Lean encoding is an `inductive` predicate `BL : Formula → Prop` — one
constructor per row above:

```lean
inductive BL : Formula → Prop
  | id  (a : Formula)      : BL (a ⇒ a)
  | a1  (a b c : Formula)  : BL ((a ⇒ b) ⇒ ((b ⇒ c) ⇒ (a ⇒ c)))
  | a2  (a b : Formula)    : BL ((a ⊗ b) ⇒ a)
  -- ...
  | a6  (a b c : Formula)  : BL (((a ⇒ b) ⇒ c) ⇒ (((b ⇒ a) ⇒ c) ⇒ c))
  | dn  (a : Formula)      : BL (∼∼a ⇒ a)
  | mp  {a b : Formula}    : BL (a ⇒ b) → BL a → BL b
```

A term of type `BL φ` is a *Lean proof that $\varphi$ is a BL theorem* —
it is a proof tree built from these eleven constructors.

### Two of the rules deserve commentary

**Divisibility ($\mathsf{a}4$)** says that the two pairs $(a, a \Rightarrow b)$
and $(b, b \Rightarrow a)$ have the same strong conjunction. Why? Both equal
$a \wedge b$ — the lattice meet. So $\mathsf{a}4$ is asserting an equality
between two expressions that happen to both compute the infimum. This is the
geometric content of "the logic is divisible".

**Prelinearity ($\mathsf{a}6$)** says: whenever some $c$ is implied by both
"$a \Rightarrow b$" and "$b \Rightarrow a$", that $c$ is already a theorem.
The contrapositive viewpoint is more vivid — at least one of $a \Rightarrow b$
or $b \Rightarrow a$ is "true enough" to deliver $c$, no matter what $c$ is.
On the standard $[0,1]$ algebra this is obvious (one of $x \le y$, $y \le x$
must hold, so one of the implications is $1$). In an arbitrary MV-algebra it
is much subtler — see §6.

---

## 5. The bridge: evaluation

To prove soundness we need to interpret a syntactic formula as an element of
an MV-algebra. The interpretation depends on a **valuation**
$v: \mathbb{N} \to A$ that assigns each variable an element of $A$. Then
$\mathrm{eval}_v$ is defined by structural recursion:

$$
\begin{aligned}
\mathrm{eval}_v(\mathsf{var}\;n) &= v(n) \\
\mathrm{eval}_v(\bot) &= 0 \\
\mathrm{eval}_v(a \Rightarrow b) &= \mathrm{eval}_v(a) \Rightarrow \mathrm{eval}_v(b)
\end{aligned}
$$

where on the right-hand side $\Rightarrow$ is the *algebraic* implication
defined back in §3. So `eval` *translates syntax into algebra*. In Lean:

```lean
def eval (v : Nat → A) : Formula → A
  | .var n   => v n
  | .bot     => zero
  | .imp a b => imp (eval v a) (eval v b)
```

A one-line lemma `eval_sconj` checks that this respects the *defined*
connectives too:

$$\mathrm{eval}_v(a \otimes b) = \mathrm{eval}_v(a) \odot \mathrm{eval}_v(b).$$

Now the main theorem is a single sentence:

```lean
theorem sound {φ : Formula} (h : BL φ) (v : Nat → A) : eval v φ = (one : A)
```

In words: **for every formula $\varphi$, if $\varphi$ is a BL theorem (`h : BL φ`),
then for every valuation $v$, the interpretation of $\varphi$ equals $1$**.
The MV-algebra $A$ is left implicit, quantified by the `[MVAlgebra A]` instance
argument — so a single proof handles *every* MV-algebra at once.

The proof is `induction h with ...`: one case per BL constructor.

---

## 6. The hard case — soundness of prelinearity ($\mathsf{a}6$)

Most of the 11 cases are short. For example, soundness of $\mathsf{a}2$
unfolds to "$x \odot y \le x$", which is one line.

$\mathsf{a}6$ is different. After unfolding `eval`, setting
$x := \mathrm{eval}_v(a)$, $y := \mathrm{eval}_v(b)$, $z := \mathrm{eval}_v(c)$,
and abbreviating

$$
P := x \Rightarrow y, \qquad Q := y \Rightarrow x,
$$

a small algebraic lemma (`a6_reduction`) shows the goal is equivalent to

$$
(P \odot \neg z) \;\oplus\; (Q \odot \neg z) \;\oplus\; z \;=\; 1.
$$

By residuation and a couple of De Morgan steps this turns into the inequality

$$
\textbf{(}\star\textbf{)} \qquad (z \oplus \neg P) \;\odot\; (z \oplus \neg Q) \;\le\; z.
$$

**Crucial subtlety:** $(\star)$ is *false* for arbitrary $P, Q$, even when they
satisfy $P \oplus Q = 1$. Concretely, in $[0,1]$ take $P = 0.7$ and $Q = 0.5$:
these satisfy $P \oplus Q = \min(1,\,1.2) = 1$, but at $z = 0.57$ the
left-hand side of $(\star)$ equals $0.87 > z$, so the inequality fails. The
inequality holds only because $P$ and $Q$ have the *specific shape*
$P = x \Rightarrow y$ and $Q = y \Rightarrow x$ for some $x, y$.

The route through is the **key equation**:

$$
\textbf{(}\dagger\textbf{)} \qquad (z \oplus \neg P) \,\wedge\, (z \oplus \neg Q) \;=\; z.
$$

In any residuated lattice $X \odot Y \le X \wedge Y$, so $(\dagger)$ implies
$(\star)$. The equation $(\dagger)$ is itself the consequence of two named
results, both proved in [`Lukasiewicz/Base.lean`](Lukasiewicz/Base.lean):

### Mundici's Proposition 1.7

$$
(x \ominus y) \,\wedge\, (y \ominus x) \;=\; 0
$$

where $x \ominus y := x \odot \neg y$ ("truncated subtraction"; on $[0,1]$
it is $\max(0,\, x - y)$). Geometrically: $x \ominus y$ and $y \ominus x$
cannot both be positive — one of them is always zero. The proof in
[`Lukasiewicz/Base.lean`](Lukasiewicz/Base.lean) is a chain of equational rewrites driven by
the **meet idiom**

$$
a \odot (\neg a \oplus b) \;=\; a \wedge b
$$

that progressively rearranges factors until $\neg x \odot x = 0$ appears
inside a product. It depends on **no axioms at all**.

### Mundici's Proposition 1.6(ii) — distributivity

$$
x \oplus (y \wedge z) \;=\; (x \oplus y) \,\wedge\, (x \oplus z).
$$

This is the lattice-distributive law for $\oplus$ over $\wedge$. It is
derived from its dual (Prop 1.6(i): $\odot$ distributes over $\vee$) via De
Morgan. Both rest on `mvsup_lub` — the proof that the operation $\vee$ we
defined is genuinely the *least* upper bound — which is itself a ten-step
chain from `mv_axiom`.

### Putting it together

With $A = a \Rightarrow b$ and $B = b \Rightarrow a$ we get
$\neg A = a \ominus b$ and $\neg B = b \ominus a$. Then

$$
\begin{aligned}
(z \oplus \neg A) \,\wedge\, (z \oplus \neg B)
&\;\overset{1.6(\mathrm{ii})}{=}\; z \oplus \bigl((a \ominus b) \,\wedge\, (b \ominus a)\bigr) \\
&\;\overset{1.7}{=}\; z \oplus 0 \\
&\;=\; z.
\end{aligned}
$$

That is exactly $(\dagger)$, packaged as `a6_key` in
[`Lukasiewicz/Base.lean`](Lukasiewicz/Base.lean) — a three-line Lean proof. Combining it with
the residuated-lattice fact $X \odot Y \le X \wedge Y$ (called
`odot_le_mvinf`) closes the $\mathsf{a}6$ case in
[`Lukasiewicz/Soundness.lean`](Lukasiewicz/Soundness.lean).

> **Why this matters.** The textbook proof of prelinearity uses **Chang's
> subdirect representation theorem**: every MV-algebra embeds into a product
> of MV-chains (totally-ordered MV-algebras), where the result is trivial
> because one of $x \le y, y \le x$ always holds. That route needs
> ultrafilters or Zorn's lemma. The proof in this repository is purely
> equational — no representation, no quotient, no choice — which is why
> `#print axioms sound` shows only the standard `propext` and never
> `Classical.choice`.

---

## 7. The other two deliverables

### [`Lukasiewicz/Equivalence.lean`](Lukasiewicz/Equivalence.lean) — BL + double negation ⊨ Łukasiewicz

Łukasiewicz's original 1920s axiomatization uses four schemes:

$$
\begin{aligned}
\text{L1.}\quad & a \Rightarrow (b \Rightarrow a) \\
\text{L2.}\quad & (a \Rightarrow b) \Rightarrow ((b \Rightarrow c) \Rightarrow (a \Rightarrow c)) \\
\text{L3.}\quad & ((a \Rightarrow b) \Rightarrow b) \Rightarrow ((b \Rightarrow a) \Rightarrow a) \\
\text{L4.}\quad & (\sim b \Rightarrow \sim a) \Rightarrow (a \Rightarrow b)
\end{aligned}
$$

[`Lukasiewicz/Equivalence.lean`](Lukasiewicz/Equivalence.lean) proves each of L1–L4 *inside* BL (which
already includes $\mathsf{dn}$, double-negation elimination, hence makes BL into
Łukasiewicz). So the two axiom bases prove the same theorems — they are
equivalent presentations. L1 and L2 are easy (L2 is literally BL's $\mathsf{a1}$);
L4 takes contraposition + double negation; L3 is the structurally hardest,
combining $\mathsf{a4}$, $\mathsf{dn}$, and L4. All four are now closed and
`#print axioms` confirms zero axiom dependency.

### [`Lukasiewicz/DeductionBL.lean`](Lukasiewicz/DeductionBL.lean) — the Local Deduction Theorem

In classical logic, the deduction theorem says: $\Gamma, a \vdash b$ if and
only if $\Gamma \vdash a \Rightarrow b$. **This fails in Łukasiewicz**, because
the logic lacks the *contraction* rule — using $a$ twice on the left does not
give two copies of $a$ on the right. The correct substitute, due to Hájek, is
the **Local Deduction Theorem**:

$$
\Gamma, a \;\vdash\; b
\quad\Longleftrightarrow\quad
\exists\, n \in \mathbb{N},\; \Gamma \;\vdash\; a^n \Rightarrow b
$$

where $a^n := a \otimes a \otimes \cdots \otimes a$ ($n$ copies). The
intuition: derivations may consume the hypothesis $a$ several times, but
finitely many. The "fusion crux" of the proof tracks how copies combine
through modus ponens. The Lean statement:

```lean
theorem localDeductionTheorem (Γ : FSet) (a b : Formula) :
    (insertF a Γ ⊢ b) ↔ ∃ n, Γ ⊢ (sconjPow a n ⇒ b)
```

(Theories `Γ` are encoded as predicates on `Formula`, not Mathlib `Set`, to
keep the file pure-core.)

---

## 8. Two further structural theorems

After soundness, the formalization establishes two further "famous" structural
facts about MV-algebras.

### Mundici's Fundamental Structure Theorem (Propositions 1.5 + 1.6)

In [`Lukasiewicz/Lattice.lean`](Lukasiewicz/Lattice.lean), the theorem
`mv_fundamental_structure` bundles eight facts that together say: every
MV-algebra is a *bounded lattice* under its natural order, with the monoid
operations distributing over the lattice operations:

$$
x \odot (y \vee z) \;=\; (x \odot y) \vee (x \odot z), \qquad
x \oplus (y \wedge z) \;=\; (x \oplus y) \wedge (x \oplus z).
$$

This is the most-cited structural result for MV-algebras and the workhorse
that every higher theorem (representation, completeness, the McNaughton
characterization of free algebras) builds on. The proof is constructive:
axiom dependency is `[propext]` only, with no use of choice or subdirect
representation.

> **Note on full lattice distributivity.** The "lattice distributivity"
> identity $x \vee (y \wedge z) = (x \vee y) \wedge (x \vee z)$ is also a
> theorem of MV-algebras, but its textbook proof in Cignoli–D'Ottaviano–
> Mundici routes through Chang's subdirect representation theorem, which
> uses Zorn's lemma. We don't prove it here for that reason; the bundled
> "semiring-like" distributivities of Proposition 1.6 are what go through
> equationally.

### Mundici's Proposition 1.10: the MV-algebra metric

In [`Lukasiewicz/Distance.lean`](Lukasiewicz/Distance.lean), the distance function

$$
d(x, y) \;:=\; (x \odot \neg y) \;\oplus\; (y \odot \neg x)
$$

(which on the standard `[0,1]` algebra computes $|x - y|$, and on a Boolean
algebra is symmetric difference) is shown to satisfy the five metric
properties:

1. $d(x, y) = 0 \iff x = y$ — identity of indiscernibles
2. $d(x, y) = d(y, x)$ — symmetry
3. $d(x, z) \le d(x, y) \oplus d(y, z)$ — triangle inequality
4. $d(x, y) = d(\neg x, \neg y)$ — negation-invariance
5. $d(x \oplus s,\, y \oplus t) \le d(x, y) \oplus d(s, t)$ — non-expansiveness of $\oplus$

The triangle inequality (property 3) is the deepest of these. Its proof
goes via a single-side bound $(x \ominus z) \le (x \ominus y) \oplus (y \ominus z)$,
which we close by showing that

$$
(x \odot \neg z) \;\odot\; \neg\bigl((x \ominus y) \oplus (y \ominus z)\bigr) \;=\; 0.
$$

After expanding the second factor via De Morgan into $(\neg x \oplus y) \odot (\neg y \oplus z)$,
the rearrangement of the four $\odot$-factors reveals the meet-idiom pattern
$x \odot (\neg x \oplus y) = x \wedge y$, leaving us with

$$
(x \wedge y) \;\odot\; (\neg z \wedge \neg y),
$$

bounded above by $y \odot \neg y = 0$. Property 5 ($\oplus$-non-expansiveness)
follows the same template with five $\odot$-factors instead of four, paired
into two meet idioms.

**All seven results in `Distance.lean` are entirely axiom-free** —
`#print axioms` reports "does not depend on any axioms" for each. The metric
structure is the entry point to the analytic theory of Łukasiewicz logic
(uniform continuity of operations, completion-theoretic constructions) and
the basis on which Mundici Proposition 1.11 characterizes congruences:
$x \sim_I y$ iff $d(x, y) \in I$ for some ideal $I$.

---

## 9. Two characterization theorems

Two final results in [`Lukasiewicz/BooleanCenter.lean`](Lukasiewicz/BooleanCenter.lean) bring the
formalization into contact with the most-quoted *characterizations* in the
theory.

### Mundici Lemma 1.2 — four characterizations of the natural order

The natural order on an MV-algebra has four equivalent formulations: for any
$x, y \in A$,

$$
x \le y
\;\iff\; \neg x \oplus y = 1
\;\iff\; x \odot \neg y = 0
\;\iff\; y = x \oplus (y \ominus x)
\;\iff\; \exists z, \ x \oplus z = y.
$$

These say, respectively: the residuum hits the top, truncated subtraction
vanishes, $y$ decomposes as the join of $x$ and a remainder, and $y$ is
"reachable" from $x$ by adding something. The first two were used implicitly
throughout the project; the third and fourth are added explicitly here for
completeness. Each direction is proved axiom-free; the bundled
$\Leftrightarrow$ statement uses `propext` (as any `iff` does).

### The Boolean Center

The most famous *intrinsic* characterization of "classical" elements inside an
MV-algebra is the theorem that says all natural definitions agree. An element
$a \in A$ satisfies any one of the following exactly when it satisfies all
four:

$$
a \odot a = a \;\;\iff\;\; a \oplus a = a \;\;\iff\;\; a \vee \neg a = 1 \;\;\iff\;\; a \wedge \neg a = 0.
$$

These say: $a$ is $\odot$-idempotent / $\oplus$-idempotent / satisfies
excluded middle / satisfies non-contradiction. Such elements are called
**Boolean** (or *sharp*, or *crisp*), and the set
$B(A) := \{a \in A : a \odot a = a\}$
is the **Boolean center** of $A$ — the largest Boolean subalgebra
sitting inside the MV-algebra. We prove the four-way equivalence and the
closure of $B(A)$ under $\odot$, $\oplus$, and $\neg$. On the standard
$[0,1]$ algebra, $B([0,1]) = \{0, 1\}$ — exactly the classical truth values.
On a Boolean algebra, $B(A) = A$.

The proof of the equivalences goes through a short chain. The key step is:

$$
(a \vee \neg a) \odot a \;\overset{\text{Prop 1.6(i)}}{=}\; (a \odot a) \vee (\neg a \odot a) \;=\; (a \odot a) \vee 0 \;=\; a \odot a.
$$

So if $a \vee \neg a = 1$, the left-hand side is $1 \odot a = a$, hence
$a \odot a = a$. The reverse direction unrolls $a \vee \neg a$ as
$(a \odot \neg \neg a) \oplus \neg a = (a \odot a) \oplus \neg a = a \oplus \neg a = 1$.
The "$\odot$-idempotent ↔ $\oplus$-idempotent" equivalence then follows
because $\neg$ swaps the two (and $a \vee \neg a$ is invariant under $a \mapsto \neg a$),
so being Boolean is a self-dual condition.

The Boolean center is intensely studied — Cignoli's "Boolean Skeletons of
MV-algebras" (2011), Mundici's "Advanced Łukasiewicz Calculus" §3 — as the
"classical part" of a many-valued algebra. It is the natural setting for
two-valued reasoning inside fuzzy logic and is what every classical-logic
fragment of a Łukasiewicz formal system computes with.

---

## 10. Two foundational lemmas: uniqueness of negation, and propagation of disjointness

[`Lukasiewicz/MVLemmas.lean`](Lukasiewicz/MVLemmas.lean) adds two of the most-cited "small" theorems
from the early pages of Cignoli–D'Ottaviano–Mundici.

### Lemma 1.3 — Uniqueness of negation

The negation $\neg a$ is the **unique** element $x$ satisfying both

$$a \oplus x = 1 \quad \text{and} \quad a \odot x = 0.$$

This is a structural strengthening: negation isn't just *one* element with these
properties, it's the only one. The proof is a textbook antisymmetry pinch — the
two equations say exactly $\neg a \le x$ and $x \le \neg a$ respectively:

- $a \oplus x = 1$ unfolds to $\neg(\neg a) \oplus x = 1$ via `neg_neg`, which
  is the definition of $\neg a \le x$.
- $a \odot x = 0$ means $\neg a \oplus \neg x = 1$ (by `neg_odot`), which is
  $a \le \neg x$, equivalently $x \le \neg a$ via `le_neg_swap`.

Apply `le_antisymm`. Both `neg_unique` and the bundle `neg_iff_unique` are
**axiom-free**.

### Lemma 1.8 — Propagation of disjointness

If $x \wedge y = 0$ then $(\underbrace{x \oplus x \oplus \cdots \oplus x}_{n}) \wedge y = 0$
for every natural $n$. This is the engine of prime-ideal existence (Mundici
Proposition 1.19), which is in turn the keystone of Chang's Subdirect
Representation Theorem.

The proof factors cleanly. Suppose $a \wedge y = 0$. Then by definition of
$\wedge$,

$$y \odot (\neg y \oplus a) = 0,$$

and by residuation, $\neg y \oplus a \le \neg y$. Combined with the trivial
$\neg y \le \neg y \oplus a$ (since $0 \le a$), antisymmetry gives

$$\neg y \oplus a = \neg y.$$

In other words, *disjointness with $y$ means adding $a$ doesn't grow $\neg y$*.
This forces the key combiner

$$\underbrace{(a \oplus b) \wedge y}_{= \,y \,\odot\, (\neg y \,\oplus\, a \,\oplus\, b)} \;=\; y \odot (\neg y \oplus b) \;=\; b \wedge y,$$

so adding any $b$ to a disjoint $a$ leaves the intersection with $y$ unchanged.
By induction on $n$, $\text{nfold}_n(x) \wedge y = 0$ at every $n$.

The full chain — `neg_oplus_eq_of_mvinf_zero` (`¬y ⊕ a = ¬y` from $a \wedge y = 0$),
`mvinf_oplus_eq_of_left_mvinf_zero` (the combiner), and
`nfold_mvinf_left_of_mvinf` (the induction) — is **fully axiom-free**. Only the
intermediate single-step `mvinf_two_left_of_mvinf` uses `propext`, since it goes
through a `calc` chain.

The two symmetric forms are immediate consequences:
$x \wedge (\text{nfold}_n y) = 0$ and $(\text{nfold}_n x) \wedge (\text{nfold}_n y) = 0$.

---

## 11. The Boolean Center IS a Boolean algebra (and Lemma 1.4)

[`Lukasiewicz/BooleanAlgebra.lean`](Lukasiewicz/BooleanAlgebra.lean) closes the Boolean-center story
and bundles the monotonicity package.

### The structural theorem

Section §9 introduced the Boolean center $B(A) = \{a : a \odot a = a\}$ and
proved it is closed under $\neg$, $\odot$, and $\oplus$. The natural follow-up
question is: do the MV-operations on $B(A)$ actually behave Boolean-like? The
answer is yes — and concretely:

$$\boxed{\quad a, b \in B(A) \;\Longrightarrow\; a \odot b = a \wedge b \;\;\text{and}\;\; a \oplus b = a \vee b. \quad}$$

This says the monoid operations *coincide* with the lattice operations on the
Boolean center. Combined with closure, it shows $(B(A), \vee, \wedge, \neg, 0, 1)$
is a Boolean subalgebra of $A$.

The proof of $a \odot b = a \wedge b$ has a short, elegant chain. The inequality
$a \odot b \le a \wedge b$ holds in every residuated lattice (the GLB property
of $\wedge$ and the bounds $a \odot b \le a$, $a \odot b \le b$). For the
reverse, we use that $b$ is idempotent:

$$
a \wedge b
\;=\; b \wedge a
\;\overset{\text{meet idiom}}{=}\; b \odot (\neg b \oplus a)
\;\overset{b \odot b = b}{=}\; (b \odot b) \odot (\neg b \oplus a)
\;=\; b \odot \bigl(b \odot (\neg b \oplus a)\bigr)
\;\overset{\text{meet idiom}}{=}\; b \odot (b \wedge a)
\;\le\; b \odot a.
$$

The last inequality uses $b \wedge a \le a$ and monotonicity of $\odot$. The
chain is completely equational once you spot the idempotence trick — and the
formalization captures it in a few lines. The headline `odot_eq_mvinf_of_isBoolean`
is **fully axiom-free**.

The companion $a \oplus b = a \vee b$ follows by De Morgan applied to the
$\odot$-version on $\neg a$ and $\neg b$, which are Boolean by the closure
under $\neg$.

### Mundici Lemma 1.4

The same file packages Mundici's *Lemma 1.4* — three monotonicity facts that
together with Lemma 1.2 form the bedrock of MV-order theory:

1. $x \le y \;\iff\; \neg y \le \neg x$ — **contraposition** (axiom-free).
2. $x \le y \;\Longrightarrow\; x \oplus z \le y \oplus z$ and
   $x \odot z \le y \odot z$ — **monotonicity** of the monoid operations.
3. $x \odot y \le z \;\iff\; x \le \neg y \oplus z$ — the **residuation/transfer law**,
   already proved in our infrastructure but now bundled explicitly as
   `residuation_lemma14`. Axiom-free.

These are *the* monotonicity tools used in every proof about MV-order — they
are why "ordering chains" of arguments work the way they do in the textbook.

---

## 12. MV-homomorphisms, ideals, and congruences

[`Lukasiewicz/Ideals.lean`](Lukasiewicz/Ideals.lean) lifts the formalization from a study of one
MV-algebra at a time to the *category-theoretic* foundation of MV-algebra
theory: morphisms, kernels, ideals, and quotient congruences.

### MV-homomorphisms (Mundici Lemma 1.9)

An MV-homomorphism $h : A \to B$ is a function preserving the three primitive
operations:

$$h(0) = 0, \qquad h(x \oplus y) = h(x) \oplus h(y), \qquad h(\neg x) = \neg h(x).$$

From these three laws, *all* the derived structure is automatically preserved:

$$
h(1) = 1, \qquad
h(x \odot y) = h(x) \odot h(y), \qquad
h(x \vee y) = h(x) \vee h(y), \qquad
h(x \wedge y) = h(x) \wedge h(y),
$$
$$
x \le y \;\Rightarrow\; h(x) \le h(y), \qquad
h(d(x, y)) = d(h(x), h(y)).
$$

Each follows from the definitions: $\odot$, $\vee$, $\wedge$, and $d$ are all
*defined in terms of* $\oplus$ and $\neg$, so unfolding plus the three
preservation axioms gives the rest mechanically. Order preservation uses
that $x \le y$ is the equation $\neg x \oplus y = 1$, which $h$ takes to
$\neg h(x) \oplus h(y) = h(1) = 1$. The distance-preservation $h(d(x,y)) = d(h(x), h(y))$
is what makes the next section work.

### Ideals and kernels

An **ideal** of $A$ is a subset $I \subseteq A$ closed under three conditions:
$0 \in I$, downward-closed under the natural order, and closed under $\oplus$.
These are exactly the conditions for "$x$ is small" to be a coherent notion in
an MV-algebra.

The *kernel* of an MV-homomorphism,

$$\text{Ker}(h) := \{ x \in A : h(x) = 0 \},$$

is an ideal — this is Mundici Lemma 1.9(v). The three closure conditions
follow effortlessly from the preservation laws: $0 \in \text{Ker}(h)$ because
$h(0) = 0$; $\text{Ker}$ is downward-closed because $y \le x$ implies $h(y) \le h(x) = 0$
and $0 \le h(y)$ always, so $h(y) = 0$; and $\text{Ker}$ is closed under $\oplus$ because
$h(x \oplus y) = h(x) \oplus h(y) = 0 \oplus 0 = 0$.

### The ideal–congruence correspondence (Mundici Prop 1.11, forward)

A **congruence** on $A$ is an equivalence relation $\sim$ that is compatible
with $\oplus$ and $\neg$ — that is,

$$x \sim y \;\land\; s \sim t \;\Rightarrow\; (x \oplus s) \sim (y \oplus t), \qquad
x \sim y \;\Rightarrow\; \neg x \sim \neg y.$$

(Compatibility with $\odot$, $\vee$, $\wedge$, etc. follows since these are
defined from $\oplus$ and $\neg$.)

The key bridge — Mundici Proposition 1.11 — is: **ideals are in natural
bijection with congruences**, via the distance function. The forward direction
(every ideal induces a congruence) is now formalized:

> Given an ideal $I$, the relation $x \equiv_I y \;:\!\iff\; d(x, y) \in I$
> is a congruence on $A$.

The proof is the cleanest possible reuse of the metric machinery from
§8 — every congruence axiom for $\equiv_I$ matches a metric property of $d$:

| Congruence axiom | Metric property | Ideal property |
|---|---|---|
| Reflexivity $x \equiv_I x$ | $d(x, x) = 0$ | $0 \in I$ |
| Symmetry $x \equiv_I y \Rightarrow y \equiv_I x$ | $d(x, y) = d(y, x)$ | (none) |
| Transitivity | $d(x,z) \le d(x,y) \oplus d(y,z)$ | $\oplus$-closed + downward-closed |
| $\oplus$-compatibility | $d(x{\oplus}s, y{\oplus}t) \le d(x,y) \oplus d(s,t)$ | $\oplus$-closed + downward-closed |
| $\neg$-compatibility | $d(\neg x, \neg y) = d(x, y)$ | (none) |

This is the payoff of `Distance.lean`: with the metric inequalities in hand,
the congruence axioms drop out as one-liners.

**The entire file is axiom-free**: `#print axioms` reports "does not depend on any
axioms" for all eight `MVHom.map_*` lemmas, both example ideals, the kernel
construction, and the ideal-to-congruence bridge. There is no `[propext]`
dependency anywhere — `Iff.rfl` settles the `≡_I y ⟺ d(x,y) ∈ I` equivalence
without needing the propositional-extensionality axiom.

### Closing the bijection (Proposition 1.11, reverse direction)

The reverse direction of Mundici's bijection is now also formalized: *every*
congruence comes from a unique ideal, completing the famous classical
correspondence

$$\{\text{ideals of }A\} \;\longleftrightarrow\; \{\text{congruences on }A\}.$$

Given a congruence $R$ on $A$, its **kernel** is

$$R.\text{kernel} := \{x \in A : x \mathrel{R} 0\}.$$

This is an ideal — the three closure conditions follow from congruence
properties. $0 \in R.\text{kernel}$ by reflexivity. Closure under $\oplus$
follows from $\oplus$-compatibility: $x R 0$ and $y R 0$ give $x \oplus y \,R\, 0 \oplus 0 = 0$.
The interesting case is downward closure: $y \le x$ and $x R 0$ imply $y R 0$.
The trick is that $y \le x$ means $y = y \wedge x$, so by automatic $\wedge$-compatibility
of any congruence, $y = y \wedge x \,R\, y \wedge 0 = 0$. The $\wedge$-compatibility itself
follows from $\oplus$- and $\neg$-compatibility because $\wedge$ is defined from $\odot$
and $\oplus$, and $\odot$ is defined from $\oplus$ and $\neg$.

The bridge $R = \equiv_{R.\text{kernel}}$ requires showing

$$x R y \iff d(x, y) \in R.\text{kernel}.$$

The forward direction is straightforward: $x R y$ implies $\neg x R \neg y$
($\neg$-compatibility), then $y \odot \neg x R x \odot \neg x = 0$ ($\odot$-compat),
similarly $x \odot \neg y R 0$, so $d(x, y) R 0$ by $\oplus$-compatibility.

The reverse direction uses the **key identity** $x \oplus (y \ominus x) = x \vee y$
(`oplus_ominus_eq_mvsup`). If $d(x, y) R 0$, then since $R.\text{kernel}$ is
downward-closed and $x \ominus y, y \ominus x \le d(x, y)$, both individual differences are
in $R.\text{kernel}$ — i.e., $(x \ominus y) R 0$ and $(y \ominus x) R 0$. Then:

$$x \;\overset{0 R (y \ominus x)}{R}\; x \oplus (y \ominus x) \;\overset{\text{key identity}}{=}\; x \vee y$$

and symmetrically $y \,R\, y \vee x = x \vee y$. By transitivity, $x R y$.

The bundle `ideal_congruence_bijection` is **fully axiom-free**.

### MV-algebras as a category

Two final structural results bundle the homomorphism story:

- `MVHom.id` — the identity function `A → A` is an MV-homomorphism.
- `MVHom.comp` — composition of MV-homomorphisms is an MV-homomorphism.
- `MVHom.id_comp`, `MVHom.comp_id`, `MVHom.comp_assoc` — the category laws,
  all holding by `rfl` since they reduce to function-composition identities.

Together with the homomorphism preservation laws, these make MV-algebras and
their morphisms into a category — exactly the structural foundation needed for
free constructions, limit/colimit theory, and the standard Cignoli–Mundici
representation theorems. **All axiom-free.**

---

## 13. Sub-MV-algebras, principal ideals, and the structural completion

[`Lukasiewicz/Subalgebras.lean`](Lukasiewicz/Subalgebras.lean) rounds out the structural foundation by
adding four notions that every textbook in MV-algebra theory uses constantly.

### Sub-MV-algebras

A **sub-MV-algebra** of $A$ is a subset closed under the three primitive
operations $0$, $\oplus$, $\neg$. Closure under $1$ is automatic ($1 = \neg 0$),
and so are closures under $\odot$, $\vee$, $\wedge$ (each definable from
$\oplus, \neg$). The four `_mem` lemmas — `one_mem`, `odot_mem`, `mvsup_mem`,
`mvinf_mem` — are all axiom-free one-liners that unfold each derived operation
to the primitives and chain the closure conditions.

### Image of a homomorphism

For any MV-homomorphism $h : A \to B$, the **image** $\text{Im}(h) = \{y \in B : \exists x,\ h(x) = y\}$
is a sub-MV-algebra of $B$. Closure under each operation follows because $h$ preserves
that operation: $h(0) = 0$ witnesses $0 \in \text{Im}(h)$; for closure under $\oplus$, given
$h(x_1) = y_1$ and $h(x_2) = y_2$, we have $h(x_1 \oplus x_2) = y_1 \oplus y_2$; similarly for $\neg$.
Axiom-free.

### The Boolean center as a sub-MV-algebra

The Boolean center $B(A) = \{a : a \odot a = a\}$ was already shown to be closed
under $\neg$, $\odot$, $\oplus$ (in `BooleanCenter.lean`) and to coincide with the
lattice operations (in `BooleanAlgebra.lean`). Here we package these closure facts
into the explicit `SubMVAlgebra` structure — `booleanCenter A : SubMVAlgebra A`.
Concretely: $0$ is Boolean, the sum of Booleans is Boolean, and the negation of a
Boolean is Boolean.

### Principal ideals

The **principal ideal** generated by an element $a$ is

$$\langle a \rangle \;=\; \{ x \in A : \exists n \in \mathbb{N},\ x \le n \cdot a \},$$

where $n \cdot a$ denotes the $n$-fold sum $\underbrace{a \oplus a \oplus \cdots \oplus a}_{n}$
(our `nfold n a`). The proof that $\langle a \rangle$ is an ideal depends on the
companion arithmetic lemma `nfold_add : nfold (n + m) x = nfold n x ⊕ nfold m x`,
which closes the $\oplus$-closure: if $x \le n \cdot a$ and $y \le m \cdot a$, then
$x \oplus y \le (n \cdot a) \oplus (m \cdot a) = (n + m) \cdot a$.

The principal ideal is the **smallest** ideal containing $a$
(`principalIdeal_minimal`): every ideal $J$ with $a \in J$ must contain $n \cdot a$ by
$\oplus$-closure and induction on $n$, hence contains every $x \le n \cdot a$ by
downward closure. So $\langle a \rangle \subseteq J$.

This is the standard "smallest ideal containing $a$" characterization, used
implicitly in every existence-of-prime-ideal argument and in Mundici's
Proposition 1.18 (every MV-chain is a quotient by a maximal ideal).

### Proper ideals

An ideal $I$ is **proper** iff $1 \notin I$ — equivalently, iff $I \ne A$. The
equivalence is immediate: if $1 \in I$, then for any $x$, $x \le 1$ gives
$x \in I$ by downward closure, so $I = A$ (`Ideal.eq_top_of_one_mem`). Conversely,
if $I$ contains everything, it contains $1$.

We also formalize that the zero ideal $\{0\}$ is proper iff $A$ is nontrivial
(i.e., $0 \ne 1$) — `zeroIdeal_isProper_iff_nontrivial` — and that the top ideal
is never proper. These are the trivial baseline characterizations needed before
any maximal-ideal theory can get started.

### Axiom situation

All four notions formalize cleanly. The closure lemmas for `SubMVAlgebra`, the
homomorphism-image construction, the proper-ideal predicate, and the
characterization theorems are all **axiom-free**. The Boolean-center
construction picks up `[propext]` (since `isBoolean_neg` uses it). The
principal-ideal machinery and `nfold_add` use the standard Lean axioms
`[propext, Quot.sound]` — the latter coming from the `omega` tactic used to
prove the simple arithmetic identity $k + 1 + m = (k + m) + 1$ in `Nat`. These
are the most mainstream Lean axioms; no `Classical.choice` or `sorryAx`
anywhere.

---

## 14. The lattice of ideals and homomorphism injectivity

[`Lukasiewicz/IdealOperations.lean`](Lukasiewicz/IdealOperations.lean) extends the ideal/homomorphism
theory with lattice structure and a famous characterization of injectivity.

### Lattice operations on ideals

The set of ideals on an MV-algebra carries a natural lattice structure, with
two key operations:

**Intersection** is straightforward: $I \cap J := \{x : x \in I \land x \in J\}$
is an ideal whenever $I$ and $J$ are. We prove `Ideal.le_inter` — the greatest
lower bound property: any ideal $K$ contained in both $I$ and $J$ is contained
in $I \cap J$.

**Sum** is more subtle. The naïve $I + J := \{x \oplus y : x \in I, y \in J\}$
fails to be downward-closed in general, so we use the closed form

$$I + J \;:=\; \{ z : \exists\, x \in I,\, y \in J,\, z \le x \oplus y \}.$$

The downward closure is built into the existential. $\oplus$-closure works via
the rearrangement identity $(x_1 \oplus y_1) \oplus (x_2 \oplus y_2) = (x_1 \oplus x_2) \oplus (y_1 \oplus y_2)$.
We prove `Ideal.sum_le`: the **least upper bound property** — any ideal $K$
containing both $I$ and $J$ contains their sum.

Together, intersection and sum make the set of ideals into a *bounded lattice*
with bottom $\{0\}$ and top $A$.

### Preimage of an ideal under a homomorphism

For $h : A \to B$ and an ideal $J \subseteq B$, the preimage

$$h^{-1}(J) \;:=\; \{ x \in A : h(x) \in J \}$$

is an ideal of $A$. Each closure property pulls back through $h$'s
preservation laws. The kernel is recovered as the special case
$\text{Ker}(h) = h^{-1}(\{0\})$ (`ker_eq_preimage_zero`).

### Mundici Lemma 1.9(vi) — injectivity ⟺ trivial kernel

The classical characterization: an MV-homomorphism is *injective* iff its
kernel is the zero ideal.

The forward direction is routine: if $h$ is injective and $h(x) = 0 = h(0)$,
then $x = 0$.

The reverse direction is where the metric machinery pays off elegantly. Assume
$\text{Ker}(h) = \{0\}$ and suppose $h(x) = h(y)$. Then

$$d(h(x),\, h(y)) = 0 \quad\Longrightarrow\quad h(d(x, y)) = 0 \quad\Longrightarrow\quad d(x, y) \in \text{Ker}(h) = \{0\} \quad\Longrightarrow\quad d(x, y) = 0 \quad\Longrightarrow\quad x = y.$$

The chain uses `h.map_dist` (distance preservation, axiom-free) and
`eq_of_dist_zero` (from `Distance.lean`, axiom-free). The bundled
`injective_iff_ker_eq_zero` is **fully axiom-free**.

### A note on the namespace alias

We needed one technical move to get dot notation right: the kernel was
originally defined as `Luk.MVAlgebra.MVHom.ker`, while the `MVHom` structure
lives at `Luk.MVHom`. Lean's dot notation `h.ker` looks at the type's natural
namespace — `Luk.MVHom`. We therefore introduce a thin alias

```
def Luk.MVHom.ker (h : MVHom A B) : MVAlgebra.Ideal A := MVAlgebra.MVHom.ker h
```

that re-binds the kernel under the expected name. The alias is trivial, axiom-free,
and makes everything thereafter resolve via dot notation as written.

### Repository status

The repo now has **13 canonical files**. The entire `IdealOperations.lean`
file is axiom-free — all 9 headline theorems pass `#print axioms` with
"does not depend on any axioms".

---

## 15. Concrete instances, `nfold` properties, and the product MV-algebra

[`Lukasiewicz/Instances.lean`](Lukasiewicz/Instances.lean) ends the structural section of the project
with three things the formalization had been missing: concrete MV-algebra
instances, the arithmetic of `nfold` (n-fold ⊕), and the natural homomorphisms
out of a product.

### Two concrete MV-algebra instances

The whole development to this point used `[MVAlgebra A]` typeclass parameters
without ever exhibiting a concrete `A`. Two natural starting examples:

**1. The trivial MV-algebra `PUnit`** — the one-element type. Every operation
collapses to the unique element, and the six Chang axioms hold by `rfl`. The
trivial algebra has $0 = 1$ and is the *terminal* object in the category of
MV-algebras (every MV-algebra has a unique homomorphism to `PUnit`).

**2. The product MV-algebra `A × B`** — for any two MV-algebras $A$ and $B$,
the product $A \times B$ is again an MV-algebra under componentwise
operations:

$$
(a_1, b_1) \oplus (a_2, b_2) := (a_1 \oplus a_2,\ b_1 \oplus b_2), \qquad
\neg(a, b) := (\neg a,\ \neg b), \qquad
0 := (0, 0).
$$

Each Chang axiom factors through the corresponding axiom on each component.
This gives us the standard *Boolean MV-algebra* $\mathbb{Z}_2 \times \mathbb{Z}_2$ that
we used informally throughout the project as a non-totally-ordered example.

The **two natural projections** are MV-homomorphisms:

- `ProdMV.fst : MVHom (A × B) A` sending $(a, b) \mapsto a$
- `ProdMV.snd : MVHom (A × B) B` sending $(a, b) \mapsto b$

Both preserve every operation by `rfl`. Their kernels are the natural
"axis-aligned" ideals: $\text{Ker}(\text{fst}) = \{(0, b) : b \in B\}$ (the
"vertical axis") and $\text{Ker}(\text{snd}) = \{(a, 0) : a \in A\}$ (the
"horizontal axis").

### Properties of `nfold`

The `n`-fold sum `nfold n a := a ⊕ a ⊕ ⋯ ⊕ a` (`n` times) appears throughout
the project: in Lemma 1.8 (propagation of disjointness), in principal ideals
(`⟨a⟩ = {x : ∃n, x ≤ n · a}`), and in the Archimedean theory we haven't yet
reached. Five basic identities now make `nfold` ergonomic:

| Statement | Why it's true |
|---|---|
| `nfold 1 a = a` | unfold one step: `a ⊕ 0 = a` |
| `nfold n 0 = 0` | induction: `0 ⊕ 0 = 0` |
| `n ≥ 1 → nfold n 1 = 1` | unfold one step: `1 ⊕ … = 1` |
| `a ≤ b → nfold n a ≤ nfold n b` | induction + ⊕-monotonicity |
| `nfold n a ≤ 1` | trivial: everything is `≤ 1` |

### MV-homomorphisms preserve `nfold`

The key lemma `MVHom.map_nfold` says:

$$h(\underbrace{a \oplus a \oplus \cdots \oplus a}_{n}) = \underbrace{h(a) \oplus h(a) \oplus \cdots \oplus h(a)}_{n}.$$

The proof is a direct induction on $n$ using `h.map_oplus`. As an immediate
application, **the image of a principal ideal is contained in the principal ideal
of the image**:

$$h(\langle a \rangle) \subseteq \langle h(a) \rangle.$$

If $x \le n \cdot a$, then $h(x) \le h(n \cdot a) = n \cdot h(a)$ by `map_le` and
`map_nfold` — so $h(x) \in \langle h(a) \rangle$.

### Axiom situation

Most theorems are fully axiom-free. The only exception is
`image_principalIdeal_le`, which uses `[propext, Quot.sound]` inherited from
`nfold_add` (via the `omega` tactic's arithmetic decisions). These are the
standard Lean 4 axioms — no `Classical.choice`, no `sorryAx`.

---

## 16. Quotient MV-algebras and the First Isomorphism Theorem

[`Lukasiewicz/Quotient.lean`](Lukasiewicz/Quotient.lean) is the capstone of the
homomorphism and ideal theory. It builds the quotient `A/I` and proves the
**First Isomorphism Theorem** — and it does so entirely without the axiom of
choice.

### The quotient construction

In §12 the relation $x \equiv_I y \iff d(x,y) \in I$ was shown to be a congruence
for any ideal $I$. To turn the set of equivalence classes into an MV-algebra we
package that congruence as a Lean `Setoid` and take the quotient type

$$A/I \;:=\; \mathrm{Quotient}\ (I.\mathrm{setoid}).$$

The operations descend from $A$ by lifting:

$$\llbracket x \rrbracket \oplus \llbracket y \rrbracket := \llbracket x \oplus y \rrbracket, \qquad \neg \llbracket x \rrbracket := \llbracket \neg x \rrbracket, \qquad 0 := \llbracket 0 \rrbracket.$$

Lean's `Quotient.lift₂` and `Quotient.lift` demand a proof that these are
**well-defined** — that the result does not depend on the chosen representatives.
That proof is *exactly* the compatibility of the congruence with $\oplus$ and
$\neg$, which we already had: if $x \equiv_I x'$ and $y \equiv_I y'$ then
$x \oplus y \equiv_I x' \oplus y'$, so $\llbracket x \oplus y \rrbracket = \llbracket x' \oplus y' \rrbracket$
by `Quotient.sound`.

The six Chang axioms on $A/I$ then transfer mechanically: each is proved by
`Quotient.inductionOn` (reduce classes to representatives) followed by the
corresponding axiom on $A$ and `congrArg`. For instance, commutativity becomes
$\llbracket x \oplus y \rrbracket = \llbracket y \oplus x \rrbracket$, which is
`congrArg` applied to `oplus_comm x y`.

### Every ideal is a kernel

The **canonical surjection** $\pi : A \to A/I$, $x \mapsto \llbracket x \rrbracket$,
is an MV-homomorphism — and because the quotient operations are *defined* by
lifting, each homomorphism law holds by `rfl`. Its kernel is computed using the
identity $d(x, 0) = x$ (itself a three-line consequence of $x \odot 1 = x$):

$$\mathrm{Ker}(\pi) = \{x : \llbracket x \rrbracket = \llbracket 0 \rrbracket\} = \{x : d(x,0) \in I\} = \{x : x \in I\} = I.$$

So `ker_mkHom` shows **every ideal is the kernel of some homomorphism** — the
exact converse of the "every kernel is an ideal" result from §12. Combined, the
two say that *ideals and kernels coincide*.

### A sub-MV-algebra as an MV-algebra

To state "$A/\mathrm{Ker}(h) \cong \mathrm{Im}(h)$" we need the image to *be* an
MV-algebra, not merely a closed subset. So `SubMVAlgebra.Subtype` forms the
subtype $\{x : S.\mathrm{carrier}\ x\}$ and `instSubMV` equips it with the
ambient operations; equality of subtype elements is equality of their values
(`Subtype.ext`), so all six axioms transfer from $A$. This construction is
**axiom-free**.

### The First Isomorphism Theorem

With both pieces in place, the canonical map is

$$\Phi : A/\mathrm{Ker}(h) \longrightarrow \mathrm{Im}(h), \qquad \llbracket x \rrbracket \longmapsto h(x)$$

(landing in the image with witness $x$). It is well-defined because

$$\llbracket x \rrbracket = \llbracket y \rrbracket \;\Rightarrow\; d(x,y) \in \mathrm{Ker}(h) \;\Rightarrow\; h(d(x,y)) = 0 \;\Rightarrow\; d(h(x), h(y)) = 0 \;\Rightarrow\; h(x) = h(y),$$

using distance-preservation (`map_dist`) and `eq_of_dist_zero`. The same chain
*run backwards* gives **injectivity**; **surjectivity** is immediate since every
element of the image is $h(a)$ for some $a$, and $\llbracket a \rrbracket \mapsto h(a)$.
So $\Phi$ is a bijective homomorphism — an isomorphism

$$A/\mathrm{Ker}(h) \;\cong\; \mathrm{Im}(h).$$

### Why "bijective homomorphism" rather than an explicit inverse

A bijective homomorphism of MV-algebras *is* an isomorphism — its set-theoretic
inverse is automatically a homomorphism. But **constructing** that inverse in
type theory means producing, for each $y \in \mathrm{Im}(h)$, a preimage $x$ with
$h(x) = y$. The witness "$\exists x,\ h(x) = y$" is a `Prop`, and extracting data
from it requires `Classical.choice`. To keep the whole development choice-free,
the theorem is recorded as `firstIsomorphismTheorem`: *there is a homomorphism
that is both injective and surjective*. Indeed, `#print axioms` confirms the
entire module rests only on `Quot.sound` (and `propext`), never on
`Classical.choice`.

---

## 17. The Correspondence Theorem and the Third Isomorphism Theorem

[`Lukasiewicz/Correspondence.lean`](Lukasiewicz/Correspondence.lean) completes
the classical suite of isomorphism theorems, on top of the quotient machinery of
§16. Both results are choice-free.

### A lemma: ideals are congruence-closed

The technical workhorse is `mem_of_dist_mem`:

$$d(x,y) \in J \;\land\; y \in J \;\Longrightarrow\; x \in J.$$

This says an ideal's membership predicate is closed under the congruence it
induces. The proof is pure congruence algebra: $d(x,y) \in J$ means $x \equiv_J y$,
$y \in J$ means $y \equiv_J 0$, so $x \equiv_J 0$ by transitivity, i.e.
$d(x,0) \in J$; and $d(x,0) = x$. It is fully axiom-free.

### The Correspondence (Lattice) Theorem

For an ideal $I$ of $A$, there is an order-preserving bijection

$$\{\text{ideals of } A/I\} \;\longleftrightarrow\; \{\text{ideals } J \text{ of } A \text{ with } I \subseteq J\}$$

given by the two maps

$$J \longmapsto J/I := \{\llbracket x\rrbracket : x \in J\} \quad(\text{pushforward}), \qquad K \longmapsto \pi^{-1}(K) \quad(\text{preimage}).$$

The preimage of any ideal automatically contains $I$ (everything in $I$ maps to
$0$). The pushforward $J/I$ is an ideal of $A/I$; the only subtle part is
downward-closure, handled by noting that if $\llbracket y\rrbracket \le \llbracket x\rrbracket$
with $x \in J$, then $y \wedge x \le x$ lies in $J$ and
$\llbracket y \wedge x\rrbracket = \llbracket y\rrbracket$.

Both round-trips are proved:

- **Pushforward then pullback recovers $J$** (for $J \supseteq I$): if
  $\llbracket z\rrbracket = \llbracket x\rrbracket$ with $z \in J$, then
  $d(x,z) \in I \subseteq J$, so $x \in J$ by `mem_of_dist_mem`.
- **Pullback then pushforward recovers $K$**: immediate from surjectivity of
  $\pi$.

These are bundled as `correspondenceTheorem`.

### The Third Isomorphism Theorem

For ideals $I \subseteq J$, the inclusion of congruences gives a well-defined
**canonical map**

$$\psi : A/I \longrightarrow A/J, \qquad \llbracket x\rrbracket_I \longmapsto \llbracket x\rrbracket_J,$$

(well-defined because $\llbracket x\rrbracket_I = \llbracket y\rrbracket_I$ means
$d(x,y) \in I \subseteq J$). It is a **surjective** homomorphism, and its
**kernel is exactly $J/I$**:

$$\llbracket x\rrbracket_I \in \mathrm{Ker}(\psi) \iff \llbracket x\rrbracket_J = \llbracket 0\rrbracket_J \iff x \in J.$$

Feeding this surjection into the First Isomorphism Theorem of §16 yields the
familiar

$$(A/I)\,/\,(J/I) \;\cong\; A/J.$$

The pieces — `thirdIsoMap`, `thirdIsoMap_surjective`, `ker_thirdIsoMap` — are
bundled as `thirdIsomorphismTheorem`. Every result in the module depends only on
`Quot.sound` and `propext`; none uses `Classical.choice`.

---

## 18. The Second Isomorphism Theorem

[`Lukasiewicz/SecondIso.lean`](Lukasiewicz/SecondIso.lean) closes the classical
suite of isomorphism theorems. It is the shortest of the four, because it is a
direct **corollary of the First Isomorphism Theorem**.

### The composite map

Given a sub-MV-algebra $S \le A$ and an ideal $I \trianglelefteq A$, form the
composite of the inclusion with the quotient map:

$$\varphi : S \hookrightarrow A \xrightarrow{\ \pi\ } A/I, \qquad s \longmapsto \llbracket s \rrbracket.$$

Since both the sub-MV-algebra operations (on the subtype $\{x : S.\mathrm{carrier}\ x\}$,
made an MV-algebra in §16) and the quotient operations are the ambient ones,
every homomorphism law for $\varphi$ holds by `rfl`.

### Kernel and image

The **kernel** is computed exactly as for the quotient map, but restricted to
$S$:

$$s \in \mathrm{Ker}(\varphi) \iff \llbracket s \rrbracket = \llbracket 0 \rrbracket \iff s \in I \iff s \in S \cap I.$$

So $\mathrm{Ker}(\varphi) = S \cap I$, where $S \cap I$ is regarded as an ideal of
$S$ (the elements of $S$ whose value lies in $I$ — `subInterIdeal`; its downward
closure uses that the order on the subtype is the ambient order on values).

The **image** is

$$\mathrm{Im}(\varphi) = \{\llbracket s \rrbracket : s \in S\},$$

which is precisely $(S + I)/I$ — the sub-MV-algebra of $A/I$ consisting of the
classes that have a representative in $S$ (`mem_image_subQuotientHom`).

### The theorem

Applying the First Isomorphism Theorem of §16 to $\varphi$ gives a bijective
homomorphism $S/\mathrm{Ker}(\varphi) \to \mathrm{Im}(\varphi)$, i.e.

$$S/(S \cap I) \;\cong\; (S + I)/I.$$

This is `secondIsomorphismTheorem`. Together with the First and Third
Isomorphism Theorems and the Correspondence Theorem, the standard package is now
complete — and every piece of it is choice-free, resting only on `Quot.sound`
and `propext`.

---

## 19. The Chinese Remainder Theorem

[`Lukasiewicz/CRT.lean`](Lukasiewicz/CRT.lean) proves a famous isomorphism
theorem that sits just beyond the standard three: the **Chinese Remainder
Theorem** for MV-algebras. It builds on the quotient construction (§16) and the
product MV-algebra (§15), and is choice-free.

### Statement

Two ideals $I, J$ are **comaximal** when $I + J = A$ — equivalently, there exist
$i \in I$ and $j \in J$ with $i \oplus j = 1$. The theorem says: for comaximal
$I, J$,

$$A/(I \cap J) \;\cong\; A/I \times A/J.$$

### The map and injectivity

The isomorphism is the induced **diagonal**

$$\overline{\delta} : A/(I \cap J) \longrightarrow A/I \times A/J, \qquad \llbracket a \rrbracket \longmapsto (\llbracket a\rrbracket_I,\ \llbracket a\rrbracket_J).$$

It is well-defined because $d(a,b) \in I \cap J$ unpacks into $d(a,b) \in I$ and
$d(a,b) \in J$ separately. **Injectivity holds for all ideals**, comaximal or
not: if $(\llbracket x\rrbracket_I, \llbracket x\rrbracket_J) = (\llbracket y\rrbracket_I, \llbracket y\rrbracket_J)$
then $d(x,y) \in I$ and $d(x,y) \in J$, hence $d(x,y) \in I \cap J$, so
$\llbracket x\rrbracket = \llbracket y\rrbracket$ in $A/(I \cap J)$.

### Surjectivity is exactly comaximality

This is the heart of the theorem. Given comaximality witnesses $i \in I$,
$j \in J$ with $i \oplus j = 1$, and any target
$(\llbracket x\rrbracket_I, \llbracket y\rrbracket_J)$, the **witness**

$$a \;=\; (y \odot i) \oplus (x \odot j)$$

maps onto it. The verification is the MV-algebra analogue of the ring-theoretic
CRT solution $a = y\,i + x\,j$, carried out entirely in congruence algebra.
From $i \oplus j = 1$ one reads off $\neg j \le i$ and $\neg i \le j$, so by
downward closure $\neg j \in I$ and $\neg i \in J$. These give four congruences:

$$i \equiv_I 0,\quad j \equiv_I 1,\qquad j \equiv_J 0,\quad i \equiv_J 1,$$

(using $d(i,0) = i$, $d(j,1) = \neg j$, and their $J$-counterparts). Now the
congruence's compatibility with $\odot$ and $\oplus$ does the work. Modulo $I$:

$$y \odot i \;\equiv_I\; y \odot 0 = 0, \qquad x \odot j \;\equiv_I\; x \odot 1 = x,$$

so $a = (y \odot i) \oplus (x \odot j) \equiv_I 0 \oplus x = x$. Symmetrically
$a \equiv_J y$. Hence $\overline\delta\,\llbracket a\rrbracket = (\llbracket x\rrbracket_I, \llbracket y\rrbracket_J)$.

Combining injectivity with surjectivity gives the bijective homomorphism
$A/(I \cap J) \cong A/I \times A/J$, recorded as `chineseRemainderTheorem`. As
the axiom audit confirms, the entire argument depends only on `Quot.sound` and
`propext`.

---

## 20. Basic isomorphism facts and the lattice of ideals

The final two modules collect the short, choice-free results that round out the
theory. Neither introduces new machinery; both are exercises in the definitions
already built.

### Basic isomorphism facts ([`Lukasiewicz/IsoBasics.lean`](Lukasiewicz/IsoBasics.lean))

The identity homomorphism is injective and surjective, and both properties are
preserved by composition — so bijective homomorphisms are closed under
composition (the isomorphisms form a subcategory). Two degenerate quotients are
identified:

$$A/\{0\} \;\cong\; A \qquad\text{and}\qquad A/A \;\cong\; \mathbf{1},$$

the first because $d(a,b) \in \{0\}$ forces $a = b$, the second because *every*
distance lies in the improper ideal, collapsing the quotient to a point. The
product projections $A \times B \to A$ and $A \times B \to B$ are surjective, and
the **universal property** of the product holds: a pair of homomorphisms
$f : A \to B$, $g : A \to C$ assembles into a single $\langle f,g\rangle : A \to B \times C$
with $\pi_1 \circ \langle f,g\rangle = f$ and $\pi_2 \circ \langle f,g\rangle = g$.

### The lattice of ideals ([`Lukasiewicz/IdealLattice.lean`](Lukasiewicz/IdealLattice.lean))

The ideals of an MV-algebra form a bounded lattice under intersection (meet) and
sum (join). To keep everything first-order, containment and equality are taken at
the level of carriers: `Ideal.Sub I J` means $I \subseteq J$, and
`Ideal.Equiv I J` means $I = J$. Then:

* $\subseteq$ is a partial order — reflexive, transitive, and antisymmetric (mutual
  containment is equality);
* $I \cap J$ is the **greatest lower bound** and $I + J$ the **least upper
  bound**;
* $\{0\}$ is the bottom and $A$ the top;
* idempotency ($I \cap I = I$, $I + I = I$), commutativity, and the absorption
  laws $I \cap (I + J) = I$ and $I + (I \cap J) = I$ all hold;
* the order is characterized by either operation:
  $$I \subseteq J \iff I \cap J = I \iff I + J = J.$$

For the **comaximal** ideals introduced with the Chinese Remainder Theorem
(§19), the natural basic facts are recorded: comaximality is symmetric, and is
equivalent to $1 \in I + J$, equivalently $I + J = A$. Every ideal is comaximal
with the improper ideal. Finally, sub-MV-algebras — like ideals — are closed
under intersection.

As the axiom audit confirms, most of these results are *completely axiom-free*;
the few that rewrite an `↔` use only `propext`, and the two degenerate-quotient
isomorphisms use `Quot.sound`. Nothing in either module touches
`Classical.choice`.

---

## 21. A suggested reading order

The MV-algebra theory lives in the dependency-ordered chain under
[`Lukasiewicz/`](Lukasiewicz/) (`Base → … → IdealLattice`); the propositional-logic
modules are self-contained. A good path through the material:

1. [`Lukasiewicz/Base.lean`](Lukasiewicz/Base.lean) — the `MVAlgebra` class, the
   derived operators (`imp`, `odot`, `le`), the `⊙`-monoid, and the heavy
   distributivity machinery culminating in `mundici_prop17` (the most intricate
   single proof in the project), `mvsup_lub`, the De Morgan laws, and `a6_key`.
2. [`Lukasiewicz/Soundness.lean`](Lukasiewicz/Soundness.lean) — the
   syntax/algebra bridge (`eval`) and the soundness cases, including the
   $\mathsf{a}6$ (prelinearity) case that leans on the `Base` machinery.
3. [`Lukasiewicz/Lattice.lean`](Lukasiewicz/Lattice.lean) and
   [`Lukasiewicz/Distance.lean`](Lukasiewicz/Distance.lean) — the Fundamental
   Structure Theorem and the MV-algebra metric.
4. [`Lukasiewicz/BooleanCenter.lean`](Lukasiewicz/BooleanCenter.lean) →
   [`Lukasiewicz/Ideals.lean`](Lukasiewicz/Ideals.lean) — characterizations of
   `≤`, the Boolean Center, then homomorphisms, ideals, and the ideal–congruence
   bijection.
5. [`Lukasiewicz/Quotient.lean`](Lukasiewicz/Quotient.lean) and
   [`Lukasiewicz/Correspondence.lean`](Lukasiewicz/Correspondence.lean) — the
   quotient `A/I`, the First Isomorphism Theorem, then the Correspondence
   Theorem, Third Isomorphism Theorem,
   [`Lukasiewicz/SecondIso.lean`](Lukasiewicz/SecondIso.lean) for the Second
   Isomorphism Theorem, and finally
   [`Lukasiewicz/CRT.lean`](Lukasiewicz/CRT.lean) for the Chinese Remainder
   Theorem, and [`Lukasiewicz/IsoBasics.lean`](Lukasiewicz/IsoBasics.lean) and
   [`Lukasiewicz/IdealLattice.lean`](Lukasiewicz/IdealLattice.lean) for the
   closing collection of basic isomorphism facts and the ideal lattice.
6. [`Lukasiewicz/Equivalence.lean`](Lukasiewicz/Equivalence.lean),
   [`Lukasiewicz/DeductionBL.lean`](Lukasiewicz/DeductionBL.lean), and
   [`Lukasiewicz/Residuation.lean`](Lukasiewicz/Residuation.lean) as
   self-contained reads.

Every theorem in the project can be inspected with

```lean
#print axioms <theorem_name>
```

which prints the **transitive closure** of axiom dependencies — a built-in
audit trail. The absence of `sorryAx` in that output is what distinguishes a
completed proof from one with an unfinished hole; the absence of
`Classical.choice` is what makes the proof constructive in the relevant sense.
