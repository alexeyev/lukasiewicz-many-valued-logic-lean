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

This is the entire axiomatization. In Lean ([`Soundness.lean`](Soundness.lean)):

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

It lives in [`MVAlgebra_scratch.lean`](MVAlgebra_scratch.lean) (axiom-free)
and is re-proved in [`Soundness.lean`](Soundness.lean).

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

In Lean ([`Soundness.lean`](Soundness.lean)):

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
> the top of [`Equivalence.lean`](Equivalence.lean).

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
results, both proved in [`prop17.lean`](prop17.lean):

### Mundici's Proposition 1.7

$$
(x \ominus y) \,\wedge\, (y \ominus x) \;=\; 0
$$

where $x \ominus y := x \odot \neg y$ ("truncated subtraction"; on $[0,1]$
it is $\max(0,\, x - y)$). Geometrically: $x \ominus y$ and $y \ominus x$
cannot both be positive — one of them is always zero. The proof in
[`prop17.lean`](prop17.lean#L100) is a chain of equational rewrites driven by
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
[`prop17.lean`](prop17.lean#L461) — a three-line Lean proof. Combining it with
the residuated-lattice fact $X \odot Y \le X \wedge Y$ (called
`odot_le_mvinf`) closes the $\mathsf{a}6$ case in
[`Soundness.lean`](Soundness.lean).

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

### [`Equivalence.lean`](Equivalence.lean) — BL + double negation ⊨ Łukasiewicz

Łukasiewicz's original 1920s axiomatization uses four schemes:

$$
\begin{aligned}
\text{L1.}\quad & a \Rightarrow (b \Rightarrow a) \\
\text{L2.}\quad & (a \Rightarrow b) \Rightarrow ((b \Rightarrow c) \Rightarrow (a \Rightarrow c)) \\
\text{L3.}\quad & ((a \Rightarrow b) \Rightarrow b) \Rightarrow ((b \Rightarrow a) \Rightarrow a) \\
\text{L4.}\quad & (\sim b \Rightarrow \sim a) \Rightarrow (a \Rightarrow b)
\end{aligned}
$$

[`Equivalence.lean`](Equivalence.lean) proves each of L1–L4 *inside* BL (which
already includes $\mathsf{dn}$, double-negation elimination, hence makes BL into
Łukasiewicz). So the two axiom bases prove the same theorems — they are
equivalent presentations. L1 and L2 are easy (L2 is literally BL's $\mathsf{a1}$);
L4 takes contraposition + double negation; L3 is the structurally hardest,
combining $\mathsf{a4}$, $\mathsf{dn}$, and L4. All four are now closed and
`#print axioms` confirms zero axiom dependency.

### [`DeductionBL.lean`](DeductionBL.lean) — the Local Deduction Theorem

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

## 8. A suggested reading order

1. [`MVAlgebra_scratch.lean`](MVAlgebra_scratch.lean) — see the class
   definition, the derived operators (`imp`, `odot`, `le`), and `residuation`
   in their cleanest form.
2. [`Soundness.lean`](Soundness.lean) up to and including `eval` — see the
   syntax/algebra bridge and the easy soundness cases like $\mathsf{id}$,
   $\mathsf{a2}$, $\mathsf{a3}$.
3. [`prop17.lean`](prop17.lean) — start with `mundici_prop17` (the most
   intricate single proof in the project), then `mvsup_lub` and the De Morgan
   laws, then `a6_key`.
4. Back to [`Soundness.lean`](Soundness.lean) for the $\mathsf{a}6$ case.
5. [`Equivalence.lean`](Equivalence.lean) and
   [`DeductionBL.lean`](DeductionBL.lean) as standalone reads.

Every theorem in the project can be inspected with

```lean
#print axioms <theorem_name>
```

which prints the **transitive closure** of axiom dependencies — a built-in
audit trail. The absence of `sorryAx` in that output is what distinguishes a
completed proof from one with an unfinished hole; the absence of
`Classical.choice` is what makes the proof constructive in the relevant sense.
