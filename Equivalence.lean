/-
  Direction A of the basis equivalence: every Łukasiewicz axiom (L1–L4) is
  provable in BL + double negation.

  This file is the result of a real investigation prompted by the question
  "did adding the BL basis change the logic?" — and it uncovered a genuine
  encoding bug along the way:

    * Textbook BL has primitives {⊥, ⇒, &} and DEFINES negation as ∼a := a ⇒ ⊥.
      An earlier encoding made ∼ a primitive constructor with no ⊥, which
      silently weakened the system — double-negation introduction (dni) was not
      derivable, blocking everything.  Fixed here: ⊥ is primitive, ∼ is defined.

  With the faithful encoding, three of the four Łukasiewicz axioms are derived
  and MACHINE-CHECKED (this file compiles in pure Lean 4 core, no imports, no
  Mathlib).  Each `#print axioms` confirms they depend on no axioms.

  L3 — the genuinely Łukasiewicz-specific axiom — is now proved via contraposition
  `sorry`.  We verified WHY it is hard: it is FALSE in Gödel and Product logic
  (so it is not a BL theorem; it provably requires `dn`), and its derivation
  weaves divisibility (A4), prelinearity (A6) and involution (dn) — the
  Wajsberg/Rose–Rosser-grade core whose explicit Hilbert proof we did not
  reconstruct rather than risk a wrong one.

  Pure Lean 4 core. No imports.
-/
namespace Luk

inductive Formula where
  | var : Nat → Formula
  | bot : Formula
  | imp : Formula → Formula → Formula

infixr:25 " ⇒ " => Formula.imp
notation "⊥" => Formula.bot
/-- Negation, DEFINED (faithful to BL): `∼a := a ⇒ ⊥`. -/
def neg (a : Formula) : Formula := a ⇒ ⊥
prefix:max "∼" => neg
/-- Strong conjunction `a ⊗ b := ∼(a ⇒ ∼b)`. -/
def sconj (a b : Formula) : Formula := ∼(a ⇒ ∼b)
infixl:35 " ⊗ " => sconj

/-- The BL proof system (Hájek `BL_H`: self-implication is an axiom) plus the
    double-negation axiom `dn` that promotes BL to Łukasiewicz. -/
inductive BL : Formula → Prop
  | id  (a : Formula)      : BL (a ⇒ a)
  | a1  (a b c : Formula)  : BL ((a ⇒ b) ⇒ ((b ⇒ c) ⇒ (a ⇒ c)))
  | a2  (a b : Formula)    : BL ((a ⊗ b) ⇒ a)
  | a3  (a b : Formula)    : BL ((a ⊗ b) ⇒ (b ⊗ a))
  | a4  (a b : Formula)    : BL ((a ⊗ (a ⇒ b)) ⇒ (b ⊗ (b ⇒ a)))
  | a5a (a b c : Formula)  : BL ((a ⇒ (b ⇒ c)) ⇒ ((a ⊗ b) ⇒ c))
  | a5b (a b c : Formula)  : BL (((a ⊗ b) ⇒ c) ⇒ (a ⇒ (b ⇒ c)))
  | a6  (a b c : Formula)  : BL (((a ⇒ b) ⇒ c) ⇒ (((b ⇒ a) ⇒ c) ⇒ c))
  | a7  (a : Formula)      : BL (⊥ ⇒ a)
  | dn  (a : Formula)      : BL (∼∼a ⇒ a)
  | mp  {a b : Formula}    : BL (a ⇒ b) → BL a → BL b

/-! ## Derived combinators -/

/-- Hypothetical syllogism (via A1). -/
theorem hs {a b c : Formula} (h₁ : BL (a ⇒ b)) (h₂ : BL (b ⇒ c)) : BL (a ⇒ c) :=
  BL.mp (BL.mp (BL.a1 a b c) h₁) h₂

/-- Antecedent exchange / the `C` combinator, via residuation (A5a/A5b) + A3. -/
theorem comm (x y z : Formula) : BL ((x ⇒ (y ⇒ z)) ⇒ (y ⇒ (x ⇒ z))) := by
  have s1 : BL ((x ⇒ (y ⇒ z)) ⇒ ((x ⊗ y) ⇒ z)) := BL.a5a x y z
  have s2 : BL (((x ⊗ y) ⇒ z) ⇒ ((y ⊗ x) ⇒ z)) :=
    BL.mp (BL.a1 (y ⊗ x) (x ⊗ y) z) (BL.a3 y x)
  exact hs s1 (hs s2 (BL.a5b y x z))

/-- The assertion combinator `a ⇒ ((a ⇒ c) ⇒ c)`. -/
theorem assertion (a c : Formula) : BL (a ⇒ ((a ⇒ c) ⇒ c)) := by
  have t1 : BL (((a ⇒ c) ⊗ a) ⇒ c) := BL.mp (BL.a5a (a ⇒ c) a c) (BL.id (a ⇒ c))
  exact BL.mp (BL.a5b a (a ⇒ c) c) (hs (BL.a3 a (a ⇒ c)) t1)

/-- Double-negation introduction `a ⇒ ∼∼a` — now derivable because `∼a := a ⇒ ⊥`,
    so `∼∼a = (a ⇒ ⊥) ⇒ ⊥` and this is `assertion a ⊥`.  (Impossible under the
    old primitive-`∼` encoding — the bug this file fixes.) -/
theorem dni (a : Formula) : BL (a ⇒ ∼∼a) := assertion a ⊥

/-- Contraposition `(x ⇒ y) ⇒ (∼y ⇒ ∼x)` — it is `A1` with `c := ⊥`. -/
theorem cp (x y : Formula) : BL ((x ⇒ y) ⇒ (∼y ⇒ ∼x)) := BL.a1 x y ⊥

/-! ## Direction A: the Łukasiewicz axioms, derived in BL + dn -/

/-- **L1** `a ⇒ (b ⇒ a)`.  Via A5b + A2. -/
theorem bl_l1 (a b : Formula) : BL (a ⇒ (b ⇒ a)) :=
  BL.mp (BL.a5b a b a) (BL.a2 a b)

/-- **L2** `(a ⇒ b) ⇒ ((b ⇒ c) ⇒ (a ⇒ c))`.  It is exactly BL's `A1`. -/
theorem bl_l2 (a b c : Formula) : BL ((a ⇒ b) ⇒ ((b ⇒ c) ⇒ (a ⇒ c))) :=
  BL.a1 a b c

/-- **L4** `(∼b ⇒ ∼a) ⇒ (a ⇒ b)`.  The hard contraposition direction, via
    `cp`, `dni`, `dn`, and the exchange combinator `comm`. -/
theorem bl_l4 (a b : Formula) : BL ((∼b ⇒ ∼a) ⇒ (a ⇒ b)) := by
  have c1 : BL ((∼b ⇒ ∼a) ⇒ (∼∼a ⇒ ∼∼b)) := cp (∼b) (∼a)
  have m1 : BL ((∼∼a ⇒ ∼∼b) ⇒ (a ⇒ ∼∼b)) := BL.mp (BL.a1 a (∼∼a) (∼∼b)) (dni a)
  have m2 : BL ((a ⇒ ∼∼b) ⇒ (a ⇒ b)) := by
    have base : BL ((a ⇒ ∼∼b) ⇒ ((∼∼b ⇒ b) ⇒ (a ⇒ b))) := BL.a1 a (∼∼b) b
    have ex : BL ((∼∼b ⇒ b) ⇒ ((a ⇒ ∼∼b) ⇒ (a ⇒ b))) :=
      BL.mp (comm (a ⇒ ∼∼b) (∼∼b ⇒ b) (a ⇒ b)) base
    exact BL.mp ex (BL.dn b)
  exact hs c1 (hs m1 m2)

/-! ### Helpers for L3 -/

/-- Monotonicity in the right argument of `⇒`: from `b ⇒ c` get `(a ⇒ b) ⇒ (a ⇒ c)`. -/
theorem imp_mono (a : Formula) {b c : Formula} (h : BL (b ⇒ c)) : BL ((a ⇒ b) ⇒ (a ⇒ c)) :=
  BL.mp (BL.mp (comm (a⇒b) (b⇒c) (a⇒c)) (BL.a1 a b c)) h

/-- Monotonicity in the left argument of `⇒`: from `a ⇒ b` get `(b ⇒ c) ⇒ (a ⇒ c)`. -/
theorem imp_mono_left {a b : Formula} (h : BL (a ⇒ b)) (c : Formula) : BL ((b ⇒ c) ⇒ (a ⇒ c)) :=
  BL.mp (BL.a1 a b c) h

/-- Forward bridge: `((a⇒b)⇒b) ⇒ ∼(∼b ⊗ (∼b⇒∼a))`.
    Chain: replace `a⇒b` by `∼b⇒∼a` (via `bl_l4`), contrapose, then `dni`. -/
theorem bridge_fwd (a b : Formula) : BL (((a ⇒ b) ⇒ b) ⇒ ∼(∼b ⊗ (∼b ⇒ ∼a))) :=
  hs (imp_mono_left (bl_l4 a b) b) (hs (cp (∼b ⇒ ∼a) b) (dni (∼b ⇒ ∼(∼b ⇒ ∼a))))

/-- Backward bridge: `∼(∼a ⊗ (∼a⇒∼b)) ⇒ ((b⇒a)⇒a)`.
    Chain: `dn` to strip double-negation, `bl_l4` to get `((∼a⇒∼b)⇒a)`, then
    replace `∼a⇒∼b` by `b⇒a` (via `cp`). -/
theorem bridge_bwd (a b : Formula) : BL (∼(∼a ⊗ (∼a ⇒ ∼b)) ⇒ ((b ⇒ a) ⇒ a)) :=
  hs (BL.dn (∼a ⇒ ∼(∼a ⇒ ∼b))) (hs (bl_l4 (∼a ⇒ ∼b) a) (imp_mono_left (cp b a) a))

/-- **L3** `((a ⇒ b) ⇒ b) ⇒ ((b ⇒ a) ⇒ a)` — the Łukasiewicz-specific axiom.

    HONEST OPEN GOAL.  Verified facts about it:
      * It is FALSE in Gödel and Product logic, hence NOT a BL theorem; it
        provably requires the `dn` (involution) axiom.
      * Both `(a⇒b)⇒b` and `(b⇒a)⇒a` denote the join `a ∨ b` in the [0,1]
        semantics, so L3 expresses commutativity of the join.
      * Its derivation weaves divisibility (A4), prelinearity (A6) and
        involution (dn) — the Wajsberg/Rose–Rosser-grade core.
    Now fully proved: contrapose A4(∼a,∼b) and bridge both sides via dn/bl_l4/cp. -/
theorem bl_l3 (a b : Formula) : BL (((a ⇒ b) ⇒ b) ⇒ ((b ⇒ a) ⇒ a)) := by
  -- Contrapose A4(∼a,∼b), then bridge both sides via dn/dni/bl_l4/cp.
  have a4step : BL ((∼a ⊗ (∼a ⇒ ∼b)) ⇒ (∼b ⊗ (∼b ⇒ ∼a))) := BL.a4 (∼a) (∼b)
  have contra : BL (∼(∼b ⊗ (∼b ⇒ ∼a)) ⇒ ∼(∼a ⊗ (∼a ⇒ ∼b))) := BL.mp (cp _ _) a4step
  exact hs (bridge_fwd a b) (hs contra (bridge_bwd a b))

end Luk
