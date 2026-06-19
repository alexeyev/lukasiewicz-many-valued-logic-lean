/-
  Local Deduction Theorem over the BL basis — the wiring.

  This file ports the LDT scaffold from `Deduction.lean` onto the BL axiom
  system of `LukasiewiczBL.lean`, GENERALIZED to a theory `Γ`.  The point:
  the two lemmas that were irreducible `sorry`s under L1–L4 —

      * `sconj_intro`        (from `Γ⊢a`, `Γ⊢b` derive `Γ⊢a⊗b`)
      * `imp_sconjPow_one_self`  (`Γ ⊢ (a ⊗ (a⇒a)) ⇒ a`)

  — are now CLOSED, because in the BL basis they are short derivations
  (`a5b`+`id` and `a2` respectively), exactly as established in
  `LukasiewiczBL.lean`.  This is the concrete payoff of the re-axiomatization.

  The fusion crux `imp_sconj_fuse` is now CLOSED (proved from the syntactic
  exponent-combining step of the hard direction).  It is the one place that
  needs the residuation *bridge* to the algebra in `MVAlgebra.lean`; it is NOT a
  basis artifact, and is left as one honest, clearly-scoped `sorry`.

  Pure Lean 4 core — no imports, no Mathlib (theories are predicates, not Set).
  the file builds alone.  (Concatenate after `LukasiewiczBL.lean` and delete the
  restated block to share definitions.)
-/

namespace LukasiewiczBL.Deduction

/-! ## Syntax (BL, primitives `¬`,`→`; `&` defined) -/

abbrev Var := Nat

inductive Formula : Type
  | var : Var → Formula
  | neg : Formula → Formula
  | imp : Formula → Formula → Formula
  deriving DecidableEq

namespace Formula
scoped infixr:25 " ⇒ " => Formula.imp
scoped prefix:max "∼" => Formula.neg
/-- Strong conjunction `a ⊗ b := ∼(a ⇒ ∼b)` (matches `LukasiewiczBL.sconj`). -/
def sconj (a b : Formula) : Formula := ∼(a ⇒ ∼b)
scoped infixl:35 " ⊗ " => Formula.sconj
end Formula

open Formula

/-! ## Hypothetical BL provability (theory `Γ`)

The BL axioms `id, a1, a2, a3, a4, a5a, a5b, a6, a7, dn`, plus hypotheses from
`Γ`, plus modus ponens.  (Plain BL provability is `Γ = ∅`.)
-/

/-! ## Theories as predicates (pure-core replacement for `Set`) -/

/-- A theory is a predicate on formulas. -/
abbrev FSet := Formula → Prop
def mem (a : Formula) (Γ : FSet) : Prop := Γ a
infix:50 " ∈ᶠ " => mem
def subset (Γ Δ : FSet) : Prop := ∀ a, Γ a → Δ a
infix:50 " ⊆ᶠ " => subset
def insertF (a : Formula) (Γ : FSet) : FSet := fun x => x = a ∨ Γ x
theorem mem_insertF (a : Formula) (Γ : FSet) : a ∈ᶠ insertF a Γ := Or.inl rfl
theorem mem_insertF_iff (x a : Formula) (Γ : FSet) :
    (x ∈ᶠ insertF a Γ) ↔ (x = a ∨ x ∈ᶠ Γ) := Iff.rfl
theorem subset_insertF (a : Formula) (Γ : FSet) : Γ ⊆ᶠ insertF a Γ :=
  fun _ h => Or.inr h

/-- Hilbert-style provability from a finite set of hypotheses `Γ` in BL.
    `HProvable Γ a` means the formula `a` is derivable from the assumptions in `Γ`
    using the BL axioms and modus ponens. -/
inductive HProvable (Γ : FSet) : Formula → Prop
  | hyp {a : Formula}     : a ∈ᶠ Γ → HProvable Γ a
  | id (a : Formula)      : HProvable Γ (a ⇒ a)
  | a1 (a b c : Formula)  : HProvable Γ ((a ⇒ b) ⇒ ((b ⇒ c) ⇒ (a ⇒ c)))
  | a2 (a b : Formula)    : HProvable Γ ((a ⊗ b) ⇒ a)
  | a3 (a b : Formula)    : HProvable Γ ((a ⊗ b) ⇒ (b ⊗ a))
  | a4 (a b : Formula)    : HProvable Γ ((a ⊗ (a ⇒ b)) ⇒ (b ⊗ (b ⇒ a)))
  | a5a (a b c : Formula) : HProvable Γ ((a ⇒ (b ⇒ c)) ⇒ ((a ⊗ b) ⇒ c))
  | a5b (a b c : Formula) : HProvable Γ (((a ⊗ b) ⇒ c) ⇒ (a ⇒ (b ⇒ c)))
  | a6 (a b c : Formula)  : HProvable Γ (((a ⇒ b) ⇒ c) ⇒ (((b ⇒ a) ⇒ c) ⇒ c))
  | a7 (a b : Formula)    : HProvable Γ (∼(a ⇒ a) ⇒ b)
  | dn (a : Formula)      : HProvable Γ (∼∼a ⇒ a)
  | mp {a b : Formula}    : HProvable Γ (a ⇒ b) → HProvable Γ a → HProvable Γ b

@[inherit_doc] scoped notation:25 Γ " ⊢ " a => HProvable Γ a

/-- Monotonicity in the theory. -/
theorem HProvable.mono {Γ Δ : FSet} (h : Γ ⊆ᶠ Δ) :
    ∀ {a}, (Γ ⊢ a) → (Δ ⊢ a) := by
  intro a hpa
  induction hpa with
  | hyp hmem        => exact HProvable.hyp (h _ hmem)
  | id a            => exact HProvable.id a
  | a1 a b c        => exact HProvable.a1 a b c
  | a2 a b          => exact HProvable.a2 a b
  | a3 a b          => exact HProvable.a3 a b
  | a4 a b          => exact HProvable.a4 a b
  | a5a a b c       => exact HProvable.a5a a b c
  | a5b a b c       => exact HProvable.a5b a b c
  | a6 a b c        => exact HProvable.a6 a b c
  | a7 a b          => exact HProvable.a7 a b
  | dn a            => exact HProvable.dn a
  | mp _ _ ih₁ ih₂  => exact HProvable.mp ih₁ ih₂

/-! ## The lemmas that were stuck under L1–L4 — now closed -/

/-- ⊗-introduction schema: `Γ ⊢ a ⇒ (b ⇒ (a ⊗ b))`.  `a5b` applied to `id`. -/
theorem sconj_intro_imp (Γ : FSet) (a b : Formula) :
    Γ ⊢ (a ⇒ (b ⇒ (a ⊗ b))) :=
  HProvable.mp (HProvable.a5b a b (a ⊗ b)) (HProvable.id (a ⊗ b))

/-- **`sconj_intro`** (was a `sorry` under L1–L4): from `Γ⊢a`, `Γ⊢b`, get
    `Γ⊢a⊗b`.  Two modus ponens. -/
theorem sconj_intro {Γ : FSet} {a b : Formula}
    (ha : Γ ⊢ a) (hb : Γ ⊢ b) : Γ ⊢ (a ⊗ b) :=
  HProvable.mp (HProvable.mp (sconj_intro_imp Γ a b) ha) hb

/-- HS via `a1`. -/
theorem hs {Γ : FSet} {a b c : Formula}
    (h₁ : Γ ⊢ (a ⇒ b)) (h₂ : Γ ⊢ (b ⇒ c)) : Γ ⊢ (a ⇒ c) :=
  HProvable.mp (HProvable.mp (HProvable.a1 a b c) h₁) h₂

/-! ## Iterated strong conjunction and the LDT scaffold -/

def sconjPow (a : Formula) : Nat → Formula
  | 0     => a ⇒ a
  | n + 1 => a ⊗ sconjPow a n

@[simp] theorem sconjPow_zero (a : Formula) : sconjPow a 0 = (a ⇒ a) := rfl
@[simp] theorem sconjPow_succ (a : Formula) (n : Nat) :
    sconjPow a (n + 1) = (a ⊗ sconjPow a n) := rfl

/-! ### Combinators and ⊗-structure for the fusion crux -/

/-- Antecedent exchange (C-combinator), via residuation + a3. -/
theorem comm (x y z : Formula) : Γ ⊢ ((x ⇒ (y ⇒ z)) ⇒ (y ⇒ (x ⇒ z))) := by
  have s1 : Γ ⊢ ((x ⇒ (y ⇒ z)) ⇒ ((x ⊗ y) ⇒ z)) := HProvable.a5a x y z
  have s2 : Γ ⊢ (((x ⊗ y) ⇒ z) ⇒ ((y ⊗ x) ⇒ z)) :=
    HProvable.mp (HProvable.a1 (y ⊗ x) (x ⊗ y) z) (HProvable.a3 y x)
  exact hs s1 (hs s2 (HProvable.a5b y x z))

/-- Composition as an implication (B-combinator). -/
theorem comp_imp (Γ : FSet) (w p q : Formula) :
    Γ ⊢ ((p ⇒ q) ⇒ ((w ⇒ p) ⇒ (w ⇒ q))) :=
  HProvable.mp (comm (w⇒p) (p⇒q) (w⇒q)) (HProvable.a1 w p q)

/-- `⊗` is monotone in its right argument. -/
theorem sconj_mono_right (Γ : FSet) (p q c : Formula) (h : Γ ⊢ (q ⇒ c)) :
    Γ ⊢ ((p ⊗ q) ⇒ (p ⊗ c)) := by
  have hintro : Γ ⊢ (p ⇒ (c ⇒ (p ⊗ c))) := sconj_intro_imp Γ p c
  have e1 : Γ ⊢ (c ⇒ (p ⇒ (p ⊗ c))) := HProvable.mp (comm p c (p ⊗ c)) hintro
  have e3 : Γ ⊢ (p ⇒ (q ⇒ (p ⊗ c))) := HProvable.mp (comm q p (p ⊗ c)) (hs h e1)
  exact HProvable.mp (HProvable.a5a p q (p ⊗ c)) e3

/-- `⊗` associativity (one direction): `(x⊗y)⊗z ⇒ x⊗(y⊗z)`. -/
theorem sconj_assoc_imp (Γ : FSet) (x y z : Formula) :
    Γ ⊢ (((x ⊗ y) ⊗ z) ⇒ (x ⊗ (y ⊗ z))) := by
  apply HProvable.mp (HProvable.a5a (x⊗y) z (x ⊗ (y ⊗ z)))
  apply HProvable.mp (HProvable.a5a x y (z ⇒ (x ⊗ (y ⊗ z))))
  have i1 : Γ ⊢ (y ⇒ (z ⇒ (y ⊗ z))) := sconj_intro_imp Γ y z
  have i2 : Γ ⊢ (x ⇒ ((y ⊗ z) ⇒ (x ⊗ (y ⊗ z)))) := sconj_intro_imp Γ x (y ⊗ z)
  have m1 : Γ ⊢ (((y⊗z) ⇒ (x⊗(y⊗z))) ⇒ ((z ⇒ (y⊗z)) ⇒ (z ⇒ (x⊗(y⊗z))))) :=
    comp_imp Γ z (y⊗z) (x⊗(y⊗z))
  have m2 : Γ ⊢ (((z ⇒ (y⊗z)) ⇒ (z ⇒ (x⊗(y⊗z)))) ⇒ (y ⇒ (z ⇒ (x⊗(y⊗z))))) :=
    HProvable.mp (HProvable.a1 y (z ⇒ (y⊗z)) (z ⇒ (x⊗(y⊗z)))) i1
  exact hs i2 (hs m1 m2)

/-- Base-case helper: `x ⇒ (x ⊗ (a⇒a))` (right-multiply by the top element). -/
theorem imp_sconj_top (Γ : FSet) (x a : Formula) : Γ ⊢ (x ⇒ (x ⊗ (a ⇒ a))) := by
  have base : Γ ⊢ (x ⇒ ((a ⇒ a) ⇒ (x ⊗ (a ⇒ a)))) := sconj_intro_imp Γ x (a ⇒ a)
  exact HProvable.mp (HProvable.mp (comm x (a⇒a) (x ⊗ (a⇒a))) base) (HProvable.id a)

/-- Splitting: `Γ ⊢ aⁿ⁺ᵐ ⇒ (aⁿ ⊗ aᵐ)`, by induction on `m`. -/
theorem sconjPow_add_imp (Γ : FSet) (a : Formula) (n m : Nat) :
    Γ ⊢ (sconjPow a (n + m) ⇒ (sconjPow a n ⊗ sconjPow a m)) := by
  induction m with
  | zero => exact imp_sconj_top Γ (sconjPow a n) a
  | succ k ih =>
      show Γ ⊢ ((a ⊗ sconjPow a (n + k)) ⇒ (sconjPow a n ⊗ (a ⊗ sconjPow a k)))
      have s1 : Γ ⊢ ((a ⊗ sconjPow a (n + k)) ⇒ (a ⊗ (sconjPow a n ⊗ sconjPow a k))) :=
        sconj_mono_right Γ a (sconjPow a (n + k)) (sconjPow a n ⊗ sconjPow a k) ih
      have s2 : Γ ⊢ ((a ⊗ (sconjPow a n ⊗ sconjPow a k)) ⇒ ((sconjPow a n ⊗ sconjPow a k) ⊗ a)) :=
        HProvable.a3 a (sconjPow a n ⊗ sconjPow a k)
      have s3 : Γ ⊢ (((sconjPow a n ⊗ sconjPow a k) ⊗ a) ⇒ (sconjPow a n ⊗ (sconjPow a k ⊗ a))) :=
        sconj_assoc_imp Γ (sconjPow a n) (sconjPow a k) a
      have s4 : Γ ⊢ ((sconjPow a n ⊗ (sconjPow a k ⊗ a)) ⇒ (sconjPow a n ⊗ (a ⊗ sconjPow a k))) :=
        sconj_mono_right Γ (sconjPow a n) (sconjPow a k ⊗ a) (a ⊗ sconjPow a k) (HProvable.a3 (sconjPow a k) a)
      exact hs s1 (hs s2 (hs s3 s4))

/-- Residuation bridge: from `Γ ⊢ p ⇒ (c ⇒ b)` get `Γ ⊢ (p ⊗ c) ⇒ b`. -/
theorem imp_to_sconj (Γ : FSet) (p c b : Formula) (h : Γ ⊢ (p ⇒ (c ⇒ b))) :
    Γ ⊢ ((p ⊗ c) ⇒ b) :=
  HProvable.mp (HProvable.a5a p c b) h

/-- From `a` as a hypothesis, every power `aⁿ` is provable.  Uses the now-closed
    `sconj_intro` at the successor step (the step that was blocked under L1–L4). -/
theorem hyp_sconjPow (Γ : FSet) (a : Formula) :
    ∀ n, (insertF a Γ ⊢ sconjPow a n) := by
  intro n
  induction n with
  | zero => simpa using HProvable.id (a := a) (Γ := insertF a Γ)
  | succ n ih =>
      have ha : insertF a Γ ⊢ a := HProvable.hyp (mem_insertF _ _)
      simpa using sconj_intro ha ih

/-- **`imp_sconjPow_one_self`** (was a `sorry` under L1–L4): `Γ ⊢ a¹ ⇒ a`.
    `a¹ = a ⊗ (a⇒a)`, so this is exactly the `a2` instance `(a ⊗ (a⇒a)) ⇒ a`. -/
theorem imp_sconjPow_one_self (Γ : FSet) (a : Formula) :
    Γ ⊢ (sconjPow a 1 ⇒ a) := by
  simpa using HProvable.a2 a (a ⇒ a)

/-- Weakening schema `Γ ⊢ b ⇒ (c ⇒ b)` (the `K` combinator), derived in BL.
    From `a2 : (b ⊗ c) ⇒ b` and `a5b : ((b⊗c)⇒b) ⇒ (b⇒(c⇒b))` by one `mp`. -/
theorem weaken_imp (Γ : FSet) (b c : Formula) : Γ ⊢ (b ⇒ (c ⇒ b)) :=
  HProvable.mp (HProvable.a5b b c b) (HProvable.a2 b c)

/-- Weakening to a power: from `Γ ⊢ b`, get `Γ ⊢ aⁿ ⇒ b`. -/
theorem imp_sconjPow_of_provable (Γ : FSet) (a b : Formula)
    (h : Γ ⊢ b) (n : Nat) : Γ ⊢ (sconjPow a n ⇒ b) := by
  -- weakening: from b derive (anything ⇒ b). In BL: a1-route or a2/a5.
  -- Use the K-schema derived from a5b+a2: ⊢ b ⇒ (c ⇒ b)? We need that weakening.
  -- Cleanest: from id and a5: but simplest is to prove the weakening schema once.
  exact HProvable.mp (weaken_imp Γ b (sconjPow a n)) h

/-! ## Easy direction (⇐) — now fully closed (no `sorry`) -/

theorem ldt_mpr (Γ : FSet) (a b : Formula)
    (h : ∃ n, Γ ⊢ (sconjPow a n ⇒ b)) : insertF a Γ ⊢ b := by
  obtain ⟨n, hn⟩ := h
  have hpow : insertF a Γ ⊢ sconjPow a n := hyp_sconjPow Γ a n
  have hn'  : insertF a Γ ⊢ (sconjPow a n ⇒ b) :=
    HProvable.mono (subset_insertF _ _) hn
  exact HProvable.mp hn' hpow

/-! ## Hard direction (⇒)

Structure complete and fully proved — no sorry.
-/

/-- ⊗-fusion / exponent-combining — THE crux.  From `aⁿ ⇒ (c⇒b)` and `aᵐ ⇒ c`,
    produce `a^k ⇒ b` for suitable `k`.  This is where the algebraic residuation
    of `MVAlgebra.lean` is needed (the syntactic ⊗-assoc/comm + residuation
    bridge).  The ONE honest, clearly-scoped open goal. -/
theorem imp_sconj_fuse (Γ : FSet) (a b c : Formula) (n m : Nat)
    (h₁ : Γ ⊢ (sconjPow a n ⇒ (c ⇒ b)))
    (h₂ : Γ ⊢ (sconjPow a m ⇒ c)) :
    ∃ k, Γ ⊢ (sconjPow a k ⇒ b) := by
  refine ⟨n + m, ?_⟩
  have split := sconjPow_add_imp Γ a n m
  have step1 : Γ ⊢ ((sconjPow a n ⊗ c) ⇒ b) := imp_to_sconj Γ _ c b h₁
  have step2 : Γ ⊢ ((sconjPow a n ⊗ sconjPow a m) ⇒ (sconjPow a n ⊗ c)) :=
    sconj_mono_right Γ (sconjPow a n) (sconjPow a m) c h₂
  exact hs split (hs step2 step1)

/-- **Hard direction of the LDT.**  All cases closed except the `mp` case's
    appeal to the crux `imp_sconj_fuse`. -/
theorem ldt_mp (Γ : FSet) (a b : Formula)
    (h : insertF a Γ ⊢ b) : ∃ n, Γ ⊢ (sconjPow a n ⇒ b) := by
  induction h with
  | @hyp c hmem =>
      rw [mem_insertF_iff] at hmem
      rcases hmem with hc | hc
      · subst hc; exact ⟨1, imp_sconjPow_one_self Γ c⟩
      · exact ⟨0, imp_sconjPow_of_provable Γ a c (HProvable.hyp hc) 0⟩
  | id c        => exact ⟨0, imp_sconjPow_of_provable Γ a _ (HProvable.id c) 0⟩
  | a1 c d e    => exact ⟨0, imp_sconjPow_of_provable Γ a _ (HProvable.a1 c d e) 0⟩
  | a2 c d      => exact ⟨0, imp_sconjPow_of_provable Γ a _ (HProvable.a2 c d) 0⟩
  | a3 c d      => exact ⟨0, imp_sconjPow_of_provable Γ a _ (HProvable.a3 c d) 0⟩
  | a4 c d      => exact ⟨0, imp_sconjPow_of_provable Γ a _ (HProvable.a4 c d) 0⟩
  | a5a c d e   => exact ⟨0, imp_sconjPow_of_provable Γ a _ (HProvable.a5a c d e) 0⟩
  | a5b c d e   => exact ⟨0, imp_sconjPow_of_provable Γ a _ (HProvable.a5b c d e) 0⟩
  | a6 c d e    => exact ⟨0, imp_sconjPow_of_provable Γ a _ (HProvable.a6 c d e) 0⟩
  | a7 c d      => exact ⟨0, imp_sconjPow_of_provable Γ a _ (HProvable.a7 c d) 0⟩
  | dn c        => exact ⟨0, imp_sconjPow_of_provable Γ a _ (HProvable.dn c) 0⟩
  | @mp c d _hcd _hc ihcd ihc =>
      obtain ⟨n, hn⟩ := ihcd
      obtain ⟨m, hm⟩ := ihc
      exact imp_sconj_fuse Γ a d c n m hn hm

/-- **Local Deduction Theorem (BL basis).**  Both directions; the forward
    direction is gated only on the crux `imp_sconj_fuse`. -/
theorem localDeductionTheorem (Γ : FSet) (a b : Formula) :
    (insertF a Γ ⊢ b) ↔ ∃ n, Γ ⊢ (sconjPow a n ⇒ b) :=
  ⟨ldt_mp Γ a b, fun h => ldt_mpr Γ a b h⟩

end LukasiewiczBL.Deduction
