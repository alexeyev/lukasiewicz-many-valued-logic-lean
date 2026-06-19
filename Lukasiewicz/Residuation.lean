/-
  MV-algebras and residuation.

  Every derived identity below was cross-checked numerically against the
  standard [0,1] model (neg x = 1-x, x ⊞ y = min 1 (x+y)) before being written.
  Cross-checking is NOT proof — only `lake build` is — but it caught several
  wrong-axiom-application errors during development.  Proofs follow Mundici,
  "Introducing MV-algebras", Ch. 1.

  PROVED: MV7, MV9, reflexivity, antisymmetry, Lemma 1.2 (i)↔(ii),
  `le_oplus_right`, `odot_neg_oplus`, the keystone `residuation`, `odot_imp_le`.

  `le_of_sup_eq` (the join⟹order converse) is now PROVED, via the supporting
  lemmas `odot_self_disjoint`, `le_neg_odot` and `oplus_odot_neg` (Lemma C).
  No distance function or cancellation axiom is needed — the chain routes through
  `sup_eq_of_le` applied to an always-true order fact.  The file is `sorry`-free.
-/
-- Pure Lean 4 core — no imports, no Mathlib.

namespace MV

class MVAlgebra (A : Type _) where
  oplus : A → A → A
  neg   : A → A
  zero  : A
  oplus_assoc   : ∀ x y z, oplus (oplus x y) z = oplus x (oplus y z)
  oplus_comm    : ∀ x y, oplus x y = oplus y x
  oplus_zero    : ∀ x, oplus x zero = x
  neg_neg       : ∀ x, neg (neg x) = x
  oplus_negzero : ∀ x, oplus x (neg zero) = neg zero
  mv_axiom      : ∀ x y, oplus (neg (oplus (neg x) y)) y
                       = oplus (neg (oplus (neg y) x)) x

namespace MVAlgebra
variable {A : Type _} [MVAlgebra A]

scoped infixl:65 " ⊞ " => MVAlgebra.oplus
scoped prefix:max "¬ᴹ" => MVAlgebra.neg

def one : A := ¬ᴹ (zero : A)
scoped notation "𝟙" => MVAlgebra.one
scoped notation "𝟘" => MVAlgebra.zero

def odot (x y : A) : A := ¬ᴹ ((¬ᴹ x) ⊞ (¬ᴹ y))
scoped infixl:70 " ⊙ " => MVAlgebra.odot

def imp (x y : A) : A := (¬ᴹ x) ⊞ y
scoped infixr:60 " ⇨ " => MVAlgebra.imp

def le (x y : A) : Prop := (x ⇨ y) = (𝟙 : A)
scoped infix:50 " ≤ᴹ " => MVAlgebra.le

@[simp] theorem neg_zero_eq_one : ¬ᴹ (𝟘 : A) = 𝟙 := rfl

@[simp] theorem neg_one_eq_zero : ¬ᴹ (𝟙 : A) = 𝟘 := by
  show ¬ᴹ (¬ᴹ (𝟘 : A)) = 𝟘
  rw [MVAlgebra.neg_neg]

@[simp] theorem MVAlgebra.oplus_zero' (x : A) : x ⊞ 𝟘 = x := MVAlgebra.oplus_zero x
@[simp] theorem zero_oplus (x : A) : (𝟘 : A) ⊞ x = x := by
  rw [MVAlgebra.oplus_comm]; exact MVAlgebra.oplus_zero x

@[simp] theorem oplus_one (x : A) : x ⊞ 𝟙 = (𝟙 : A) := MVAlgebra.oplus_negzero x
@[simp] theorem one_oplus (x : A) : (𝟙 : A) ⊞ x = (𝟙 : A) := by
  rw [MVAlgebra.oplus_comm]; exact MVAlgebra.oplus_negzero x

/-- MV9, `¬x ⊞ x = 1`.  From MV6 at `y := 1`.  Proved without `simp` so the
    axiom audit stays clean (MV9 is a dependency of `residuation`). -/
theorem neg_oplus_self (x : A) : (¬ᴹ x) ⊞ x = (𝟙 : A) := by
  have h := MVAlgebra.mv_axiom x (𝟙 : A)
  simp only [oplus_one, neg_one_eq_zero, zero_oplus] at h
  exact h.symm

@[simp] theorem imp_self (x : A) : (x ⇨ x) = (𝟙 : A) := neg_oplus_self x

theorem le_refl (x : A) : x ≤ᴹ x := imp_self x

/-- `a ≤ᴹ a ⊞ b`: `¬a ⊞ (a ⊞ b) = (¬a ⊞ a) ⊞ b = 1 ⊞ b = 1`. -/
theorem le_oplus_right (a b : A) : a ≤ᴹ (a ⊞ b) := by
  unfold le imp
  rw [← MVAlgebra.oplus_assoc, neg_oplus_self, one_oplus]

theorem odot_neg (x y : A) : x ⊙ (¬ᴹ y) = ¬ᴹ ((¬ᴹ x) ⊞ y) := by
  unfold odot; rw [MVAlgebra.neg_neg]

/-- Lemma 1.2, (i) ↔ (ii). -/
theorem le_iff_odot_neg_eq_zero (x y : A) :
    (x ≤ᴹ y) ↔ (x ⊙ (¬ᴹ y) = (𝟘 : A)) := by
  unfold le imp
  rw [odot_neg]
  constructor
  · intro h; rw [h]; exact neg_one_eq_zero
  · intro h
    have : ¬ᴹ (¬ᴹ ((¬ᴹ x) ⊞ y)) = ¬ᴹ (𝟘 : A) := by rw [h]
    rwa [MVAlgebra.neg_neg, neg_zero_eq_one] at this

/-- General identity `a ⊙ ¬(a ⊞ b) = 0` (since `a ≤ᴹ a ⊞ b`). -/
theorem odot_neg_oplus (a b : A) : a ⊙ (¬ᴹ (a ⊞ b)) = (𝟘 : A) :=
  (le_iff_odot_neg_eq_zero a (a ⊞ b)).mp (le_oplus_right a b)

def sup (x y : A) : A := (¬ᴹ ((¬ᴹ x) ⊞ y)) ⊞ y
scoped infixl:68 " ⊔ᴹ " => MVAlgebra.sup

theorem sup_comm (x y : A) : x ⊔ᴹ y = y ⊔ᴹ x := MVAlgebra.mv_axiom x y

theorem sup_eq_of_le {x y : A} (h : x ≤ᴹ y) : x ⊔ᴹ y = y := by
  unfold sup
  have hh : (¬ᴹ x) ⊞ y = (𝟙 : A) := h
  rw [hh, neg_one_eq_zero, zero_oplus]

/-- `¬(x ⊙ ¬y) = ¬x ⊞ y`. -/
theorem neg_odot_neg (x y : A) : ¬ᴹ (x ⊙ (¬ᴹ y)) = (¬ᴹ x) ⊞ y := by
  unfold odot; rw [MVAlgebra.neg_neg, MVAlgebra.neg_neg]

/-- `y ≤ᴹ ¬(x ⊙ ¬y)` — always true: `¬y ⊞ (¬x ⊞ y) = ¬x ⊞ 1 = 1`. -/
theorem le_neg_odot (x y : A) : y ≤ᴹ (¬ᴹ (x ⊙ (¬ᴹ y))) := by
  unfold le imp
  rw [neg_odot_neg]
  -- goal: ¬y ⊞ (¬x ⊞ y) = 1
  rw [← MVAlgebra.oplus_assoc, MVAlgebra.oplus_comm (¬ᴹ y) (¬ᴹ x), MVAlgebra.oplus_assoc, neg_oplus_self, oplus_one]

/-- `(x ⊙ ¬y) ⊙ y = 0` (disjointness) — `¬a ⊞ ¬y = ¬x ⊞ (y ⊞ ¬y) = 1` with `a := x⊙¬y`. -/
theorem odot_self_disjoint (x y : A) : (x ⊙ (¬ᴹ y)) ⊙ y = (𝟘 : A) := by
  -- (a ⊙ y = 0) ↔ a ≤ᴹ ¬y, via le_iff_odot_neg with `¬¬y = y`.
  have hle : (x ⊙ (¬ᴹ y)) ≤ᴹ (¬ᴹ y) := by
    -- a ≤ᴹ ¬y  is  ¬a ⊞ ¬y = 1
    unfold le imp
    rw [neg_odot_neg]
    -- goal: (¬x ⊞ y) ⊞ ¬y = 1
    rw [MVAlgebra.oplus_assoc, MVAlgebra.oplus_comm y (¬ᴹ y), neg_oplus_self, oplus_one]
  have := (le_iff_odot_neg_eq_zero (x ⊙ (¬ᴹ y)) (¬ᴹ y)).mp hle
  rwa [MVAlgebra.neg_neg] at this

/-- Lemma C: `(a ⊞ y) ⊙ ¬y = a` where `a := x ⊙ ¬y`.
    Equivalently `¬((a⊞y)⊙¬y) = ¬a`, i.e. `sup(¬a, y) = ¬a`, from `y ≤ᴹ ¬a`. -/
theorem oplus_odot_neg_aux (a y : A) (hy_le : y ≤ᴹ (¬ᴹ a)) :
    (((a ⊞ y) ⊙ (¬ᴹ y)) = a) := by
  have hsup : (¬ᴹ a) ⊔ᴹ y = (¬ᴹ a) := by
    rw [sup_comm]; exact sup_eq_of_le hy_le
  unfold sup at hsup
  rw [MVAlgebra.neg_neg] at hsup
  rw [odot_neg]
  rw [hsup, MVAlgebra.neg_neg]

theorem oplus_odot_neg (x y : A) :
    (((x ⊙ (¬ᴹ y)) ⊞ y) ⊙ (¬ᴹ y)) = x ⊙ (¬ᴹ y) :=
  oplus_odot_neg_aux (x ⊙ (¬ᴹ y)) y (le_neg_odot x y)

/-- **Converse**, fully proved. -/
theorem le_of_sup_eq {x y : A} (h : x ⊔ᴹ y = y) : x ≤ᴹ y := by
  rw [le_iff_odot_neg_eq_zero]
  have hay : (x ⊙ (¬ᴹ y)) ⊞ y = y := by
    have hh := h
    unfold sup at hh
    rw [← odot_neg] at hh
    exact hh
  have hC : (((x ⊙ (¬ᴹ y)) ⊞ y) ⊙ (¬ᴹ y)) = x ⊙ (¬ᴹ y) := oplus_odot_neg x y
  rw [hay] at hC
  have hyy : y ⊙ (¬ᴹ y) = (𝟘 : A) := by
    rw [odot, MVAlgebra.neg_neg, neg_oplus_self, neg_one_eq_zero]
  rw [hyy] at hC
  exact hC.symm

theorem le_iff_sup_eq (x y : A) : (x ≤ᴹ y) ↔ (x ⊔ᴹ y = y) :=
  ⟨sup_eq_of_le, le_of_sup_eq⟩

/-- Antisymmetry — uses only the PROVED `sup_eq_of_le` and `sup_comm`. -/
theorem le_antisymm {x y : A} (hxy : x ≤ᴹ y) (hyx : y ≤ᴹ x) : x = y := by
  have h1 := sup_eq_of_le hxy
  have h2 := sup_eq_of_le hyx
  calc x = y ⊔ᴹ x := h2.symm
    _ = x ⊔ᴹ y := sup_comm y x
    _ = y := h1

theorem neg_odot (x z : A) : ¬ᴹ (x ⊙ z) = (¬ᴹ x) ⊞ (¬ᴹ z) := by
  unfold odot; rw [MVAlgebra.neg_neg]

/-- **Residuation / adjunction** — fully proved. -/
theorem residuation (x y z : A) :
    (x ⊙ z) ≤ᴹ y ↔ z ≤ᴹ (x ⇨ y) := by
  unfold le imp
  -- goal: ¬(x⊙z) ⊞ y = 1  ↔  ¬z ⊞ (¬x ⊞ y) = 1
  rw [neg_odot, MVAlgebra.oplus_assoc]
  -- goal: ¬x ⊞ (¬z ⊞ y) = 1  ↔  ¬z ⊞ (¬x ⊞ y) = 1
  constructor
  · intro h
    rw [← h, ← MVAlgebra.oplus_assoc, MVAlgebra.oplus_comm (¬ᴹ z) (¬ᴹ x), MVAlgebra.oplus_assoc]
  · intro h
    rw [← h, ← MVAlgebra.oplus_assoc, MVAlgebra.oplus_comm (¬ᴹ x) (¬ᴹ z), MVAlgebra.oplus_assoc]

/-- Detachment: `x ⊙ (x ⇨ y) ≤ᴹ y`. -/
theorem odot_imp_le (x y : A) : (x ⊙ (x ⇨ y)) ≤ᴹ y := by
  rw [residuation]; exact le_refl _

/-! ## Further algebraic identities

Each is a short equational consequence of the lemmas above, and each was
cross-checked against the standard [0,1] model before being written.
(De Morgan for `⊙→⊞` is already `neg_odot`; here is its dual and the monoid
laws for `⊙`.)
-/

/-- De Morgan: `¬(x ⊞ y) = ¬x ⊙ ¬y`. -/
theorem neg_oplus (x y : A) : ¬ᴹ (x ⊞ y) = (¬ᴹ x) ⊙ (¬ᴹ y) := by
  -- ¬x ⊙ ¬y = ¬(¬¬x ⊞ ¬¬y) = ¬(x ⊞ y)
  unfold odot; rw [MVAlgebra.neg_neg, MVAlgebra.neg_neg]

/-- `⊙` is commutative. -/
theorem odot_comm (x y : A) : x ⊙ y = y ⊙ x := by
  unfold odot; rw [MVAlgebra.oplus_comm]

/-- `⊙` is associative. -/
theorem odot_assoc (x y z : A) : (x ⊙ y) ⊙ z = x ⊙ (y ⊙ z) := by
  -- (x⊙y)⊙z = ¬(¬(x⊙y) ⊞ ¬z) = ¬((¬x⊞¬y) ⊞ ¬z) = ¬(¬x ⊞ (¬y⊞¬z))
  --         = ¬(¬x ⊞ ¬(y⊙z)) = x⊙(y⊙z)
  show ¬ᴹ ((¬ᴹ (x ⊙ y)) ⊞ (¬ᴹ z)) = ¬ᴹ ((¬ᴹ x) ⊞ (¬ᴹ (y ⊙ z)))
  rw [neg_odot, neg_odot, MVAlgebra.oplus_assoc]

/-- `1` is a right identity for `⊙`. -/
@[simp] theorem odot_one (x : A) : x ⊙ 𝟙 = x := by
  -- x⊙1 = ¬(¬x ⊞ ¬1) = ¬(¬x ⊞ 0) = ¬(¬x) = x
  show ¬ᴹ ((¬ᴹ x) ⊞ (¬ᴹ (𝟙 : A))) = x
  rw [neg_one_eq_zero, MVAlgebra.oplus_zero, MVAlgebra.neg_neg]

/-- `0` is absorbing for `⊙`. -/
@[simp] theorem odot_zero (x : A) : x ⊙ 𝟘 = (𝟘 : A) := by
  -- x⊙0 = ¬(¬x ⊞ ¬0) = ¬(¬x ⊞ 1) = ¬1 = 0
  show ¬ᴹ ((¬ᴹ x) ⊞ (¬ᴹ (𝟘 : A))) = (𝟘 : A)
  rw [neg_zero_eq_one, oplus_one, neg_one_eq_zero]

/-- Negation is antitone for the natural order: `x ≤ᴹ y → ¬y ≤ᴹ ¬x`. -/
theorem neg_antitone {x y : A} (h : x ≤ᴹ y) : (¬ᴹ y) ≤ᴹ (¬ᴹ x) := by
  -- x≤y is ¬x⊞y=1; ¬y≤¬x is ¬¬y⊞¬x = y⊞¬x = ¬x⊞y = 1.
  unfold le imp at h ⊢
  rw [MVAlgebra.neg_neg, MVAlgebra.oplus_comm]; exact h

/-! ## Lattice fragment: idempotency, `⊙`-decrease, and absorption

`sup_idem` and `odot_le_left` are short equational facts; absorption then follows
by combining `odot_le_left` with `sup_eq_of_le`.  (Full lattice associativity of
`⊔` is genuinely harder in MV-algebras — it goes through distributivity — and is
not attempted here.)  All three are model-verified.
-/

/-- `⊔ᴹ` is idempotent: `x ⊔ᴹ x = x`.  From MV9. -/
@[simp] theorem sup_idem (x : A) : x ⊔ᴹ x = x := by
  -- x⊔x = ¬(¬x⊞x)⊞x = ¬1⊞x = 0⊞x = x
  unfold sup
  rw [neg_oplus_self, neg_one_eq_zero, zero_oplus]

/-- `⊙` is decreasing in its left argument: `x ⊙ y ≤ᴹ x`. -/
theorem odot_le_left (x y : A) : (x ⊙ y) ≤ᴹ x := by
  -- (x⊙y) ≤ x  ↔  (x⊙y) ⊙ ¬x = 0.
  rw [le_iff_odot_neg_eq_zero]
  -- (x⊙y)⊙¬x = ¬(¬(x⊙y) ⊞ ¬¬x) = ¬((¬x⊞¬y) ⊞ x)
  show ¬ᴹ ((¬ᴹ (x ⊙ y)) ⊞ (¬ᴹ (¬ᴹ x))) = (𝟘 : A)
  rw [neg_odot, MVAlgebra.neg_neg]
  -- ¬((¬x⊞¬y) ⊞ x) = ¬((¬y⊞¬x) ⊞ x) = ¬(¬y ⊞ (¬x⊞x)) = ¬(¬y ⊞ 1) = ¬1 = 0
  rw [MVAlgebra.oplus_comm (¬ᴹ x) (¬ᴹ y), MVAlgebra.oplus_assoc, neg_oplus_self, oplus_one, neg_one_eq_zero]

/-- `⊙` is decreasing in its right argument (by commutativity): `x ⊙ y ≤ᴹ y`. -/
theorem odot_le_right (x y : A) : (x ⊙ y) ≤ᴹ y := by
  rw [odot_comm]; exact odot_le_left y x

/-- Meet, in the standard MV form `x ⊓ y := x ⊙ (x ⇨ y)`. -/
def inf (x y : A) : A := x ⊙ (x ⇨ y)
scoped infixl:69 " ⊓ᴹ " => MVAlgebra.inf

/-- The meet is below the left argument: `x ⊓ᴹ y ≤ᴹ x`. -/
theorem inf_le_left (x y : A) : (x ⊓ᴹ y) ≤ᴹ x := odot_le_left x (x ⇨ y)

/-- **Absorption**: `x ⊔ᴹ (x ⊓ᴹ y) = x`.
    Since `x ⊓ᴹ y ≤ᴹ x` (`inf_le_left`), `sup_eq_of_le` gives `(x⊓y) ⊔ x = x`,
    and `sup_comm` flips it. -/
theorem sup_inf_absorb (x y : A) : x ⊔ᴹ (x ⊓ᴹ y) = x := by
  have h : (x ⊓ᴹ y) ⊔ᴹ x = x := sup_eq_of_le (inf_le_left x y)
  rw [sup_comm]; exact h

/-! ## Axiom audit

These print the axioms each theorem actually depends on.  Expected output for a
choice-free development is `[propext, Quot.sound]` (and possibly nothing more).
If `Classical.choice` appears, it was pulled in by a tactic (e.g. `simp` reaching
for a classical lemma), not by the mathematics — the offending step can then be
made explicit to remove it.  `propext` (propositional extensionality) and
`Quot.sound` (quotient soundness) are the benign axioms underlying essentially
all of Mathlib and do NOT amount to the axiom of choice.
-/

#print axioms neg_oplus_self          -- MV9
#print axioms le_iff_odot_neg_eq_zero  -- Lemma 1.2 (i)↔(ii)
#print axioms le_antisymm              -- order is a partial order
#print axioms residuation              -- the keystone
#print axioms odot_imp_le              -- detachment
#print axioms le_of_sup_eq             -- the lemma we just closed
#print axioms odot_assoc               -- ⊙ monoid: associativity
#print axioms neg_oplus                -- De Morgan dual
#print axioms sup_inf_absorb           -- lattice absorption

end MVAlgebra
end MV
