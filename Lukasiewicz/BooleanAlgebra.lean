import Lukasiewicz.MVLemmas

namespace Luk.MVAlgebra

variable {A : Type _} [MVAlgebra A]


-- ============================================================================
-- THE BOOLEAN CENTER IS A BOOLEAN ALGEBRA
--
-- Building on `BooleanCenter.lean`, we now prove the centerpiece structural
-- theorem: when both a and b are Boolean (a ⊙ a = a and b ⊙ b = b), the
-- monoid and lattice operations coincide:
--
--   a ⊙ b = a ∧ b,   a ⊕ b = a ∨ b.
--
-- Combined with the earlier closure results (B(A) is closed under ⊙, ⊕, ¬),
-- this shows that B(A) carries the structure of a Boolean algebra. This is
-- the standard theorem on the "Boolean skeleton" of an MV-algebra and is
-- intensely studied (Cignoli "Boolean Skeletons of MV-algebras" 2011).
-- ============================================================================

/-- **Key lemma**: if `b` is Boolean then `b ⊙ b = b`, so for any `a`,
    `b ⊙ (b ∧ a) ≤ b ⊙ a`. -/
theorem odot_mvinf_le_odot {b : A} (_hb : IsBoolean b) (a : A) :
    le (odot b (mvinf b a)) (odot b a) := by
  -- b ∧ a ≤ a (mvinf_glb's lower-bound property), so b ⊙ (b ∧ a) ≤ b ⊙ a
  -- by odot_mono on the right.
  exact odot_mono_right b (le_mvinf_right b a)

/-- **The product-is-meet theorem on the Boolean center**: if both `a` and `b`
    are Boolean (i.e., `⊙`-idempotent), then `a ⊙ b = a ∧ b`. -/
theorem odot_eq_mvinf_of_isBoolean {a b : A} (_ha : IsBoolean a) (hb : IsBoolean b) :
    odot a b = mvinf a b := by
  -- We have a⊙b ≤ a∧b in any MV-algebra. So we need a∧b ≤ a⊙b.
  -- Strategy:
  --   a ∧ b = b ⊙ (¬b ⊕ a)  [meet_idiom_swap]
  --        = (b ⊙ b) ⊙ (¬b ⊕ a)  [hb: b ⊙ b = b]
  --        = b ⊙ (b ⊙ (¬b ⊕ a))  [odot_assoc]
  --        = b ⊙ (b ∧ a)         [meet_idiom_swap reversed]
  --        ≤ b ⊙ a               [b ∧ a ≤ a, then odot_mono]
  --        = a ⊙ b                [odot_comm]
  -- So a∧b ≤ a⊙b, combined with the reverse we get equality.
  apply le_antisymm
  · -- First subgoal (forward direction of equality): le (odot a b) (mvinf a b).
    -- This is the standard a ⊙ b ≤ a ∧ b — holds in any residuated lattice.
    apply mvinf_glb
    · exact odot_le_left' a b
    · exact odot_le_right' a b
  · -- Second subgoal: le (mvinf a b) (odot a b) — the harder direction, uses Boolean hyp.
    -- Chain: mvinf a b = mvinf b a [comm] = b ⊙ (¬b ⊕ a) [meet idiom]
    --      = (b ⊙ b) ⊙ (¬b ⊕ a) [hb] = b ⊙ (b ⊙ (¬b ⊕ a)) [assoc] = b ⊙ mvinf b a [meet idiom]
    --      ≤ b ⊙ a [b's lower bound on mvinf b a] = a ⊙ b [comm].
    rw [mvinf_comm]
    -- Goal: le (mvinf b a) (odot a b)
    have step1 : mvinf b a = odot b (oplus (neg b) a) := (meet_idiom b a).symm
    rw [step1]
    have step2 : odot b (oplus (neg b) a) = odot (odot b b) (oplus (neg b) a) := by rw [hb]
    rw [step2]
    rw [odot_assoc]
    rw [meet_idiom]
    -- Goal: le (odot b (mvinf b a)) (odot a b)
    rw [odot_comm a b]
    -- Goal: le (odot b (mvinf b a)) (odot b a)
    exact odot_mvinf_le_odot hb a

/-- **The sum-is-join theorem on the Boolean center**: if both `a` and `b`
    are Boolean, then `a ⊕ b = a ∨ b`. Follows from the previous via De Morgan. -/
theorem oplus_eq_mvsup_of_isBoolean {a b : A} (ha : IsBoolean a) (hb : IsBoolean b) :
    oplus a b = mvsup a b := by
  -- a ⊕ b = ¬(¬a ⊙ ¬b)  [neg_oplus reversed via neg_neg]
  --        = ¬(¬a ∧ ¬b)  [using ¬a, ¬b Boolean and odot_eq_mvinf_of_isBoolean]
  --        = a ∨ b       [De Morgan: ¬(¬a ∧ ¬b) = a ∨ b ... let's check]
  -- mvsup a b = ¬(¬a ∧ ¬b)? neg_mvinf: ¬(¬a ∧ ¬b) = ¬¬a ∨ ¬¬b = a ∨ b. ✓
  -- So a ⊕ b = ¬(¬a ⊙ ¬b) = ¬(¬a ∧ ¬b) = a ∨ b.
  have hna : IsBoolean (neg a) := (isBoolean_neg a).mp ha
  have hnb : IsBoolean (neg b) := (isBoolean_neg b).mp hb
  -- a ⊕ b = ¬(¬a ⊙ ¬b)
  have step1 : oplus a b = neg (odot (neg a) (neg b)) := by
    rw [neg_odot, neg_neg, neg_neg]
  rw [step1]
  rw [odot_eq_mvinf_of_isBoolean hna hnb]
  -- Goal: ¬(mvinf ¬a ¬b) = mvsup a b
  rw [neg_mvinf, neg_neg, neg_neg]

/-- **The Boolean Center is a Boolean algebra (combined statement).** For any
    two `⊙`-idempotent elements `a, b ∈ B(A)`, the monoid and lattice operations
    coincide: `a ⊙ b = a ∧ b` and `a ⊕ b = a ∨ b`. Combined with the closure
    of B(A) under `¬`, `⊙`, and `⊕`, this makes `(B(A), ∨, ∧, ¬, 0, 1)` a
    Boolean subalgebra of `A`. -/
theorem isBoolean_subalgebra (a b : A) (ha : IsBoolean a) (hb : IsBoolean b) :
    odot a b = mvinf a b ∧ oplus a b = mvsup a b :=
  ⟨odot_eq_mvinf_of_isBoolean ha hb, oplus_eq_mvsup_of_isBoolean ha hb⟩

/-! ## Mundici Lemma 1.4 — the monotonicity bundle

  Mundici's Lemma 1.4 collects three properties of the natural order:
  (i)   `x ≤ y ⟺ ¬y ≤ ¬x`            (contraposition)
  (ii)  `x ≤ y ⟹ x ⊕ z ≤ y ⊕ z`       (⊕ is monotone)
  (ii') `x ≤ y ⟹ x ⊙ z ≤ y ⊙ z`       (⊙ is monotone)
  (iii) `x ⊙ y ≤ z ⟺ x ≤ ¬y ⊕ z`      (residuation / "transfer law")
-/

/-- **Mundici Lemma 1.4(i)**: `x ≤ y ⟺ ¬y ≤ ¬x`. -/
theorem le_iff_neg_le (x y : A) : le x y ↔ le (neg y) (neg x) := by
  constructor
  · intro h
    -- le x y ⟺ ¬x ⊕ y = 1. le ¬y ¬x ⟺ ¬¬y ⊕ ¬x = y ⊕ ¬x = ¬x ⊕ y = 1. ✓
    show oplus (neg (neg y)) (neg x) = one
    rw [neg_neg, oplus_comm]
    exact h
  · intro h
    show oplus (neg x) y = one
    -- We have ¬¬y ⊕ ¬x = 1, i.e., y ⊕ ¬x = 1. So ¬x ⊕ y = 1 by oplus_comm.
    have h' : oplus (neg (neg y)) (neg x) = one := h
    rw [neg_neg, oplus_comm] at h'
    exact h'

/-- **Mundici Lemma 1.4(ii)**: `⊕` is monotone — `x ≤ y` implies `x ⊕ z ≤ y ⊕ z`. -/
theorem oplus_mono_left' {x y : A} (z : A) (h : le x y) : le (oplus x z) (oplus y z) :=
  oplus_mono_left z h

/-- **Mundici Lemma 1.4(ii')**: `⊙` is monotone — `x ≤ y` implies `x ⊙ z ≤ y ⊙ z`. -/
theorem odot_mono_left' {x y : A} (z : A) (h : le x y) : le (odot x z) (odot y z) :=
  odot_mono_left z h

/-- **Mundici Lemma 1.4(iii)**: residuation, `x ⊙ y ≤ z ⟺ x ≤ ¬y ⊕ z`. -/
theorem residuation_lemma14 (x y z : A) : le (odot x y) z ↔ le x (oplus (neg y) z) := by
  -- This is essentially le_iff_odot_neg_zero applied with appropriate substitutions.
  -- Forward: assume x ⊙ y ≤ z. Then (x⊙y) ⊙ ¬z = 0. Want x ⊙ ¬(¬y ⊕ z) = 0, i.e., 
  -- x ⊙ (y ⊙ ¬z) = 0 (by neg_oplus + neg_neg). By odot_assoc, (x⊙y) ⊙ ¬z = 0. ✓
  constructor
  · intro h
    -- le (x⊙y) z ⟺ (x⊙y) ⊙ ¬z = 0
    have h1 : odot (odot x y) (neg z) = zero := odot_neg_zero_of_le h
    -- Want le x (¬y ⊕ z) ⟺ x ⊙ ¬(¬y ⊕ z) = 0 ⟺ x ⊙ (¬¬y ⊙ ¬z) = 0 ⟺ x ⊙ (y ⊙ ¬z) = 0
    apply le_of_odot_neg_zero
    show odot x (neg (oplus (neg y) z)) = zero
    rw [neg_oplus, neg_neg]
    -- Goal: x ⊙ (y ⊙ ¬z) = 0
    rw [← odot_assoc]
    -- Goal: (x ⊙ y) ⊙ ¬z = 0
    exact h1
  · intro h
    -- Reverse: assume le x (¬y ⊕ z). Then x ⊙ ¬(¬y ⊕ z) = 0, i.e., x ⊙ y ⊙ ¬z = 0.
    have h1 : odot x (neg (oplus (neg y) z)) = zero := odot_neg_zero_of_le h
    rw [neg_oplus, neg_neg] at h1
    -- h1 : x ⊙ (y ⊙ ¬z) = 0
    apply le_of_odot_neg_zero
    -- Goal: (x ⊙ y) ⊙ ¬z = 0
    rw [odot_assoc]
    exact h1

/-! ## Triviality dichotomy -/

/-- An MV-algebra is **nontrivial** iff `0 ≠ 1`, equivalently iff it has more
    than one element. (The trivial MV-algebra has only `0 = 1 = ¬0`.) -/
def Nontrivial (A : Type _) [MVAlgebra A] : Prop := (zero : A) ≠ one

/-- In a nontrivial MV-algebra, no element is both `0` and `1`. -/
theorem nontrivial_iff (A : Type _) [MVAlgebra A] :
    Nontrivial A ↔ (zero : A) ≠ one := Iff.rfl

end MVAlgebra
end Luk
