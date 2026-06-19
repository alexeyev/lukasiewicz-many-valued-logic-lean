import Lukasiewicz.Distance

namespace Luk.MVAlgebra

variable {A : Type _} [MVAlgebra A]


-- ============================================================================
-- TWO FOUNDATIONAL CHARACTERIZATIONS IN MV-ALGEBRA THEORY
--
-- 1. Mundici's Lemma 1.2: four equivalent characterizations of the natural order.
-- 2. The Boolean Center Theorem: the ⊙-idempotent elements of an MV-algebra
--    coincide with the ⊕-idempotent elements and with the "complemented"
--    elements (those a satisfying a ∨ ¬a = 1, equivalently a ∧ ¬a = 0).
--    The Boolean Center is the largest Boolean subalgebra of A.
-- ============================================================================

/-! ## Mundici's Lemma 1.2: characterizations of the natural order

  For any x, y in an MV-algebra, the following are equivalent:
  (i)   ¬x ⊕ y = 1                  [our definition of `le x y`]
  (ii)  x ⊙ ¬y = 0
  (iii) y = x ⊕ (y ⊖ x)               [where y ⊖ x := y ⊙ ¬x]
  (iv)  ∃ z, x ⊕ z = y
-/

/-- **Mundici Lemma 1.2(iii)**: if `x ≤ y` then `y = x ⊕ (y ⊖ x)`. -/
theorem le_iff_oplus_ominus {x y : A} (h : le x y) : y = oplus x (odot y (neg x)) := by
  -- The MV axiom MV6: ¬(¬x ⊕ y) ⊕ y = ¬(¬y ⊕ x) ⊕ x.
  -- LHS: ¬(¬x ⊕ y) ⊕ y = (x ⊙ ¬y) ⊕ y = 0 ⊕ y = y  [using x ≤ y, so x ⊙ ¬y = 0].
  -- RHS: ¬(¬y ⊕ x) ⊕ x = (y ⊙ ¬x) ⊕ x = (y ⊖ x) ⊕ x.
  -- Therefore y = (y ⊖ x) ⊕ x = x ⊕ (y ⊖ x).
  have hxy_zero : odot x (neg y) = zero := odot_neg_zero_of_le h
  have key := MVAlgebra.mv_axiom x y
  -- key : oplus (neg (oplus (neg x) y)) y = oplus (neg (oplus (neg y) x)) x
  -- Rewrite ¬(¬x ⊕ y) as x ⊙ ¬y (using neg_oplus + neg_neg):
  rw [show neg (oplus (neg x) y) = odot x (neg y) by rw [neg_oplus, neg_neg]] at key
  rw [show neg (oplus (neg y) x) = odot y (neg x) by rw [neg_oplus, neg_neg]] at key
  -- key : (x ⊙ ¬y) ⊕ y = (y ⊙ ¬x) ⊕ x
  rw [hxy_zero, zero_oplus] at key
  -- key : y = (y ⊖ x) ⊕ x
  rw [oplus_comm x (odot y (neg x))]
  exact key

/-- **Mundici Lemma 1.2(iv)**: if `x ≤ y` then there exists `z` with `x ⊕ z = y`. -/
theorem le_iff_exists_oplus {x y : A} (h : le x y) : ∃ z, oplus x z = y :=
  ⟨odot y (neg x), (le_iff_oplus_ominus h).symm⟩

/-- **Mundici Lemma 1.2(iv) ⇒ (i)**: if `x ⊕ z = y` for some `z`, then `x ≤ y`. -/
theorem le_of_exists_oplus {x y : A} (h : ∃ z, oplus x z = y) : le x y := by
  obtain ⟨z, hz⟩ := h
  show oplus (neg x) y = one
  rw [← hz]
  -- Goal: ¬x ⊕ (x ⊕ z) = 1
  rw [← oplus_assoc, neg_oplus_self]
  exact one_oplus z

/-- **Mundici Lemma 1.2**: the four characterizations of `≤` are equivalent.
    We state the bundle as a 4-fold equivalence. -/
theorem le_iff_quad (x y : A) :
    (le x y) ↔ (odot x (neg y) = zero) ∧
               (y = oplus x (odot y (neg x))) ∧
               (∃ z, oplus x z = y) := by
  constructor
  · intro h
    exact ⟨odot_neg_zero_of_le h, le_iff_oplus_ominus h, le_iff_exists_oplus h⟩
  · rintro ⟨_, _, hz⟩
    exact le_of_exists_oplus hz

/-! ## The Boolean Center

  An element `a ∈ A` is **Boolean** iff `a ⊙ a = a` (idempotent under `⊙`).
  This is equivalent to several other natural conditions, all of which say "a
  behaves like a classical truth value." The classical key result is:

      a ⊙ a = a   ⟺   a ⊕ a = a   ⟺   a ∨ ¬a = 1   ⟺   a ∧ ¬a = 0.

  The set `B(A) := { a : a ⊙ a = a }` is called the **Boolean center** of `A`.
  It forms the largest Boolean subalgebra of `A` and is intensely studied:
  Cignoli's "Boolean Skeletons of MV-algebras" (2011), Mundici's "Advanced
  Łukasiewicz Calculus" §3, etc. The Boolean center is `{0, 1}` for `[0,1]`
  and is all of `A` when `A` is itself a Boolean algebra.
-/

/-- An element of an MV-algebra is **Boolean** iff it is `⊙`-idempotent. -/
def IsBoolean (a : A) : Prop := odot a a = a

/-- `0` is a Boolean element. -/
theorem zero_isBoolean : IsBoolean (zero : A) := by
  show odot zero zero = zero
  exact zero_odot zero

/-- `1` is a Boolean element. -/
theorem one_isBoolean : IsBoolean (one : A) := by
  show odot one one = one
  -- odot one one = neg(oplus (neg one) (neg one)) = neg(oplus zero zero) = neg zero = one.
  show neg (oplus (neg one) (neg one)) = one
  rw [neg_one_eq_zero, oplus_zero]
  -- Goal: neg zero = one — definitionally true.
  rfl

/-- **(i) ⇒ (iii)**: `a ⊙ a = a` implies `a ∨ ¬a = 1`. Clean direct calculation. -/
theorem mvsup_neg_eq_one_of_isBoolean {a : A} (h : IsBoolean a) :
    mvsup a (neg a) = one := by
  -- a ∨ ¬a = (a ⊙ ¬¬a) ⊕ ¬a = (a ⊙ a) ⊕ ¬a [neg_neg] = a ⊕ ¬a [hypothesis] = 1.
  show oplus (odot a (neg (neg a))) (neg a) = one
  rw [neg_neg, h, self_oplus_neg]

/-- **(iii) ⇒ (i)**: `a ∨ ¬a = 1` implies `a ⊙ a = a`. -/
theorem isBoolean_of_mvsup_neg {a : A} (h : mvsup a (neg a) = one) :
    IsBoolean a := by
  -- From a ∨ ¬a = 1, multiply both sides by a (on the right):
  --   (a ∨ ¬a) ⊙ a = 1 ⊙ a = a.
  -- LHS by Prop 1.6(i): (a ⊙ a) ∨ (¬a ⊙ a) = (a⊙a) ∨ 0 = a⊙a.
  -- So a⊙a = a.
  show odot a a = a
  -- Compute (a ∨ ¬a) ⊙ a in two ways.
  have step1 : odot (mvsup a (neg a)) a = a := by
    rw [h]
    -- Goal: odot one a = a.  odot one a = ¬(¬one ⊕ ¬a) = ¬(0 ⊕ ¬a) = ¬¬a = a.
    show neg (oplus (neg one) (neg a)) = a
    rw [neg_one_eq_zero, zero_oplus, neg_neg]
  -- And by Prop 1.6(i), with a swapped (note: odot_distrib_mvsup_left is x ⊙ (y∨z))
  -- We need (y ∨ z) ⊙ x. Use odot_comm to swap.
  have step2 : odot (mvsup a (neg a)) a = mvsup (odot a a) zero := by
    rw [odot_comm (mvsup a (neg a)) a]
    -- Goal: a ⊙ (a ∨ ¬a) = (a⊙a) ∨ 0
    rw [odot_distrib_mvsup_left a a (neg a)]
    -- Goal: (a⊙a) ∨ (a⊙¬a) = (a⊙a) ∨ 0
    rw [self_odot_neg]
  rw [step2] at step1
  -- step1 : (a⊙a) ∨ 0 = a. Now mvsup (a⊙a) 0 = (a⊙a) (since mvsup x 0 = x trivially):
  -- (a⊙a) ∨ 0 = ((a⊙a) ⊙ ¬0) ⊕ 0 = ((a⊙a) ⊙ 1) ⊕ 0 = (a⊙a) ⊕ 0 = a⊙a.
  have mvsup_zero_eq : mvsup (odot a a) zero = odot a a := by
    show oplus (odot (odot a a) (neg zero)) zero = odot a a
    rw [oplus_zero]
    -- Goal: odot (odot a a) (neg zero) = odot a a.
    -- Unfold odot: neg(oplus (neg(odot a a)) (neg (neg zero))) = odot a a.
    show neg (oplus (neg (odot a a)) (neg (neg zero))) = odot a a
    rw [neg_neg, oplus_zero, neg_neg]
  rw [mvsup_zero_eq] at step1
  exact step1

/-- `a ⊙ a = a ⟺ a ∨ ¬a = 1`. -/
theorem isBoolean_iff_mvsup_neg (a : A) : IsBoolean a ↔ mvsup a (neg a) = one :=
  ⟨mvsup_neg_eq_one_of_isBoolean, isBoolean_of_mvsup_neg⟩

/-- **(iii) ⟺ (iv)**: `a ∨ ¬a = 1 ⟺ a ∧ ¬a = 0`. Trivial via De Morgan. -/
theorem mvinf_neg_eq_zero_iff (a : A) : mvinf a (neg a) = zero ↔ mvsup a (neg a) = one := by
  constructor
  · intro h
    -- a ∨ ¬a = ¬(¬a ∧ ¬¬a) = ¬(¬a ∧ a) = ¬(a ∧ ¬a) [comm] = ¬0 = 1.
    have : neg (mvsup a (neg a)) = mvinf (neg a) (neg (neg a)) := neg_mvsup a (neg a)
    rw [neg_neg] at this
    rw [mvinf_comm (neg a) a] at this
    -- this : ¬(a ∨ ¬a) = a ∧ ¬a = 0
    rw [h] at this
    -- this : ¬(a ∨ ¬a) = 0
    -- So a ∨ ¬a = ¬0 = 1.
    have : neg (neg (mvsup a (neg a))) = neg zero := by rw [this]
    rw [neg_neg] at this
    rw [this]; rfl
  · intro h
    -- a ∧ ¬a = ¬(¬a ∨ ¬¬a) = ¬(¬a ∨ a) = ¬(a ∨ ¬a) = ¬1 = 0.
    have : neg (mvinf a (neg a)) = mvsup (neg a) (neg (neg a)) := neg_mvinf a (neg a)
    rw [neg_neg] at this
    rw [mvsup_comm (neg a) a] at this
    rw [h] at this
    have : neg (neg (mvinf a (neg a))) = neg one := by rw [this]
    rw [neg_neg, neg_one_eq_zero] at this
    exact this

/-- **`a ⊙ a = a ⟺ a ∧ ¬a = 0`**. -/
theorem isBoolean_iff_mvinf_neg (a : A) : IsBoolean a ↔ mvinf a (neg a) = zero := by
  rw [isBoolean_iff_mvsup_neg, ← mvinf_neg_eq_zero_iff]

/-- **`a` is Boolean iff `¬a` is Boolean**. The Boolean center is closed under `¬`. -/
theorem isBoolean_neg (a : A) : IsBoolean a ↔ IsBoolean (neg a) := by
  rw [isBoolean_iff_mvsup_neg, isBoolean_iff_mvsup_neg]
  rw [neg_neg]
  -- Goal: a ∨ ¬a = 1 ↔ ¬a ∨ a = 1
  rw [mvsup_comm (neg a) a]

/-- **(i) ⟺ (ii)**: `a ⊙ a = a ⟺ a ⊕ a = a`. The ⊙-idempotents coincide with
    the ⊕-idempotents. -/
theorem isBoolean_iff_oplus_idem (a : A) : IsBoolean a ↔ oplus a a = a := by
  constructor
  · intro h
    -- (i) for a ⟹ (i) for ¬a (via isBoolean_neg). 
    -- (i) for ¬a says ¬a ⊙ ¬a = ¬a, i.e., ¬(a⊕a) = ¬a, i.e., a⊕a = a.
    have h2 : IsBoolean (neg a) := (isBoolean_neg a).mp h
    -- h2 : ¬a ⊙ ¬a = ¬a. Take neg of both sides:
    --   neg(¬a ⊙ ¬a) = neg(¬a)
    --   ¬¬a ⊕ ¬¬a = ¬¬a    [neg_odot then neg_neg]
    --    a ⊕ a = a          [neg_neg]
    -- Direct: from h2 we have ¬a ⊙ ¬a = ¬a. By definition ¬a ⊙ ¬a = ¬(a ⊕ a).
    -- So ¬(a ⊕ a) = ¬a, hence a ⊕ a = a (apply neg to both sides and use neg_neg).
    have step : neg (oplus a a) = neg a := by
      rw [neg_oplus]
      exact h2
    have step2 : neg (neg (oplus a a)) = neg (neg a) := congrArg neg step
    rwa [neg_neg, neg_neg] at step2
  · intro h
    -- a ⊕ a = a ⟹ ¬a ⊙ ¬a = ¬a (by taking ¬, since ¬(a⊕a) = ¬a ⊙ ¬a).
    -- Then (i) for ¬a ⟹ (i) for a.
    have h2 : IsBoolean (neg a) := by
      show odot (neg a) (neg a) = neg a
      rw [← neg_oplus, h]
    exact (isBoolean_neg a).mpr h2

/-- **The Boolean-element characterization theorem** — the centerpiece. All four
    common definitions of "Boolean element" of an MV-algebra coincide. -/
theorem isBoolean_iff_quad (a : A) :
    (odot a a = a) ↔
    (oplus a a = a) ∧
    (mvsup a (neg a) = one) ∧
    (mvinf a (neg a) = zero) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · exact (isBoolean_iff_oplus_idem a).mp h
    · exact mvsup_neg_eq_one_of_isBoolean h
    · exact (mvinf_neg_eq_zero_iff a).mpr (mvsup_neg_eq_one_of_isBoolean h)
  · rintro ⟨_, h, _⟩
    exact isBoolean_of_mvsup_neg h

/-! ## Closure properties of the Boolean center

  The Boolean center `B(A) := {a : a ⊙ a = a}` is closed under `¬`, `⊙`, `⊕`,
  and the lattice operations `∨` and `∧`. On the Boolean center, all the
  MV-operations collapse to the corresponding Boolean ones: `⊙` is `∧`, `⊕` is `∨`.
  This makes `B(A)` a Boolean subalgebra of `A`. We prove the two essential
  closure facts here.
-/

/-- The Boolean center is closed under `⊙`: if `a` and `b` are Boolean, so is `a ⊙ b`. -/
theorem isBoolean_odot {a b : A} (ha : IsBoolean a) (hb : IsBoolean b) :
    IsBoolean (odot a b) := by
  -- Use the (a ∨ ¬a = 1) characterization. Want (a⊙b) ∨ ¬(a⊙b) = 1.
  -- ¬(a⊙b) = ¬a ⊕ ¬b. So goal: (a⊙b) ∨ (¬a ⊕ ¬b) = 1.
  --
  -- Alternative direct proof: use Prop 1.6(i) on (a⊙b) ⊙ (a⊙b) and rearrange.
  show odot (odot a b) (odot a b) = odot a b
  -- (a⊙b) ⊙ (a⊙b) = a ⊙ b ⊙ a ⊙ b = a ⊙ a ⊙ b ⊙ b [comm]
  --              = (a⊙a) ⊙ (b⊙b) = a ⊙ b.
  rw [odot_assoc a b (odot a b)]
  -- Goal: a ⊙ (b ⊙ (a ⊙ b)) = a ⊙ b
  rw [← odot_assoc b a b]
  -- Goal: a ⊙ ((b ⊙ a) ⊙ b) = a ⊙ b
  rw [odot_comm b a]
  -- Goal: a ⊙ ((a ⊙ b) ⊙ b) = a ⊙ b
  rw [odot_assoc a b b]
  -- Goal: a ⊙ (a ⊙ (b ⊙ b)) = a ⊙ b
  rw [hb]
  -- Goal: a ⊙ (a ⊙ b) = a ⊙ b
  rw [← odot_assoc a a b]
  -- Goal: (a ⊙ a) ⊙ b = a ⊙ b
  rw [ha]

/-- The Boolean center is closed under `⊕`: if `a` and `b` are Boolean, so is `a ⊕ b`. -/
theorem isBoolean_oplus {a b : A} (ha : IsBoolean a) (hb : IsBoolean b) :
    IsBoolean (oplus a b) := by
  -- a Boolean ⟺ a ⊕ a = a (just proved). Use this characterization.
  rw [isBoolean_iff_oplus_idem]
  rw [isBoolean_iff_oplus_idem] at ha hb
  -- ha : a ⊕ a = a, hb : b ⊕ b = b. Want (a⊕b) ⊕ (a⊕b) = a⊕b.
  -- Same rearrangement as for ⊙.
  rw [oplus_assoc a b (oplus a b)]
  rw [← oplus_assoc b a b]
  rw [oplus_comm b a]
  rw [oplus_assoc a b b]
  rw [hb]
  rw [← oplus_assoc a a b]
  rw [ha]

end MVAlgebra
end Luk
