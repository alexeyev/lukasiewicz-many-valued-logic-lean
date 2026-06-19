import Lukasiewicz.BooleanCenter

namespace Luk.MVAlgebra

variable {A : Type _} [MVAlgebra A]


-- ============================================================================
-- TWO CORE LEMMAS FROM MUNDICI CHAPTER 1
--
-- 1. Mundici Lemma 1.3 — uniqueness of negation: ¬a is the UNIQUE element
--    x satisfying both a ⊕ x = 1 and a ⊙ x = 0.
--
-- 2. Mundici Lemma 1.8 — propagation of disjointness: if x ∧ y = 0 then
--    (x ⊕ x) ∧ y = 0 (and by symmetry x ∧ (y ⊕ y) = 0). This is the engine
--    that powers the existence of prime ideals (Proposition 1.19) which in
--    turn drives Chang's Subdirect Representation Theorem.
-- ============================================================================

/-! ## Lemma 1.3 — Uniqueness of negation

  For any element `a` of an MV-algebra, `¬a` is the *unique* element `x` such
  that both `a ⊕ x = 1` and `a ⊙ x = 0`. This says: negation in an MV-algebra
  is determined by its algebraic role (the unique complement under the
  combined "join-to-top" and "meet-to-bottom" conditions). On a Boolean
  algebra this collapses to ordinary Boolean complementation.
-/

/-- One direction (existence): `a ⊕ ¬a = 1` and `a ⊙ ¬a = 0`. -/
theorem neg_satisfies (a : A) : oplus a (neg a) = one ∧ odot a (neg a) = zero :=
  ⟨self_oplus_neg a, self_odot_neg a⟩

/-- **Mundici Lemma 1.3**: `¬a` is the unique `x` with `a ⊕ x = 1` and `a ⊙ x = 0`.
    The proof: the two conditions say exactly `¬a ≤ x` and `x ≤ ¬a` respectively,
    so antisymmetry gives `x = ¬a`. -/
theorem neg_unique {a x : A} (h1 : oplus a x = one) (h2 : odot a x = zero) : x = neg a := by
  -- a ⊕ x = 1 ⟺ ¬¬a ⊕ x = 1 ⟺ le ¬a x.
  have h_le_x : le (neg a) x := by
    show oplus (neg (neg a)) x = one
    rw [neg_neg]; exact h1
  -- a ⊙ x = 0 ⟺ neg(¬a ⊕ ¬x) = 0 ⟺ ¬a ⊕ ¬x = ¬0 = 1 ⟺ le a (¬x) ⟺ le x ¬a (by le_neg_swap).
  have h_le_neg : le x (neg a) := by
    -- From odot a x = 0 = neg one, take neg: neg(odot a x) = one, i.e., neg a ⊕ neg x = one.
    -- That says le a (neg x). By le_neg_swap, le x (neg (neg a)) — wait, want le x ¬a.
    -- le X Y ⟺ le ¬Y ¬X (le_neg_swap forward). 
    -- We have le a (¬x). By le_neg_swap, le ¬(¬x) ¬a, i.e., le x ¬a [neg_neg].
    have step : le a (neg x) := by
      show oplus (neg a) (neg x) = one
      -- Use: neg(odot a x) = oplus (neg a) (neg x). And neg(zero) = one.
      have : neg (odot a x) = neg zero := congrArg neg h2
      rw [neg_odot] at this
      rw [this]
      rfl
    have := le_neg_swap step
    rwa [neg_neg] at this
  exact le_antisymm h_le_neg h_le_x

/-- Full Lemma 1.3 statement: `¬a` is characterized by `a ⊕ ¬a = 1` and `a ⊙ ¬a = 0`,
    and is the UNIQUE such element. -/
theorem neg_iff_unique (a x : A) :
    (oplus a x = one ∧ odot a x = zero) ↔ x = neg a := by
  constructor
  · rintro ⟨h1, h2⟩; exact neg_unique h1 h2
  · intro h; rw [h]; exact neg_satisfies a

/-! ## Lemma 1.8 — Propagation of disjointness

  The classical statement: if `x ∧ y = 0` (i.e., `x` and `y` are "disjoint"),
  then `(nx) ∧ (ny) = 0` for every natural `n`, where `nx = x ⊕ x ⊕ ⋯ ⊕ x`.

  This is essential for the existence of prime ideals: it ensures that
  doubling (or n-folding) preserves disjointness, which lets the Zorn's-lemma
  argument in Proposition 1.19 separate any nonzero `a` from `{0}` by a prime
  ideal. We prove the structural single-step version,

      x ∧ y = 0  ⟹  (x ⊕ x) ∧ y = 0,

  from which the symmetric statement and arbitrary iteration follow.
-/

/-- The key inequality: if `x ∧ y = 0` then `(2x) ∧ y = 0`. The proof follows
    Mundici's chain: `x = x ⊕ 0 = x ⊕ (x ∧ y) = (x⊕x) ∧ (x⊕y) ≥ (2x) ∧ y`,
    using Proposition 1.6(ii) (distributivity of `⊕` over `∧`) and monotonicity. -/
theorem mvinf_two_left_of_mvinf {x y : A} (h : mvinf x y = zero) :
    mvinf (oplus x x) y = zero := by
  -- Step 1: x = (x⊕x) ∧ (x⊕y).
  -- Compute: x = x ⊕ 0 = x ⊕ (x ∧ y) = (x⊕x) ∧ (x⊕y)  [Prop 1.6(ii)].
  have eq1 : x = mvinf (oplus x x) (oplus x y) := by
    calc x = oplus x zero := (oplus_zero x).symm
      _ = oplus x (mvinf x y) := by rw [h]
      _ = mvinf (oplus x x) (oplus x y) := oplus_distrib_mvinf_left x x y
  -- Step 2: x ⊕ y ≥ y (since 0 ≤ x).
  have hy_le : le y (oplus x y) := by
    -- y = 0 ⊕ y, and 0 ≤ x, so 0 ⊕ y ≤ x ⊕ y by oplus_mono_left.
    have := oplus_mono_left y (le_zero x)
    -- this : le (oplus zero y) (oplus x y)
    rwa [zero_oplus] at this
  -- Step 3: (2x) ∧ y ≤ (2x) ∧ (x⊕y) = x (by eq1 reversed and meet monotonicity).
  have step3 : le (mvinf (oplus x x) y) (mvinf (oplus x x) (oplus x y)) := by
    -- mvinf is monotone in the second arg: y ≤ x⊕y ⟹ (2x ∧ y) ≤ (2x ∧ (x⊕y)).
    -- We have mvinf_glb: w ≤ a ∧ w ≤ b → w ≤ mvinf a b. Apply with w = mvinf (2x) y.
    apply mvinf_glb
    · exact le_mvinf_left (oplus x x) y
    · exact le_trans (le_mvinf_right (oplus x x) y) hy_le
  -- Step 4: (2x) ∧ y ≤ x (using eq1).
  rw [← eq1] at step3
  -- step3 : le (mvinf (oplus x x) y) x
  -- Step 5: also (2x) ∧ y ≤ y (lower bound).
  have step5 : le (mvinf (oplus x x) y) y := le_mvinf_right (oplus x x) y
  -- Step 6: so (2x) ∧ y ≤ x ∧ y = 0.
  have step6 : le (mvinf (oplus x x) y) (mvinf x y) := mvinf_glb step3 step5
  rw [h] at step6
  exact eq_zero_of_le_zero step6

/-- Symmetric form: if `x ∧ y = 0` then `x ∧ (y ⊕ y) = 0`. -/
theorem mvinf_two_right_of_mvinf {x y : A} (h : mvinf x y = zero) :
    mvinf x (oplus y y) = zero := by
  rw [mvinf_comm]
  rw [mvinf_comm] at h
  exact mvinf_two_left_of_mvinf h

/-- Combining the two: if `x ∧ y = 0` then `(2x) ∧ (2y) = 0`. -/
theorem mvinf_two_both_of_mvinf {x y : A} (h : mvinf x y = zero) :
    mvinf (oplus x x) (oplus y y) = zero := by
  exact mvinf_two_right_of_mvinf (mvinf_two_left_of_mvinf h)

/-! ## Iterated `n`-fold disjointness

  Define `nfold n x = x ⊕ x ⊕ ⋯ ⊕ x` (n times). Then if `x ∧ y = 0`, we have
  `(nfold n x) ∧ y = 0` for all `n ≥ 0`. (And by symmetry, also
  `x ∧ (nfold n y) = 0` and `(nfold n x) ∧ (nfold n y) = 0` for all `n`.)

  This is Mundici Lemma 1.8 in its full generality.
-/

/-- `n`-fold sum: `nfold 0 x = 0`, `nfold (n+1) x = x ⊕ nfold n x`. -/
def nfold (n : Nat) (x : A) : A :=
  match n with
  | 0 => zero
  | n+1 => oplus x (nfold n x)

@[simp] theorem nfold_zero (x : A) : nfold 0 x = (zero : A) := rfl
@[simp] theorem nfold_succ (n : Nat) (x : A) : nfold (n+1) x = oplus x (nfold n x) := rfl

/-! Helper for the n-fold extension: if `a ∧ y = 0` then adding any element to `a`
    on the `⊕` side doesn't introduce new overlap with `y`. -/

/-- If `a ∧ y = 0` then `¬y ⊕ a = ¬y`. (The disjointness forces `a` to "fit under" `¬y`.) -/
theorem neg_oplus_eq_of_mvinf_zero {a y : A} (h : mvinf a y = zero) :
    oplus (neg y) a = neg y := by
  -- a ∧ y = y ⊙ (¬y ⊕ a) [via meet_idiom_swap on the canonical form].
  -- Actually: mvinf a y = a ⊙ (¬a ⊕ y) by def of mvinf. Use mvinf_comm to get y ⊙ (¬y ⊕ a).
  have h' : odot y (oplus (neg y) a) = zero := by
    have := h
    rw [mvinf_comm] at this
    -- this : mvinf y a = 0, which unfolds to: odot y (oplus (neg y) a) = 0
    exact this
  -- From odot y X = 0 with X = (¬y ⊕ a), we get X ≤ ¬y via residuation.
  -- odot y X = neg(¬y ⊕ ¬X) = 0 means ¬y ⊕ ¬X = ¬0 = 1, i.e., le X ¬y.
  have hle : le (oplus (neg y) a) (neg y) := by
    apply le_of_odot_neg_zero
    -- Goal: (¬y ⊕ a) ⊙ ¬¬y = 0, i.e., (¬y ⊕ a) ⊙ y = 0
    rw [neg_neg]
    rw [odot_comm]
    exact h'
  -- And ¬y ≤ ¬y ⊕ a trivially.
  have hge : le (neg y) (oplus (neg y) a) := by
    show oplus (neg (neg y)) (oplus (neg y) a) = one
    rw [neg_neg, ← oplus_assoc, self_oplus_neg, one_oplus]
  exact le_antisymm hle hge

/-- The key combiner: if `a ∧ y = 0` then `(a ⊕ b) ∧ y = b ∧ y` for every `b`. -/
theorem mvinf_oplus_eq_of_left_mvinf_zero {a y : A} (h : mvinf a y = zero) (b : A) :
    mvinf (oplus a b) y = mvinf b y := by
  -- (a⊕b) ∧ y = y ⊙ (¬y ⊕ (a⊕b)) = y ⊙ (¬y ⊕ a ⊕ b) = y ⊙ (¬y ⊕ b) = b ∧ y.
  -- Using neg_oplus_eq_of_mvinf_zero: ¬y ⊕ a = ¬y, so ¬y ⊕ a ⊕ b = ¬y ⊕ b.
  rw [mvinf_comm, mvinf_comm b y]
  -- Goal: mvinf y (oplus a b) = mvinf y b
  show odot y (oplus (neg y) (oplus a b)) = odot y (oplus (neg y) b)
  rw [← oplus_assoc]
  rw [neg_oplus_eq_of_mvinf_zero h]

/-- **Mundici Lemma 1.8 (full version)**: if `x ∧ y = 0` then `(nfold n x) ∧ y = 0`
    for every natural `n`. -/
theorem nfold_mvinf_left_of_mvinf {x y : A} (h : mvinf x y = zero) :
    ∀ n, mvinf (nfold n x) y = zero
  | 0 => by
      show mvinf zero y = zero
      apply eq_zero_of_le_zero
      exact le_mvinf_left zero y
  | n+1 => by
      show mvinf (oplus x (nfold n x)) y = zero
      have ih := nfold_mvinf_left_of_mvinf h n
      -- By the combiner: (x ⊕ nfold n x) ∧ y = (nfold n x) ∧ y = 0 (by IH).
      rw [mvinf_oplus_eq_of_left_mvinf_zero h (nfold n x)]
      exact ih

end MVAlgebra
end Luk
