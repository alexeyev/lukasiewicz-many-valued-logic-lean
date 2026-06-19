import Lukasiewicz.Lattice

namespace Luk.MVAlgebra

variable {A : Type _} [MVAlgebra A]


-- ============================================================================
-- THE DISTANCE FUNCTION ON AN MV-ALGEBRA
-- (Mundici, "Introducing MV-Algebras", Proposition 1.10)
--
-- The function d(x, y) := (x ⊖ y) ⊕ (y ⊖ x), where x ⊖ y := x ⊙ ¬y, gives
-- every MV-algebra a natural distance structure. On the standard MV-algebra
-- [0,1] it computes |x - y|; on a Boolean algebra it is symmetric difference.
--
-- This file proves the five metric properties of Mundici's Proposition 1.10.
-- The distance function bridges MV-algebra theory to analysis (uniform
-- continuity of the operations) and is the machinery via which congruences
-- on MV-algebras are characterized:  x ~ y  iff  d(x, y) ∈ I  for some ideal I.
-- ============================================================================

/-- The **distance function** on an MV-algebra:
    `d(x, y) := (x ⊖ y) ⊕ (y ⊖ x)`, where `x ⊖ y := x ⊙ ¬y`.
    On `[0,1]` this computes `|x − y|`. -/
def dist (x y : A) : A := oplus (odot x (neg y)) (odot y (neg x))

/-! ## Useful auxiliary order facts -/

/-- `x ⊙ y ≤ x`. -/
theorem odot_le_left' (x y : A) : le (odot x y) x := by
  show oplus (neg (odot x y)) x = one
  rw [neg_odot, oplus_comm (neg x) (neg y), oplus_assoc, neg_oplus_self]
  exact oplus_one _

/-- `x ⊙ y ≤ y`. -/
theorem odot_le_right' (x y : A) : le (odot x y) y := by
  rw [odot_comm]; exact odot_le_left' y x

/-- `mvinf x y ≤ y`. -/
theorem le_mvinf_le_right (x y : A) : le (mvinf x y) y := le_mvinf_right x y

/-- `mvinf x y ≤ x`. -/
theorem le_mvinf_le_left (x y : A) : le (mvinf x y) x := le_mvinf_left x y

/-- `x ≤ y → x ⊙ ¬y = 0` (Mundici Lemma 1.2 (i) ⇒ (ii)). -/
theorem odot_neg_zero_of_le {x y : A} (h : le x y) : odot x (neg y) = zero := by
  unfold le imp at h
  show neg (oplus (neg x) (neg (neg y))) = zero
  rw [neg_neg, h]; exact neg_one_eq_zero

/-- `x ⊙ ¬y = 0 → x ≤ y` (Lemma 1.2 (ii) ⇒ (i)). -/
theorem le_of_odot_neg_zero {x y : A} (h : odot x (neg y) = zero) : le x y := by
  have e1 : neg (odot x (neg y)) = oplus (neg x) y := by
    rw [neg_odot, neg_neg]
  have : oplus (neg x) y = neg zero := by rw [← e1, h]
  show oplus (neg x) y = one
  rw [this]; rfl

/-- An element ≤ zero equals zero. -/
theorem eq_zero_of_le_zero {x : A} (h : le x zero) : x = zero :=
  le_antisymm h (le_zero x)

/-! ## Property (i): `d(x, y) = 0 ↔ x = y` -/

@[simp] theorem dist_self (x : A) : dist x x = zero := by
  unfold dist
  rw [self_odot_neg]; exact zero_oplus _

theorem eq_of_dist_zero {x y : A} (h : dist x y = zero) : x = y := by
  -- d(x,y) = (x⊖y) ⊕ (y⊖x) = 0. Both summands are ≤ d(x,y) = 0.
  have h1 : odot x (neg y) = zero := by
    apply eq_zero_of_le_zero
    have key : le (odot x (neg y)) (dist x y) := by
      show oplus (neg (odot x (neg y))) (dist x y) = one
      unfold dist
      rw [← oplus_assoc, oplus_comm (neg (odot x (neg y))) (odot x (neg y)),
          self_oplus_neg, one_oplus]
    rw [h] at key; exact key
  have h2 : odot y (neg x) = zero := by
    apply eq_zero_of_le_zero
    have key : le (odot y (neg x)) (dist x y) := by
      show oplus (neg (odot y (neg x))) (dist x y) = one
      unfold dist
      rw [oplus_comm (odot x (neg y)) (odot y (neg x))]
      rw [← oplus_assoc, oplus_comm (neg (odot y (neg x))) (odot y (neg x)),
          self_oplus_neg, one_oplus]
    rw [h] at key; exact key
  exact le_antisymm (le_of_odot_neg_zero h1) (le_of_odot_neg_zero h2)

theorem dist_eq_zero_iff (x y : A) : dist x y = zero ↔ x = y :=
  ⟨eq_of_dist_zero, fun h => h ▸ dist_self x⟩

/-- `x ⊙ 1 = x`: the top element is the `⊙`-identity. -/
theorem odot_one (x : A) : odot x one = x := by
  show neg (oplus (neg x) (neg one)) = x
  rw [neg_one_eq_zero, oplus_zero, neg_neg]

/-- `d(x, 0) = x`: the distance of `x` from the bottom element is `x` itself. -/
theorem dist_zero_right (x : A) : dist x zero = x := by
  show oplus (odot x (neg zero)) (odot zero (neg x)) = x
  rw [neg_zero_eq_one, odot_one, zero_odot, oplus_zero]

/-- `d(x, 1) = ¬x`: the distance of `x` from the top element is its negation. -/
theorem dist_one_right (x : A) : dist x one = neg x := by
  show oplus (odot x (neg one)) (odot one (neg x)) = neg x
  rw [neg_one_eq_zero, odot_zero, zero_oplus]
  show neg (oplus (neg one) (neg (neg x))) = neg x
  rw [neg_one_eq_zero, zero_oplus, neg_neg]

/-! ## Property (ii): symmetry `d(x, y) = d(y, x)` -/

theorem dist_comm (x y : A) : dist x y = dist y x := by
  unfold dist; rw [oplus_comm]

/-! ## Property (iii): triangle inequality

The key step is the single-side bound `(x⊖z) ≤ (x⊖y) ⊕ (y⊖z)`. Its proof
identifies `x ⊙ ¬z ⊙ (¬x⊕y) ⊙ (¬y⊕z)` (via residuation = `0`) as `mvinf x y ⊙ mvinf ¬z ¬y`,
which is bounded above by `y ⊙ ¬y = 0`.
-/

/-- `(x⊖z) ≤ (x⊖y) ⊕ (y⊖z)` — the single-side triangle inequality. -/
theorem ominus_triangle (x y z : A) :
    le (odot x (neg z)) (oplus (odot x (neg y)) (odot y (neg z))) := by
  -- Strategy via le_of_odot_neg_zero:
  -- Show (x⊙¬z) ⊙ ¬((x⊙¬y) ⊕ (y⊙¬z)) = 0.
  -- Expand the right factor:
  --   ¬((x⊙¬y) ⊕ (y⊙¬z)) = ¬(x⊙¬y) ⊙ ¬(y⊙¬z) = (¬x⊕y) ⊙ (¬y⊕z).
  -- So we need (x⊙¬z) ⊙ (¬x⊕y) ⊙ (¬y⊕z) = 0.
  -- Rearrange via odot_assoc + odot_comm:
  --   = x ⊙ (¬x⊕y) ⊙ ¬z ⊙ (¬y⊕z)
  --   = mvinf x y ⊙ ¬z ⊙ (¬y⊕z)        [meet_idiom: x⊙(¬x⊕y) = mvinf x y]
  --   = mvinf x y ⊙ (¬z ⊙ (¬y⊕z))
  -- Now ¬z ⊙ (¬y⊕z) = ¬z ⊙ (z⊕¬y) [oplus_comm] = mvinf ¬z ¬y [meet_idiom_neg].
  --   = mvinf x y ⊙ mvinf ¬z ¬y.
  -- And mvinf x y ≤ y, mvinf ¬z ¬y ≤ ¬y, so their ⊙ ≤ y ⊙ ¬y = 0.
  apply le_of_odot_neg_zero
  -- Goal: (x⊙¬z) ⊙ ¬((x⊙¬y) ⊕ (y⊙¬z)) = 0
  show odot (odot x (neg z))
            (neg (oplus (odot x (neg y)) (odot y (neg z)))) = zero
  rw [neg_oplus, neg_odot, neg_odot, neg_neg, neg_neg]
  -- Goal: odot (odot x (neg z)) (odot (oplus (neg x) y) (oplus (neg y) z)) = zero
  -- Rearrange to expose mvinf structure. Apply odot_assoc to flatten:
  rw [odot_assoc]
  -- Goal: x ⊙ (¬z ⊙ ((¬x⊕y) ⊙ (¬y⊕z))) = 0
  rw [← odot_assoc (neg z) (oplus (neg x) y) _]
  -- Goal: x ⊙ ((¬z ⊙ (¬x⊕y)) ⊙ (¬y⊕z)) = 0
  rw [odot_comm (neg z) (oplus (neg x) y)]
  -- Goal: x ⊙ (((¬x⊕y) ⊙ ¬z) ⊙ (¬y⊕z)) = 0
  -- Reassoc the inner triple so (¬x⊕y) ⊙ (¬z ⊙ (¬y⊕z)):
  rw [odot_assoc (oplus (neg x) y) (neg z) (oplus (neg y) z)]
  -- Goal: x ⊙ ((¬x⊕y) ⊙ (¬z ⊙ (¬y⊕z))) = 0
  rw [← odot_assoc x (oplus (neg x) y) _]
  -- Goal: (x ⊙ (¬x⊕y)) ⊙ (¬z ⊙ (¬y⊕z)) = 0
  rw [meet_idiom]
  -- Goal: mvinf x y ⊙ (¬z ⊙ (¬y⊕z)) = 0
  rw [oplus_comm (neg y) z]
  -- Goal: mvinf x y ⊙ (¬z ⊙ (z⊕¬y)) = 0
  rw [meet_idiom_neg]
  -- Goal: mvinf x y ⊙ mvinf (neg z) (neg y) = 0
  -- Now mvinf x y ≤ y and mvinf (neg z) (neg y) ≤ neg y.
  -- So the product ≤ y ⊙ ¬y = 0.
  have h1 : le (mvinf x y) y := le_mvinf_right x y
  have h2 : le (mvinf (neg z) (neg y)) (neg y) := le_mvinf_right (neg z) (neg y)
  have h3 : le (odot (mvinf x y) (mvinf (neg z) (neg y))) (odot y (neg y)) := by
    have step1 := odot_mono_left (mvinf (neg z) (neg y)) h1
    -- step1 : le (odot (mvinf x y) (mvinf (neg z) (neg y))) (odot y (mvinf (neg z) (neg y)))
    have step2 := odot_mono_right y h2
    -- step2 : le (odot y (mvinf (neg z) (neg y))) (odot y (neg y))
    exact le_trans step1 step2
  rw [self_odot_neg] at h3
  -- h3 : le (...) zero
  exact eq_zero_of_le_zero h3

theorem dist_triangle (x y z : A) :
    le (dist x z) (oplus (dist x y) (dist y z)) := by
  unfold dist
  -- d(x,z) = (x⊖z) ⊕ (z⊖x)
  -- ≤ ((x⊖y) ⊕ (y⊖z)) ⊕ ((z⊖y) ⊕ (y⊖x))   [two applications of ominus_triangle]
  -- = ((x⊖y) ⊕ (y⊖x)) ⊕ ((y⊖z) ⊕ (z⊖y))   [reorder]
  -- = d(x,y) ⊕ d(y,z)
  have t1 : le (odot x (neg z)) (oplus (odot x (neg y)) (odot y (neg z))) :=
    ominus_triangle x y z
  have t2 : le (odot z (neg x)) (oplus (odot z (neg y)) (odot y (neg x))) :=
    ominus_triangle z y x
  have combo : le (oplus (odot x (neg z)) (odot z (neg x)))
                  (oplus (oplus (odot x (neg y)) (odot y (neg z)))
                         (oplus (odot z (neg y)) (odot y (neg x)))) := by
    exact le_trans (oplus_mono_left _ t1) (oplus_mono _ t2)
  -- Reorder the four-term sum:
  -- ((x⊖y) ⊕ (y⊖z)) ⊕ ((z⊖y) ⊕ (y⊖x)) = ((x⊖y) ⊕ (y⊖x)) ⊕ ((y⊖z) ⊕ (z⊖y))
  have rearr :
      oplus (oplus (odot x (neg y)) (odot y (neg z)))
            (oplus (odot z (neg y)) (odot y (neg x)))
    = oplus (oplus (odot x (neg y)) (odot y (neg x)))
            (oplus (odot y (neg z)) (odot z (neg y))) := by
    -- LHS = (X⊕Y) ⊕ (Z⊕W), where X=x⊖y, Y=y⊖z, Z=z⊖y, W=y⊖x.
    -- RHS = (X⊕W) ⊕ (Y⊕Z).
    -- Both equal X ⊕ Y ⊕ Z ⊕ W (or rearrangement of it).
    -- Path: X ⊕ Y ⊕ Z ⊕ W = X ⊕ Y ⊕ (Z ⊕ W) = X ⊕ (Y ⊕ (Z ⊕ W)) = ...
    -- = X ⊕ W ⊕ Y ⊕ Z via comm.
    rw [oplus_assoc (odot x (neg y)) (odot y (neg z)) _]
    rw [oplus_assoc (odot x (neg y)) (odot y (neg x)) _]
    congr 1
    -- Goal: oplus (y⊖z) (oplus (z⊖y) (y⊖x)) = oplus (y⊖x) (oplus (y⊖z) (z⊖y))
    rw [← oplus_assoc (odot y (neg z)) (odot z (neg y)) _]
    rw [← oplus_assoc (odot y (neg x)) (odot y (neg z)) _]
    rw [oplus_comm (oplus (odot y (neg z)) (odot z (neg y))) (odot y (neg x))]
    rw [oplus_assoc (odot y (neg x))]
  rw [rearr] at combo
  exact combo

/-! ## Property (iv): negation invariance `d(x, y) = d(¬x, ¬y)` -/

theorem dist_neg (x y : A) : dist x y = dist (neg x) (neg y) := by
  unfold dist
  rw [neg_neg, neg_neg]
  rw [odot_comm (neg x) y, odot_comm (neg y) x]
  rw [oplus_comm]

/-! ## Property (v): `d(x ⊕ s, y ⊕ t) ≤ d(x, y) ⊕ d(s, t)` —
    `⊕` is non-expansive in both arguments. -/

/-- `(x⊕s) ⊖ (y⊕t) ≤ (x⊖y) ⊕ (s⊖t)`. -/
theorem ominus_oplus_bound (x y s t : A) :
    le (odot (oplus x s) (neg (oplus y t)))
       (oplus (odot x (neg y)) (odot s (neg t))) := by
  -- Strategy via `le_of_odot_neg_zero`: show that
  --   (x⊕s) ⊙ ¬(y⊕t) ⊙ ¬((x⊖y) ⊕ (s⊖t)) = 0.
  -- Expand the two negations:
  --   ¬(y⊕t)             = ¬y ⊙ ¬t                (neg_oplus)
  --   ¬((x⊖y) ⊕ (s⊖t))  = (¬x⊕y) ⊙ (¬s⊕t)         (neg_oplus + neg_odot + neg_neg)
  -- So we need
  --   (x⊕s) ⊙ (¬y ⊙ ¬t) ⊙ ((¬x⊕y) ⊙ (¬s⊕t)) = 0.
  -- The trick: rearrange the five ⊙-factors so the meet idioms appear,
  --   ¬y ⊙ (¬x⊕y) = mvinf ¬y ¬x      (meet_idiom_neg, after oplus_comm)
  --   ¬t ⊙ (¬s⊕t) = mvinf ¬t ¬s      (meet_idiom_neg, after oplus_comm)
  -- yielding
  --   (x⊕s) ⊙ mvinf ¬y ¬x ⊙ mvinf ¬t ¬s.
  -- Bound: mvinf ¬y ¬x ≤ ¬x, mvinf ¬t ¬s ≤ ¬s, so this is
  --   ≤ (x⊕s) ⊙ ¬x ⊙ ¬s = (x⊕s) ⊙ (¬x ⊙ ¬s) = (x⊕s) ⊙ ¬(x⊕s) = 0.
  apply le_of_odot_neg_zero
  show odot (odot (oplus x s) (neg (oplus y t)))
            (neg (oplus (odot x (neg y)) (odot s (neg t)))) = zero
  -- Expand negations on the right.
  rw [neg_oplus (odot x (neg y)) (odot s (neg t))]
  rw [neg_odot x (neg y), neg_odot s (neg t)]
  rw [neg_neg, neg_neg]
  -- Goal: (x⊕s) ⊙ ¬(y⊕t) ⊙ ((¬x⊕y) ⊙ (¬s⊕t)) = 0
  rw [neg_oplus y t]
  -- Goal: ((x⊕s) ⊙ (¬y ⊙ ¬t)) ⊙ ((¬x⊕y) ⊙ (¬s⊕t)) = 0
  -- Rewrite to the target form (x⊕s) ⊙ (mvinf ¬y ¬x ⊙ mvinf ¬t ¬s), then bound by 0.
  -- The plan is: rearrange the parenthesization so it becomes
  --   (x⊕s) ⊙ ((¬y ⊙ (¬x⊕y)) ⊙ (¬t ⊙ (¬s⊕t)))
  -- which then equals (x⊕s) ⊙ (mvinf ¬y ¬x ⊙ mvinf ¬t ¬s).
  -- Each step uses odot_assoc and odot_comm.
  have key :
      odot (odot (oplus x s) (odot (neg y) (neg t)))
           (odot (oplus (neg x) y) (oplus (neg s) t))
    = odot (oplus x s)
           (odot (odot (neg y) (oplus (neg x) y))
                 (odot (neg t) (oplus (neg s) t))) := by
    -- Both sides equal (x⊕s) ⊙ ¬y ⊙ ¬t ⊙ (¬x⊕y) ⊙ (¬s⊕t) after associativity + commutativity
    -- on the inner four factors. We prove it by rewriting LHS and RHS to that flat form.
    rw [odot_assoc (oplus x s) (odot (neg y) (neg t)) _]
    -- LHS: (x⊕s) ⊙ ((¬y ⊙ ¬t) ⊙ ((¬x⊕y) ⊙ (¬s⊕t)))
    congr 1
    -- Goal: (¬y ⊙ ¬t) ⊙ ((¬x⊕y) ⊙ (¬s⊕t)) = (¬y ⊙ (¬x⊕y)) ⊙ (¬t ⊙ (¬s⊕t))
    -- Both expand to ¬y ⊙ ¬t ⊙ (¬x⊕y) ⊙ (¬s⊕t) after flattening.
    rw [odot_assoc (neg y) (neg t) (odot (oplus (neg x) y) (oplus (neg s) t))]
    -- LHS: ¬y ⊙ (¬t ⊙ ((¬x⊕y) ⊙ (¬s⊕t)))
    rw [odot_assoc (neg y) (oplus (neg x) y) (odot (neg t) (oplus (neg s) t))]
    -- RHS: ¬y ⊙ ((¬x⊕y) ⊙ (¬t ⊙ (¬s⊕t)))
    congr 1
    -- Goal: ¬t ⊙ ((¬x⊕y) ⊙ (¬s⊕t)) = (¬x⊕y) ⊙ (¬t ⊙ (¬s⊕t))
    rw [← odot_assoc (neg t) (oplus (neg x) y) _]
    -- LHS: (¬t ⊙ (¬x⊕y)) ⊙ (¬s⊕t)
    rw [← odot_assoc (oplus (neg x) y) (neg t) _]
    -- RHS: ((¬x⊕y) ⊙ ¬t) ⊙ (¬s⊕t)
    -- Now LHS = (¬t ⊙ (¬x⊕y)) ⊙ (¬s⊕t)  vs  RHS = ((¬x⊕y) ⊙ ¬t) ⊙ (¬s⊕t).
    rw [odot_comm (neg t) (oplus (neg x) y)]
  rw [key]
  -- Goal: (x⊕s) ⊙ ((¬y ⊙ (¬x⊕y)) ⊙ (¬t ⊙ (¬s⊕t))) = 0
  -- Apply meet idiom to both inner factors.
  rw [oplus_comm (neg x) y, oplus_comm (neg s) t]
  -- Goal: (x⊕s) ⊙ ((¬y ⊙ (y ⊕ ¬x)) ⊙ (¬t ⊙ (t ⊕ ¬s))) = 0
  rw [meet_idiom_neg y (neg x), meet_idiom_neg t (neg s)]
  -- Goal: (x⊕s) ⊙ (mvinf ¬y ¬x ⊙ mvinf ¬t ¬s) = 0
  -- Now bound: mvinf ¬y ¬x ≤ ¬x, mvinf ¬t ¬s ≤ ¬s.
  -- So (x⊕s) ⊙ (mvinf ¬y ¬x ⊙ mvinf ¬t ¬s) ≤ (x⊕s) ⊙ (¬x ⊙ ¬s) = (x⊕s) ⊙ ¬(x⊕s) = 0.
  have h1 : le (mvinf (neg y) (neg x)) (neg x) := le_mvinf_right (neg y) (neg x)
  have h2 : le (mvinf (neg t) (neg s)) (neg s) := le_mvinf_right (neg t) (neg s)
  have h3 : le (odot (mvinf (neg y) (neg x)) (mvinf (neg t) (neg s)))
               (odot (neg x) (neg s)) := by
    exact le_trans (odot_mono_left _ h1) (odot_mono_right (neg x) h2)
  have h4 : le (odot (oplus x s) (odot (mvinf (neg y) (neg x)) (mvinf (neg t) (neg s))))
               (odot (oplus x s) (odot (neg x) (neg s))) :=
    odot_mono_right (oplus x s) h3
  -- (x⊕s) ⊙ (¬x ⊙ ¬s) = (x⊕s) ⊙ ¬(x⊕s) = 0.
  have h5 : odot (oplus x s) (odot (neg x) (neg s)) = zero := by
    rw [← neg_oplus]; exact self_odot_neg _
  rw [h5] at h4
  exact eq_zero_of_le_zero h4

theorem dist_oplus_bound (x y s t : A) :
    le (dist (oplus x s) (oplus y t)) (oplus (dist x y) (dist s t)) := by
  -- Apply ominus_oplus_bound twice and rearrange the four-term sum.
  unfold dist
  -- Goal: le ((x⊕s)⊖(y⊕t) ⊕ (y⊕t)⊖(x⊕s)) (((x⊖y) ⊕ (y⊖x)) ⊕ ((s⊖t) ⊕ (t⊖s)))
  have h1 : le (odot (oplus x s) (neg (oplus y t)))
               (oplus (odot x (neg y)) (odot s (neg t))) := ominus_oplus_bound x y s t
  have h2 : le (odot (oplus y t) (neg (oplus x s)))
               (oplus (odot y (neg x)) (odot t (neg s))) := ominus_oplus_bound y x t s
  have combo : le (oplus (odot (oplus x s) (neg (oplus y t)))
                         (odot (oplus y t) (neg (oplus x s))))
                  (oplus (oplus (odot x (neg y)) (odot s (neg t)))
                         (oplus (odot y (neg x)) (odot t (neg s)))) := by
    exact le_trans (oplus_mono_left _ h1) (oplus_mono _ h2)
  -- Reorder RHS from ((x⊖y) ⊕ (s⊖t)) ⊕ ((y⊖x) ⊕ (t⊖s))
  --             to  ((x⊖y) ⊕ (y⊖x)) ⊕ ((s⊖t) ⊕ (t⊖s)).
  have rearr :
      oplus (oplus (odot x (neg y)) (odot s (neg t)))
            (oplus (odot y (neg x)) (odot t (neg s)))
    = oplus (oplus (odot x (neg y)) (odot y (neg x)))
            (oplus (odot s (neg t)) (odot t (neg s))) := by
    rw [oplus_assoc (odot x (neg y)) (odot s (neg t)) _]
    rw [oplus_assoc (odot x (neg y)) (odot y (neg x)) _]
    congr 1
    -- Goal: (s⊖t) ⊕ ((y⊖x) ⊕ (t⊖s)) = (y⊖x) ⊕ ((s⊖t) ⊕ (t⊖s))
    -- Setting a = s⊖t, b = y⊖x, c = t⊖s: a ⊕ (b ⊕ c) = b ⊕ (a ⊕ c).
    rw [← oplus_assoc (odot s (neg t)) (odot y (neg x)) (odot t (neg s))]
    -- (s⊖t) ⊕ (y⊖x) ⊕ (t⊖s) = (y⊖x) ⊕ ((s⊖t) ⊕ (t⊖s))
    rw [oplus_comm (odot s (neg t)) (odot y (neg x))]
    -- (y⊖x) ⊕ (s⊖t) ⊕ (t⊖s) = (y⊖x) ⊕ ((s⊖t) ⊕ (t⊖s))
    rw [oplus_assoc (odot y (neg x)) (odot s (neg t)) (odot t (neg s))]
  rw [rearr] at combo
  exact combo

end MVAlgebra
end Luk
