namespace Luk
class MVAlgebra (A : Type _) where
  oplus : A → A → A
  neg : A → A
  zero : A
  oplus_assoc : ∀ x y z, oplus (oplus x y) z = oplus x (oplus y z)
  oplus_comm : ∀ x y, oplus x y = oplus y x
  oplus_zero : ∀ x, oplus x zero = x
  neg_neg : ∀ x, neg (neg x) = x
  oplus_negzero : ∀ x, oplus x (neg zero) = neg zero
  mv_axiom : ∀ x y, oplus (neg (oplus (neg x) y)) y = oplus (neg (oplus (neg y) x)) x

namespace MVAlgebra
variable {A : Type _} [MVAlgebra A]

def one : A := neg (zero : A)
def imp (x y : A) : A := oplus (neg x) y
def odot (x y : A) : A := neg (oplus (neg x) (neg y))
def le (x y : A) : Prop := imp x y = one

@[simp] theorem neg_zero_eq_one : neg (zero:A) = one := rfl
@[simp] theorem neg_one_eq_zero : neg (one:A) = zero := by show neg (neg (zero:A)) = zero; rw [neg_neg]
@[simp] theorem zero_oplus (x:A) : oplus (zero:A) x = x := by rw [oplus_comm]; exact oplus_zero x
@[simp] theorem oplus_one (x:A) : oplus x (one:A) = one := oplus_negzero x
@[simp] theorem one_oplus (x:A) : oplus (one:A) x = one := by rw [oplus_comm]; exact oplus_negzero x

theorem neg_oplus_self (x:A) : oplus (neg x) x = (one:A) := by
  have h := mv_axiom x (one:A); simp at h; exact h.symm
theorem self_oplus_neg (x:A) : oplus x (neg x) = (one:A) := by rw [oplus_comm]; exact neg_oplus_self x

theorem odot_neg (x y:A) : odot x (neg y) = neg (oplus (neg x) y) := by unfold odot; rw [neg_neg]
theorem neg_odot (x z:A) : neg (odot x z) = oplus (neg x) (neg z) := by unfold odot; rw [neg_neg]
theorem odot_comm (x y:A) : odot x y = odot y x := by unfold odot; rw [oplus_comm]
theorem neg_oplus (x y:A) : neg (oplus x y) = odot (neg x) (neg y) := by unfold odot; rw [neg_neg, neg_neg]

theorem neg_odot_self (x : A) : odot (neg x) x = zero := by
  show neg (oplus (neg (neg x)) (neg x)) = zero
  rw [neg_neg, self_oplus_neg, show (one:A) = neg zero from rfl, neg_neg]

theorem self_odot_neg (x : A) : odot x (neg x) = zero := by
  rw [odot_comm]; exact neg_odot_self x

theorem odot_assoc (x y z : A) : odot (odot x y) z = odot x (odot y z) := by
  unfold odot; congr 1; rw [neg_neg, neg_neg, oplus_assoc]

theorem odot_zero (x : A) : odot x zero = zero := by
  show neg (oplus (neg x) (neg zero)) = zero
  rw [oplus_negzero, neg_neg]

theorem zero_odot (x : A) : odot (zero : A) x = zero := by
  rw [odot_comm]; exact odot_zero x

/-- Sup definition. -/
def mvsup (x y : A) : A := oplus (odot x (neg y)) y

theorem mvsup_comm (x y : A) : mvsup x y = mvsup y x := by
  unfold mvsup
  rw [odot_neg, odot_neg]
  exact mv_axiom x y

/-- Inf (lattice meet). -/
def mvinf (x y : A) : A := odot x (imp x y)

theorem mvinf_comm (a b : A) : mvinf a b = mvinf b a := by
  unfold mvinf
  show neg (oplus (neg a) (neg (oplus (neg a) b))) = neg (oplus (neg b) (neg (oplus (neg b) a)))
  congr 1
  have h := mv_axiom (neg a) (neg b)
  rw [neg_neg, neg_neg] at h
  rw [oplus_comm _ (neg b)] at h; rw [oplus_comm _ (neg a)] at h
  rw [oplus_comm (neg a) b, oplus_comm (neg b) a]
  exact h.symm

-- An alternative form of the meet idiom: a ⊙ (¬a ⊕ b) = b ⊙ (¬b ⊕ a).
theorem meet_idiom_swap (a b : A) : odot a (oplus (neg a) b) = odot b (oplus (neg b) a) := by
  -- This is mvinf a b = mvinf b a unfolded.
  show odot a (imp a b) = odot b (imp b a)
  exact mvinf_comm a b

/-- Helper: a ⊙ (¬a ⊕ b) = a ∧ b, in the form needed. -/
theorem meet_idiom (a b : A) : odot a (oplus (neg a) b) = mvinf a b := by
  unfold mvinf imp; rfl

/-- The meet idiom swapped (≡ mvinf_comm). -/  
theorem meet_idiom_dual (a b : A) : odot a (oplus (neg a) b) = odot b (oplus (neg b) a) := by
  rw [meet_idiom, meet_idiom]
  exact mvinf_comm a b

/-- mvinf with negated first argument: `mvinf (¬a) b = (¬a) ⊙ (a ⊕ b)`. -/
theorem mvinf_neg_form (a b : A) : mvinf (neg a) b = odot (neg a) (oplus a b) := by
  show odot (neg a) (oplus (neg (neg a)) b) = odot (neg a) (oplus a b)
  rw [neg_neg]

/-- meet idiom with negated first argument: `(¬a) ⊙ (a ⊕ b) = mvinf (¬a) b`. -/
theorem meet_idiom_neg (a b : A) : odot (neg a) (oplus a b) = mvinf (neg a) b :=
  (mvinf_neg_form a b).symm

/-- MUNDICI'S PROPOSITION 1.7: (x⊖y) ∧ (y⊖x) = 0. 
    Proof by sequence of meet_idiom swaps + odot_assoc/comm, ending with ¬x ⊙ x = 0. -/
theorem mundici_prop17 (x y : A) : mvinf (odot x (neg y)) (odot y (neg x)) = zero := by
  -- Unfold mvinf to get explicit form.
  show odot (odot x (neg y)) (oplus (neg (odot x (neg y))) (odot y (neg x))) = zero
  -- Simplify neg(x⊙¬y) = ¬x ⊕ y
  rw [show neg (odot x (neg y)) = oplus (neg x) y by rw [neg_odot, neg_neg]]
  -- Reassociate inner oplus: (¬x ⊕ y) ⊕ q  = y ⊕ (¬x ⊕ q)
  rw [oplus_comm (neg x) y, oplus_assoc y (neg x) (odot y (neg x))]
  -- Break the outer odot using odot_assoc: odot (x⊙¬y) Z = odot x (¬y ⊙ Z)
  rw [odot_assoc x (neg y) _]
  -- Goal now: odot x (odot (neg y) (oplus y (oplus (neg x) (odot y (neg x))))) = zero
  -- Apply meet idiom (negated): odot (¬y) (oplus y X) = mvinf (¬y) X
  rw [meet_idiom_neg y (oplus (neg x) (odot y (neg x)))]
  -- Goal: odot x (mvinf (neg y) (oplus (neg x) (odot y (neg x)))) = zero
  -- Apply mvinf_comm: mvinf (¬y) Z = mvinf Z (¬y)
  rw [mvinf_comm]
  -- Goal: odot x (mvinf (oplus (neg x) (odot y (neg x))) (neg y)) = zero
  -- Unfold mvinf to get: ((¬x⊕q) ⊙ (¬(¬x⊕q) ⊕ ¬y))
  show odot x (odot (oplus (neg x) (odot y (neg x))) 
                    (oplus (neg (oplus (neg x) (odot y (neg x)))) (neg y))) = zero
  -- Break the inner odot using odot_assoc backwards (so x is multiplied with (¬x⊕q)).
  rw [← odot_assoc]
  -- Goal: odot (odot x (oplus (neg x) (odot y (neg x)))) (oplus (neg (oplus (neg x) (odot y (neg x)))) (neg y)) = zero
  -- The factor (x ⊙ (¬x ⊕ q)) is mvinf x q. Apply meet_idiom_dual to swap to (q ⊙ (¬q ⊕ x)).
  rw [meet_idiom_dual x (odot y (neg x))]
  -- Goal: odot (odot (y⊙¬x) (oplus (neg(y⊙¬x)) x)) (oplus (neg (oplus (neg x) (y⊙¬x))) (neg y)) = zero
  -- Expand (y⊙¬x) ⊙ Z using odot_assoc: = y ⊙ (¬x ⊙ Z)
  rw [odot_assoc y (neg x) _]
  -- Apply outer odot_assoc to flatten:
  rw [odot_assoc y _ _]
  -- Goal: odot y (odot (odot (neg x) (oplus (neg(y⊙¬x)) x)) (oplus (neg (oplus (neg x) (y⊙¬x))) (neg y))) = zero
  -- 
  -- Move y to the right: by odot_comm.
  rw [odot_comm y _]
  -- Goal: odot (odot (odot (neg x) (oplus (neg(y⊙¬x)) x)) (oplus (neg (oplus (neg x) (y⊙¬x))) (neg y))) y = zero
  -- Re-associate so y is paired with the rightmost factor (last oplus expression):
  rw [odot_assoc (odot (neg x) (oplus (neg (odot y (neg x))) x)) _ y]
  -- Goal: odot (odot (neg x) (oplus (neg(y⊙¬x)) x)) (odot (oplus (neg(¬x⊕(y⊙¬x))) (neg y)) y) = zero
  -- Now the rightmost: odot (oplus (neg X) (neg y)) y where X = ¬x ⊕ (y⊙¬x).
  -- By odot_comm: = odot y (oplus (neg X) (neg y)).
  -- By oplus_comm: = odot y (oplus (neg y) (neg X)).
  -- This is mvinf y (neg X) by meet_idiom.
  -- Hmm but I need to bring (neg X) in a more useful form. Let me first try the rewrite.
  rw [odot_comm (oplus (neg (oplus (neg x) (odot y (neg x)))) (neg y)) y]
  rw [oplus_comm (neg (oplus (neg x) (odot y (neg x)))) (neg y)]
  -- Goal: ... odot y (oplus (neg y) (neg (¬x⊕(y⊙¬x))))
  -- Apply meet_idiom: odot y (oplus (neg y) X) = mvinf y X
  rw [meet_idiom y (neg (oplus (neg x) (odot y (neg x))))]
  -- Now neg of the inner: neg(¬x ⊕ (y⊙¬x)) = (x ⊙ ¬(y⊙¬x))  [neg_oplus + neg_neg]
  -- = x ⊙ (¬y ⊕ x)  [neg_odot + neg_neg... wait neg(y⊙¬x) = ¬y ⊕ x]
  -- Let me just rewrite.
  rw [show neg (oplus (neg x) (odot y (neg x))) = odot x (neg (odot y (neg x))) by
        rw [neg_oplus, neg_neg]]
  -- Goal: ... mvinf y (odot x (neg (odot y (neg x))))
  -- Apply mvinf_comm: 
  rw [mvinf_comm y _]
  -- Goal: ... mvinf (odot x (neg (odot y (neg x)))) y
  -- Unfold mvinf to get: (x⊙¬q) ⊙ (¬(x⊙¬q) ⊕ y)
  show odot (odot (neg x) (oplus (neg (odot y (neg x))) x)) 
       (odot (odot x (neg (odot y (neg x))))
             (oplus (neg (odot x (neg (odot y (neg x))))) y)) = zero
  -- After unfolding mvinf, we have the state:
  --   (¬x ⊙ (¬q ⊕ x)) ⊙ ((x ⊙ ¬q) ⊙ Z) = 0
  -- where q = y⊙¬x, Z = ¬(x⊙¬q) ⊕ y.
  -- 
  -- Plan: rearrange via assoc + comm to (¬x ⊙ x) ⊙ rest, then neg_odot_self.
  -- Step 1: odot_assoc forward (outer): (¬x⊙A)⊙B → ¬x⊙(A⊙B).
  rw [odot_assoc (neg x) (oplus (neg (odot y (neg x))) x) _]
  -- State: ¬x ⊙ ((¬q⊕x) ⊙ ((x⊙¬q)⊙Z))
  -- Step 2: odot_assoc forward inner: (x⊙¬q)⊙Z → x⊙(¬q⊙Z).
  rw [odot_assoc x (neg (odot y (neg x))) _]
  -- State: ¬x ⊙ ((¬q⊕x) ⊙ (x ⊙ (¬q⊙Z)))
  -- Step 3: odot_assoc backward: (¬q⊕x) ⊙ (x⊙W) → ((¬q⊕x)⊙x)⊙W
  rw [← odot_assoc (oplus (neg (odot y (neg x))) x) x _]
  -- State: ¬x ⊙ (((¬q⊕x)⊙x) ⊙ (¬q⊙Z))
  -- Step 4: odot_comm on ((¬q⊕x)⊙x) → (x⊙(¬q⊕x))
  rw [odot_comm (oplus (neg (odot y (neg x))) x) x]
  -- State: ¬x ⊙ ((x⊙(¬q⊕x)) ⊙ (¬q⊙Z))
  -- Step 5: odot_assoc forward: x⊙(¬q⊕x)⊙W → x⊙((¬q⊕x)⊙W)
  rw [odot_assoc x (oplus (neg (odot y (neg x))) x) _]
  -- State: ¬x ⊙ (x ⊙ ((¬q⊕x) ⊙ (¬q⊙Z)))
  -- Step 6: odot_assoc backward: ¬x ⊙ (x⊙W) → (¬x⊙x)⊙W
  rw [← odot_assoc (neg x) x _]
  -- State: (¬x⊙x) ⊙ ((¬q⊕x) ⊙ (¬q⊙Z))
  rw [neg_odot_self]
  -- State: zero ⊙ (...) = 0
  rw [zero_odot]


/-- `mvsup` ≤ each component. The MV-algebraic equation says that
    if `x ≤ y` then `x ∨ y = y`.  Mundici Lemma 1.2(iii) phrased via mvsup. -/
theorem mvsup_eq_of_le {x y : A} (h : le x y) : mvsup x y = y := by
  unfold mvsup
  -- Goal: (x ⊙ ¬y) ⊕ y = y. 
  -- le x y means imp x y = 1, i.e., ¬x ⊕ y = 1. 
  -- So neg(¬x ⊕ y) = 0, i.e., (x ⊙ ¬y) = 0 [neg_oplus + neg_neg].
  have key : odot x (neg y) = zero := by
    show neg (oplus (neg x) (neg (neg y))) = zero
    rw [neg_neg]
    -- Goal: neg (oplus (neg x) y) = zero
    -- From h: imp x y = one, i.e., oplus (neg x) y = one.
    unfold le imp at h
    rw [h]
    -- Goal: neg one = zero
    exact neg_one_eq_zero
  rw [key, zero_oplus]

/-- `mvsup x x = x`. Idempotence. -/
theorem mvsup_idem (x : A) : mvsup x x = x := by
  unfold mvsup
  show oplus (odot x (neg x)) x = x
  rw [self_odot_neg, zero_oplus]

/-- If `le y z` then `(z⊖y) ⊕ y = z`.  Mundici Lemma 1.2(iii). -/
theorem le_mvsup_eq (y z : A) (h : le y z) : oplus (odot z (neg y)) y = z := by
  -- By mvsup_comm: mvsup z y = mvsup y z = z (by mvsup_eq_of_le).
  have h1 : mvsup z y = mvsup y z := mvsup_comm z y
  have h2 : mvsup y z = z := mvsup_eq_of_le h
  -- mvsup z y = (z⊙¬y) ⊕ y by definition.
  show oplus (odot z (neg y)) y = z
  have : mvsup z y = oplus (odot z (neg y)) y := rfl
  rw [← this, h1, h2]

/-- Helper: `¬(P ⊕ y) ⊕ y = (y ⊙ P) ⊕ ¬P`.  This is `mv_axiom(¬P, y)` with `neg_neg`. -/
theorem neg_oplus_swap (P y : A) : oplus (neg (oplus P y)) y = oplus (odot y P) (neg P) := by
  -- mv_axiom(neg P, y): oplus(neg(oplus(neg(neg P)) y)) y = oplus(neg(oplus(neg y)(neg P)))(neg P)
  -- = oplus(neg(oplus P y)) y = oplus(neg(oplus(neg y)(neg P)))(neg P)
  -- RHS: neg(oplus(neg y)(neg P)) = odot y P [by neg_oplus + neg_neg].
  have h := mv_axiom (neg P) y
  rw [neg_neg] at h
  -- h: oplus(neg(oplus P y)) y = oplus(neg(oplus(neg y)(neg P)))(neg P)
  rw [h]
  -- Goal: oplus(neg(oplus(neg y)(neg P)))(neg P) = oplus(odot y P)(neg P)
  -- After rw [h]: goal is oplus(neg(oplus(neg y)(neg P)))(neg P) = oplus(odot y P)(neg P)
  -- Both sides are equal because neg(oplus(neg y)(neg P)) = odot y P by def of odot.
  rfl

/-- **MVSUP_LUB**: If `a ≤ c` and `b ≤ c` then `mvsup a b ≤ c`. 
    Mundici's proof of Proposition 1.5(5) (sup is least upper bound). -/
theorem mvsup_lub {a b c : A} (h1 : le a c) (h2 : le b c) : le (mvsup a b) c := by
  -- Goal: imp (mvsup a b) c = one
  -- mvsup a b = (a⊖b) ⊕ b. Let P = a⊖b. Need ¬((P⊕b)) ⊕ c = one.
  unfold le imp mvsup
  -- Goal: oplus (neg (oplus (odot a (neg b)) b)) c = one
  -- Step 1: substitute c = (c⊖b) ⊕ b using le_mvsup_eq h2.
  rw [show c = oplus (odot c (neg b)) b from (le_mvsup_eq b c h2).symm]
  -- Goal: oplus (neg (oplus (odot a (neg b)) b)) (oplus (odot c (neg b)) b) = one
  -- Step 2: rearrange to bring things in form A ⊕ B ⊕ (z⊖y).
  -- (¬(P⊕b)) ⊕ ((c⊖b) ⊕ b) = (¬(P⊕b)) ⊕ b ⊕ (c⊖b) [comm + assoc on inner]
  rw [oplus_comm (odot c (neg b)) b, ← oplus_assoc]
  -- Goal: oplus (oplus (neg (oplus (odot a (neg b)) b)) b) (odot c (neg b)) = one
  -- Step 3: apply neg_oplus_swap to (¬(P⊕b)) ⊕ b
  rw [neg_oplus_swap (odot a (neg b)) b]
  -- Goal: oplus (oplus (odot b (odot a (neg b))) (neg (odot a (neg b)))) (odot c (neg b)) = one
  -- Step 4: ¬(odot a (neg b)) = oplus (neg a) b [neg_odot + neg_neg]
  rw [show neg (odot a (neg b)) = oplus (neg a) b by
        rw [neg_odot, neg_neg]]
  -- Goal: oplus (oplus (odot b (odot a (neg b))) (oplus (neg a) b)) (odot c (neg b)) = one
  -- Step 5: rearrange. We have: ((b⊙(a⊖b)) ⊕ (¬a ⊕ b)) ⊕ (c⊖b).
  -- By oplus_assoc: = (b⊙(a⊖b)) ⊕ ((¬a ⊕ b) ⊕ (c⊖b))
  rw [oplus_assoc (odot b (odot a (neg b))) (oplus (neg a) b) (odot c (neg b))]
  -- Step 6: reorder inner: (¬a ⊕ b) ⊕ (c⊖b) = ¬a ⊕ (b ⊕ (c⊖b))
  rw [oplus_assoc (neg a) b (odot c (neg b))]
  -- Goal: ... ⊕ (oplus (neg a) (oplus b (odot c (neg b)))) = one
  -- Step 7: b ⊕ (c⊖b) = (c⊖b) ⊕ b = c [by le_mvsup_eq with le b c]
  rw [oplus_comm b (odot c (neg b)), le_mvsup_eq b c h2]
  -- Goal: oplus (odot b (odot a (neg b))) (oplus (neg a) c) = one
  -- Step 8: from le a c (h1): oplus (neg a) c = one.
  unfold le imp at h1
  rw [h1]
  -- Goal: oplus (odot b (odot a (neg b))) one = one
  exact oplus_one _


/-- `mv_swap`: a useful symmetry. -/
theorem mv_swap (a p : A) : oplus (odot (neg a) (neg p)) a = oplus (odot a p) (neg p) := by
  show oplus (neg (oplus (neg (neg a)) (neg (neg p)))) a
     = oplus (neg (oplus (neg a) (neg p))) (neg p)
  rw [neg_neg, neg_neg]
  have h := mv_axiom a (neg p)
  rw [neg_neg] at h; rw [oplus_comm p a] at h; exact h.symm

/-- `oplus` is monotone in the right argument. -/
theorem oplus_mono (a : A) {p q : A} (h : le p q) : le (oplus a p) (oplus a q) := by
  show oplus (neg (oplus a p)) (oplus a q) = one
  rw [neg_oplus, ← oplus_assoc, mv_swap, oplus_assoc]
  unfold le imp at h; rw [h]; exact oplus_one _

/-- `oplus` is monotone in the left argument. -/
theorem oplus_mono_left {p q : A} (a : A) (h : le p q) : le (oplus p a) (oplus q a) := by
  rw [oplus_comm p a, oplus_comm q a]; exact oplus_mono a h

/-- `le X (one)` always. -/
theorem le_one (x : A) : le x (one:A) := by
  unfold le imp; exact oplus_one _

/-- Negation flips ≤. -/
theorem le_neg_swap {x y : A} (h : le x y) : le (neg y) (neg x) := by
  unfold le imp at h ⊢
  rw [neg_neg, oplus_comm]; exact h

/-- Transitivity of ≤. -/
theorem le_trans {x y z : A} (h1 : le x y) (h2 : le y z) : le x z := by
  have key := oplus_mono (neg x) h2
  unfold le imp at h1 ⊢ key
  rw [h1] at key
  rw [neg_one_eq_zero, zero_oplus] at key
  exact key

/-- ⊙ monotone in the left argument: derived from oplus_mono via negation. -/
theorem odot_mono_left {a b : A} (c : A) (h : le a b) : le (odot a c) (odot b c) := by
  have h1 : le (neg b) (neg a) := le_neg_swap h
  have h2 : le (oplus (neg c) (neg b)) (oplus (neg c) (neg a)) := oplus_mono (neg c) h1
  have e1 : oplus (neg c) (neg b) = neg (odot b c) := by
    rw [oplus_comm]; exact (neg_odot b c).symm
  have e2 : oplus (neg c) (neg a) = neg (odot a c) := by
    rw [oplus_comm]; exact (neg_odot a c).symm
  rw [e1, e2] at h2
  have h3 : le (neg (neg (odot a c))) (neg (neg (odot b c))) := le_neg_swap h2
  rw [neg_neg, neg_neg] at h3
  exact h3

/-- ⊙ monotone in the right argument. -/
theorem odot_mono_right {a b : A} (c : A) (h : le a b) : le (odot c a) (odot c b) := by
  rw [odot_comm c a, odot_comm c b]; exact odot_mono_left c h

/-- `y ≤ x ∨ y` (sup is upper bound). -/
theorem le_mvsup_right (x y : A) : le y (mvsup x y) := by
  unfold mvsup le imp
  rw [← oplus_assoc, oplus_comm (neg y) (odot x (neg y)), oplus_assoc, neg_oplus_self]
  exact oplus_one _

/-- `x ≤ x ∨ y` (sup is upper bound). -/
theorem le_mvsup_left (x y : A) : le x (mvsup x y) := by
  rw [mvsup_comm]; exact le_mvsup_right y x

/-- `le x (x ⊕ y)`. -/
theorem le_oplus_right (x y : A) : le x (oplus x y) := by
  unfold le imp
  rw [← oplus_assoc, neg_oplus_self, one_oplus]

/-- `le y (x ⊕ y)`. -/
theorem le_oplus_left (x y : A) : le y (oplus x y) := by
  rw [oplus_comm]; exact le_oplus_right y x

/-- `residuation`: le (x⊙z) y ⟺ le z (imp x y). Already shown. -/
theorem residuation (x y z : A) : le (odot x z) y ↔ le z (imp x y) := by
  unfold le imp; rw [neg_odot, oplus_assoc]; constructor
  · intro h; rw [← h, ← oplus_assoc, oplus_comm (neg z) (neg x), oplus_assoc]
  · intro h; rw [← h, ← oplus_assoc, oplus_comm (neg x) (neg z), oplus_assoc]

/-- Antisymmetry of `le`. -/
theorem le_antisymm {x y : A} (h1 : le x y) (h2 : le y x) : x = y := by
  -- mvsup x y = y (by mvsup_eq_of_le h1). 
  -- mvsup y x = x (by mvsup_eq_of_le h2).
  -- And mvsup x y = mvsup y x (mvsup_comm).
  -- So x = mvsup y x = mvsup x y = y.
  have e1 : mvsup x y = y := mvsup_eq_of_le h1
  have e2 : mvsup y x = x := mvsup_eq_of_le h2
  have e3 : mvsup y x = mvsup x y := mvsup_comm y x
  -- x = mvsup y x = mvsup x y = y
  exact e2.symm.trans (e3.trans e1)

#check @oplus_mono
#check @le_trans
#check @le_antisymm

/-- **Mundici Proposition 1.6(i)**: `x ⊙ (y ∨ z) = (x⊙y) ∨ (x⊙z)`. -/
theorem odot_distrib_mvsup_left (x y z : A) :
    odot x (mvsup y z) = mvsup (odot x y) (odot x z) := by
  -- Show both ≤ via le_antisymm.
  apply le_antisymm
  · -- le (x ⊙ (y∨z)) (mvsup (x⊙y) (x⊙z)).
    -- By residuation: ⟺ le (y∨z) (imp x M) where M = mvsup (x⊙y) (x⊙z).
    rw [show le (odot x (mvsup y z)) (mvsup (odot x y) (odot x z))
          ↔ le (mvsup y z) (imp x (mvsup (odot x y) (odot x z))) from 
        residuation x (mvsup (odot x y) (odot x z)) (mvsup y z)]
    apply mvsup_lub
    · -- le y (imp x M) ⟺ le (x⊙y) M [residuation].
      rw [show le y (imp x (mvsup (odot x y) (odot x z)))
            ↔ le (odot x y) (mvsup (odot x y) (odot x z)) from
          (residuation x (mvsup (odot x y) (odot x z)) y).symm]
      exact le_mvsup_left _ _
    · -- le z (imp x M) ⟺ le (x⊙z) M.
      rw [show le z (imp x (mvsup (odot x y) (odot x z)))
            ↔ le (odot x z) (mvsup (odot x y) (odot x z)) from
          (residuation x (mvsup (odot x y) (odot x z)) z).symm]
      exact le_mvsup_right _ _
  · -- le (mvsup (x⊙y) (x⊙z)) (x ⊙ (y∨z)).
    apply mvsup_lub
    · -- le (x⊙y) (x⊙(y∨z)) by odot_mono_right and le y (y∨z).
      exact odot_mono_right x (le_mvsup_left y z)
    · -- le (x⊙z) (x⊙(y∨z)) by odot_mono_right and le z (y∨z).
      exact odot_mono_right x (le_mvsup_right y z)

#check @odot_distrib_mvsup_left

theorem neg_imp (x y : A) : neg (imp x y) = odot x (neg y) := by
  unfold imp
  rw [neg_oplus, neg_neg]

/-- De Morgan: `neg (mvsup x y) = mvinf (neg x) (neg y)`. -/
theorem neg_mvsup (x y : A) : neg (mvsup x y) = mvinf (neg x) (neg y) := by
  unfold mvsup
  rw [neg_oplus, neg_odot, neg_neg]  -- gets us to (¬x ⊕ y) ⊙ ¬y
  -- Goal: odot (oplus (neg x) y) (neg y) = mvinf (neg x) (neg y)
  rw [odot_comm]
  -- Goal: odot (neg y) (oplus (neg x) y) = mvinf (neg x) (neg y)
  rw [oplus_comm]
  -- Goal: odot (neg y) (oplus y (neg x)) = mvinf (neg x) (neg y)
  rw [meet_idiom_neg]  -- gives mvinf (neg y) (neg x)
  rw [mvinf_comm]

#check @neg_mvsup

/-- De Morgan: `neg (mvinf x y) = mvsup (neg x) (neg y)`. -/
theorem neg_mvinf (x y : A) : neg (mvinf x y) = mvsup (neg x) (neg y) := by
  -- Derive from neg_mvsup applied to (¬x) and (¬y), then apply neg_neg twice.
  have h := neg_mvsup (neg x) (neg y)
  -- h: neg (mvsup (neg x) (neg y)) = mvinf (neg (neg x)) (neg (neg y))
  rw [neg_neg, neg_neg] at h
  -- h: neg (mvsup (neg x) (neg y)) = mvinf x y
  -- Apply neg to both sides:
  have h2 : neg (neg (mvsup (neg x) (neg y))) = neg (mvinf x y) := by rw [h]
  rw [neg_neg] at h2
  exact h2.symm

#check @neg_mvinf

/-- **Mundici Proposition 1.6(ii)**: `x ⊕ (y ∧ z) = (x⊕y) ∧ (x⊕z)`.
    Derived from 1.6(i) via De Morgan. -/
theorem oplus_distrib_mvinf_left (x y z : A) :
    oplus x (mvinf y z) = mvinf (oplus x y) (oplus x z) := by
  -- Via De Morgan: x ⊕ M = ¬(¬x ⊙ ¬M). So:
  -- x ⊕ (y ∧ z) = ¬(¬x ⊙ ¬(y∧z))
  --             = ¬(¬x ⊙ (¬y ∨ ¬z))  [neg_mvinf]
  --             = ¬((¬x⊙¬y) ∨ (¬x⊙¬z))  [Prop 1.6(i)]
  --             = ¬(¬x⊙¬y) ∧ ¬(¬x⊙¬z)  [neg_mvsup]
  --             = (x⊕y) ∧ (x⊕z)  [neg_odot + neg_neg].
  have key : oplus x (mvinf y z) = neg (odot (neg x) (neg (mvinf y z))) := by
    -- Unfold odot on RHS: neg(neg(oplus(neg(neg x))(neg(neg(mvinf y z))))) = oplus x (mvinf y z) [neg_neg twice].
    rw [neg_odot, neg_neg, neg_neg]
  rw [key]
  -- Goal: neg (odot (neg x) (neg (mvinf y z))) = mvinf (oplus x y) (oplus x z)
  rw [neg_mvinf]
  -- Goal: neg (odot (neg x) (mvsup (neg y) (neg z))) = mvinf (oplus x y) (oplus x z)
  rw [odot_distrib_mvsup_left]
  -- Goal: neg (mvsup (odot (neg x) (neg y)) (odot (neg x) (neg z))) = mvinf (oplus x y) (oplus x z)
  rw [neg_mvsup]
  -- Goal: mvinf (neg (odot (neg x) (neg y))) (neg (odot (neg x) (neg z))) = mvinf (oplus x y) (oplus x z)
  rw [show neg (odot (neg x) (neg y)) = oplus x y by rw [neg_odot, neg_neg, neg_neg]]
  rw [show neg (odot (neg x) (neg z)) = oplus x z by rw [neg_odot, neg_neg, neg_neg]]

#check @oplus_distrib_mvinf_left



#check @oplus_mono
#check @mvsup_eq_of_le
#check @mvsup_idem

/-- **KEY EQUATION** for a6: `(z ⊕ ¬A) ∧ (z ⊕ ¬B) = z` where `A = imp x y, B = imp y x`. -/
theorem a6_key (x y z : A) :
    mvinf (oplus z (odot x (neg y))) (oplus z (odot y (neg x))) = z := by
  -- Rewrite RHS using Prop 1.6(ii) + Prop 1.7.
  rw [← oplus_distrib_mvinf_left]
  -- Goal: oplus z (mvinf (odot x (neg y)) (odot y (neg x))) = z
  rw [mundici_prop17]
  -- Goal: oplus z zero = z
  exact oplus_zero z

#check @a6_key

end MVAlgebra
end Luk
