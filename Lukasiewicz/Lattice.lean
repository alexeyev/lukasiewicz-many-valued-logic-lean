import Lukasiewicz.Base

namespace Luk.MVAlgebra

variable {A : Type _} [MVAlgebra A]


-- ============================================================================
-- THE FUNDAMENTAL STRUCTURE THEOREM FOR MV-ALGEBRAS
-- (Mundici, "Introducing MV-Algebras", Propositions 1.5 + 1.6)
--
-- Every MV-algebra is a bounded lattice under its natural order, and the monoid
-- operations distribute over the lattice operations. This is the most-cited
-- structural result in the theory of MV-algebras.
-- ============================================================================

/-- `0` is the bottom element of the lattice: `le zero x` always. -/
theorem le_zero (x : A) : le (zero : A) x := by
  show oplus (neg zero) x = one
  rw [show neg (zero : A) = one from rfl]
  exact one_oplus x

/-- `mvinf x y ≤ x`. The lattice meet is a lower bound on its first argument. -/
theorem le_mvinf_left (x y : A) : le (mvinf x y) x := by
  -- mvinf x y = ¬(mvsup ¬x ¬y), so le (mvinf x y) x ⟺ le ¬x (mvsup ¬x ¬y).
  have h : neg (mvinf x y) = mvsup (neg x) (neg y) := neg_mvinf x y
  -- le X x ⟺ le ¬x ¬X [le_neg_swap], so le (mvinf x y) x ⟺ le ¬x ¬(mvinf x y)
  --                                                  ⟺ le ¬x (mvsup ¬x ¬y) [by h]
  have step : le (neg x) (neg (mvinf x y)) := by
    rw [h]; exact le_mvsup_left (neg x) (neg y)
  -- Now from le ¬x ¬(mvinf x y), derive le (mvinf x y) x by le_neg_swap + neg_neg.
  have := le_neg_swap step
  rw [neg_neg, neg_neg] at this
  exact this

/-- `mvinf x y ≤ y`. Symmetric. -/
theorem le_mvinf_right (x y : A) : le (mvinf x y) y := by
  rw [mvinf_comm]; exact le_mvinf_left y x

/-- **GLB property of `mvinf`**: if `w ≤ x` and `w ≤ y` then `w ≤ mvinf x y`. -/
theorem mvinf_glb {x y w : A} (h1 : le w x) (h2 : le w y) : le w (mvinf x y) := by
  -- By De Morgan: mvinf x y = ¬(mvsup ¬x ¬y).
  -- le w (¬M) ⟺ le M ¬w [le_neg_swap], so le w (mvinf x y) ⟺ le (mvsup ¬x ¬y) ¬w.
  -- From h1: le w x → le ¬x ¬w. From h2: le w y → le ¬y ¬w.
  -- Apply mvsup_lub.
  have hx : le (neg x) (neg w) := le_neg_swap h1
  have hy : le (neg y) (neg w) := le_neg_swap h2
  have hsup : le (mvsup (neg x) (neg y)) (neg w) := mvsup_lub hx hy
  -- Now le_neg_swap on hsup:
  have hnn : le (neg (neg w)) (neg (mvsup (neg x) (neg y))) := le_neg_swap hsup
  rw [neg_neg] at hnn
  -- hnn : le w (neg (mvsup (neg x) (neg y)))
  -- Rewrite the right side using neg_mvsup applied to ¬x, ¬y:
  rw [neg_mvsup, neg_neg, neg_neg] at hnn
  exact hnn

/-! 
## The fundamental structure theorem

We now assemble the cumulative content of Mundici's Propositions 1.5 and 1.6 into
one statement. This is the structural backbone of MV-algebra theory: every result
about MV-algebras ultimately rests on these eight facts.
-/

/--
**Mundici's Fundamental Structure Theorem (Propositions 1.5 + 1.6).**

In every MV-algebra `A`, the natural order `x ≤ y ⟺ x ⇒ y = 1` carries a
bounded lattice structure given by the algebraic operations

  x ∨ y = (x ⊙ ¬y) ⊕ y,
  x ∧ y = x ⊙ (¬x ⊕ y),

and the monoid operations distribute over the lattice operations:

  x ⊙ (y ∨ z) = (x ⊙ y) ∨ (x ⊙ z),     [Prop 1.6(i)]
  x ⊕ (y ∧ z) = (x ⊕ y) ∧ (x ⊕ z).     [Prop 1.6(ii)]

This is the most-cited structural result for MV-algebras (Cignoli-D'Ottaviano-
Mundici, Chapter 1; Mundici tutorial Propositions 1.5–1.6). It is proved
constructively from Chang's six axioms, with no use of choice or
subdirect-representation arguments. The full statement bundles eight facts.
-/
theorem mv_fundamental_structure (x y z : A) :
    -- (a) `mvsup` is the least upper bound (Proposition 1.5, `∨` part):
    le x (mvsup x y) ∧ le y (mvsup x y) ∧
    (∀ w, le x w → le y w → le (mvsup x y) w) ∧
    -- (b) `mvinf` is the greatest lower bound (Proposition 1.5, `∧` part):
    le (mvinf x y) x ∧ le (mvinf x y) y ∧
    (∀ w, le w x → le w y → le w (mvinf x y)) ∧
    -- (c) Distributivity of ⊙ over ∨ (Proposition 1.6(i)):
    odot x (mvsup y z) = mvsup (odot x y) (odot x z) ∧
    -- (d) Distributivity of ⊕ over ∧ (Proposition 1.6(ii)):
    oplus x (mvinf y z) = mvinf (oplus x y) (oplus x z) ∧
    -- (e) The lattice is bounded below by `zero` and above by `one`:
    le zero x ∧ le x one := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_mvsup_left x y
  · exact le_mvsup_right x y
  · intro w hx hy; exact mvsup_lub hx hy
  · exact le_mvinf_left x y
  · exact le_mvinf_right x y
  · intro w hx hy; exact mvinf_glb hx hy
  · exact odot_distrib_mvsup_left x y z
  · exact oplus_distrib_mvinf_left x y z
  · exact le_zero x
  · exact le_one x

end MVAlgebra
end Luk
