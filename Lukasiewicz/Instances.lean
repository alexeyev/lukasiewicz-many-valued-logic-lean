import Lukasiewicz.IdealOperations

namespace Luk.MVAlgebra

variable {A : Type _} [MVAlgebra A]

-- ============================================================================
-- MV-ALGEBRA INSTANCES, NFOLD PROPERTIES, AND HOMOMORPHISM PRESERVATION
--
-- This file gives:
--   1. The trivial MV-algebra: PUnit (one-element type).
--   2. The product MV-algebra: A × B for any two MV-algebras.
--   3. Properties of `nfold` (n-fold ⊕): nfold 1 a = a, nfold n 0 = 0, monotonicity,
--      and h(n·a) = n·h(a) for homomorphisms.
--   4. Image of a principal ideal under a homomorphism: h "(⟨a⟩) ⊆ ⟨h a⟩.
-- ============================================================================

/-! ## Properties of `nfold` -/

@[simp] theorem nfold_one (a : A) : nfold 1 a = a := by
  show oplus a (nfold 0 a) = a
  show oplus a zero = a
  exact oplus_zero a

theorem nfold_of_zero (n : Nat) : nfold n (zero : A) = zero := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show oplus zero (nfold k zero) = zero
    rw [zero_oplus, ih]

theorem nfold_of_one : ∀ n, n ≥ 1 → nfold n (one : A) = one
  | n+1, _ => by
    show oplus one (nfold n one) = one
    exact one_oplus _

theorem nfold_mono_arg (n : Nat) {a b : A} (h : le a b) : le (nfold n a) (nfold n b) := by
  induction n with
  | zero =>
    show le zero zero
    exact le_zero _
  | succ k ih =>
    show le (oplus a (nfold k a)) (oplus b (nfold k b))
    exact le_trans (oplus_mono_left _ h) (oplus_mono _ ih)

theorem nfold_le_one (n : Nat) (a : A) : le (nfold n a) one := le_one _

end MVAlgebra

namespace MVHom

variable {A B : Type _} [MVAlgebra A] [MVAlgebra B]

/-- **An MV-homomorphism preserves `nfold`**: `h(n·a) = n·(h a)` for all `n`. -/
@[simp] theorem map_nfold (h : MVHom A B) (n : Nat) (a : A) :
    h (MVAlgebra.nfold n a) = MVAlgebra.nfold n (h a) := by
  induction n with
  | zero =>
    show h MVAlgebra.zero = MVAlgebra.zero
    exact h.map_zero
  | succ k ih =>
    show h (MVAlgebra.oplus a (MVAlgebra.nfold k a))
       = MVAlgebra.oplus (h a) (MVAlgebra.nfold k (h a))
    rw [h.map_oplus, ih]

open MVAlgebra in
/-- **Image of a principal ideal is contained in the principal ideal of the image**:
    if `y` is in the image of `⟨a⟩` under `h`, then `y ∈ ⟨h a⟩`. -/
theorem image_principalIdeal_le (h : MVHom A B) (a : A) :
    ∀ y, (∃ x, (principalIdeal a).carrier x ∧ h x = y) → (principalIdeal (h a)).carrier y := by
  intro y ⟨x, hx_in, hxy⟩
  obtain ⟨n, hxn⟩ := hx_in
  -- hxn : le x (nfold n a). Apply h: h x ≤ h (nfold n a) = nfold n (h a). And h x = y.
  refine ⟨n, ?_⟩
  have hle_after : le (h x) (h (nfold n a)) := h.map_le hxn
  rw [h.map_nfold] at hle_after
  rw [← hxy]
  exact hle_after

end MVHom

/-! ## The trivial MV-algebra `PUnit` -/

/-- The **trivial MV-algebra** on `PUnit` (a one-element type). Every element
    equals `0 = 1`, and all operations are constant. -/
instance trivialMV : MVAlgebra PUnit where
  zero := PUnit.unit
  oplus := fun _ _ => PUnit.unit
  neg := fun _ => PUnit.unit
  oplus_assoc := fun _ _ _ => rfl
  oplus_comm := fun _ _ => rfl
  oplus_zero := fun _ => rfl
  neg_neg := fun _ => rfl
  oplus_negzero := fun _ => rfl
  mv_axiom := fun _ _ => rfl

namespace TrivialMV
/-- In the trivial MV-algebra, `0 = 1`. -/
theorem zero_eq_one : (MVAlgebra.zero : PUnit) = MVAlgebra.one := rfl
end TrivialMV

/-! ## The product MV-algebra -/

/-- The **product MV-algebra**: if `A` and `B` are MV-algebras, so is `A × B` with
    componentwise operations. The projections become MV-homomorphisms. -/
instance prodMV (A B : Type _) [MVAlgebra A] [MVAlgebra B] : MVAlgebra (A × B) where
  zero := (MVAlgebra.zero, MVAlgebra.zero)
  oplus := fun p q => (MVAlgebra.oplus p.1 q.1, MVAlgebra.oplus p.2 q.2)
  neg := fun p => (MVAlgebra.neg p.1, MVAlgebra.neg p.2)
  oplus_assoc := fun p q r => by
    show (MVAlgebra.oplus (MVAlgebra.oplus p.1 q.1) r.1,
          MVAlgebra.oplus (MVAlgebra.oplus p.2 q.2) r.2)
       = (MVAlgebra.oplus p.1 (MVAlgebra.oplus q.1 r.1),
          MVAlgebra.oplus p.2 (MVAlgebra.oplus q.2 r.2))
    rw [MVAlgebra.oplus_assoc, MVAlgebra.oplus_assoc]
  oplus_comm := fun p q => by
    show (MVAlgebra.oplus p.1 q.1, MVAlgebra.oplus p.2 q.2)
       = (MVAlgebra.oplus q.1 p.1, MVAlgebra.oplus q.2 p.2)
    rw [MVAlgebra.oplus_comm p.1, MVAlgebra.oplus_comm p.2]
  oplus_zero := fun p => by
    show (MVAlgebra.oplus p.1 MVAlgebra.zero, MVAlgebra.oplus p.2 MVAlgebra.zero) = p
    rw [MVAlgebra.oplus_zero, MVAlgebra.oplus_zero]
  neg_neg := fun p => by
    show (MVAlgebra.neg (MVAlgebra.neg p.1), MVAlgebra.neg (MVAlgebra.neg p.2)) = p
    rw [MVAlgebra.neg_neg, MVAlgebra.neg_neg]
  oplus_negzero := fun p => by
    show (MVAlgebra.oplus p.1 (MVAlgebra.neg MVAlgebra.zero),
          MVAlgebra.oplus p.2 (MVAlgebra.neg MVAlgebra.zero))
       = (MVAlgebra.neg MVAlgebra.zero, MVAlgebra.neg MVAlgebra.zero)
    rw [MVAlgebra.oplus_negzero, MVAlgebra.oplus_negzero]
  mv_axiom := fun p q => by
    -- (¬(¬p ⊕ q) ⊕ q).i = ¬(¬p.i ⊕ q.i) ⊕ q.i, same for the other side.
    -- Pairwise equal by mv_axiom on each component.
    show (MVAlgebra.oplus (MVAlgebra.neg (MVAlgebra.oplus (MVAlgebra.neg p.1) q.1)) q.1,
          MVAlgebra.oplus (MVAlgebra.neg (MVAlgebra.oplus (MVAlgebra.neg p.2) q.2)) q.2)
       = (MVAlgebra.oplus (MVAlgebra.neg (MVAlgebra.oplus (MVAlgebra.neg q.1) p.1)) p.1,
          MVAlgebra.oplus (MVAlgebra.neg (MVAlgebra.oplus (MVAlgebra.neg q.2) p.2)) p.2)
    rw [MVAlgebra.mv_axiom p.1 q.1, MVAlgebra.mv_axiom p.2 q.2]

namespace ProdMV
variable {A B : Type _} [MVAlgebra A] [MVAlgebra B]

/-- The **first projection** `π₁ : A × B → A` is an MV-homomorphism. -/
def fst : MVHom (A × B) A where
  toFun := fun p => p.1
  map_zero := rfl
  map_oplus := fun _ _ => rfl
  map_neg := fun _ => rfl

/-- The **second projection** `π₂ : A × B → B` is an MV-homomorphism. -/
def snd : MVHom (A × B) B where
  toFun := fun p => p.2
  map_zero := rfl
  map_oplus := fun _ _ => rfl
  map_neg := fun _ => rfl

/-- The kernel of `fst` is `{(0, b) : b ∈ B}` — the "second axis" ideal. -/
theorem ker_fst_carrier (p : A × B) : fst.ker.carrier p ↔ p.1 = MVAlgebra.zero := Iff.rfl

/-- The kernel of `snd` is `{(a, 0) : a ∈ A}` — the "first axis" ideal. -/
theorem ker_snd_carrier (p : A × B) : snd.ker.carrier p ↔ p.2 = MVAlgebra.zero := Iff.rfl

end ProdMV

end Luk
