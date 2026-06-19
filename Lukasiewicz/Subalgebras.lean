import Lukasiewicz.Ideals

namespace Luk.MVAlgebra

variable {A : Type _} [MVAlgebra A]


variable {A : Type _} [MVAlgebra A]

-- ============================================================================
-- SUB-MV-ALGEBRAS, IMAGES OF HOMOMORPHISMS, AND PRINCIPAL IDEALS
--
-- This section adds the remaining structural foundations:
--
--   1. SubMVAlgebra: a subset closed under 0, ⊕, ¬ (the natural notion of
--      "sub-algebra" in the variety of MV-algebras). Automatically closed
--      under 1, ⊙, ∧, ∨.
--
--   2. Image of a homomorphism is a sub-MV-algebra.
--
--   3. The Boolean center B(A) is a sub-MV-algebra of A.
--
--   4. Principal ideal ⟨a⟩ — the smallest ideal containing a, with the
--      explicit characterization ⟨a⟩ = {x : ∃n, x ≤ n·a}.
--
--   5. Proper ideal predicate and its characterization: I is proper iff 1 ∉ I.
-- ============================================================================

/-! ## Sub-MV-algebras -/

/-- A **sub-MV-algebra** of `A` is a subset closed under the three primitive
    operations `0`, `⊕`, `¬`. Closure under `1`, `⊙`, `∧`, `∨` follows
    automatically since these are definable from the primitives. -/
structure SubMVAlgebra (A : Type _) [MVAlgebra A] where
  carrier : A → Prop
  zero_mem : carrier zero
  oplus_mem : ∀ {x y}, carrier x → carrier y → carrier (oplus x y)
  neg_mem : ∀ {x}, carrier x → carrier (neg x)

namespace SubMVAlgebra

instance : CoeFun (SubMVAlgebra A) (fun _ => A → Prop) := ⟨SubMVAlgebra.carrier⟩

/-- A sub-MV-algebra contains `1`. -/
theorem one_mem (S : SubMVAlgebra A) : S.carrier one := by
  -- 1 = ¬0
  show S.carrier (neg zero)
  exact S.neg_mem S.zero_mem

/-- A sub-MV-algebra is closed under `⊙` (since `x ⊙ y = ¬(¬x ⊕ ¬y)`). -/
theorem odot_mem (S : SubMVAlgebra A) {x y : A} (hx : S.carrier x) (hy : S.carrier y) :
    S.carrier (odot x y) := by
  show S.carrier (neg (oplus (neg x) (neg y)))
  exact S.neg_mem (S.oplus_mem (S.neg_mem hx) (S.neg_mem hy))

/-- A sub-MV-algebra is closed under `mvsup` (i.e., `∨`). -/
theorem mvsup_mem (S : SubMVAlgebra A) {x y : A} (hx : S.carrier x) (hy : S.carrier y) :
    S.carrier (mvsup x y) := by
  -- mvsup x y = (x ⊙ ¬y) ⊕ y
  show S.carrier (oplus (odot x (neg y)) y)
  exact S.oplus_mem (S.odot_mem hx (S.neg_mem hy)) hy

/-- A sub-MV-algebra is closed under `mvinf` (i.e., `∧`). -/
theorem mvinf_mem (S : SubMVAlgebra A) {x y : A} (hx : S.carrier x) (hy : S.carrier y) :
    S.carrier (mvinf x y) := by
  -- mvinf x y = x ⊙ (¬x ⊕ y)
  show S.carrier (odot x (oplus (neg x) y))
  exact S.odot_mem hx (S.oplus_mem (S.neg_mem hx) hy)

end SubMVAlgebra

/-! ## The Boolean center as a sub-MV-algebra -/

/-- **The Boolean center is a sub-MV-algebra**: pulling together the
    `IsBoolean` closure properties from `BooleanCenter.lean` into the
    `SubMVAlgebra` structure. -/
def booleanCenter (A : Type _) [MVAlgebra A] : SubMVAlgebra A where
  carrier := fun a => IsBoolean a
  zero_mem := zero_isBoolean
  oplus_mem := fun hx hy => isBoolean_oplus hx hy
  neg_mem := fun hx => (isBoolean_neg _).mp hx

/-! ## Image of a homomorphism is a sub-MV-algebra -/

/-- **The image of an MV-homomorphism is a sub-MV-algebra of the codomain.** -/
def MVHom.image {A B : Type _} [MVAlgebra A] [MVAlgebra B] (h : MVHom A B) : SubMVAlgebra B where
  carrier := fun y => ∃ x, h x = y
  zero_mem := ⟨zero, h.map_zero⟩
  oplus_mem := fun {y1 y2} hy1 hy2 => by
    obtain ⟨x1, hx1⟩ := hy1
    obtain ⟨x2, hx2⟩ := hy2
    refine ⟨oplus x1 x2, ?_⟩
    rw [h.map_oplus, hx1, hx2]
  neg_mem := fun {y} hy => by
    obtain ⟨x, hx⟩ := hy
    refine ⟨neg x, ?_⟩
    rw [h.map_neg, hx]

/-! ## Principal ideals -/

/-- Helper lemma: `nfold (n + m) x = nfold n x ⊕ nfold m x`. -/
theorem nfold_add (n m : Nat) (x : A) :
    nfold (n + m) x = oplus (nfold n x) (nfold m x) := by
  induction n with
  | zero =>
    -- nfold (0 + m) x = nfold m x, and oplus (nfold 0 x) (nfold m x) = 0 ⊕ nfold m x = nfold m x.
    -- 0 + m doesn't reduce definitionally in Nat, so we rewrite explicitly.
    have h0m : (0 : Nat) + m = m := Nat.zero_add m
    rw [h0m]
    show nfold m x = oplus zero (nfold m x)
    rw [zero_oplus]
  | succ k ih =>
    -- nfold (k+1 + m) x = nfold ((k+m) + 1) x = x ⊕ nfold (k+m) x
    --                   = x ⊕ (nfold k x ⊕ nfold m x)  [by IH]
    --                   = (x ⊕ nfold k x) ⊕ nfold m x  [oplus_assoc]
    --                   = nfold (k+1) x ⊕ nfold m x.
    show nfold (k + 1 + m) x = oplus (nfold (k + 1) x) (nfold m x)
    have hkm : k + 1 + m = (k + m) + 1 := by omega
    rw [hkm]
    show oplus x (nfold (k + m) x) = oplus (oplus x (nfold k x)) (nfold m x)
    rw [ih, oplus_assoc]

/-- Helper lemma: `nfold n x` is monotone in `n` (each step adds something nonneg). -/
theorem le_nfold_succ (n : Nat) (x : A) : le (nfold n x) (nfold (n + 1) x) := by
  -- nfold (n+1) x = x ⊕ nfold n x. So nfold n x ≤ x ⊕ nfold n x = nfold (n+1) x.
  show le (nfold n x) (oplus x (nfold n x))
  exact le_oplus_left x (nfold n x)

/-- The **principal ideal** generated by `a ∈ A`: the smallest ideal containing `a`,
    characterized as `⟨a⟩ = {x : ∃n, x ≤ n·a}`. -/
def principalIdeal (a : A) : Ideal A where
  carrier := fun x => ∃ n : Nat, le x (nfold n a)
  zero_mem := ⟨0, le_zero _⟩  -- 0 ≤ nfold 0 a = 0
  downward_closed := fun {x y} hx hyx => by
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, le_trans hyx hn⟩
  oplus_mem := fun {x y} hx hy => by
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    -- x ≤ n·a, y ≤ m·a. Want: x ⊕ y ≤ (n+m)·a.
    refine ⟨n + m, ?_⟩
    rw [nfold_add]
    -- Goal: le (oplus x y) (oplus (nfold n a) (nfold m a))
    exact le_trans (oplus_mono_left y hn) (oplus_mono (nfold n a) hm)

/-- `a` is a member of its own principal ideal `⟨a⟩`. -/
theorem mem_principalIdeal_self (a : A) : (principalIdeal a).carrier a := by
  refine ⟨1, ?_⟩
  -- Goal: le a (nfold 1 a) = le a (oplus a (nfold 0 a)) = le a (oplus a zero) = le a a.
  show le a (oplus a (nfold 0 a))
  show le a (oplus a zero)
  rw [oplus_zero]
  -- Goal: le a a — reflexivity
  show oplus (neg a) a = one
  exact neg_oplus_self a

/-- `⟨a⟩` is the **smallest** ideal containing `a`: if `J` is any ideal containing `a`,
    then `⟨a⟩ ⊆ J` (as predicates). -/
theorem principalIdeal_minimal (a : A) (J : Ideal A) (h_a_in_J : J.carrier a) :
    ∀ x, (principalIdeal a).carrier x → J.carrier x := by
  intro x hx
  obtain ⟨n, hn⟩ := hx
  -- x ≤ nfold n a, and nfold n a ∈ J (by induction on n + closure of J under ⊕).
  -- Then x ∈ J by downward closure.
  have h_nfold_in_J : ∀ k, J.carrier (nfold k a) := by
    intro k
    induction k with
    | zero => exact J.zero_mem
    | succ j ih =>
      show J.carrier (oplus a (nfold j a))
      exact J.oplus_mem h_a_in_J ih
  exact J.downward_closed (h_nfold_in_J n) hn

/-! ## Proper ideals -/

/-- An ideal `I` is **proper** iff `1 ∉ I`. (Equivalently, `I` is not the
    improper ideal `topIdeal`.) -/
def Ideal.IsProper (I : Ideal A) : Prop := ¬ I.carrier one

/-- An ideal `I` is proper iff it does not contain `1`. -/
theorem Ideal.isProper_iff_one_not_mem (I : Ideal A) : I.IsProper ↔ ¬ I.carrier one := Iff.rfl

/-- If an ideal contains `1`, it contains everything. -/
theorem Ideal.eq_top_of_one_mem (I : Ideal A) (h : I.carrier one) :
    ∀ x, I.carrier x := by
  intro x
  -- x ≤ 1, and 1 ∈ I, so x ∈ I by downward closure.
  have h_x_le_one : le x one := le_one x
  exact I.downward_closed h h_x_le_one

/-- A proper ideal does not contain everything. -/
theorem Ideal.exists_not_mem_of_isProper (I : Ideal A) (h : I.IsProper) :
    ∃ x, ¬ I.carrier x := ⟨one, h⟩

/-- The zero ideal is proper iff the MV-algebra is nontrivial. -/
theorem zeroIdeal_isProper_iff_nontrivial (A : Type _) [MVAlgebra A] :
    (zeroIdeal A).IsProper ↔ Nontrivial A := by
  -- zeroIdeal.carrier 1 := 1 = 0. So ¬(1 = 0), i.e., 0 ≠ 1, equivalently Nontrivial A.
  constructor
  · intro h
    -- h : ¬ (1 = 0). Want: 0 ≠ 1.
    intro heq
    apply h
    show one = zero
    exact heq.symm
  · intro h
    -- h : Nontrivial A = (0 ≠ 1). Want: ¬ (1 = 0).
    intro heq
    apply h
    show zero = one
    exact heq.symm

/-- The top ideal is NEVER proper (it contains everything including `1`). -/
theorem topIdeal_not_isProper (A : Type _) [MVAlgebra A] :
    ¬ (topIdeal A).IsProper := by
  intro h
  -- h : ¬ True. Contradiction.
  exact h trivial

end MVAlgebra
end Luk
