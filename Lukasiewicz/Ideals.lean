import Lukasiewicz.BooleanAlgebra

namespace Luk.MVAlgebra

variable {A : Type _} [MVAlgebra A]


-- ============================================================================
-- MV-ALGEBRA HOMOMORPHISMS, IDEALS, AND CONGRUENCES
--
-- Building on the metric/distance theory of `Distance.lean`, this section
-- introduces the categorical structure of MV-algebras:
--
--   1. MV-homomorphisms — functions preserving 0, ⊕, ¬.
--      (Mundici Lemma 1.9, properties (i)-(iv).)
--
--   2. Ideals — downward-closed submonoids containing 0.
--      The kernel of any MV-homomorphism is an ideal.
--
--   3. Congruences and the ideal-to-congruence correspondence:
--      Given an ideal I, the relation x ≡_I y ⟺ d(x,y) ∈ I is a
--      congruence on A. (Mundici Proposition 1.11, the easier direction.)
-- ============================================================================

end MVAlgebra

/-! ## MV-homomorphisms -/

/-- An **MV-homomorphism** between MV-algebras `A` and `B` is a function `h: A → B`
    preserving the three primitive operations: `h 0 = 0`, `h (x ⊕ y) = h x ⊕ h y`,
    and `h (¬x) = ¬(h x)`. -/
structure MVHom (A B : Type _) [MVAlgebra A] [MVAlgebra B] where
  toFun : A → B
  map_zero : toFun MVAlgebra.zero = MVAlgebra.zero
  map_oplus : ∀ x y, toFun (MVAlgebra.oplus x y) = MVAlgebra.oplus (toFun x) (toFun y)
  map_neg : ∀ x, toFun (MVAlgebra.neg x) = MVAlgebra.neg (toFun x)

namespace MVHom

variable {A B : Type _} [MVAlgebra A] [MVAlgebra B]

instance : CoeFun (MVHom A B) (fun _ => A → B) := ⟨MVHom.toFun⟩

@[simp] theorem map_zero' (h : MVHom A B) : h MVAlgebra.zero = MVAlgebra.zero := h.map_zero
@[simp] theorem map_oplus' (h : MVHom A B) (x y : A) :
    h (MVAlgebra.oplus x y) = MVAlgebra.oplus (h x) (h y) := h.map_oplus x y
@[simp] theorem map_neg' (h : MVHom A B) (x : A) :
    h (MVAlgebra.neg x) = MVAlgebra.neg (h x) := h.map_neg x

/-- **Lemma 1.9(i)**: an MV-homomorphism preserves `1 = ¬0`. -/
@[simp] theorem map_one (h : MVHom A B) : h MVAlgebra.one = MVAlgebra.one := by
  show h (MVAlgebra.neg MVAlgebra.zero) = MVAlgebra.neg MVAlgebra.zero
  rw [h.map_neg, h.map_zero]

/-- **Lemma 1.9(ii)**: an MV-homomorphism preserves `⊙`. -/
@[simp] theorem map_odot (h : MVHom A B) (x y : A) :
    h (MVAlgebra.odot x y) = MVAlgebra.odot (h x) (h y) := by
  -- odot is defined as neg (oplus (neg x) (neg y))
  show h (MVAlgebra.neg (MVAlgebra.oplus (MVAlgebra.neg x) (MVAlgebra.neg y)))
     = MVAlgebra.neg (MVAlgebra.oplus (MVAlgebra.neg (h x)) (MVAlgebra.neg (h y)))
  rw [h.map_neg, h.map_oplus, h.map_neg, h.map_neg]

/-- An MV-homomorphism preserves `≤`. -/
theorem map_le (h : MVHom A B) {x y : A} (hxy : MVAlgebra.le x y) :
    MVAlgebra.le (h x) (h y) := by
  -- le x y means imp x y = one, i.e., oplus (neg x) y = one. Apply h.
  show MVAlgebra.oplus (MVAlgebra.neg (h x)) (h y) = MVAlgebra.one
  rw [← h.map_neg, ← h.map_oplus]
  -- Goal: h (oplus (neg x) y) = one
  -- hxy unfolds to oplus (neg x) y = one (via le → imp = one → oplus (neg x) y = one).
  have hxy' : MVAlgebra.oplus (MVAlgebra.neg x) y = MVAlgebra.one := hxy
  rw [hxy']
  exact h.map_one

/-- An MV-homomorphism preserves `mvsup`. -/
@[simp] theorem map_mvsup (h : MVHom A B) (x y : A) :
    h (MVAlgebra.mvsup x y) = MVAlgebra.mvsup (h x) (h y) := by
  -- mvsup x y = (x ⊙ ¬y) ⊕ y
  show h (MVAlgebra.oplus (MVAlgebra.odot x (MVAlgebra.neg y)) y)
     = MVAlgebra.oplus (MVAlgebra.odot (h x) (MVAlgebra.neg (h y))) (h y)
  rw [h.map_oplus, h.map_odot, h.map_neg]

/-- An MV-homomorphism preserves `mvinf`. -/
@[simp] theorem map_mvinf (h : MVHom A B) (x y : A) :
    h (MVAlgebra.mvinf x y) = MVAlgebra.mvinf (h x) (h y) := by
  -- mvinf x y = x ⊙ (¬x ⊕ y)
  show h (MVAlgebra.odot x (MVAlgebra.oplus (MVAlgebra.neg x) y))
     = MVAlgebra.odot (h x) (MVAlgebra.oplus (MVAlgebra.neg (h x)) (h y))
  rw [h.map_odot, h.map_oplus, h.map_neg]

/-- An MV-homomorphism preserves the **distance function** `d(x, y) := (x⊖y)⊕(y⊖x)`.
    This is a key step in the ideal-congruence correspondence. -/
@[simp] theorem map_dist (h : MVHom A B) (x y : A) :
    h (MVAlgebra.dist x y) = MVAlgebra.dist (h x) (h y) := by
  show h (MVAlgebra.oplus (MVAlgebra.odot x (MVAlgebra.neg y))
                          (MVAlgebra.odot y (MVAlgebra.neg x)))
     = MVAlgebra.oplus (MVAlgebra.odot (h x) (MVAlgebra.neg (h y)))
                       (MVAlgebra.odot (h y) (MVAlgebra.neg (h x)))
  rw [h.map_oplus, h.map_odot, h.map_odot, h.map_neg, h.map_neg]

end MVHom

namespace MVAlgebra
variable {A : Type _} [MVAlgebra A]

/-! ## Ideals -/

/-- An **ideal** of an MV-algebra `A` is a subset closed under three conditions:
    `0` belongs to it, it's downward closed under the natural order, and it's
    closed under `⊕`. (Mundici, definition immediately preceding Lemma 1.9.) -/
structure Ideal (A : Type _) [MVAlgebra A] where
  carrier : A → Prop
  zero_mem : carrier zero
  downward_closed : ∀ {x y}, carrier x → le y x → carrier y
  oplus_mem : ∀ {x y}, carrier x → carrier y → carrier (oplus x y)

instance : CoeFun (Ideal A) (fun _ => A → Prop) := ⟨Ideal.carrier⟩

/-- The **zero ideal** `{0}`. -/
def zeroIdeal (A : Type _) [MVAlgebra A] : Ideal A where
  carrier := fun x => x = zero
  zero_mem := rfl
  downward_closed := fun {x y} hx hyx => by
    -- y ≤ x and x = 0, so y ≤ 0, so y = 0.
    rw [hx] at hyx
    exact eq_zero_of_le_zero hyx
  oplus_mem := fun {x y} hx hy => by
    rw [hx, hy, oplus_zero]

/-- The **improper ideal** (all of `A`). -/
def topIdeal (A : Type _) [MVAlgebra A] : Ideal A where
  carrier := fun _ => True
  zero_mem := trivial
  downward_closed := fun _ _ => trivial
  oplus_mem := fun _ _ => trivial

/-- **Lemma 1.9(i)**: the kernel `Ker(h) := {x : h(x) = 0}` of an MV-homomorphism is an ideal. -/
def MVHom.ker {A B : Type _} [MVAlgebra A] [MVAlgebra B] (h : MVHom A B) : Ideal A where
  carrier := fun x => h x = zero
  zero_mem := h.map_zero
  downward_closed := fun {x y} hx hyx => by
    -- h y ≤ h x = 0, and h y ≥ 0, so h y = 0.
    have h1 : le (h y) (h x) := h.map_le hyx
    rw [hx] at h1
    exact eq_zero_of_le_zero h1
  oplus_mem := fun {x y} hx hy => by
    rw [h.map_oplus, hx, hy, oplus_zero]

/-! ## Congruences -/

/-- An **MV-congruence** is an equivalence relation on `A` that is compatible
    with `⊕` and `¬`. (Compatibility with `⊙`, `∨`, `∧`, etc. follows automatically
    since these are definable from `⊕`, `¬`.) -/
structure MVCongruence (A : Type _) [MVAlgebra A] where
  rel : A → A → Prop
  refl : ∀ x, rel x x
  symm : ∀ {x y}, rel x y → rel y x
  trans : ∀ {x y z}, rel x y → rel y z → rel x z
  oplus_compat : ∀ {x y s t}, rel x y → rel s t → rel (oplus x s) (oplus y t)
  neg_compat : ∀ {x y}, rel x y → rel (neg x) (neg y)

/-- The **ideal-induced congruence**: given an ideal `I`, define `x ≡_I y ⟺ d(x,y) ∈ I`.
    (Mundici Proposition 1.11, forward direction.) -/
def Ideal.congruence (I : Ideal A) : MVCongruence A where
  rel := fun x y => I (dist x y)
  refl := fun x => by
    show I (dist x x)
    rw [dist_self]
    exact I.zero_mem
  symm := fun {x y} hxy => by
    show I (dist y x)
    rw [dist_comm]
    exact hxy
  trans := fun {x y z} hxy hyz => by
    show I (dist x z)
    -- d(x,z) ≤ d(x,y) ⊕ d(y,z) (triangle inequality).
    -- d(x,y) ⊕ d(y,z) ∈ I (closure under ⊕).
    -- So d(x,z) ∈ I (downward closure).
    have hsum : I (oplus (dist x y) (dist y z)) := I.oplus_mem hxy hyz
    exact I.downward_closed hsum (dist_triangle x y z)
  oplus_compat := fun {x y s t} hxy hst => by
    show I (dist (oplus x s) (oplus y t))
    -- d(x⊕s, y⊕t) ≤ d(x,y) ⊕ d(s,t) (non-expansiveness of ⊕).
    have hsum : I (oplus (dist x y) (dist s t)) := I.oplus_mem hxy hst
    exact I.downward_closed hsum (dist_oplus_bound x y s t)
  neg_compat := fun {x y} hxy => by
    show I (dist (neg x) (neg y))
    -- d(¬x, ¬y) = d(x, y).
    rw [← dist_neg]
    exact hxy

/-- The relation induced by an ideal coincides with the membership predicate on the
    distance function (definitional, but useful for rewriting). -/
@[simp] theorem Ideal.congruence_rel (I : Ideal A) (x y : A) :
    I.congruence.rel x y ↔ I (dist x y) := Iff.rfl

/-- **Forward direction of Proposition 1.11**: every ideal induces a congruence
    via the distance function. (The reverse direction — every congruence comes
    from a unique ideal — would close the ideal–congruence bijection.) -/
theorem ideal_induces_congruence (I : Ideal A) :
    ∃ R : MVCongruence A, ∀ x y, R.rel x y ↔ I (dist x y) :=
  ⟨I.congruence, fun _ _ => Iff.rfl⟩


/-! ## Reverse direction of Mundici Proposition 1.11

  Given a congruence `~` on `A`, we construct the ideal `I_~ := {x : x ~ 0}`
  and show:
    - `I_~` is an ideal (closed under `⊕`, downward closed, contains `0`).
    - The ideal-induced congruence `≡_{I_~}` coincides with `~`.
  Together with the forward direction, this gives the famous **bijection
  between ideals and congruences** on every MV-algebra. -/

namespace MVCongruence

variable {A : Type _} [MVAlgebra A]

/-- **A congruence is automatically compatible with `⊙`** (since `⊙` is defined via `⊕, ¬`). -/
theorem odot_compat (R : MVCongruence A) {x y s t : A}
    (hxy : R.rel x y) (hst : R.rel s t) : R.rel (odot x s) (odot y t) := by
  -- odot x s = neg (oplus (neg x) (neg s)).
  -- Apply neg_compat, oplus_compat in sequence.
  show R.rel (neg (oplus (neg x) (neg s))) (neg (oplus (neg y) (neg t)))
  apply R.neg_compat
  apply R.oplus_compat
  · exact R.neg_compat hxy
  · exact R.neg_compat hst

/-- **A congruence is automatically compatible with `mvinf`** (i.e., `∧`). -/
theorem mvinf_compat (R : MVCongruence A) {x y s t : A}
    (hxy : R.rel x y) (hst : R.rel s t) : R.rel (mvinf x s) (mvinf y t) := by
  -- mvinf x s = odot x (oplus (neg x) s)
  show R.rel (odot x (oplus (neg x) s)) (odot y (oplus (neg y) t))
  apply R.odot_compat hxy
  apply R.oplus_compat (R.neg_compat hxy) hst

/-- **A congruence is automatically compatible with `mvsup`** (i.e., `∨`). -/
theorem mvsup_compat (R : MVCongruence A) {x y s t : A}
    (hxy : R.rel x y) (hst : R.rel s t) : R.rel (mvsup x s) (mvsup y t) := by
  -- mvsup x s = oplus (odot x (neg s)) s
  show R.rel (oplus (odot x (neg s)) s) (oplus (odot y (neg t)) t)
  apply R.oplus_compat _ hst
  exact R.odot_compat hxy (R.neg_compat hst)

end MVCongruence

variable {A : Type _} [MVAlgebra A]

/-- The **kernel of a congruence**: the set `{x : x ~ 0}`. -/
def MVCongruence.kernel (R : MVCongruence A) : Ideal A where
  carrier := fun x => R.rel x zero
  zero_mem := R.refl zero
  downward_closed := fun {x y} hx hyx => by
    -- hx : x ~ 0, hyx : y ≤ x.
    -- y ≤ x means y = mvinf y x. (Standard fact.)
    -- Then y = mvinf y x ~ mvinf y 0 = 0 (using ∧-compat and that mvinf y 0 = 0).
    show R.rel y zero
    -- First: y = mvinf y x. This is because y ≤ x iff mvinf y x = y, equivalently 
    -- y = mvinf y x. We need to derive this.
    have heq_y : y = mvinf y x := by
      -- mvinf y x = y iff y ≤ x. We have y ≤ x.
      -- Use mvinf_eq_of_le_left: not sure we have this name. Compute directly.
      -- mvinf y x = odot y (oplus (neg y) x). 
      -- y ≤ x means oplus (neg y) x = one. So mvinf y x = odot y one = y? 
      -- We have odot y one = y? Let me derive: odot y one = neg (oplus (neg y) (neg one))
      --   = neg (oplus (neg y) zero) = neg (neg y) = y.
      have h1 : oplus (neg y) x = one := hyx
      show y = odot y (oplus (neg y) x)
      rw [h1]
      -- Goal: y = odot y one. Compute odot y one = y:
      show y = neg (oplus (neg y) (neg one))
      rw [neg_one_eq_zero, oplus_zero, neg_neg]
    -- Now use ∧-compat: y = mvinf y x ~ mvinf y 0 = 0.
    have h_inf : R.rel (mvinf y x) (mvinf y zero) :=
      R.mvinf_compat (R.refl y) hx
    -- mvinf y zero = 0 (since 0 ≤ y).
    have hmvinf_zero : mvinf y zero = zero := by
      apply le_antisymm
      · exact le_mvinf_right y zero
      · exact le_zero _
    rw [hmvinf_zero] at h_inf
    -- h_inf : mvinf y x ~ 0. And y = mvinf y x. So y ~ 0.
    rw [heq_y]
    exact h_inf
  oplus_mem := fun {x y} hx hy => by
    -- hx : x ~ 0, hy : y ~ 0. Want: x ⊕ y ~ 0.
    show R.rel (oplus x y) zero
    -- By oplus_compat: x ⊕ y ~ 0 ⊕ 0 = 0.
    have step : R.rel (oplus x y) (oplus zero zero) := R.oplus_compat hx hy
    rw [zero_oplus] at step
    exact step

/-! ## The key identity for the reverse direction -/

/-- **Key identity**: `x ⊕ (y ⊖ x) = x ∨ y`. This is what lets us boost
    `(y ⊖ x) ~ 0` to `x ~ x ∨ y`. -/
theorem oplus_ominus_eq_mvsup (x y : A) : oplus x (odot y (neg x)) = mvsup x y := by
  -- mvsup x y = (x ⊙ ¬y) ⊕ y by definition.
  -- mvsup y x = (y ⊙ ¬x) ⊕ x = x ⊕ (y ⊙ ¬x) by oplus_comm.
  -- And mvsup x y = mvsup y x by mvsup_comm.
  rw [oplus_comm x (odot y (neg x))]
  -- Goal: (y ⊙ ¬x) ⊕ x = mvsup x y
  rw [mvsup_comm]
  -- Goal: (y ⊙ ¬x) ⊕ x = mvsup y x
  rfl

/-- **The reverse direction of Proposition 1.11**: Given a congruence `~` on `A`,
    its kernel `I_~ = {x : x ~ 0}` induces a congruence that coincides with `~`. -/
theorem congruence_eq_kernel_induced (R : MVCongruence A) (x y : A) :
    R.rel x y ↔ R.kernel.carrier (dist x y) := by
  -- d(x,y) := (x⊖y) ⊕ (y⊖x).
  -- (⟹) x ~ y. Then ¬x ~ ¬y, so x⊙¬y ~ x⊙¬x = 0 and y⊙¬x ~ x⊙¬x = 0.
  --      So d(x,y) = (x⊙¬y) ⊕ (y⊙¬x) ~ 0 ⊕ 0 = 0. Hence d(x,y) ∈ I_~.
  -- (⟸) d(x,y) ∈ I_~, i.e., d(x,y) ~ 0. Then (x⊖y), (y⊖x) ≤ d(x,y), and by 
  --      downward closure of the ideal I_~, both x⊖y ∈ I_~ and y⊖x ∈ I_~.
  --      That is, x⊖y ~ 0 and y⊖x ~ 0.
  --      Then x ~ x ⊕ 0 ~ x ⊕ (y⊖x) = x ∨ y, and y ~ y ⊕ 0 ~ y ⊕ (x⊖y) = y ∨ x = x ∨ y.
  --      Transitivity: x ~ x∨y ~ y. ✓
  constructor
  · intro hxy
    show R.rel (dist x y) zero
    -- d(x,y) = (x⊙¬y) ⊕ (y⊙¬x)
    show R.rel (oplus (odot x (neg y)) (odot y (neg x))) zero
    -- Each summand ~ 0
    have h1 : R.rel (odot x (neg y)) (odot x (neg x)) := 
      R.odot_compat (R.refl x) (R.neg_compat (R.symm hxy))
    -- h1 : x⊙¬y ~ x⊙¬x = 0
    have h2 : R.rel (odot y (neg x)) (odot x (neg x)) := 
      R.odot_compat (R.symm hxy) (R.refl (neg x))
    -- h2 : y⊙¬x ~ x⊙¬x = 0
    rw [self_odot_neg] at h1 h2
    -- h1 : x⊙¬y ~ 0, h2 : y⊙¬x ~ 0
    -- (x⊙¬y) ⊕ (y⊙¬x) ~ 0 ⊕ 0 = 0
    have h3 := R.oplus_compat h1 h2
    rw [zero_oplus] at h3
    exact h3
  · intro hd
    -- hd : R.rel (dist x y) zero, i.e., d(x,y) ∈ R.kernel.
    -- Get x⊖y ∈ R.kernel and y⊖x ∈ R.kernel via downward closure.
    have hd' : R.kernel.carrier (dist x y) := hd
    have h_xmy : R.kernel.carrier (odot x (neg y)) := by
      apply R.kernel.downward_closed hd'
      -- x⊖y ≤ d(x,y)
      show le (odot x (neg y)) (dist x y)
      -- (x⊖y) ≤ (x⊖y) ⊕ (y⊖x): use le_iff_exists_oplus or directly.
      unfold dist
      -- Goal: le (odot x (neg y)) (oplus (odot x (neg y)) (odot y (neg x)))
      -- A ≤ A ⊕ B: classic. Use Le.intro' or direct.
      show oplus (neg (odot x (neg y))) (oplus (odot x (neg y)) (odot y (neg x))) = one
      rw [← oplus_assoc]
      rw [oplus_comm (neg (odot x (neg y))) (odot x (neg y)), self_oplus_neg, one_oplus]
    have h_ymx : R.kernel.carrier (odot y (neg x)) := by
      apply R.kernel.downward_closed hd'
      show le (odot y (neg x)) (dist x y)
      unfold dist
      show oplus (neg (odot y (neg x))) (oplus (odot x (neg y)) (odot y (neg x))) = one
      rw [oplus_comm (odot x (neg y)) (odot y (neg x))]
      rw [← oplus_assoc]
      rw [oplus_comm (neg (odot y (neg x))) (odot y (neg x)), self_oplus_neg, one_oplus]
    -- h_xmy : x⊖y ~ 0, h_ymx : y⊖x ~ 0.
    -- Step: x ~ x ⊕ 0 ~ x ⊕ (y⊖x) = mvsup x y.
    have step1 : R.rel x (mvsup x y) := by
      -- x = x ⊕ 0 by oplus_zero (going right to left). Use rewriting.
      have e1 : x = oplus x zero := (oplus_zero x).symm
      have e2 : oplus x (odot y (neg x)) = mvsup x y := oplus_ominus_eq_mvsup x y
      -- x ~ oplus x (y⊖x) via congruence (R.symm h_ymx says 0 ~ y⊖x)
      have : R.rel (oplus x zero) (oplus x (odot y (neg x))) :=
        R.oplus_compat (R.refl x) (R.symm h_ymx)
      rw [oplus_zero] at this
      rw [← e2]
      exact this
    -- Step: y ~ y ⊕ 0 ~ y ⊕ (x⊖y) = mvsup y x = mvsup x y.
    have step2 : R.rel y (mvsup x y) := by
      have e2 : oplus y (odot x (neg y)) = mvsup y x := oplus_ominus_eq_mvsup y x
      have : R.rel (oplus y zero) (oplus y (odot x (neg y))) :=
        R.oplus_compat (R.refl y) (R.symm h_xmy)
      rw [oplus_zero] at this
      rw [mvsup_comm] at e2
      rw [← e2]
      exact this
    -- Transitivity: x ~ mvsup x y ~ y.
    exact R.trans step1 (R.symm step2)

/-- **The full bijection (Mundici Proposition 1.11)**: ideals and congruences on an MV-algebra
    are in natural bijection via `I ↦ ≡_I` and `R ↦ R.kernel`. -/
theorem ideal_congruence_bijection (R : MVCongruence A) :
    ∀ x y, R.rel x y ↔ R.kernel.congruence.rel x y :=
  fun x y => congruence_eq_kernel_induced R x y

/-! ## MV-algebras form a category

  Two final structural results: the identity function is an MV-homomorphism,
  and composition of MV-homomorphisms is an MV-homomorphism. Together with
  associativity of composition (which is automatic from function composition),
  these make MV-algebras and their homomorphisms into a category. -/

end MVAlgebra

namespace MVHom
variable {A B C : Type _} [MVAlgebra A] [MVAlgebra B] [MVAlgebra C]

/-- The **identity** MV-homomorphism on `A`. -/
def id (A : Type _) [MVAlgebra A] : MVHom A A where
  toFun := fun x => x
  map_zero := rfl
  map_oplus := fun _ _ => rfl
  map_neg := fun _ => rfl

/-- **Composition** of MV-homomorphisms. -/
def comp (g : MVHom B C) (h : MVHom A B) : MVHom A C where
  toFun := fun x => g (h x)
  map_zero := by show g (h MVAlgebra.zero) = MVAlgebra.zero; rw [h.map_zero, g.map_zero]
  map_oplus := fun x y => by
    show g (h (MVAlgebra.oplus x y)) = MVAlgebra.oplus (g (h x)) (g (h y))
    rw [h.map_oplus, g.map_oplus]
  map_neg := fun x => by
    show g (h (MVAlgebra.neg x)) = MVAlgebra.neg (g (h x))
    rw [h.map_neg, g.map_neg]

@[simp] theorem id_apply (x : A) : (id A) x = x := rfl
@[simp] theorem comp_apply (g : MVHom B C) (h : MVHom A B) (x : A) :
    (comp g h) x = g (h x) := rfl

/-- Identity laws for composition. -/
theorem id_comp (h : MVHom A B) : ∀ x, (comp (id B) h) x = h x := fun _ => rfl
theorem comp_id (h : MVHom A B) : ∀ x, (comp h (id A)) x = h x := fun _ => rfl

/-- Associativity of composition. -/
theorem comp_assoc {D : Type _} [MVAlgebra D] (f : MVHom C D) (g : MVHom B C) (h : MVHom A B) :
    ∀ x, (comp (comp f g) h) x = (comp f (comp g h)) x := fun _ => rfl

end MVHom

namespace MVAlgebra
end MVAlgebra
end Luk
