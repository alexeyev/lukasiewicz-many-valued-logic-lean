import Lukasiewicz.Subalgebras

namespace Luk.MVAlgebra

variable {A : Type _} [MVAlgebra A]


-- ============================================================================
-- IDEAL LATTICE OPERATIONS AND HOMOMORPHISM INJECTIVITY
--
-- This section adds:
--   1. Intersection of two ideals is an ideal.
--   2. Sum of two ideals — the smallest ideal containing both.
--   3. Preimage of an ideal under an MV-homomorphism is an ideal.
--   4. Injectivity ⟺ trivial kernel — Mundici Lemma 1.9(vi).
--   5. Kernel containment via composition.
-- ============================================================================

/-! ## Intersection of ideals -/

/-- The **intersection of two ideals** is an ideal. -/
def Ideal.inter (I J : Ideal A) : Ideal A where
  carrier := fun x => I.carrier x ∧ J.carrier x
  zero_mem := ⟨I.zero_mem, J.zero_mem⟩
  downward_closed := fun {_ _} hx hyx =>
    ⟨I.downward_closed hx.1 hyx, J.downward_closed hx.2 hyx⟩
  oplus_mem := fun {_ _} hx hy =>
    ⟨I.oplus_mem hx.1 hy.1, J.oplus_mem hx.2 hy.2⟩

@[simp] theorem Ideal.inter_carrier (I J : Ideal A) (x : A) :
    (I.inter J).carrier x ↔ I.carrier x ∧ J.carrier x := Iff.rfl

theorem Ideal.inter_le_left (I J : Ideal A) :
    ∀ x, (I.inter J).carrier x → I.carrier x := fun _ h => h.1

theorem Ideal.inter_le_right (I J : Ideal A) :
    ∀ x, (I.inter J).carrier x → J.carrier x := fun _ h => h.2

/-- The intersection is the **greatest lower bound** in the lattice of ideals:
    any ideal `K` contained in both `I` and `J` is contained in their intersection. -/
theorem Ideal.le_inter (I J K : Ideal A)
    (h1 : ∀ x, K.carrier x → I.carrier x)
    (h2 : ∀ x, K.carrier x → J.carrier x) :
    ∀ x, K.carrier x → (I.inter J).carrier x :=
  fun x hx => ⟨h1 x hx, h2 x hx⟩

/-! ## Sum of two ideals -/

/-- The **sum of two ideals**: `I + J := {z : ∃ x ∈ I, y ∈ J, z ≤ x ⊕ y}`.
    This is the smallest ideal containing both `I` and `J`. -/
def Ideal.sum (I J : Ideal A) : Ideal A where
  carrier := fun z => ∃ x y, I.carrier x ∧ J.carrier y ∧ le z (oplus x y)
  zero_mem := ⟨zero, zero, I.zero_mem, J.zero_mem, by
    rw [oplus_zero]; exact le_zero _⟩
  downward_closed := fun {x y} hx hyx => by
    obtain ⟨a, b, ha, hb, hxab⟩ := hx
    exact ⟨a, b, ha, hb, le_trans hyx hxab⟩
  oplus_mem := fun {z1 z2} hz1 hz2 => by
    obtain ⟨x1, y1, hx1, hy1, h1⟩ := hz1
    obtain ⟨x2, y2, hx2, hy2, h2⟩ := hz2
    refine ⟨oplus x1 x2, oplus y1 y2, I.oplus_mem hx1 hx2, J.oplus_mem hy1 hy2, ?_⟩
    have step : le (oplus z1 z2) (oplus (oplus x1 y1) (oplus x2 y2)) :=
      le_trans (oplus_mono_left z2 h1) (oplus_mono _ h2)
    have eq : oplus (oplus x1 y1) (oplus x2 y2) = oplus (oplus x1 x2) (oplus y1 y2) := by
      rw [oplus_assoc x1 y1 (oplus x2 y2)]
      rw [oplus_assoc x1 x2 (oplus y1 y2)]
      congr 1
      rw [← oplus_assoc y1 x2 y2, ← oplus_assoc x2 y1 y2, oplus_comm y1 x2]
    rw [← eq]
    exact step

/-- `I ⊆ I + J`. -/
theorem Ideal.le_sum_left (I J : Ideal A) :
    ∀ x, I.carrier x → (I.sum J).carrier x :=
  fun x hx => ⟨x, zero, hx, J.zero_mem, by
    rw [oplus_zero]
    show oplus (neg x) x = one
    exact neg_oplus_self x⟩

/-- `J ⊆ I + J`. -/
theorem Ideal.le_sum_right (I J : Ideal A) :
    ∀ x, J.carrier x → (I.sum J).carrier x :=
  fun x hx => ⟨zero, x, I.zero_mem, hx, by
    rw [zero_oplus]
    show oplus (neg x) x = one
    exact neg_oplus_self x⟩

/-- **The sum is the smallest ideal containing both**: any ideal `K` containing both
    `I` and `J` contains their sum. -/
theorem Ideal.sum_le (I J K : Ideal A)
    (h1 : ∀ x, I.carrier x → K.carrier x)
    (h2 : ∀ x, J.carrier x → K.carrier x) :
    ∀ x, (I.sum J).carrier x → K.carrier x := by
  intro z hz
  obtain ⟨x, y, hx, hy, hzxy⟩ := hz
  have hxK : K.carrier x := h1 x hx
  have hyK : K.carrier y := h2 y hy
  have hxyK : K.carrier (oplus x y) := K.oplus_mem hxK hyK
  exact K.downward_closed hxyK hzxy

end MVAlgebra

-- =====
-- The next batch lives in namespace MVHom (= Luk.MVHom), where the MVHom
-- structure was originally declared. This is critical for dot notation:
-- since h : Luk.MVHom A B, Lean's dot notation `h.foo` looks for `Luk.MVHom.foo`.
-- We use `open MVAlgebra in` clauses to bring needed names into scope.
-- =====

namespace MVHom

variable {A B : Type _} [MVAlgebra A] [MVAlgebra B]

/-- Alias `Luk.MVHom.ker` for the kernel of an MV-homomorphism. Originally defined
    as `Luk.MVAlgebra.MVHom.ker`; we re-bind it here so that `h.ker` (with `h` of
    type `Luk.MVHom A B`) resolves via dot notation. -/
def ker (h : MVHom A B) : MVAlgebra.Ideal A := MVAlgebra.MVHom.ker h

@[simp] theorem ker_carrier (h : MVHom A B) (x : A) :
    h.ker.carrier x ↔ h x = MVAlgebra.zero := Iff.rfl

open MVAlgebra in
/-- The **preimage of an ideal** under an MV-homomorphism is an ideal. -/
def preimage (h : MVHom A B) (J : Ideal B) : Ideal A where
  carrier := fun x => J.carrier (h x)
  zero_mem := by
    show J.carrier (h zero)
    rw [h.map_zero]; exact J.zero_mem
  downward_closed := fun {x y} hx hyx => by
    show J.carrier (h y)
    have h_le : le (h y) (h x) := h.map_le hyx
    exact J.downward_closed hx h_le
  oplus_mem := fun {x y} hx hy => by
    show J.carrier (h (oplus x y))
    rw [h.map_oplus]
    exact J.oplus_mem hx hy

open MVAlgebra in
/-- The kernel of a homomorphism is the preimage of the zero ideal. -/
theorem ker_eq_preimage_zero (h : MVHom A B) :
    ∀ x, h.ker.carrier x ↔ (h.preimage (zeroIdeal B)).carrier x :=
  fun _ => Iff.rfl

/-- An MV-homomorphism is **injective** in the usual sense. -/
def Injective (h : MVHom A B) : Prop := ∀ {x y}, h x = h y → x = y

open MVAlgebra in
/-- **Mundici Lemma 1.9(vi)** — fundamental kernel characterization: an MV-homomorphism
    is injective iff its kernel is the zero ideal `{0}`.

    The proof uses the distance function: from `h(x) = h(y)` we get
    `d(h x, h y) = 0`, then `h(d x y) = 0` (preservation of distance), so
    `d(x,y) ∈ ker h = {0}`, hence `d(x,y) = 0`, hence `x = y`. -/
theorem injective_iff_ker_eq_zero (h : MVHom A B) :
    h.Injective ↔ (∀ x, h.ker.carrier x → x = zero) := by
  constructor
  · intro hinj x hx
    -- hx : h x = 0. And h 0 = 0. So h x = h 0. By injectivity, x = 0.
    have h_zero : h x = h zero := by
      rw [h.map_zero]; exact hx
    exact hinj h_zero
  · intro hker x y heq
    -- From h x = h y, get d(h x, h y) = 0, then h(d x y) = 0.
    have hd : dist (h x) (h y) = zero := by
      rw [heq]; exact dist_self _
    have hd' : h (dist x y) = zero := by
      rw [h.map_dist]; exact hd
    have hd_in_ker : h.ker.carrier (dist x y) := hd'
    have hd_zero : dist x y = zero := hker _ hd_in_ker
    exact eq_of_dist_zero hd_zero

open MVAlgebra in
/-- The kernel of a composition contains the kernel of the inner map:
    `ker h ⊆ ker (g ∘ h)`. -/
theorem ker_comp_ge_ker {C : Type _} [MVAlgebra C]
    (g : MVHom B C) (h : MVHom A B) :
    ∀ x, h.ker.carrier x → (MVHom.comp g h).ker.carrier x := by
  intro x hx
  show g (h x) = zero
  rw [show h x = zero from hx, g.map_zero]

end MVHom

namespace MVAlgebra

variable {A : Type _} [MVAlgebra A]

end MVAlgebra
end Luk
