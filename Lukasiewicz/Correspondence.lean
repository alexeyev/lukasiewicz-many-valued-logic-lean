import Lukasiewicz.Quotient

/-!
# The Correspondence Theorem and the Third Isomorphism Theorem

Building on the quotient construction (`Quotient.lean`), this module completes
the standard suite of isomorphism theorems for MV-algebras:

* **The Correspondence Theorem** (a.k.a. the Lattice / Fourth Isomorphism
  Theorem): for an ideal `I`, the ideals of the quotient `A/I` are in bijection
  with the ideals of `A` that contain `I`. The bijection is
  `J ↦ J/I` (pushforward) and `K ↦ π⁻¹(K)` (preimage).

* **The Third Isomorphism Theorem**: for ideals `I ⊆ J`, the canonical map
  `A/I → A/J`, `⟦x⟧_I ↦ ⟦x⟧_J`, is a surjective homomorphism whose kernel is
  `J/I`. Hence `(A/I)/(J/I) ≅ A/J`.

Everything here is **choice-free**: the only axioms used are `Quot.sound` and
`propext`.

A key technical lemma threaded throughout is `mem_of_dist_mem`: an ideal's
membership predicate is closed under the induced congruence
(`d(x,y) ∈ J ∧ y ∈ J ⟹ x ∈ J`), which follows from transitivity of the
congruence and the identity `d(x,0) = x`.
-/

namespace Luk
namespace MVAlgebra

variable {A : Type _} [MVAlgebra A]

/-! ## Helper lemmas -/

/-- **Ideal membership is closed under the induced congruence.** If the distance
    `d(x,y)` lies in `J` and `y ∈ J`, then `x ∈ J`. Proof: `d(x,y) ∈ J` says
    `x ≈_J y`, `y ∈ J` says `y ≈_J 0`, so `x ≈_J 0` by transitivity, i.e.
    `d(x,0) ∈ J`; and `d(x,0) = x`. -/
theorem mem_of_dist_mem (J : Ideal A) {x y : A}
    (hd : J.carrier (dist x y)) (hy : J.carrier y) : J.carrier x := by
  have hx0 : J.congruence.rel x zero :=
    J.congruence.trans (hd : J.congruence.rel x y)
      (by show J.carrier (dist y zero); rw [dist_zero_right]; exact hy)
  have h2 : J.carrier (dist x zero) := hx0
  rw [dist_zero_right] at h2
  exact h2

/-- If `x ≤ y` then `x ∧ y = x`. (A small lattice fact used to show pushforward
    ideals are downward closed.) -/
theorem mvinf_eq_left_of_le {x y : A} (hxy : le x y) : mvinf x y = x := by
  show odot x (oplus (neg x) y) = x
  have h1 : oplus (neg x) y = one := hxy
  rw [h1]
  show neg (oplus (neg x) (neg one)) = x
  rw [neg_one_eq_zero, oplus_zero, neg_neg]

/-- The quotient projection, returning the `QuotientByIdeal` type so the
    MV-algebra instance on the quotient is found by type-class resolution. -/
def Ideal.qmk (I : Ideal A) (x : A) : QuotientByIdeal I := Quotient.mk I.setoid x

/-! ## The two maps of the correspondence -/

/-- **Preimage direction**: pull an ideal `K` of `A/I` back to an ideal of `A`
    (necessarily containing `I`). This is just the preimage under the quotient
    map. -/
def corrPreimage (I : Ideal A) (K : Ideal (QuotientByIdeal I)) : Ideal A :=
  (Ideal.mkHom I).preimage K

/-- The preimage `π⁻¹(K)` contains `I`: every element of `I` maps to `0 ∈ K`. -/
theorem corrPreimage_contains (I : Ideal A) (K : Ideal (QuotientByIdeal I)) :
    ∀ x, I.carrier x → (corrPreimage I K).carrier x := by
  intro x hx
  show K.carrier (Quotient.mk I.setoid x)
  have : Quotient.mk I.setoid x = Quotient.mk I.setoid zero := by
    apply Quotient.sound
    show I.carrier (dist x zero); rw [dist_zero_right]; exact hx
  rw [this]
  exact K.zero_mem

/-- **Pushforward direction**: push an ideal `J ⊇ I` of `A` forward to the ideal
    `J/I := {⟦x⟧ : x ∈ J}` of `A/I`. -/
def corrImage (I J : Ideal A) (_hIJ : ∀ x, I.carrier x → J.carrier x) :
    Ideal (QuotientByIdeal I) where
  carrier := fun p => ∃ x, J.carrier x ∧ I.qmk x = p
  zero_mem := ⟨zero, J.zero_mem, rfl⟩
  downward_closed := by
    rintro p q ⟨x, hx, rfl⟩ hqp
    induction q using Quotient.inductionOn with | _ y =>
    -- q = ⟦y⟧ ≤ ⟦x⟧. Witness y by y ∧ x: it is ≤ x ∈ J (downward), and ⟦y ∧ x⟧ = ⟦y⟧.
    refine ⟨mvinf y x, J.downward_closed hx (le_mvinf_right y x), ?_⟩
    show I.qmk (mvinf y x) = I.qmk y
    exact mvinf_eq_left_of_le (hqp : le (I.qmk y) (I.qmk x))
  oplus_mem := by
    rintro p q ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨oplus x y, J.oplus_mem hx hy, rfl⟩

/-! ## The Correspondence Theorem -/

/-- **Correspondence Theorem, first round-trip**: pulling `J/I` back recovers `J`
    (for any ideal `J ⊇ I`). -/
theorem corr_left_inv (I J : Ideal A) (hIJ : ∀ x, I.carrier x → J.carrier x) (x : A) :
    (corrPreimage I (corrImage I J hIJ)).carrier x ↔ J.carrier x := by
  show (∃ z, J.carrier z ∧ I.qmk z = I.qmk x) ↔ J.carrier x
  constructor
  · rintro ⟨z, hz, hzx⟩
    have hd : I.carrier (dist z x) := Quotient.exact hzx
    have hdJ' : J.carrier (dist x z) := by rw [dist_comm]; exact hIJ _ hd
    exact mem_of_dist_mem J hdJ' hz
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- **Correspondence Theorem, second round-trip**: pushing `π⁻¹(K)` forward
    recovers `K` (for any ideal `K` of `A/I`). -/
theorem corr_right_inv (I : Ideal A) (K : Ideal (QuotientByIdeal I))
    (hcontains : ∀ x, I.carrier x → (corrPreimage I K).carrier x)
    (p : QuotientByIdeal I) :
    (corrImage I (corrPreimage I K) hcontains).carrier p ↔ K.carrier p := by
  constructor
  · rintro ⟨x, hx, hxp⟩
    have hk : K.carrier (I.qmk x) := hx
    rw [hxp] at hk
    exact hk
  · intro hp
    induction p using Quotient.inductionOn with | _ x =>
    exact ⟨x, hp, rfl⟩

/-- **The Correspondence Theorem.** For an ideal `I` of `A`, the maps
    `J ↦ J/I` and `K ↦ π⁻¹(K)` are mutually inverse bijections between the
    ideals of `A` containing `I` and the ideals of `A/I`. (Stated as the
    conjunction of the two round-trips, at the level of carriers.) -/
theorem correspondenceTheorem (I : Ideal A) :
    -- pushforward then pullback is the identity on ideals J ⊇ I
    (∀ (J : Ideal A) (hIJ : ∀ x, I.carrier x → J.carrier x) (x : A),
        (corrPreimage I (corrImage I J hIJ)).carrier x ↔ J.carrier x)
    ∧
    -- pullback then pushforward is the identity on ideals K of A/I
    (∀ (K : Ideal (QuotientByIdeal I))
        (hcontains : ∀ x, I.carrier x → (corrPreimage I K).carrier x)
        (p : QuotientByIdeal I),
        (corrImage I (corrPreimage I K) hcontains).carrier p ↔ K.carrier p) :=
  ⟨corr_left_inv I, corr_right_inv I⟩

/-! ## The Third Isomorphism Theorem -/

/-- **The canonical map `A/I → A/J`** for `I ⊆ J`, sending `⟦x⟧_I ↦ ⟦x⟧_J`. It
    is well-defined because `⟦x⟧_I = ⟦y⟧_I` means `d(x,y) ∈ I ⊆ J`, so
    `⟦x⟧_J = ⟦y⟧_J`. -/
def thirdIsoMap (I J : Ideal A) (hIJ : ∀ x, I.carrier x → J.carrier x) :
    MVHom (QuotientByIdeal I) (QuotientByIdeal J) where
  toFun := Quotient.lift (fun x => Quotient.mk J.setoid x)
    (by
      intro a b hab
      apply Quotient.sound
      show J.carrier (dist a b)
      exact hIJ _ hab)
  map_zero := rfl
  map_oplus := by
    intro p q
    induction p using Quotient.inductionOn with | _ x =>
    induction q using Quotient.inductionOn with | _ y =>
    rfl
  map_neg := by
    intro p
    induction p using Quotient.inductionOn with | _ x =>
    rfl

/-- The canonical map `A/I → A/J` is **surjective**. -/
theorem thirdIsoMap_surjective (I J : Ideal A) (hIJ : ∀ x, I.carrier x → J.carrier x) :
    ∀ q, ∃ p, thirdIsoMap I J hIJ p = q := by
  intro q
  induction q using Quotient.inductionOn with | _ x =>
  exact ⟨Quotient.mk I.setoid x, rfl⟩

/-- **The kernel of `A/I → A/J` is `J/I`**: a class `⟦x⟧_I` is in the kernel iff
    `x ∈ J`. This is the precise sense in which the kernel "is" `J/I`. -/
theorem ker_thirdIsoMap (I J : Ideal A) (hIJ : ∀ x, I.carrier x → J.carrier x) (x : A) :
    (thirdIsoMap I J hIJ).ker.carrier (Quotient.mk I.setoid x) ↔ J.carrier x := by
  show (Quotient.mk J.setoid x = Quotient.mk J.setoid zero) ↔ J.carrier x
  constructor
  · intro h
    have hh : J.carrier (dist x zero) := Quotient.exact h
    rw [dist_zero_right] at hh
    exact hh
  · intro h
    apply Quotient.sound
    show J.carrier (dist x zero); rw [dist_zero_right]; exact h

/-- **The Third Isomorphism Theorem.** For ideals `I ⊆ J` of `A`, there is a
    surjective MV-homomorphism `A/I → A/J` whose kernel consists exactly of the
    classes `⟦x⟧_I` with `x ∈ J` (that is, `J/I`). Composing with the First
    Isomorphism Theorem yields `(A/I)/(J/I) ≅ A/J`. -/
theorem thirdIsomorphismTheorem (I J : Ideal A) (hIJ : ∀ x, I.carrier x → J.carrier x) :
    ∃ φ : MVHom (QuotientByIdeal I) (QuotientByIdeal J),
      (∀ q, ∃ p, φ p = q) ∧
      (∀ x, φ.ker.carrier (Quotient.mk I.setoid x) ↔ J.carrier x) :=
  ⟨thirdIsoMap I J hIJ, thirdIsoMap_surjective I J hIJ, ker_thirdIsoMap I J hIJ⟩

end MVAlgebra
end Luk
