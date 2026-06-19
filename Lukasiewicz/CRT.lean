import Lukasiewicz.SecondIso

/-!
# The Chinese Remainder Theorem for MV-algebras

This module proves the **Chinese Remainder Theorem (CRT)**: for *comaximal*
ideals `I` and `J` of an MV-algebra `A` (meaning `I + J = A`, equivalently there
exist `i ∈ I`, `j ∈ J` with `i ⊕ j = 1`),

> `A / (I ∩ J) ≅ A/I × A/J`.

The isomorphism is the induced **diagonal** `⟦a⟧ ↦ (⟦a⟧_I, ⟦a⟧_J)`:

* it is **always injective** (its construction collapses exactly `I ∩ J`), and
* it is **surjective precisely when `I` and `J` are comaximal**.

The surjectivity witness is the MV-algebra analogue of the classical CRT
construction. Given `i ∈ I`, `j ∈ J` with `i ⊕ j = 1`, and a target
`(⟦x⟧_I, ⟦y⟧_J)`, the element

$$a \;=\; (y \odot i) \oplus (x \odot j)$$

solves the system `a ≡ x (mod I)` and `a ≡ y (mod J)`. The verification is pure
congruence algebra: from `i ⊕ j = 1` one gets `¬j ≤ i ∈ I` and `¬i ≤ j ∈ J`, so
`i ≈_I 0`, `j ≈_I 1`, `j ≈_J 0`, `i ≈_J 1`; feeding these through the
congruence's `⊙`- and `⊕`-compatibility collapses `a` to `x` modulo `I` and to
`y` modulo `J`.

Everything here is **choice-free**: the only axioms are `Quot.sound` and
`propext`.
-/

namespace Luk
namespace MVAlgebra

variable {A : Type _} [MVAlgebra A]

/-! ## Helper identities -/

-- (`dist_one_right`, `odot_one`, and `dist_zero_right` are general identities
-- proved once in `Distance.lean`; the CRT proofs below reuse them directly.)

/-! ## Comaximality and the witness lemmas -/

/-- **Comaximal ideals**: `I` and `J` are comaximal when `I + J = A`, witnessed
    concretely by elements `i ∈ I`, `j ∈ J` with `i ⊕ j = 1`. -/
def Comaximal (I J : Ideal A) : Prop :=
  ∃ i j, I.carrier i ∧ J.carrier j ∧ oplus i j = one

/-- **CRT witness, `I`-component**: with `i ∈ I` and `¬j ∈ I`, the witness
    `(y ⊙ i) ⊕ (x ⊙ j)` is congruent to `x` modulo `I`. -/
theorem witness_rel_I (I : Ideal A) {i j : A}
    (hi : I.carrier i) (hnj : I.carrier (neg j)) (x y : A) :
    I.congruence.rel (oplus (odot y i) (odot x j)) x := by
  have hi0 : I.congruence.rel i zero := by
    show I.carrier (dist i zero); rwa [dist_zero_right]
  have hj1 : I.congruence.rel j one := by
    show I.carrier (dist j one); rwa [dist_one_right]
  have e1 : I.congruence.rel (odot y i) (odot y zero) :=
    I.congruence.odot_compat (I.congruence.refl y) hi0
  rw [odot_zero] at e1
  have e2 : I.congruence.rel (odot x j) (odot x one) :=
    I.congruence.odot_compat (I.congruence.refl x) hj1
  rw [odot_one] at e2
  have e3 := I.congruence.oplus_compat e1 e2
  rwa [zero_oplus] at e3

/-- **CRT witness, `J`-component**: with `j ∈ J` and `¬i ∈ J`, the witness
    `(y ⊙ i) ⊕ (x ⊙ j)` is congruent to `y` modulo `J`. -/
theorem witness_rel_J (J : Ideal A) {i j : A}
    (hj : J.carrier j) (hni : J.carrier (neg i)) (x y : A) :
    J.congruence.rel (oplus (odot y i) (odot x j)) y := by
  have hj0 : J.congruence.rel j zero := by
    show J.carrier (dist j zero); rwa [dist_zero_right]
  have hi1 : J.congruence.rel i one := by
    show J.carrier (dist i one); rwa [dist_one_right]
  have e1 : J.congruence.rel (odot x j) (odot x zero) :=
    J.congruence.odot_compat (J.congruence.refl x) hj0
  rw [odot_zero] at e1
  have e2 : J.congruence.rel (odot y i) (odot y one) :=
    J.congruence.odot_compat (J.congruence.refl y) hi1
  rw [odot_one] at e2
  have e3 := J.congruence.oplus_compat e2 e1
  rwa [oplus_zero] at e3

/-! ## The CRT isomorphism -/

/-- **The induced CRT map** `A/(I ∩ J) → A/I × A/J`, sending
    `⟦a⟧ ↦ (⟦a⟧_I, ⟦a⟧_J)`. Well-defined because `d(a,b) ∈ I ∩ J` gives
    `d(a,b) ∈ I` and `d(a,b) ∈ J` separately. -/
def crtMap (I J : Ideal A) :
    MVHom (QuotientByIdeal (Ideal.inter I J))
          (QuotientByIdeal I × QuotientByIdeal J) where
  toFun := Quotient.lift (fun a => (Quotient.mk I.setoid a, Quotient.mk J.setoid a))
    (by
      intro a b hab
      apply Prod.ext
      · exact Quotient.sound (hab.1 : I.carrier (dist a b))
      · exact Quotient.sound (hab.2 : J.carrier (dist a b)))
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

/-- **The CRT map is always injective.** If `(⟦x⟧_I, ⟦x⟧_J) = (⟦y⟧_I, ⟦y⟧_J)`
    then `d(x,y) ∈ I` and `d(x,y) ∈ J`, so `d(x,y) ∈ I ∩ J` and the classes are
    equal. -/
theorem crtMap_injective (I J : Ideal A) : MVHom.Injective (crtMap I J) := by
  intro p q hpq
  induction p using Quotient.inductionOn with | _ x =>
  induction q using Quotient.inductionOn with | _ y =>
  have h1 : Quotient.mk I.setoid x = Quotient.mk I.setoid y := congrArg Prod.fst hpq
  have h2 : Quotient.mk J.setoid x = Quotient.mk J.setoid y := congrArg Prod.snd hpq
  apply Quotient.sound
  show (Ideal.inter I J).carrier (dist x y)
  exact ⟨Quotient.exact h1, Quotient.exact h2⟩

/-- **The CRT map is surjective when `I` and `J` are comaximal.** Given the
    comaximality witnesses `i ∈ I`, `j ∈ J` with `i ⊕ j = 1`, the element
    `(y ⊙ i) ⊕ (x ⊙ j)` maps onto any target `(⟦x⟧_I, ⟦y⟧_J)`. -/
theorem crtMap_surjective (I J : Ideal A) (h : Comaximal I J) :
    MVHom.Surjective (crtMap I J) := by
  obtain ⟨i, j, hi, hj, hij⟩ := h
  -- `¬j ≤ i ∈ I` and `¬i ≤ j ∈ J`, hence `¬j ∈ I` and `¬i ∈ J`.
  have hnj : I.carrier (neg j) :=
    I.downward_closed hi (by show oplus (neg (neg j)) i = one; rw [neg_neg, oplus_comm]; exact hij)
  have hni : J.carrier (neg i) :=
    J.downward_closed hj (by show oplus (neg (neg i)) j = one; rw [neg_neg]; exact hij)
  intro q
  obtain ⟨qI, qJ⟩ := q
  induction qI using Quotient.inductionOn with | _ x =>
  induction qJ using Quotient.inductionOn with | _ y =>
  refine ⟨Quotient.mk (Ideal.inter I J).setoid (oplus (odot y i) (odot x j)), ?_⟩
  show (Quotient.mk I.setoid (oplus (odot y i) (odot x j)),
        Quotient.mk J.setoid (oplus (odot y i) (odot x j))) = (_, _)
  apply Prod.ext
  · exact Quotient.sound (witness_rel_I I hi hnj x y)
  · exact Quotient.sound (witness_rel_J J hj hni x y)

/-- **The Chinese Remainder Theorem for MV-algebras.** For comaximal ideals
    `I` and `J`, the canonical diagonal map `A/(I ∩ J) → A/I × A/J` is a
    bijective MV-homomorphism — an isomorphism

    `A / (I ∩ J) ≅ A/I × A/J`.

    (Injectivity holds for *all* ideals; comaximality is exactly what supplies
    surjectivity.) -/
theorem chineseRemainderTheorem (I J : Ideal A) (h : Comaximal I J) :
    ∃ φ : MVHom (QuotientByIdeal (Ideal.inter I J))
                (QuotientByIdeal I × QuotientByIdeal J),
      MVHom.Injective φ ∧ MVHom.Surjective φ :=
  ⟨crtMap I J, crtMap_injective I J, crtMap_surjective I J h⟩

end MVAlgebra
end Luk
