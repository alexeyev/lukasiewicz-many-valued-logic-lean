import Lukasiewicz.Instances

/-!
# Quotient MV-algebras and the First Isomorphism Theorem

Building on the ideal–congruence correspondence (`Ideals.lean`), this module
constructs the **quotient MV-algebra** `A/I` for an ideal `I`, and proves the
**First Isomorphism Theorem**:

> for any MV-homomorphism `h : A → B`, the quotient `A / Ker(h)` is isomorphic
> to the image `Im(h)` — via the canonical map `⟦x⟧ ↦ h x`, which is shown to
> be a bijective homomorphism.

The construction is entirely choice-free: it uses Lean's quotient types
(`Quotient`, `Quotient.lift`, `Quotient.sound`, `Quotient.ind`), whose only
axiom is `Quot.sound`. An isomorphism is presented honestly as a homomorphism
that is both injective and surjective (constructing the literal inverse map
would require the axiom of choice, since membership in the image is a `Prop`).

Highlights:
- `Ideal.setoid`, `QuotientByIdeal` — the quotient type `A/I`.
- `instQuotientMV` — `A/I` is an MV-algebra under the lifted operations.
- `Ideal.mkHom` — the canonical surjection `A → A/I`, with `Ker = I`.
- `SubMVAlgebra.Subtype`, `instSubMV` — a sub-MV-algebra as an MV-algebra in
  its own right (needed to talk about `Im(h)` as a type).
- `firstIso`, `firstIso_injective`, `firstIso_surjective` — the First
  Isomorphism Theorem.
-/

namespace Luk
namespace MVAlgebra

variable {A B : Type _} [MVAlgebra A] [MVAlgebra B]

/-! ## The quotient MV-algebra `A/I` -/

/-- The **setoid induced by an ideal** `I`: declare `x ≈ y` exactly when the
    distance `d(x,y)` lies in `I`. The equivalence laws are inherited from the
    congruence `Ideal.congruence` proved in `Ideals.lean`. -/
def Ideal.setoid (I : Ideal A) : Setoid A where
  r := fun x y => I.carrier (dist x y)
  iseqv :=
    { refl  := fun x => I.congruence.refl x
      symm  := fun {_ _} h => I.congruence.symm h
      trans := fun {_ _ _} h1 h2 => I.congruence.trans h1 h2 }

/-- The **quotient type** `A/I`. -/
def QuotientByIdeal (I : Ideal A) : Type _ := Quotient I.setoid

/-- The **quotient MV-algebra**: `A/I` carries an MV-algebra structure with
    operations lifted componentwise from `A`. Well-definedness of `⊕` and `¬`
    is exactly the compatibility of the ideal-induced congruence; the six Chang
    axioms transfer through `Quotient.inductionOn` from the axioms on `A`. -/
instance instQuotientMV (I : Ideal A) : MVAlgebra (QuotientByIdeal I) where
  zero := Quotient.mk I.setoid zero
  oplus := Quotient.lift₂ (fun x y => Quotient.mk I.setoid (oplus x y))
    (fun _ _ _ _ hx hy => Quotient.sound (I.congruence.oplus_compat hx hy))
  neg := Quotient.lift (fun x => Quotient.mk I.setoid (neg x))
    (fun _ _ hx => Quotient.sound (I.congruence.neg_compat hx))
  oplus_assoc := by
    intro p q r
    induction p using Quotient.inductionOn with | _ x =>
    induction q using Quotient.inductionOn with | _ y =>
    induction r using Quotient.inductionOn with | _ z =>
    exact congrArg (Quotient.mk I.setoid) (oplus_assoc x y z)
  oplus_comm := by
    intro p q
    induction p using Quotient.inductionOn with | _ x =>
    induction q using Quotient.inductionOn with | _ y =>
    exact congrArg (Quotient.mk I.setoid) (oplus_comm x y)
  oplus_zero := by
    intro p
    induction p using Quotient.inductionOn with | _ x =>
    exact congrArg (Quotient.mk I.setoid) (oplus_zero x)
  neg_neg := by
    intro p
    induction p using Quotient.inductionOn with | _ x =>
    exact congrArg (Quotient.mk I.setoid) (neg_neg x)
  oplus_negzero := by
    intro p
    induction p using Quotient.inductionOn with | _ x =>
    exact congrArg (Quotient.mk I.setoid) (oplus_negzero x)
  mv_axiom := by
    intro p q
    induction p using Quotient.inductionOn with | _ x =>
    induction q using Quotient.inductionOn with | _ y =>
    exact congrArg (Quotient.mk I.setoid) (mv_axiom x y)

/-! ## The canonical quotient homomorphism and its kernel -/

-- (`odot_one`, `dist_zero_right`, `dist_one_right` are general identities now
-- proved once in `Distance.lean` and reused throughout.)

/-- The **canonical quotient homomorphism** `A → A/I`, `x ↦ ⟦x⟧`. Because the
    quotient operations are defined by lifting, every preservation law holds by
    `rfl`. -/
def Ideal.mkHom (I : Ideal A) : MVHom A (QuotientByIdeal I) where
  toFun := fun x => Quotient.mk I.setoid x
  map_zero := rfl
  map_oplus := fun _ _ => rfl
  map_neg := fun _ => rfl

/-- **The kernel of the quotient map `A → A/I` is exactly `I`.** This is the
    other half of "ideals are kernels": every ideal is the kernel of *some*
    homomorphism (namely its own quotient map). -/
theorem ker_mkHom (I : Ideal A) (x : A) :
    (Ideal.mkHom I).ker.carrier x ↔ I.carrier x := by
  show (Quotient.mk I.setoid x = Quotient.mk I.setoid zero) ↔ I.carrier x
  constructor
  · intro h
    have hr : I.carrier (dist x zero) := Quotient.exact h
    rw [dist_zero_right] at hr
    exact hr
  · intro h
    apply Quotient.sound
    show I.carrier (dist x zero)
    rw [dist_zero_right]; exact h

/-- The quotient map `A → A/I` is **surjective**. -/
theorem mkHom_surjective (I : Ideal A) :
    ∀ p : QuotientByIdeal I, ∃ x, (Ideal.mkHom I) x = p := by
  intro p
  induction p using Quotient.inductionOn with | _ x =>
  exact ⟨x, rfl⟩

/-! ## A sub-MV-algebra as an MV-algebra in its own right -/

/-- The **underlying subtype** of a sub-MV-algebra `S` — the elements of `A`
    satisfying `S.carrier`. -/
def SubMVAlgebra.Subtype (S : SubMVAlgebra A) := {x : A // S.carrier x}

/-- **A sub-MV-algebra is itself an MV-algebra.** The operations are the
    ambient ones, with closure witnesses supplied by `S`; equality of subtype
    elements reduces to equality of their values (`Subtype.ext`), so every
    Chang axiom transfers from `A`. -/
instance instSubMV (S : SubMVAlgebra A) : MVAlgebra S.Subtype where
  zero := ⟨zero, S.zero_mem⟩
  oplus := fun a b => ⟨oplus a.1 b.1, S.oplus_mem a.2 b.2⟩
  neg := fun a => ⟨neg a.1, S.neg_mem a.2⟩
  oplus_assoc := fun a b c => Subtype.ext (oplus_assoc a.1 b.1 c.1)
  oplus_comm := fun a b => Subtype.ext (oplus_comm a.1 b.1)
  oplus_zero := fun a => Subtype.ext (oplus_zero a.1)
  neg_neg := fun a => Subtype.ext (neg_neg a.1)
  oplus_negzero := fun a => Subtype.ext (oplus_negzero a.1)
  mv_axiom := fun a b => Subtype.ext (mv_axiom a.1 b.1)

/-! ## The First Isomorphism Theorem -/

/-- An MV-homomorphism is **surjective** if every element of the codomain is hit. -/
def MVHom.Surjective (h : MVHom A B) : Prop := ∀ y, ∃ x, h x = y

-- (Injectivity uses the predicate `MVHom.Injective` already defined in
-- `IdealOperations.lean`; surjectivity is `MVHom.Surjective` above.)

/-- **The canonical map of the First Isomorphism Theorem**: `A / Ker(h) → Im(h)`
    sending `⟦x⟧ ↦ h x` (landing in the image with witness `x`). It is
    well-defined because `⟦x⟧ = ⟦y⟧` means `d(x,y) ∈ Ker(h)`, i.e.
    `h(d(x,y)) = 0`, i.e. `d(h x, h y) = 0`, i.e. `h x = h y`. -/
def firstIso (h : MVHom A B) :
    MVHom (QuotientByIdeal (MVHom.ker h)) (MVHom.image h).Subtype where
  toFun := Quotient.lift (fun x => (⟨h x, ⟨x, rfl⟩⟩ : (MVHom.image h).Subtype))
    (by
      intro a b hab
      apply Subtype.ext
      show h a = h b
      have hk : (MVHom.ker h).carrier (dist a b) := hab
      have hz : h (dist a b) = zero := hk
      rw [h.map_dist] at hz
      exact eq_of_dist_zero hz)
  map_zero := Subtype.ext h.map_zero
  map_oplus := by
    intro p q
    induction p using Quotient.inductionOn with | _ x =>
    induction q using Quotient.inductionOn with | _ y =>
    apply Subtype.ext
    show h (oplus x y) = oplus (h x) (h y)
    rw [h.map_oplus]
  map_neg := by
    intro p
    induction p using Quotient.inductionOn with | _ x =>
    apply Subtype.ext
    show h (neg x) = neg (h x)
    rw [h.map_neg]

/-- **First Isomorphism Theorem, injectivity half**: the canonical map
    `A / Ker(h) → Im(h)` is injective. If `h x = h y` then `d(x,y) ∈ Ker(h)`,
    so `⟦x⟧ = ⟦y⟧`. -/
theorem firstIso_injective (h : MVHom A B) : MVHom.Injective (firstIso h) := by
  intro p q hpq
  induction p using Quotient.inductionOn with | _ x =>
  induction q using Quotient.inductionOn with | _ y =>
  have hxy : h x = h y := congrArg Subtype.val hpq
  apply Quotient.sound
  show (MVHom.ker h).carrier (dist x y)
  show h (dist x y) = zero
  rw [h.map_dist, hxy, dist_self]

/-- **First Isomorphism Theorem, surjectivity half**: the canonical map
    `A / Ker(h) → Im(h)` is surjective. Every element of the image is `h a`
    for some `a`, and `⟦a⟧` maps to it. -/
theorem firstIso_surjective (h : MVHom A B) : MVHom.Surjective (firstIso h) := by
  intro y
  obtain ⟨b, a, hab⟩ := y
  refine ⟨Quotient.mk _ a, ?_⟩
  apply Subtype.ext
  show h a = b
  exact hab

/-- **The First Isomorphism Theorem.** For every MV-homomorphism `h : A → B`,
    there is a bijective MV-homomorphism `A / Ker(h) → Im(h)` — i.e.
    `A / Ker(h) ≅ Im(h)`. (Bijective homomorphism = isomorphism of MV-algebras;
    the inverse is automatically a homomorphism, though exhibiting it requires
    choice, so we record bijectivity directly.) -/
theorem firstIsomorphismTheorem (h : MVHom A B) :
    ∃ φ : MVHom (QuotientByIdeal (MVHom.ker h)) (MVHom.image h).Subtype,
      MVHom.Injective φ ∧ MVHom.Surjective φ :=
  ⟨firstIso h, firstIso_injective h, firstIso_surjective h⟩

end MVAlgebra
end Luk
