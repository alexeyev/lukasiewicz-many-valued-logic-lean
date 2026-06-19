import Lukasiewicz.CRT

/-!
# Basic facts about injective/surjective homomorphisms and degenerate quotients

A collection of short, choice-free results that round out the homomorphism and
quotient theory:

* identity and composition behave correctly with respect to injectivity and
  surjectivity (so bijective homomorphisms are closed under composition);
* `A/{0} ≅ A` — quotienting by the zero ideal changes nothing;
* `A/A ≅ 1` — quotienting by the improper ideal yields the trivial algebra;
* the product projections `A × B → A` and `A × B → B` are surjective.

All of these depend only on `Quot.sound` (and `propext` where an `↔` is
rewritten); none uses `Classical.choice`.
-/

namespace Luk
namespace MVAlgebra

variable {A B C : Type _} [MVAlgebra A] [MVAlgebra B] [MVAlgebra C]

/-! ## Identity and composition -/

/-- The identity homomorphism is injective. -/
theorem id_injective : MVHom.Injective (MVHom.id A) := fun h => h

/-- The identity homomorphism is surjective. -/
theorem id_surjective : MVHom.Surjective (MVHom.id A) := fun y => ⟨y, rfl⟩

/-- A composite of injective homomorphisms is injective. -/
theorem comp_injective {g : MVHom B C} {h : MVHom A B}
    (hg : MVHom.Injective g) (hh : MVHom.Injective h) :
    MVHom.Injective (MVHom.comp g h) :=
  fun hxy => hh (hg hxy)

/-- A composite of surjective homomorphisms is surjective. -/
theorem comp_surjective {g : MVHom B C} {h : MVHom A B}
    (hg : MVHom.Surjective g) (hh : MVHom.Surjective h) :
    MVHom.Surjective (MVHom.comp g h) := by
  intro z
  obtain ⟨y, hy⟩ := hg z
  obtain ⟨x, hx⟩ := hh y
  exact ⟨x, by show g (h x) = z; rw [hx, hy]⟩

/-! ## `A / {0} ≅ A` -/

/-- **The quotient by the zero ideal is `A` itself**: the map `⟦a⟧ ↦ a` is a
    well-defined homomorphism (since `d(a,b) = 0` forces `a = b`). -/
def quotZeroIso : MVHom (QuotientByIdeal (zeroIdeal A)) A where
  toFun := Quotient.lift (fun a => a)
    (by
      intro a b hab
      exact eq_of_dist_zero (hab : dist a b = zero))
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

/-- `A/{0} → A` is injective. -/
theorem quotZeroIso_injective : MVHom.Injective (quotZeroIso (A := A)) := by
  intro p q hpq
  induction p using Quotient.inductionOn with | _ x =>
  induction q using Quotient.inductionOn with | _ y =>
  have hxy : x = y := hpq
  apply Quotient.sound
  show (zeroIdeal A).carrier (dist x y)
  show dist x y = zero
  rw [hxy, dist_self]

/-- `A/{0} → A` is surjective. -/
theorem quotZeroIso_surjective : MVHom.Surjective (quotZeroIso (A := A)) :=
  fun y => ⟨Quotient.mk _ y, rfl⟩

/-- **`A / {0} ≅ A`** as a bijective homomorphism. -/
theorem quotZero_iso :
    ∃ φ : MVHom (QuotientByIdeal (zeroIdeal A)) A,
      MVHom.Injective φ ∧ MVHom.Surjective φ :=
  ⟨quotZeroIso, quotZeroIso_injective, quotZeroIso_surjective⟩

/-! ## `A / A ≅ 1` -/

/-- **The quotient by the improper ideal is trivial**: the unique map to `PUnit`. -/
def quotTopToTrivial : MVHom (QuotientByIdeal (topIdeal A)) PUnit where
  toFun := fun _ => PUnit.unit
  map_zero := rfl
  map_oplus := fun _ _ => rfl
  map_neg := fun _ => rfl

/-- `A/A → 1` is injective: any two classes are equal because every distance lies
    in the improper ideal. -/
theorem quotTopToTrivial_injective : MVHom.Injective (quotTopToTrivial (A := A)) := by
  intro p q _
  induction p using Quotient.inductionOn with | _ x =>
  induction q using Quotient.inductionOn with | _ y =>
  apply Quotient.sound
  show (topIdeal A).carrier (dist x y)
  trivial

/-- `A/A → 1` is surjective. -/
theorem quotTopToTrivial_surjective : MVHom.Surjective (quotTopToTrivial (A := A)) := by
  intro y
  exact ⟨Quotient.mk _ zero, by cases y; rfl⟩

/-- **`A / A ≅ 1`** (the trivial MV-algebra) as a bijective homomorphism. -/
theorem quotTop_iso :
    ∃ φ : MVHom (QuotientByIdeal (topIdeal A)) PUnit,
      MVHom.Injective φ ∧ MVHom.Surjective φ :=
  ⟨quotTopToTrivial, quotTopToTrivial_injective, quotTopToTrivial_surjective⟩

/-! ## Product projections are surjective -/

/-- The first projection `A × B → A` is surjective. -/
theorem fst_surjective : MVHom.Surjective (ProdMV.fst : MVHom (A × B) A) :=
  fun a => ⟨(a, (zero : B)), rfl⟩

/-- The second projection `A × B → B` is surjective. -/
theorem snd_surjective : MVHom.Surjective (ProdMV.snd : MVHom (A × B) B) :=
  fun b => ⟨((zero : A), b), rfl⟩

/-! ## The universal property of the product -/

/-- **Pairing**: a pair of homomorphisms `f : A → B` and `g : A → C` induces a
    single homomorphism `⟨f, g⟩ : A → B × C`, `a ↦ (f a, g a)`. -/
def MVHom.pair (f : MVHom A B) (g : MVHom A C) : MVHom A (B × C) where
  toFun := fun a => (f a, g a)
  map_zero := by
    show (f zero, g zero) = ((zero, zero) : B × C); rw [f.map_zero, g.map_zero]
  map_oplus := fun x y => by
    show (f (oplus x y), g (oplus x y)) = (oplus (f x) (f y), oplus (g x) (g y))
    rw [f.map_oplus, g.map_oplus]
  map_neg := fun x => by
    show (f (neg x), g (neg x)) = (neg (f x), neg (g x))
    rw [f.map_neg, g.map_neg]

/-- Projecting the pairing onto the first factor recovers `f`. -/
theorem fst_comp_pair (f : MVHom A B) (g : MVHom A C) (a : A) :
    ProdMV.fst (MVHom.pair f g a) = f a := rfl

/-- Projecting the pairing onto the second factor recovers `g`. -/
theorem snd_comp_pair (f : MVHom A B) (g : MVHom A C) (a : A) :
    ProdMV.snd (MVHom.pair f g a) = g a := rfl

end MVAlgebra
end Luk
