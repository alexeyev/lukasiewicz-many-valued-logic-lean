import Lukasiewicz.IsoBasics

/-!
# The lattice of ideals

The ideals of an MV-algebra form a bounded lattice under intersection (meet) and
sum (join), with the zero ideal at the bottom and the improper ideal at the top.
This module records that structure as a collection of short, choice-free lemmas,
together with the basic theory of **comaximal** ideals (those whose sum is the
whole algebra).

To keep statements first-order and avoid quotient types on ideals, containment
and equality of ideals are expressed at the level of carriers:

* `Ideal.Sub I J` — every element of `I` is in `J` (`I ⊆ J`);
* `Ideal.Equiv I J` — `I` and `J` have the same elements (`I = J`).

Results include: `Sub` is a partial order (reflexive, transitive,
antisymmetric); intersection is the greatest lower bound and sum the least upper
bound; the bottom/top laws; idempotency, commutativity, and absorption; the
order characterizations `I ⊆ J ⟺ I ∩ J = I ⟺ I + J = J`; and that comaximality
is symmetric and equivalent to `1 ∈ I + J` (equivalently `I + J = A`).

Everything depends only on `propext` (for the `↔` lemmas); none uses
`Classical.choice`.
-/

namespace Luk
namespace MVAlgebra

variable {A : Type _} [MVAlgebra A]

/-! ## Containment and equality of ideals -/

/-- **Ideal containment** `I ⊆ J`: every element of `I` lies in `J`. -/
def Ideal.Sub (I J : Ideal A) : Prop := ∀ x, I.carrier x → J.carrier x

/-- **Ideal equality** `I = J`: the two ideals have exactly the same elements. -/
def Ideal.Equiv (I J : Ideal A) : Prop := ∀ x, I.carrier x ↔ J.carrier x

/-- `⊆` is reflexive. -/
theorem Ideal.Sub.refl (I : Ideal A) : I.Sub I := fun _ h => h

/-- `⊆` is transitive. -/
theorem Ideal.Sub.trans {I J K : Ideal A} (h1 : I.Sub J) (h2 : J.Sub K) : I.Sub K :=
  fun x hx => h2 x (h1 x hx)

/-- `⊆` is antisymmetric: mutual containment is equality of ideals. -/
theorem Ideal.sub_antisymm {I J : Ideal A} (h1 : I.Sub J) (h2 : J.Sub I) : I.Equiv J :=
  fun x => ⟨h1 x, h2 x⟩

/-! ## Bottom and top -/

/-- The zero ideal is the **bottom**: `{0} ⊆ I` for every `I`. -/
theorem zeroIdeal_sub (I : Ideal A) : (zeroIdeal A).Sub I := by
  intro x hx
  have hx0 : x = zero := hx
  rw [hx0]; exact I.zero_mem

/-- The improper ideal is the **top**: `I ⊆ A` for every `I`. -/
theorem sub_topIdeal (I : Ideal A) : I.Sub (topIdeal A) := fun _ _ => trivial

/-! ## Intersection is the greatest lower bound -/

/-- `I ∩ J ⊆ I`. -/
theorem inter_sub_left (I J : Ideal A) : (Ideal.inter I J).Sub I := fun _ h => h.1

/-- `I ∩ J ⊆ J`. -/
theorem inter_sub_right (I J : Ideal A) : (Ideal.inter I J).Sub J := fun _ h => h.2

/-- Any lower bound of `I` and `J` is below `I ∩ J`. -/
theorem sub_inter {I J K : Ideal A} (h1 : K.Sub I) (h2 : K.Sub J) :
    K.Sub (Ideal.inter I J) :=
  fun x hx => ⟨h1 x hx, h2 x hx⟩

/-! ## Sum is the least upper bound -/

/-- `I ⊆ I + J`. -/
theorem left_sub_sum (I J : Ideal A) : I.Sub (Ideal.sum I J) := Ideal.le_sum_left I J

/-- `J ⊆ I + J`. -/
theorem right_sub_sum (I J : Ideal A) : J.Sub (Ideal.sum I J) := Ideal.le_sum_right I J

/-- Any upper bound of `I` and `J` is above `I + J`. -/
theorem sum_sub {I J K : Ideal A} (h1 : I.Sub K) (h2 : J.Sub K) :
    (Ideal.sum I J).Sub K :=
  Ideal.sum_le I J K h1 h2

/-! ## Idempotency and commutativity -/

/-- `I ∩ I = I`. -/
theorem inter_self (I : Ideal A) : (Ideal.inter I I).Equiv I :=
  fun _ => ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

/-- `I + I = I`. -/
theorem sum_self (I : Ideal A) : (Ideal.sum I I).Equiv I :=
  fun _ => ⟨fun h => Ideal.sum_le I I I (fun _ k => k) (fun _ k => k) _ h,
            fun h => Ideal.le_sum_left I I _ h⟩

/-- `I ∩ J = J ∩ I`. -/
theorem inter_comm (I J : Ideal A) : (Ideal.inter I J).Equiv (Ideal.inter J I) :=
  fun _ => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- `I + J = J + I`. -/
theorem sum_comm (I J : Ideal A) : (Ideal.sum I J).Equiv (Ideal.sum J I) := by
  intro z
  constructor
  · rintro ⟨x, y, hx, hy, h⟩; exact ⟨y, x, hy, hx, by rw [oplus_comm]; exact h⟩
  · rintro ⟨x, y, hx, hy, h⟩; exact ⟨y, x, hy, hx, by rw [oplus_comm]; exact h⟩

/-! ## Absorption -/

/-- `I ∩ (I + J) = I`. -/
theorem absorb_inter_sum (I J : Ideal A) : (Ideal.inter I (Ideal.sum I J)).Equiv I :=
  fun _ => ⟨fun h => h.1, fun h => ⟨h, Ideal.le_sum_left I J _ h⟩⟩

/-- `I + (I ∩ J) = I`. -/
theorem absorb_sum_inter (I J : Ideal A) : (Ideal.sum I (Ideal.inter I J)).Equiv I :=
  fun _ => ⟨fun h => Ideal.sum_le I (Ideal.inter I J) I (fun _ k => k) (fun _ k => k.1) _ h,
            fun h => Ideal.le_sum_left I (Ideal.inter I J) _ h⟩

/-! ## Order characterizations -/

/-- `I ⊆ J` iff `I + J = J`. -/
theorem sub_iff_sum_eq_right (I J : Ideal A) :
    I.Sub J ↔ (Ideal.sum I J).Equiv J := by
  constructor
  · intro h x
    exact ⟨fun hx => Ideal.sum_le I J J h (fun _ k => k) x hx,
           fun hx => Ideal.le_sum_right I J x hx⟩
  · intro h x hx
    exact (h x).1 (Ideal.le_sum_left I J x hx)

/-- `I ⊆ J` iff `I ∩ J = I`. -/
theorem sub_iff_inter_eq_left (I J : Ideal A) :
    I.Sub J ↔ (Ideal.inter I J).Equiv I := by
  constructor
  · intro h x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, h x hx⟩⟩
  · intro h x hx
    exact ((h x).2 hx).2

/-! ## Comaximal ideals -/

/-- **Comaximality is symmetric.** -/
theorem comaximal_symm {I J : Ideal A} (h : Comaximal I J) : Comaximal J I := by
  obtain ⟨i, j, hi, hj, hij⟩ := h
  exact ⟨j, i, hj, hi, by rw [oplus_comm]; exact hij⟩

/-- **Comaximality is equivalent to `1 ∈ I + J`.** -/
theorem comaximal_iff_one_mem_sum (I J : Ideal A) :
    Comaximal I J ↔ (Ideal.sum I J).carrier one := by
  constructor
  · rintro ⟨i, j, hi, hj, hij⟩
    exact ⟨i, j, hi, hj, by rw [hij]; exact le_one _⟩
  · rintro ⟨x, y, hx, hy, h1⟩
    exact ⟨x, y, hx, hy, le_antisymm (le_one _) h1⟩

/-- **Comaximality is equivalent to `I + J` being the whole algebra.** -/
theorem comaximal_iff_top_sub_sum (I J : Ideal A) :
    Comaximal I J ↔ (topIdeal A).Sub (Ideal.sum I J) := by
  rw [comaximal_iff_one_mem_sum]
  constructor
  · intro h1 x _
    exact (Ideal.sum I J).downward_closed h1 (le_one x)
  · intro h
    exact h one trivial

/-- Every ideal is comaximal with the improper ideal. -/
theorem comaximal_top (I : Ideal A) : Comaximal I (topIdeal A) :=
  ⟨zero, one, I.zero_mem, trivial, by rw [zero_oplus]⟩

/-! ## Intersection of sub-MV-algebras -/

/-- **The intersection of two sub-MV-algebras is a sub-MV-algebra.** (Sub-MV-algebras
    are also closed under intersection — the meet in their lattice.) -/
def SubMVAlgebra.inter (S T : SubMVAlgebra A) : SubMVAlgebra A where
  carrier := fun x => S.carrier x ∧ T.carrier x
  zero_mem := ⟨S.zero_mem, T.zero_mem⟩
  oplus_mem := fun hx hy => ⟨S.oplus_mem hx.1 hy.1, T.oplus_mem hx.2 hy.2⟩
  neg_mem := fun hx => ⟨S.neg_mem hx.1, T.neg_mem hx.2⟩

end MVAlgebra
end Luk
