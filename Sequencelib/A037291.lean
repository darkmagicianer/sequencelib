import Mathlib
import Sequencelib.Meta


open Synth

/-!
# A037291 sequence

## References

- T. Gauthier; and J. Urban (2023). Learning Program Synthesis for Integer Sequences from Scratch.
  The Thirty-Seventh AAAI Conference on Artificial Intelligence (AAAI-23)
-/
abbrev RingOfOrder (n : ℕ) := {R : RingCat.{0} // ENat.card R = n}

def FiniteRingSetoid (n : ℕ) : Setoid (RingOfOrder n) where
  r := fun ⟨r1, _⟩ ⟨r2, _⟩ => Nonempty (r1 ≅ r2)
  iseqv := {
    refl := fun ⟨X, _⟩ => ⟨CategoryTheory.Iso.refl X⟩
    symm := fun ⟨a⟩ => ⟨a.symm⟩
    trans := fun ⟨a⟩ ⟨b⟩ => ⟨a.trans b⟩
  }

abbrev NonIsoFiniteRing (n : ℕ) := Quotient (FiniteRingSetoid n)



namespace Sequence

noncomputable def A037291 (n : ℕ) : ℕ := Nat.card (NonIsoFiniteRing n)

end Sequence

lemma A037291_one : Sequence.A037291 1 = 1 := by
  change Nat.card (NonIsoFiniteRing 1) = 1
  rw [Nat.card_eq_one_iff_unique]
  constructor
  constructor
  intro a b
  obtain ⟨R1⟩ := a
  obtain ⟨R2⟩ := b
  apply Quot.sound
  change Nonempty (R1.1 ≅ R2.1)
  let one_R1 : R1.1 := 1
  let one_R2 : R2.1 := 1
  have hsub1: Unique R1.1 := (ENat.card_eq_one_iff_unique.mp R1.2).some
  have hsub2 : Unique R2.1 := (ENat.card_eq_one_iff_unique.mp R2.2).some
  let f : R1.1 →+* R2.1 := {
    toFun := fun _ => one_R2
    map_one' := rfl
    map_mul' := fun _ _ => Subsingleton.elim _ _
    map_zero' := Subsingleton.elim _ _
    map_add' := fun _ _ => Subsingleton.elim _ _
  }
  have hfbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_surjective_and_card]
    refine ⟨fun y => ⟨1, Subsingleton.elim _ _⟩, by simp⟩
  let g : R1.1 ≃+* R2.1 := RingEquiv.ofBijective f hfbij
  exact (⟨{
    hom := RingCat.ofHom g.toRingHom
    inv := RingCat.ofHom g.symm.toRingHom
    hom_inv_id := by ext x; exact g.symm_apply_apply x
    inv_hom_id := by ext y; exact g.apply_symm_apply y
  }⟩)
  let R0 : RingOfOrder 1 := ⟨RingCat.of PUnit, ENat.card_eq_one_iff_unique.mpr ⟨inferInstance⟩⟩
  exact ⟨Quotient.mk (FiniteRingSetoid 1) R0⟩
