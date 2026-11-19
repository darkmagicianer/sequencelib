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

lemma A037291_two : Sequence.A037291 2 = 1 := by
  change Nat.card (NonIsoFiniteRing 2) = 1
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
  let zero_R1 : R1.1 := 0
  let zero_R2 : R2.1 := 0
  have : Nontrivial R1.1 := (ENat.one_lt_card_iff_nontrivial R1.1).mp (by rw [R1.2]; norm_num)
  have : Nontrivial R2.1 := (ENat.one_lt_card_iff_nontrivial R2.1).mp (by rw [R2.2]; norm_num)
  have onenezeroR1 : ¬ (1 : R1.1) = 0 := zero_ne_one.symm
  have onenezeroR2 : ¬ (1 : R2.1) = 0 := zero_ne_one.symm
  have elem_nezero_then_oneR1 : ∀ x : R1.1, ¬ (x = 0) → x = 1 := by
    intro x hx
    by_contra
    have h_card1 : Nat.card R1.1 = 2 := by
      have h := congr_arg ENat.toNat R1.2
      simpa [Nat.card, ENat.card] using h
    obtain ⟨a, b, _, huniv⟩ := Nat.card_eq_two_iff.mp h_card1
    have h_cases : ∀ z : R1.1, z = a ∨ z = b := by
      intro z
      have hz : z ∈ ({a, b} : Set R1.1) := huniv.symm ▸ Set.mem_univ z
      simpa using hz
    rcases h_cases 0 with h0 | h0 <;> rcases h_cases 1 with h1 | h1 <;> rcases h_cases x with hx' | hx' <;>
    simp_all [zero_ne_one]
  have elem_nezero_then_oneR2 : ∀ x : R2.1, ¬ (x = 0) → x = 1 := by
    intro x hx
    by_contra
    have h_card1 : Nat.card R2.1 = 2 := by
      have h := congr_arg ENat.toNat R2.2
      simpa [Nat.card, ENat.card] using h
    obtain ⟨a, b, _, huniv⟩ := Nat.card_eq_two_iff.mp h_card1
    have h_cases : ∀ z : R2.1, z = a ∨ z = b := by
      intro z
      have hz : z ∈ ({a, b} : Set R2.1) := huniv.symm ▸ Set.mem_univ z
      simpa using hz
    rcases h_cases 0 with h0 | h0 <;> rcases h_cases 1 with h1 | h1 <;> rcases h_cases x with hx' | hx' <;>
    simp_all [zero_ne_one]
  have oneplusonezeroR1 : (1 : R1.1) + (1 : R1.1) = (0 :R1.1) := by
    by_contra h
    have h1 : (1 : R1.1) + 1 = 1 := elem_nezero_then_oneR1 ((1 : R1.1) + 1) h
    have h2 : (1 : R1.1) = 0 := add_eq_right.mp h1
    exact one_ne_zero h2

  have oneplusonezeroR2 : (1 : R2.1) + (1 : R2.1) = (0 :R2.1) := by
    by_contra h
    have h1 : (1 : R2.1) + 1 = 1 := elem_nezero_then_oneR2 ((1 : R2.1) + 1) h
    have h2 : (1 : R2.1) = 0 := add_eq_right.mp h1
    exact one_ne_zero h2

  classical
  let f : R1.1 →+* R2.1 := {
    toFun := fun x => if (x = (0 : R1.1)) then (0 : R2.1) else (1 : R2.1)
    map_one' := by rw [if_neg zero_ne_one.symm]
    map_mul' := by
      intro x y
      by_cases hx : x = 0 <;> by_cases hy : y = 0
      rw [if_pos]; rw [if_pos]; rw [if_pos]; simp; exact hy; exact hx; bound
      rw [if_pos]; rw [if_pos]; rw[if_neg]; simp; exact hy; exact hx; bound
      rw [if_pos]; rw[if_neg]; rw [if_pos]; simp; exact hy; exact hx; bound
      rw [if_neg]; rw[if_neg]; rw[if_neg]; simp; exact hy; exact hx;
      have hx' : x = 1 := elem_nezero_then_oneR1 x hx
      have hy' : y = 1 := elem_nezero_then_oneR1 y hy
      have hxy : x * y = 1 := by bound
      rw [hxy.symm] at onenezeroR1
      exact onenezeroR1
    map_zero' := by rw[if_pos]; rfl
    map_add' := by
      intro x y
      by_cases hx : x = 0 <;> by_cases hy : y = 0
      rw [if_pos]; rw [if_pos]; rw [if_pos]; simp; exact hy; exact hx; bound
      rw [if_neg]; rw [if_pos]; rw [if_neg]; simp; exact hy; exact hx; have : y = 1 := elem_nezero_then_oneR1 y hy; have hxy : x + y = 1 := by bound;
      rw [hxy.symm] at onenezeroR1; exact onenezeroR1
      rw [if_neg]; rw[if_neg]; rw[if_pos]; simp; exact hy; exact hx;have : x = 1 := elem_nezero_then_oneR1 x hx; have hxy : x + y = 1 := by bound;
      rw [hxy.symm] at onenezeroR1; exact onenezeroR1
      rw [if_pos]; rw[if_neg]; rw[if_neg]; exact oneplusonezeroR2.symm; exact hy; exact hx; have : x = 1 := elem_nezero_then_oneR1 x hx; have : y = 1 := elem_nezero_then_oneR1 y hy; bound
    }
  have hfbij : Function.Bijective f := by
    constructor
    intro x y hxy
    by_cases hx : x = 0 <;> by_cases hy : y = 0
    rw[hx]; rw[hy]
    simp [f, hx, hy] at hxy
    simp [f, hx, hy] at hxy
    rw[elem_nezero_then_oneR1 x hx]
    rw[elem_nezero_then_oneR1 y hy]
    intro x
    by_cases hx : x = (0 : R2.1)
    use 0; bound
    have h : x = 1 := elem_nezero_then_oneR2 x hx
    use 1; bound
  let g : R1.1 ≃+* R2.1 := RingEquiv.ofBijective f hfbij
  exact (⟨{
    hom := RingCat.ofHom g.toRingHom
    inv := RingCat.ofHom g.symm.toRingHom
    hom_inv_id := by ext x; exact g.symm_apply_apply x
    inv_hom_id := by ext y; exact g.apply_symm_apply y
  }⟩)
  let R0 : RingOfOrder 2 := ⟨RingCat.of (ZMod 2), by rw [ENat.card_eq_coe_natCard]; norm_cast; exact Nat.card_zmod 2⟩
  exact ⟨Quotient.mk (FiniteRingSetoid 2) R0⟩


lemma RingsOfPrimeOrder : ∀ p : ℕ, Nat.Prime p → (R : RingOfOrder p) → Nonempty (R.1 ≅ RingCat.of (ZMod p)) := by
  intro p hp R
  have hcard : Nat.card R.1 = p := by
    have h := congr_arg ENat.toNat R.2
    simpa [Nat.card, ENat.card] using h
  letI : Fact p.Prime := ⟨hp⟩
  have RCyclic : IsAddCyclic R.1 := isAddCyclic_of_prime_card hcard
  have h1 : ZMod p ≃+ R.1 :=
    (ZMod.ringEquivCongr hcard.symm).toAddEquiv.trans (zmodAddCyclicAddEquiv RCyclic)
  haveI : Finite R.1 := Finite.of_equiv (ZMod p) h1.toEquiv
  letI : Nontrivial R.1 :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; exact hp.one_lt)
  let c : ZMod p := h1.symm 1
  have hc : c ≠ 0 := by
    intro h0
    have h01 : (0 : R.1) = 1 := by
      have := h1.apply_symm_apply 1
      simpa [c, h0] using this
    exact (zero_ne_one (α := R.1)) h01
  let mulC : ZMod p ≃+ ZMod p :=
    { Equiv.mulLeft₀ c hc with
      map_add' := mul_add c }
  let h1' : ZMod p ≃+ R.1 := mulC.trans h1
  have h1'_one : h1' 1 = 1 := by simp [h1', mulC, c]
  have h1'_nat : ∀ n : ℕ, h1' n = n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simp [ih, h1'_one]
  let e : ZMod p ≃+* R.1 :=
    { h1' with
      map_mul' := fun x y => by
        obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
        change h1' ((n : ZMod p) * y) = h1' (n : ZMod p) * h1' y
        rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]
        congr 1
        obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
        · simp [h1'_nat m]
        · simp [h1'_nat m] }
  exact ⟨{
    hom := RingCat.ofHom e.symm.toRingHom
    inv := RingCat.ofHom e.toRingHom
    hom_inv_id := by ext x; exact e.apply_symm_apply x
    inv_hom_id := by ext x; exact e.symm_apply_apply x
  }⟩
