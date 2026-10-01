import ModifiedCartan.SpechtRestrictionPairing

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem specht_fixedPoint_pairing (μ ν : YoungDiagram)
    (hμ : Fintype.card A = partitionSize μ + 1) (hν : Fintype.card A = partitionSize ν) (a : A) :
    (∑ g : Equiv.Perm A, if hg : g a = a then
      spechtCharacterOn μ (card_erase_of_successor_size μ hμ a) (deleteFixedPoint a g hg)⁻¹ *
        spechtCharacterOn ν hν g else 0) =
      (Nat.card (Equiv.Perm (↥(Finset.univ.erase a))) : ℂ) *
        (if PartitionCovers ν μ then 1 else 0) := by
  rw [sum_fixedPointPermutations]
  have hd (p : Equiv.Perm (↥(Finset.univ.erase a))) :
      deleteFixedPoint a (fixedPointPermutationEquiv a p).val
        (fixedPointPermutationEquiv a p).property = p :=
    (fixedPointPermutationEquiv a).symm_apply_apply p
  simp only [hd]
  have hH : (Nat.card (Equiv.Perm (↥(Finset.univ.erase a))) : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero (α := Equiv.Perm (↥(Finset.univ.erase a)))
  have hp := congrArg (fun c : ℂ => (Nat.card (Equiv.Perm (↥(Finset.univ.erase a))) : ℂ) * c)
    (specht_restriction_pairing μ ν hμ hν a)
  simpa only [← mul_assoc, mul_inv_cancel₀ hH, one_mul] using hp

/-- The exact coefficient of every larger Specht character in one-letter
induction, calculated by fixed-letter summation and proved restriction branching. -/
theorem inducedSpechtCharacter_pairing (μ ν : YoungDiagram)
    (hμ : Fintype.card A = partitionSize μ + 1) (hν : Fintype.card A = partitionSize ν) :
    (Nat.card (Equiv.Perm A) : ℂ)⁻¹ * ∑ g : Equiv.Perm A,
      inducedSpechtCharacter μ hμ g⁻¹ * spechtCharacterOn ν hν g =
      if PartitionCovers ν μ then 1 else 0 := by
  simp_rw [inducedSpechtCharacter_inv, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hp (a : A) :
      (∑ g : Equiv.Perm A,
        (if hg : g a = a then spechtCharacterOn μ (card_erase_of_successor_size μ hμ a)
          (deleteFixedPoint a g hg)⁻¹ else 0) * spechtCharacterOn ν hν g) =
        ((partitionSize μ).factorial : ℂ) * (if PartitionCovers ν μ then 1 else 0) := by
    have h := specht_fixedPoint_pairing μ ν hμ hν a
    have hc : Nat.card (Equiv.Perm (↥(Finset.univ.erase a))) = (partitionSize μ).factorial := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, card_erase_of_successor_size μ hμ a]
    rw [hc] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro g _
    by_cases hg : g a = a <;> simp only [hg, dite_true, dite_false, zero_mul]
  simp only [hp, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hcG : Nat.card (Equiv.Perm A) = (partitionSize μ + 1) * (partitionSize μ).factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, hμ, Nat.factorial_succ]
  have hn : ((partitionSize μ + 1) * (partitionSize μ).factorial : ℕ) ≠ 0 := by positivity
  have hnc : (((partitionSize μ + 1) * (partitionSize μ).factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn
  have hfac : ((partitionSize μ).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (partitionSize μ)
  rw [hcG, hμ]
  push_cast
  field_simp

end
end ModifiedCartan


