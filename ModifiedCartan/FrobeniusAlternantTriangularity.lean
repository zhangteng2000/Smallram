import ModifiedCartan.FiniteAlternants
import ModifiedCartan.FrobeniusMinimalVanishing

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- All nonidentity alternant terms vanish at or below the row weight.
    Auxiliary to the character/Schur bridge for paper `lem:KP-correspondence`. -/
theorem finiteVandermondeFrobenius_coeff_eq_of_weight_le {m : ℕ}
    (μ : YoungDiagram) (d : Fin m →₀ ℕ) (hd : finiteColorWeight d ≤ partitionRowWeight μ) :
    MvPolynomial.coeff (d + finiteStaircaseDegree m)
      (finiteVandermondeAlternant m * finiteFrobeniusPolynomial (Fin m) μ) =
        MvPolynomial.coeff d (finiteFrobeniusPolynomial (Fin m) μ) := by
  rw [finiteVandermondeAlternant_coeff_mul, Finset.sum_eq_single 1]
  · have hs : finiteStaircaseDegree m ≤ d + finiteStaircaseDegree m :=
      le_add_left le_rfl
    simp [hs]
  · intro σ _ hσ
    by_cases hs : finitePermutedStaircaseDegree σ ≤ d + finiteStaircaseDegree m
    · rw [if_pos hs, finiteFrobeniusPolynomial_coeff_zero_of_weight_lt μ _
        ((staircase_sub_weight_lt d σ hσ hs).trans_le hd), mul_zero]
    · rw [if_neg hs]
  · simp

theorem finiteVandermondeFrobenius_coeff_zero_of_le_ne {m : ℕ}
    (μ ν : YoungDiagram) (hν : ν.colLen 0 ≤ m)
    (hw : partitionRowWeight ν ≤ partitionRowWeight μ) (hne : ν ≠ μ) :
    MvPolynomial.coeff (partitionFiniteDegree m ν + finiteStaircaseDegree m)
      (finiteVandermondeAlternant m * finiteFrobeniusPolynomial (Fin m) μ) = 0 := by
  have hd : finiteColorWeight (partitionFiniteDegree m ν) ≤ partitionRowWeight μ := by
    rw [finiteColorWeight_partitionFiniteDegree ν hν]
    exact hw
  rw [finiteVandermondeFrobenius_coeff_eq_of_weight_le μ _ hd]
  apply finiteFrobeniusPolynomial_coeff_zero_of_weight_le_ne μ _ hd
  rw [partitionFiniteDegree_mapDomain ν hν]
  exact fun he => hne (partitionRowDegree_injective he)

theorem finiteVandermondeFrobenius_diagonal_nat {m : ℕ}
    (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ m) :
    ∃ k : ℕ, MvPolynomial.coeff (partitionFiniteDegree m μ + finiteStaircaseDegree m)
      (finiteVandermondeAlternant m * finiteFrobeniusPolynomial (Fin m) μ) = (k : ℂ) := by
  rw [finiteVandermondeFrobenius_coeff_eq_of_weight_le μ _
    (by rw [finiteColorWeight_partitionFiniteDegree μ hμ])]
  exact finiteFrobeniusPolynomial_coeff_nat μ _

end
end ModifiedCartan

#print axioms ModifiedCartan.finiteVandermondeFrobenius_coeff_zero_of_le_ne
#print axioms ModifiedCartan.finiteVandermondeFrobenius_diagonal_nat
