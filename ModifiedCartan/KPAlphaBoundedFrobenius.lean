import ModifiedCartan.KPAlphaFrobeniusCoefficients
import ModifiedCartan.SizedPartitionsInSquare

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem supportedCycleSum_bounded_frobenius_coeff {A B : Type*} [Fintype A] [Fintype B]
    (X : Finset A) (θ : Equiv.Perm A) :
    (supportedCycleSum B X).coeff θ =
      ∑ μ : Subpartition (partitionSquare (Fintype.card A)),
        MvPolynomial.C ((kpAlpha μ.val X).coeff θ) * finiteFrobeniusPolynomial B μ.val := by
  have hX : Fintype.card X ≤ Fintype.card A := by
    rw [Fintype.card_coe]
    exact Finset.card_le_univ X
  rw [supportedCycleSum_frobenius_coeff,
    sum_sizedYoungDiagram_in_square (Fintype.card A) (Fintype.card X) hX
      (fun μ => MvPolynomial.C ((kpAlpha μ X).coeff θ) * finiteFrobeniusPolynomial B μ)]
  apply Finset.sum_congr rfl
  intro μ hμ
  by_cases hs : partitionSize μ.val = Fintype.card X
  · rw [ite_eq_left hs]
  · rw [ite_eq_right hs]
    have hn : X.card ≠ partitionSize μ.val := by
      intro he
      apply hs
      rw [Fintype.card_coe]
      exact he.symm
    rw [kpAlpha_of_card_ne μ.val X hn]
    simp

end
end ModifiedCartan

