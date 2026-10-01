import ModifiedCartan.KPCoefficientTableaux
import ModifiedCartan.KPCoefficientDegree
import ModifiedCartan.MinorTranslation

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

theorem kpBetaCoefficientPolynomial_translation {A : Type*} [Fintype A] [DecidableEq A]
    (μ : YoungDiagram) (z : A → ℂ) (g : Equiv.Perm A) (a t : ℂ) :
    (kpBetaCoefficientPolynomial μ z g).eval (a + t) =
      ∑ ν : Subpartition (partitionSquare (Fintype.card A)),
        (standardSkewTableauCount ν.val μ : ℂ) / ((partitionSize ν.val - partitionSize μ).factorial : ℂ) *
          t ^ (partitionSize ν.val - partitionSize μ) * (kpBetaCoefficientPolynomial ν.val z g).eval a := by
  rw [FewInflection.polynomial_eval_eq_jet_sum (kpBetaCoefficientPolynomial μ z g)
    (kpBetaCoefficientPolynomial_natDegree_le μ z g) a (a + t)]
  have ht : a + t - a = t := by ring
  simp_rw [ht, FewInflection.iteratedDeriv_polynomial_eval,
    iterate_derivative_kpBetaCoefficientPolynomial_eval, Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ν _
  by_cases hν : partitionSize ν.val ≤ Fintype.card A
  · by_cases hμν : μ ≤ ν.val
    · apply sum_taylor_degree_selector
      · exact partitionSize_mono hμν
      · omega
    · rw [standardSkewTableauCount_of_not_le hμν]
      simp
  · have hgt : Fintype.card A < partitionSize ν.val := by omega
    rw [kpBetaCoefficientPolynomial_of_size_gt ν.val z g hgt]
    simp

end
end ModifiedCartan


