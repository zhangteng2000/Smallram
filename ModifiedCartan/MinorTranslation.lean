import ModifiedCartan.MinorDerivativeSubpartitions
import ModifiedCartan.PartitionMinorDegree

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem iterate_derivative_partitionPolynomialMinor_eval_subpartitions
    {n : ℕ} {μ ω : YoungDiagram} (p : Fin (n + 1) → Polynomial ℂ)
    (hμ : PartitionFits n μ) (hω : PartitionFits n ω)
    (hp : ∀ j, (p j).natDegree ≤ partitionMinorOrders n ω j) (k : ℕ) (a : ℂ) :
    (Polynomial.derivative^[k] (partitionPolynomialMinor μ p)).eval a =
      ∑ ν : Subpartition ω,
        if partitionSize ν.val = partitionSize μ + k then
          (standardSkewTableauCount ν.val μ : ℂ) * (partitionPolynomialMinor ν.val p).eval a
        else 0 := by
  rw [iterate_derivative_partitionPolynomialMinor_subpartitions p hμ hω hp k,
    Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro ν _
  split_ifs <;> simp

theorem sum_taylor_degree_selector (d m N : ℕ) (hm : m ≤ N) (hd : N - m ≤ d)
    (c q t : ℂ) :
    (∑ k ∈ Finset.range (d + 1), (if N = m + k then c * q else 0) /
      (k.factorial : ℂ) * t ^ k) =
      c / ((N - m).factorial : ℂ) * t ^ (N - m) * q := by
  rw [Finset.sum_eq_single_of_mem (N - m) (Finset.mem_range.mpr (by omega))]
  · rw [if_pos (by omega : N = m + (N - m))]
    ring
  · intro k _ hne
    have hk : N ≠ m + k := by omega
    simp [hk]

/-- Unnormalized form of LaTeX `eq:Plucker-translation`. -/
theorem partitionPolynomialMinor_translation_of_fits {n : ℕ} {μ ω : YoungDiagram}
    (p : Fin (n + 1) → Polynomial ℂ) (hμ : PartitionFits n μ) (hω : PartitionFits n ω)
    (hp : ∀ j, (p j).natDegree ≤ partitionMinorOrders n ω j) (a t : ℂ) :
    (partitionPolynomialMinor μ p).eval (a + t) =
      ∑ ν : Subpartition ω,
        (standardSkewTableauCount ν.val μ : ℂ) /
          ((partitionSize ν.val - partitionSize μ).factorial : ℂ) *
        t ^ (partitionSize ν.val - partitionSize μ) * (partitionPolynomialMinor ν.val p).eval a := by
  rw [FewInflection.polynomial_eval_eq_jet_sum (partitionPolynomialMinor μ p)
    (partitionPolynomialMinor_natDegree_le μ ω p hp) a (a + t)]
  have ht : a + t - a = t := by ring
  simp_rw [ht, FewInflection.iteratedDeriv_polynomial_eval,
    iterate_derivative_partitionPolynomialMinor_eval_subpartitions p hμ hω hp,
    Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ν _
  by_cases hμν : μ ≤ ν.val
  · apply sum_taylor_degree_selector
    · exact partitionSize_mono hμν
    · have := partitionSize_mono ν.property
      omega
  · rw [standardSkewTableauCount_of_not_le hμν]
    simp

/-- The translation identity also covers partitions having too many rows. -/
theorem partitionPolynomialMinor_translation {n : ℕ} {ω : YoungDiagram}
    (μ : YoungDiagram) (p : Fin (n + 1) → Polynomial ℂ) (hω : PartitionFits n ω)
    (hp : ∀ j, (p j).natDegree ≤ partitionMinorOrders n ω j) (a t : ℂ) :
    (partitionPolynomialMinor μ p).eval (a + t) =
      ∑ ν : Subpartition ω,
        (standardSkewTableauCount ν.val μ : ℂ) /
          ((partitionSize ν.val - partitionSize μ).factorial : ℂ) *
        t ^ (partitionSize ν.val - partitionSize μ) * (partitionPolynomialMinor ν.val p).eval a := by
  by_cases hμ : PartitionFits n μ
  · exact partitionPolynomialMinor_translation_of_fits p hμ hω hp a t
  · rw [partitionPolynomialMinor_of_not_fits hμ p, Polynomial.eval_zero]
    symm
    apply Finset.sum_eq_zero
    intro ν _
    have hnot : ¬ μ ≤ ν.val := fun h => hμ (hω.of_le (h.trans ν.property))
    rw [standardSkewTableauCount_of_not_le hnot]
    simp

end
end ModifiedCartan


