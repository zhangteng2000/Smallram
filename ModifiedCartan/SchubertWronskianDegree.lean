import ModifiedCartan.MinorDerivativeSubpartitions
import ModifiedCartan.PartitionMinorDegree
import ModifiedCartan.PartitionTopMinor
import ModifiedCartan.TableauCountPositive

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

@[simp] theorem partitionSize_bot : partitionSize (⊥ : YoungDiagram) = 0 := by
  simp [partitionSize]

theorem iterate_derivative_wronskian_top {n : ℕ} {ω : YoungDiagram}
    (p : Fin (n + 1) → Polynomial ℂ) (hω : PartitionFits n ω)
    (hp : ∀ j, (p j).natDegree ≤ partitionMinorOrders n ω j) :
    Polynomial.derivative^[partitionSize ω] (FewInflection.polynomialWronskian p) =
      (standardSkewTableauCount ω ⊥ : Polynomial ℂ) * partitionPolynomialMinor ω p := by
  rw [← partitionPolynomialMinor_bot p,
    iterate_derivative_partitionPolynomialMinor_subpartitions p
      (by simp [PartitionFits]) hω hp]
  rw [Finset.sum_eq_single (⟨ω, le_rfl⟩ : Subpartition ω)]
  · simp only [partitionSize_bot, zero_add, ite_true]
  · intro ν _ hne
    have hs : partitionSize ν.val ≠ partitionSize ω := by
      intro hs
      apply hne
      apply Subtype.ext
      exact partition_eq_of_le_of_size_le ν.property hs.ge
    simp only [partitionSize_bot, zero_add, if_neg hs]
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem factorial_mul_wronskian_top_coeff {n : ℕ} {ω : YoungDiagram}
    (p : Fin (n + 1) → Polynomial ℂ) (hω : PartitionFits n ω)
    (hp : ∀ j, (p j).natDegree ≤ partitionMinorOrders n ω j) :
    ((partitionSize ω).factorial : ℂ) *
        (FewInflection.polynomialWronskian p).coeff (partitionSize ω) =
      (standardSkewTableauCount ω ⊥ : ℂ) * (partitionPolynomialMinor ω p).eval 0 := by
  rw [← FewInflection.iteratedDeriv_polynomial_eval_zero,
    FewInflection.iteratedDeriv_polynomial_eval, iterate_derivative_wronskian_top p hω hp,
    Polynomial.eval_mul, Polynomial.eval_natCast]

/-- The Wronskian degree is the size of the degree shape, including size zero. -/
theorem polynomialWronskian_natDegree_eq_partitionSize {n : ℕ} {ω : YoungDiagram}
    (p : Fin (n + 1) → Polynomial ℂ) (hω : PartitionFits n ω)
    (hp0 : ∀ j, p j ≠ 0) (hp : ∀ j, (p j).natDegree = partitionMinorOrders n ω j) :
    (FewInflection.polynomialWronskian p).natDegree = partitionSize ω := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · have hd := partitionPolynomialMinor_natDegree_le ⊥ ω p (fun j => (hp j).le)
    simpa only [partitionPolynomialMinor_bot, partitionSize_bot, Nat.sub_zero] using hd
  · have he := factorial_mul_wronskian_top_coeff p hω (fun j => (hp j).le)
    have hf : (standardSkewTableauCount ω ⊥ : ℂ) ≠ 0 := by
      exact_mod_cast (standardSkewTableauCount_pos bot_le hω).ne'
    have hz := mul_ne_zero hf (partitionPolynomialMinor_top_eval_ne_zero hω p hp0 hp 0)
    intro hc
    rw [hc, mul_zero] at he
    exact hz he.symm

end
end ModifiedCartan


