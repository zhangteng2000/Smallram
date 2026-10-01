import ModifiedCartan.PartitionBoxes
import ModifiedCartan.PolynomialMinors

open scoped BigOperators Classical

namespace ModifiedCartan

noncomputable section

theorem partitionMinorOrders_addPartitionBox {n : ℕ} (μ : YoungDiagram)
    (i : Fin (n + 1)) (h : AddablePartitionRow μ (n - (i : ℕ))) :
    partitionMinorOrders n (addPartitionBox μ (n - (i : ℕ)) h) =
      raiseMinorOrder (partitionMinorOrders n μ) i := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [partitionMinorOrders, rowLen_addPartitionBox, add_assoc]
  · have hne : n - (j : ℕ) ≠ n - (i : ℕ) := by
      intro heq
      apply hji
      apply Fin.ext
      have hi := i.isLt
      have hj := j.isLt
      omega
    simp [partitionMinorOrders, rowLen_addPartitionBox, hne, hji]

theorem partitionMinorOrders_collision_of_not_addable {n : ℕ}
    (μ : YoungDiagram) (i : Fin (n + 1))
    (h : ¬ AddablePartitionRow μ (n - (i : ℕ))) :
    ∃ j : Fin (n + 1), i ≠ j ∧
      partitionMinorOrders n μ i + 1 = partitionMinorOrders n μ j := by
  have hne : n - (i : ℕ) ≠ 0 := fun hz => h (Or.inl hz)
  have hnot : ¬ μ.rowLen (n - (i : ℕ)) < μ.rowLen (n - (i : ℕ) - 1) :=
    fun hlt => h (Or.inr hlt)
  have hle := μ.rowLen_anti (n - (i : ℕ) - 1) (n - (i : ℕ)) (by omega)
  let j : Fin (n + 1) := ⟨(i : ℕ) + 1, by omega⟩
  refine ⟨j, ?_, ?_⟩
  · intro hij
    have heq := congrArg Fin.val hij
    dsimp [j] at heq
    omega
  · dsimp [partitionMinorOrders, j]
    have hsub : n - ((i : ℕ) + 1) = n - (i : ℕ) - 1 := by omega
    rw [hsub]
    omega

/-- LaTeX `eq:derivative-minor`, with zero coordinates for excess rows. -/
def partitionPolynomialMinor {n : ℕ} (μ : YoungDiagram)
    (p : Fin (n + 1) → Polynomial ℂ) : Polynomial ℂ := by
  classical
  exact if PartitionFits n μ then polynomialDerivativeMinor (partitionMinorOrders n μ) p else 0

theorem partitionPolynomialMinor_of_fits {n : ℕ} {μ : YoungDiagram}
    (h : PartitionFits n μ) (p : Fin (n + 1) → Polynomial ℂ) :
    partitionPolynomialMinor μ p = polynomialDerivativeMinor (partitionMinorOrders n μ) p := by
  classical
  simp [partitionPolynomialMinor, h]

theorem partitionPolynomialMinor_of_not_fits {n : ℕ} {μ : YoungDiagram}
    (h : ¬ PartitionFits n μ) (p : Fin (n + 1) → Polynomial ℂ) :
    partitionPolynomialMinor μ p = 0 := by
  classical
  simp [partitionPolynomialMinor, h]

@[simp] theorem partitionPolynomialMinor_bot {n : ℕ}
    (p : Fin (n + 1) → Polynomial ℂ) :
    partitionPolynomialMinor ⊥ p = FewInflection.polynomialWronskian p := by
  rw [partitionPolynomialMinor_of_fits (by simp [PartitionFits]),
    partitionMinorOrders_bot, polynomialDerivativeMinor_wronskian]

/-- The derivative is the sum over exactly the legal single-box additions. -/
theorem derivative_partitionPolynomialMinor {n : ℕ} (μ : YoungDiagram)
    (p : Fin (n + 1) → Polynomial ℂ) (hμ : PartitionFits n μ) :
    (partitionPolynomialMinor μ p).derivative =
      ∑ i : Fin (n + 1), if h : AddablePartitionRow μ (n - (i : ℕ)) then
        partitionPolynomialMinor (addPartitionBox μ (n - (i : ℕ)) h) p else 0 := by
  classical
  rw [partitionPolynomialMinor_of_fits hμ, derivative_polynomialDerivativeMinor]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with hi
  · rw [partitionPolynomialMinor_of_fits
      (hμ.addPartitionBox (by omega) hi), partitionMinorOrders_addPartitionBox]
  · obtain ⟨j, hij, hord⟩ := partitionMinorOrders_collision_of_not_addable μ i hi
    exact polynomialDerivativeMinor_raised_eq_zero_of_collision _ p hij hord

end
end ModifiedCartan



