import ModifiedCartan.MinorTranslation
import ModifiedCartan.PartitionTopMinor
import ModifiedCartan.TableauCountPositive

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- LaTeX `eq:normalized-Plucker-coordinates`, including its precise scalar. -/
def normalizedPartitionMinor {n : ℕ} (ω : YoungDiagram)
    (p : Fin (n + 1) → Polynomial ℂ) (μ : YoungDiagram) (a : ℂ) : ℂ :=
  (partitionSize ω).factorial / (standardSkewTableauCount ω ⊥ : ℂ) *
    (partitionPolynomialMinor μ p).eval a / (partitionPolynomialMinor ω p).eval a

theorem partitionPolynomialMinor_top_eval_eq {n : ℕ} {ω : YoungDiagram}
    (p : Fin (n + 1) → Polynomial ℂ) (hω : PartitionFits n ω)
    (hp : ∀ j, (p j).natDegree ≤ partitionMinorOrders n ω j) (a b : ℂ) :
    (partitionPolynomialMinor ω p).eval a = (partitionPolynomialMinor ω p).eval b := by
  rw [partitionPolynomialMinor_top_eq_C hω p hp]
  simp only [Polynomial.eval_C]

theorem normalizedPartitionMinor_top {n : ℕ} {ω : YoungDiagram}
    (p : Fin (n + 1) → Polynomial ℂ) (hω : PartitionFits n ω)
    (hp0 : ∀ j, p j ≠ 0) (hp : ∀ j, (p j).natDegree = partitionMinorOrders n ω j) (a : ℂ) :
    normalizedPartitionMinor ω p ω a =
      (partitionSize ω).factorial / (standardSkewTableauCount ω ⊥ : ℂ) := by
  unfold normalizedPartitionMinor
  exact mul_div_cancel_right₀ _ (partitionPolynomialMinor_top_eval_ne_zero hω p hp0 hp a)

theorem normalizedPartitionMinor_eq_zero_of_not_le {n : ℕ} {ω : YoungDiagram}
    (p : Fin (n + 1) → Polynomial ℂ)
    (hp : ∀ j, (p j).natDegree ≤ partitionMinorOrders n ω j)
    (μ : YoungDiagram) (h : ¬ μ ≤ ω) (a : ℂ) : normalizedPartitionMinor ω p μ a = 0 := by
  rw [normalizedPartitionMinor, partitionPolynomialMinor_eq_zero_of_not_le μ ω p hp h]
  simp

/-- Normalized finite translation; no spectral correspondence is used. -/
theorem normalizedPartitionMinor_translation {n : ℕ} {ω : YoungDiagram}
    (μ : YoungDiagram) (p : Fin (n + 1) → Polynomial ℂ) (hω : PartitionFits n ω)
    (hp : ∀ j, (p j).natDegree ≤ partitionMinorOrders n ω j) (a t : ℂ) :
    normalizedPartitionMinor ω p μ (a + t) =
      ∑ ν : Subpartition ω,
        (standardSkewTableauCount ν.val μ : ℂ) /
          ((partitionSize ν.val - partitionSize μ).factorial : ℂ) *
        t ^ (partitionSize ν.val - partitionSize μ) * normalizedPartitionMinor ω p ν.val a := by
  unfold normalizedPartitionMinor
  rw [partitionPolynomialMinor_top_eval_eq p hω hp (a + t) a,
    partitionPolynomialMinor_translation μ p hω hp a t,
    Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ν _
  ring

end
end ModifiedCartan


