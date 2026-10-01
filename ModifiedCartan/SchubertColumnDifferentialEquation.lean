import ModifiedCartan.ColumnMinorDifferentialEquation
import ModifiedCartan.SchubertCoordinates
import ModifiedCartan.KPJointCoefficientSpace

namespace ModifiedCartan
noncomputable section
open scoped Classical BigOperators

/-- Normalized Schubert-coordinate polynomials give an actual polynomial
    differential equation on every basis vector, including at Wronskian zeros.
    Auxiliary to manuscript `lem:KP-correspondence`. -/
theorem schubert_columnValues_differential_identity {n D : ℕ} {τ : YoungDiagram}
    {V : Submodule ℂ (Polynomial ℂ)} (hV : V ∈ polynomialSchubertCell n D τ)
    (b : Module.Basis (Fin (n + 1)) ℂ V) (f : YoungDiagram → Polynomial ℂ)
    (hf : ∀ μ a, (f μ).eval a = normalizedSchubertCoordinate hV μ a)
    (j : Fin (n + 1)) :
    (∑ i : Fin (n + 2),
      Polynomial.C ((-1 : ℂ) ^ (n + 1 - i.val)) *
        f (columnPartition (n + 1 - i.val)) *
          Polynomial.derivative^[i.val] (b j).val) = 0 := by
  apply Polynomial.funext
  intro a
  let p : Fin (n + 1) → Polynomial ℂ := fun l => (b l).val
  let s : ℂ := ((partitionSize τ).factorial : ℂ) /
    (standardSkewTableauCount τ ⊥ : ℂ) / (partitionPolynomialMinor τ p).eval a
  have hc (μ : YoungDiagram) : (f μ).eval a =
      s * (partitionPolynomialMinor μ p).eval a := by
    rw [hf, normalizedSchubertCoordinate_eq_basis hV b, normalizedPartitionMinor]
    dsimp only [s, p]
    ring
  have hp := congrArg (fun q : Polynomial ℂ => q.eval a)
    (polynomial_columnMinor_differential_identity p j)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_finsetSum,
    Polynomial.eval_C, Polynomial.eval_zero] at hp
  rw [Fin.sum_univ_castSucc]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_finsetSum,
    Polynomial.eval_C, Polynomial.eval_zero, Fin.val_castSucc, Fin.val_last,
    Nat.sub_self, pow_zero, one_mul, hc, columnPartition_zero_eq_bot,
    partitionPolynomialMinor_bot]
  change (∑ i : Fin (n + 1), ((-1 : ℂ) ^ (n + 1 - i.val) *
      (s * (partitionPolynomialMinor (columnPartition (n + 1 - i.val)) p).eval a)) *
        (Polynomial.derivative^[i.val] (p j)).eval a) +
      (s * (FewInflection.polynomialWronskian p).eval a) *
        (Polynomial.derivative^[n + 1] (p j)).eval a = 0
  calc
    _ = (∑ i : Fin (n + 1), s * (((-1 : ℂ) ^ (n + 1 - i.val) *
        (partitionPolynomialMinor (columnPartition (n + 1 - i.val)) p).eval a) *
          (Polynomial.derivative^[i.val] (p j)).eval a)) +
        s * ((FewInflection.polynomialWronskian p).eval a *
          (Polynomial.derivative^[n + 1] (p j)).eval a) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        ring
      · ring
    _ = s * ((FewInflection.polynomialWronskian p).eval a *
        (Polynomial.derivative^[n + 1] (p j)).eval a +
          ∑ i : Fin (n + 1), ((-1 : ℂ) ^ (n + 1 - i.val) *
            (partitionPolynomialMinor (columnPartition (n + 1 - i.val)) p).eval a) *
              (Polynomial.derivative^[i.val] (p j)).eval a) := by
      rw [mul_add, Finset.mul_sum]
      ring
    _ = 0 := by rw [hp, mul_zero]

end
end ModifiedCartan

#print axioms ModifiedCartan.schubert_columnValues_differential_identity
