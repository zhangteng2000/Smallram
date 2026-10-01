import ModifiedCartan.PolynomialValueSpan
import ModifiedCartan.BetheAlgebra
import ModifiedCartan.KPJointWronskian

open scoped Classical BigOperators MonoidAlgebra

namespace ModifiedCartan
noncomputable section

theorem polynomialCombination_linear_coeff {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℂ V] (w : ι → Polynomial ℂ) (v : ι → V)
    (L : V →ₗ[ℂ] ℂ) (p : Polynomial ℂ)
    (h : ∀ a : ℂ, L (∑ i, (w i).eval a • v i) = p.eval a) (k : ℕ) :
    L (∑ i, (w i).coeff k • v i) = p.coeff k := by
  have hp : (∑ i, Polynomial.C (L (v i)) * w i) = p := by
    apply Polynomial.funext
    intro a
    have hh := h a
    simpa only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      map_sum, map_smul, smul_eq_mul, mul_comm] using hh
  have hh := congrArg (fun q : Polynomial ℂ => q.coeff k) hp
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul] at hh
  simpa only [map_sum, map_smul, smul_eq_mul, mul_comm] using hh

theorem polynomialCombination_coeff_eq_smul {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℂ V] (w : ι → Polynomial ℂ) (v : ι → V)
    (p : Polynomial ℂ) (u : V)
    (h : ∀ a : ℂ, (∑ i, (w i).eval a • v i) = p.eval a • u) (k : ℕ) :
    (∑ i, (w i).coeff k • v i) = p.coeff k • u := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro L
  rw [map_sub, map_smul, smul_eq_mul]
  apply sub_eq_zero.mpr
  have hh := polynomialCombination_linear_coeff w v L (Polynomial.C (L u) * p)
    (fun a => by
      rw [h, map_smul, Polynomial.eval_mul, Polynomial.eval_C]
      exact mul_comm _ _) k
  rw [Polynomial.coeff_C_mul] at hh
  exact hh.trans (mul_comm _ _)

/-- The eigenvector identity holds for each polynomial coefficient of beta. -/
theorem kpBetaPowerCoefficient_action {A : Type*} [Fintype A] [DecidableEq A]
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (v : YoungSpechtModule τ)
    (hv : v ∈ kpJointEigenspace τ hτ z χ) (μ : YoungDiagram) (k : ℕ) :
    (spechtRepresentationOn τ hτ).asAlgebraHom (kpBetaPowerCoefficient μ z k) v =
      (kpJointValuePolynomial (Fintype.card A) χ μ).coeff k • v := by
  let ρ := (spechtRepresentationOn τ hτ).asAlgebraHom
  have he (a : ℂ) :
      (∑ I : SizedLetterSubset A (partitionSize μ),
        (kpWeightPolynomial z I.val).eval a • ρ (kpAlpha μ I.val) v) =
      (kpJointValuePolynomial (Fintype.card A) χ μ).eval a • v := by
    have hh := kpJointValuePolynomial_action τ hτ z χ v hv μ a
    rw [kpBeta_eq_polynomialCombination, map_sum, LinearMap.sum_apply] at hh
    simpa only [map_smul, LinearMap.smul_apply] using hh
  have hh := polynomialCombination_coeff_eq_smul
    (fun I : SizedLetterSubset A (partitionSize μ) => kpWeightPolynomial z I.val)
    (fun I => ρ (kpAlpha μ I.val) v) _ v he k
  simpa only [kpBetaPowerCoefficient, map_sum, LinearMap.sum_apply,
    map_smul, LinearMap.smul_apply] using hh

end
end ModifiedCartan

#print axioms ModifiedCartan.kpBetaPowerCoefficient_action
