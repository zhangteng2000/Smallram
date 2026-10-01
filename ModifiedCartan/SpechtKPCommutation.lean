import ModifiedCartan.KPCurveMatrix
import ModifiedCartan.KPBetaDeformedCommutation
import ModifiedCartan.PolynomialInverseContinuation

open scoped Classical

namespace ModifiedCartan
noncomputable section

/-- The polynomial continuation proves beta-beta commutativity in each actual
Specht representation for all parameters, including repeated parameters. -/
theorem specht_kpBeta_commute {N : ℕ} (τ : YoungDiagram)
    (h : Fintype.card (Fin N) = partitionSize τ) (z : Fin N → ℂ)
    (μ ν : YoungDiagram) (a b : ℂ) :
    Commute ((spechtRepresentationOn τ h).asAlgebraHom (kpBeta μ z a))
      ((spechtRepresentationOn τ h).asAlgebraHom (kpBeta ν z b)) := by
  let B := youngStandardPolytabloidBasis τ
  have hzero (r c : StandardYoungTableau τ) :
      kpCurveCommutatorPolynomial B (spechtRepresentationOn τ h) μ ν z a b r c = 0 := by
    apply polynomial_eq_zero_of_eventually_inverse_eval_zero
    filter_upwards [specht_kpBeta_deformed_eventually_commute τ h z μ ν a b] with t ht
    intro hne
    rw [kpCurveCommutatorPolynomial_eval, kpPolynomialParameters_inv]
    have hz := sub_eq_zero.mpr (ht hne).eq
    have hh := congrArg (fun T : Module.End ℂ (YoungSpechtModule τ) =>
      LinearMap.toMatrixAlgEquiv B T r c) hz
    simpa only [map_zero, Matrix.zero_apply] using hh
  change _ = _
  apply sub_eq_zero.mp
  apply (LinearMap.toMatrixAlgEquiv B).injective
  ext r c
  have he := congrArg (Polynomial.eval (0 : ℂ)) (hzero r c)
  rw [kpCurveCommutatorPolynomial_eval, kpPolynomialParameters_zero, Polynomial.eval_zero] at he
  simpa only [map_zero, Matrix.zero_apply] using he

end
end ModifiedCartan


