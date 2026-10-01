import ModifiedCartan.PolynomialNormCompactness
import ModifiedCartan.LogMeasureTransfer
import ModifiedCartan.ReplacementNormProperties

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- LaTeX `eq:polynomial-norm`: the exact Taylor polynomials in the
replacement construction have the same local L1 norm limit as its gauges. -/
theorem Paper.eq_polynomial_norm {n : ℕ} {f : Curve n}
    (hf0 : ∀ j, f.coord j 0 ≠ 0)
    {t s : ℕ → ℝ} {C A L : ℝ} {H : ℕ → ℂ → ℂ}
    {p : ℕ → Index n → Polynomial ℂ}
    {a : (ν : ℕ) → Fin (FewInflection.polynomialWronskian (p ν)).natDegree → ℂ}
    {η : ℕ → ℝ} (h : PolynomialReplacementData f t s C A L H p a η)
    (hC : 0 < C) (hA : 0 < A) (hL : 0 < L)
    (hspos : ∀ ν, 0 < s ν) (hs : Tendsto s atTop atTop) {u : ℂ → ℝ}
    (hg : LocalLpConvergence 1 (ball (0 : ℂ) 4)
      (fun ν z => (s ν)⁻¹ * Real.log (euclideanNorm
        (fun j => rescaledRepresentation f (t ν) (H ν) j z))) u)
    (hu : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 4), 0 ≤ u z) :
    LocalLpConvergence 1 (ball (0 : ℂ) 4)
      (fun ν z => (s ν)⁻¹ * Real.log (euclideanNorm (fun j => (p ν j).eval z))) u := by
  have hmeasure : LocalMeasureConvergence (ball (0 : ℂ) 4)
      (fun ν z => Real.log (euclideanNorm (fun j => (p ν j).eval z)) / s ν) u := by
    apply localMeasure_log_transfer_of_exponential_close isOpen_ball hA hs
      (fun ν z _ => rescaledRepresentation_norm_pos f (t ν) (H ν) z) _ _ hu h.norm_error
    · intro K hK _ ν
      have hv : ContinuousOn (fun z => (fun j => (p ν j).eval z)) K :=
        continuousOn_pi.mpr (fun j =>
          ((AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (p ν j)).continuousOn.mono (subset_univ _)))
      exact (euclideanNorm_continuous.comp_continuousOn hv).aestronglyMeasurable hK.measurableSet
    · simpa only [div_eq_mul_inv, mul_comm] using hg.inMeasure (by norm_num)
  apply polynomial_norm_localL1_of_measure hspos hs
  · intro ν j
    rw [h.taylor_center hL hspos]
    simpa only [rescaledRepresentation, mul_zero] using
      mul_ne_zero (Complex.exp_ne_zero (-(H ν 0))) (hf0 j)
  · exact h.polynomial_coordinate_bound hC hA hs
  · intro j
    simpa only [h.taylor_center hL hspos] using h.coordinate_centers j
  · simpa only [div_eq_mul_inv, mul_comm] using hmeasure

end ModifiedCartan
#print axioms ModifiedCartan.Paper.eq_polynomial_norm
