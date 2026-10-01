import ModifiedCartan.LocalL1Max
import ModifiedCartan.LocalL1SmallError
import ModifiedCartan.NormalizedNormMax
import ModifiedCartan.AnalyticLogSubharmonic

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- LaTeX `eq:norm-limit`, the convergence of the actual Euclidean
logarithm to the finite maximum of the coordinate logarithm limits. -/
theorem normalized_euclidean_log_localL1_limit {n : ℕ} {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    {f : ℕ → Index n → ℂ → ℂ} {s : ℕ → ℝ} {u : Index n → ℂ → ℝ}
    (hf : ∀ ν j, AnalyticOnNhd ℂ (f ν j) U)
    (hnz : ∀ ν j, ∃ z ∈ U, f ν j z ≠ 0)
    (hspos : ∀ ν, 0 < s ν) (hs : Tendsto s atTop atTop)
    (hlim : ∀ j, LocalLpConvergence 1 U
      (fun ν z => (s ν)⁻¹ * Real.log ‖f ν j z‖) (u j)) :
    LocalLpConvergence 1 U
      (fun ν z => (s ν)⁻¹ * Real.log (euclideanNorm (fun j => f ν j z)))
      (fun z => Finset.univ.sup' Finset.univ_nonempty (fun j => u j z)) := by
  have hm := localLpConvergence_finset_sup' Finset.univ Finset.univ_nonempty (fun j _ => hlim j)
  apply hm.of_ae_uniform_error (δ := fun ν => (s ν)⁻¹ * Real.log (Real.sqrt (n + 1)))
  · intro K hK hKU ν
    have hv : ContinuousOn (fun z => (fun j => f ν j z)) K :=
      continuousOn_pi.mpr (fun j => (hf ν j).continuousOn.mono hKU)
    have hnorm := euclideanNorm_continuous.comp_continuousOn hv
    exact aestronglyMeasurable_const.mul
      ((hnorm.aestronglyMeasurable hK.measurableSet).aemeasurable.log.aestronglyMeasurable)
  · simpa only [Function.comp_def, zero_mul] using
      (tendsto_inv_atTop_zero.comp hs).mul_const (Real.log (Real.sqrt (n + 1)))
  · intro ν
    filter_upwards [ae_all_iff.mpr (fun j => analytic_ae_ne_zero hU hUc (hf ν j) (hnz ν j))]
      with z hz
    exact normalized_log_euclideanNorm_sub_max_bound (fun j => f ν j z) (hspos ν) hz

end ModifiedCartan
#print axioms ModifiedCartan.normalized_euclidean_log_localL1_limit
