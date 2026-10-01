import ModifiedCartan.Homogeneity
import ModifiedCartan.DiskMeanLimits

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem LocalLpConvergence.integral_ball_tendsto {U : Set ℂ}
    {F : ℕ → ℂ → ℝ} {v : ℂ → ℝ} (h : LocalLpConvergence 1 U F v)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hball : closedBall c R ⊆ U) :
    Tendsto (fun ν => ∫ z in ball c R, F ν z) atTop (𝓝 (∫ z in ball c R, v z)) := by
  have he (w : ℂ → ℝ) : (Real.pi * R ^ 2) * diskAverage R w c = ∫ z in ball c R, w z := by
    rw [diskAverage_eq hR.le, ← mul_assoc, mul_inv_cancel₀
      (mul_ne_zero Real.pi_ne_zero (pow_ne_zero 2 hR.ne')), one_mul]
  have hfun : (fun ν => ∫ z in ball c R, F ν z) =
      (fun ν => (Real.pi * R ^ 2) * diskAverage R (F ν) c) := funext (fun ν => (he (F ν)).symm)
  rw [hfun, ← he v]
  exact (h.diskAverage_tendsto hR hball).const_mul (Real.pi * R ^ 2)

/-- The same normalized norm logarithm as in `eq:norm-limit`. -/
noncomputable def ArbitraryRadiusLimitData.normLog
    {n : ℕ} {f : Curve n} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (ν : ℕ) (z : ℂ) : ℝ :=
  (characteristic f (r (d.subseq ν)))⁻¹ * Real.log (euclideanNorm
    (fun j => rescaledRepresentation f (r (d.subseq ν)) (d.gauge ν) j z))

theorem ArbitraryRadiusLimitData.normLog_localLp
    {n : ℕ} {f : Curve n} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ) :
    LocalLpConvergence 1 (ball (0 : ℂ) 4) d.normLog (fun z => (d.U z).toReal) := by
  apply d.norm_limit.congr_ae (fun _ => EventuallyEq.rfl)
  filter_upwards [d.representative] with z hz
  rw [hz, EReal.toReal_coe]

theorem ArbitraryRadiusLimitData.normLog_continuous
    {n : ℕ} {f : Curve n} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ) :
    ∀ᶠ ν in atTop, ContinuousOn (d.normLog ν) (ball (0 : ℂ) 64) := by
  filter_upwards [d.replacement.gauge_analytic] with ν hH
  have hc : ContinuousOn
      (fun z => Real.log (euclideanNorm (fun j =>
        rescaledRepresentation f (r (d.subseq ν)) (d.gauge ν) j z))) (ball (0 : ℂ) 64) := by
    simpa only [rescaledRepresentation_log_norm, Function.comp_def, Pi.mul_apply, Pi.sub_apply, id_eq] using!
      ((curve_log_euclideanNorm_continuous f).comp (continuous_const.mul continuous_id)).continuousOn.sub
        (Complex.continuous_re.comp_continuousOn hH.continuousOn)
  exact continuousOn_const.mul hc

end ModifiedCartan
#print axioms ModifiedCartan.LocalLpConvergence.integral_ball_tendsto
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.normLog_localLp

