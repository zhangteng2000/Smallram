import ModifiedCartan.HomogeneousRadialMeans
import ModifiedCartan.NormLogIntegrals
import ModifiedCartan.CurveCoordinateCounting

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem ArbitraryRadiusLimitData.norm_integral_eq_ratio_primitive
    {n : ℕ} {f : Curve n} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    {R : ℝ} (hR : 0 < R) (hR4 : R < 4) :
    ∀ᶠ ν in atTop,
      (∫ t in (0 : ℝ)..R, t * (characteristic f (t * r (d.subseq ν)) / characteristic f (r (d.subseq ν)))) =
        (∫ z in ball (0 : ℂ) R, d.normLog ν z) / (2 * Real.pi) -
          d.mean_error ν * ∫ t in (0 : ℝ)..R, t := by
  filter_upwards [d.normLog_continuous, d.radial_mean] with ν hc hm
  have hR64 : R < 64 := hR4.trans (by norm_num)
  have he := integral_ball_eq_radial_mean_of_continuousOn hR
    (hc.mono (closedBall_subset_ball hR64))
    (fun t ht htR => hm t ht (htR.trans hR64))
  have hcont : Continuous (fun t : ℝ => t * (characteristic f (t * r (d.subseq ν)) /
      characteristic f (r (d.subseq ν)))) :=
    continuous_id.mul (((characteristic_continuous f).comp (continuous_id.mul continuous_const)).div_const _)
  have hsplit : (∫ t in (0 : ℝ)..R, t * (characteristic f (t * r (d.subseq ν)) /
      characteristic f (r (d.subseq ν)) + d.mean_error ν)) =
      (∫ t in (0 : ℝ)..R, t * (characteristic f (t * r (d.subseq ν)) / characteristic f (r (d.subseq ν)))) +
        d.mean_error ν * ∫ t in (0 : ℝ)..R, t := by
    simp_rw [mul_add]
    rw [intervalIntegral.integral_add (hcont.intervalIntegrable _ _)
      ((show Continuous (fun t : ℝ => t * d.mean_error ν) from continuous_id.mul_const _).intervalIntegrable _ _), intervalIntegral.integral_mul_const]
    ring
  change (∫ z in ball (0 : ℂ) R, d.normLog ν z) = _ at he
  rw [he, hsplit, mul_div_cancel_left₀ _ (mul_ne_zero two_ne_zero Real.pi_ne_zero)]
  ring

theorem ArbitraryRadiusLimitData.homogeneous_integral_ball
    {n : ℕ} {f : Curve n} {r : ℕ → ℝ} {ρ : ℝ}
    (hρ : 0 < ρ) (d : ArbitraryRadiusLimitData f r ρ)
    {R : ℝ} (hR : 0 < R) (hR2 : R < 2) :
    (∫ z in ball (0 : ℂ) R, (d.U z).toReal) =
      (2 * Real.pi) * (Real.circleAverage (fun z => (d.U z).toReal) 0 1 *
        ∫ t in (0 : ℝ)..R, t * t ^ ρ) := by
  have he := integral_ball_eq_radial_mean_of_continuousOn hR
    (d.norm_limit_continuous.2.mono (closedBall_subset_ball (hR2.trans (by norm_num : (2 : ℝ) < 4))))
    (fun t ht htR => d.circleAverage_homogeneous hρ ht (htR.trans hR2))
  rw [he]
  simp_rw [← mul_assoc]
  rw [intervalIntegral.integral_mul_const]
  ring

theorem ArbitraryRadiusLimitData.ratio_primitive_tendsto
    {n : ℕ} {f : Curve n} {r : ℕ → ℝ} {ρ : ℝ}
    (hρ : 0 < ρ) (d : ArbitraryRadiusLimitData f r ρ)
    {R : ℝ} (hR : 0 < R) (hR2 : R < 2) :
    Tendsto (fun ν => ∫ t in (0 : ℝ)..R,
      t * (characteristic f (t * r (d.subseq ν)) / characteristic f (r (d.subseq ν))))
      atTop (𝓝 (Real.circleAverage (fun z => (d.U z).toReal) 0 1 *
        ∫ t in (0 : ℝ)..R, t * t ^ ρ)) := by
  have hR4 : R < 4 := hR2.trans (by norm_num)
  have hi := d.normLog_localLp.integral_ball_tendsto hR (closedBall_subset_ball hR4)
  have ht : Tendsto (fun ν => (∫ z in ball (0 : ℂ) R, d.normLog ν z) / (2 * Real.pi) -
      d.mean_error ν * ∫ t in (0 : ℝ)..R, t) atTop
      (𝓝 ((∫ z in ball (0 : ℂ) R, (d.U z).toReal) / (2 * Real.pi))) := by
    simpa only [zero_mul, sub_zero] using!
      (hi.div_const (2 * Real.pi)).sub (d.mean_error_zero.mul_const (∫ t in (0 : ℝ)..R, t))
  rw [d.homogeneous_integral_ball hρ hR hR2,
    mul_div_cancel_left₀ _ (mul_ne_zero two_ne_zero Real.pi_ne_zero)] at ht
  apply ht.congr'
  exact (d.norm_integral_eq_ratio_primitive hR hR4).mono (fun _ he => he.symm)

theorem ArbitraryRadiusLimitData.annular_ratio_tendsto
    {n : ℕ} {f : Curve n} {r : ℕ → ℝ} {ρ : ℝ}
    (hρ : 0 < ρ) (d : ArbitraryRadiusLimitData f r ρ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 2) :
    Tendsto (fun ν => ∫ t in a..b,
      t * (characteristic f (t * r (d.subseq ν)) / characteristic f (r (d.subseq ν))))
      atTop (𝓝 (Real.circleAverage (fun z => (d.U z).toReal) 0 1 *
        ∫ t in a..b, t * t ^ ρ)) := by
  have hc (ν : ℕ) : Continuous (fun t : ℝ => t * (characteristic f (t * r (d.subseq ν)) /
      characteristic f (r (d.subseq ν)))) :=
    continuous_id.mul (((characteristic_continuous f).comp (continuous_id.mul continuous_const)).div_const _)
  have hg : Continuous (fun t : ℝ => t * t ^ ρ) := continuous_id.mul (Real.continuous_rpow_const hρ.le)
  have he (ν : ℕ) := intervalIntegral.integral_interval_sub_left (μ := volume)
    ((hc ν).intervalIntegrable 0 b) ((hc ν).intervalIntegrable 0 a)
  have helim := intervalIntegral.integral_interval_sub_left (μ := volume)
    (hg.intervalIntegrable 0 b) (hg.intervalIntegrable 0 a)
  have ht := (d.ratio_primitive_tendsto hρ (ha.trans hab) hb).sub
    (d.ratio_primitive_tendsto hρ ha (hab.trans hb))
  simpa only [he, ← mul_sub, helim] using! ht

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.annular_ratio_tendsto

