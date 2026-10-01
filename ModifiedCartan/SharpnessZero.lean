import ModifiedCartan.ZeroSharpCurveBounds
import ModifiedCartan.QuadraticLogLimits

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- Exact leading characteristic asymptotic for LaTeX `prop:sharpness-zero`. -/
theorem zeroSharpCurve_characteristic_logsquare_limit (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun r : ℝ => characteristic (zeroSharpCurve n hn) r / (Real.log r) ^ 2)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  obtain ⟨A, B, C, hb⟩ := zeroSharpCurve_characteristic_quadratic_bounds n hn
  apply tendsto_of_quadratic_log_bounds (b := -1) (c := -B) (d := A) (e := C)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  obtain ⟨hl, hu⟩ := hb r hr
  constructor <;> linarith

theorem zeroSharp_derivative_logCounting_logsquare_limit (m : ℕ) :
    Tendsto (fun r : ℝ =>
      ValueDistribution.logCounting (iteratedDeriv m zeroSharpFunction) (0 : WithTop ℂ) r /
        (Real.log r) ^ 2) atTop (𝓝 (1 / 2 : ℝ)) := by
  obtain ⟨A, B, hb⟩ := zeroSharp_derivative_logCounting_quadratic_bounds m
  apply tendsto_of_quadratic_log_bounds (b := -((m : ℝ) + 1)) (c := -1) (d := A) (e := B)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  obtain ⟨hl, hu⟩ := hb r hr
  constructor <;> linarith

theorem zeroSharpCurve_transcendental (n : ℕ) (hn : 1 ≤ n) :
    (zeroSharpCurve n hn).Transcendental :=
  transcendental_of_positive_characteristic_logsquare_limit _ (by norm_num)
    (zeroSharpCurve_characteristic_logsquare_limit n hn)

theorem zeroSharpCurve_order (n : ℕ) (hn : 1 ≤ n) : order (zeroSharpCurve n hn) = 0 := by
  have ht := log_growth_zero_of_logsquare_limit (by norm_num : (1 / 2 : ℝ) ≠ 0)
    (zeroSharpCurve_characteristic_logsquare_limit n hn)
  exact (EReal.tendsto_coe.mpr ht).limsup_eq

theorem zeroSharpCurve_ramification_ratio (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun r : ℝ => ramification (zeroSharpCurve n hn) r /
      characteristic (zeroSharpCurve n hn) r) atTop (𝓝 1) := by
  have hN : Tendsto (fun r : ℝ => ramification (zeroSharpCurve n hn) r / (Real.log r) ^ 2)
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [zeroSharpCurve_ramification] using zeroSharp_derivative_logCounting_logsquare_limit n
  have hh := hN.div (zeroSharpCurve_characteristic_logsquare_limit n hn) (by norm_num)
  have hh' : Tendsto (fun r : ℝ =>
      (ramification (zeroSharpCurve n hn) r / (Real.log r) ^ 2) /
      (characteristic (zeroSharpCurve n hn) r / (Real.log r) ^ 2)) atTop (𝓝 1) := by
    change Tendsto (fun r : ℝ =>
      (ramification (zeroSharpCurve n hn) r / (Real.log r) ^ 2) /
      (characteristic (zeroSharpCurve n hn) r / (Real.log r) ^ 2)) atTop
      (𝓝 ((1 / 2 : ℝ) / (1 / 2 : ℝ))) at hh
    norm_num at hh
    exact hh
  apply hh'.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
  have hnz : (Real.log r) ^ 2 ≠ 0 := pow_ne_zero _ (Real.log_pos (by linarith : 1 < r)).ne'
  exact div_div_div_cancel_right₀ hnz _ _

namespace Paper

/-- LaTeX `prop:sharpness-zero`, for the exact prescribed infinite product
and coordinate tuple `eq:zero-sharp-example`. -/
theorem prop_sharpness_zero (n : ℕ) : SharpnessZeroTarget n := by
  intro hn
  exact ⟨zeroSharp_factors_multipliable, zeroSharpCurve n hn, rfl,
    zeroSharpCurve_transcendental n hn, zeroSharpCurve_linearlyNonDegenerate n hn,
    zeroSharpCurve_order n hn, zeroSharpCurve_ramification_ratio n hn⟩

end Paper
end ModifiedCartan
#print axioms ModifiedCartan.zeroSharpCurve_characteristic_logsquare_limit
#print axioms ModifiedCartan.zeroSharpCurve_ramification_ratio
#print axioms ModifiedCartan.Paper.prop_sharpness_zero
