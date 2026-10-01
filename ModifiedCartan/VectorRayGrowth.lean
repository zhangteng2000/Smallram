import ModifiedCartan.ExponentialUpperRate
import ModifiedCartan.RescaledGauge
import ModifiedCartan.PowerExpLog
import ModifiedCartan.NormalizedCharacteristic

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem euclidean_exponential_decay_of_coordinate_upper_rates {n : ℕ} {H : ℝ}
    {v : ℝ → Index n → ℂ} (hv : ∀ j, HasExponentialUpperRate H (fun t => v t j))
    {a : ℝ} (ha : H < a) :
    Tendsto (fun t => Real.exp (-a * t) * euclideanNorm (v t)) atTop (𝓝 0) := by
  have hcomp (j : Index n) :
      Tendsto (fun t : ℝ => ((Real.exp (-a * t) : ℝ) : ℂ) * v t j) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply (hv j a ha).congr'
    filter_upwards [] with t
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hvec : Tendsto (fun t : ℝ => fun j => ((Real.exp (-a * t) : ℝ) : ℂ) * v t j)
      atTop (𝓝 (0 : Index n → ℂ)) := tendsto_pi_nhds.mpr hcomp
  have hh := euclideanNorm_continuous.continuousAt.tendsto.comp hvec
  change Tendsto (fun t : ℝ => euclideanNorm (fun j => ((Real.exp (-a * t) : ℝ) : ℂ) * v t j))
    atTop (𝓝 (euclideanNorm (0 : Index n → ℂ))) at hh
  have hz : euclideanNorm (0 : Index n → ℂ) = 0 := by simp [euclideanNorm]
  rw [hz] at hh
  apply hh.congr'
  filter_upwards [] with t
  rw [euclideanNorm_mul_scalar, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

/-- Coordinate upper rates and one controlled scalar combination with the exact
lower rate determine the Euclidean vector logarithmic limit. -/
theorem vector_log_limit_of_scalar_lower {n : ℕ} {H C : ℝ}
    {v : ℝ → Index n → ℂ} {f : ℝ → ℂ}
    (hC : 0 < C) (hv : ∀ᶠ t in atTop, v t ≠ 0)
    (hfne : ∀ᶠ t in atTop, f t ≠ 0)
    (hupper : ∀ j, HasExponentialUpperRate H (fun t => v t j))
    (hbound : ∀ᶠ t in atTop, ‖f t‖ ≤ C * euclideanNorm (v t))
    (hlower : Tendsto (fun t => Real.log ‖f t‖ / t) atTop (𝓝 H)) :
    Tendsto (fun t => Real.log (euclideanNorm (v t)) / t) atTop (𝓝 H) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hsmall : Tendsto (fun t : ℝ => Real.log C / t) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hl := hlower.sub hsmall
    simp only [sub_zero] at hl
    filter_upwards [hv, hfne, hbound, eventually_gt_atTop (0 : ℝ),
      (tendsto_order.mp hl).1 a ha] with t hvt hft hbt ht hat
    have hN := euclideanNorm_pos hvt
    have hlog := Real.log_le_log (norm_pos_iff.mpr hft) hbt
    rw [Real.log_mul hC.ne' hN.ne'] at hlog
    have he : Real.log ‖f t‖ - Real.log C ≤ Real.log (euclideanNorm (v t)) := by linarith
    have he' := div_le_div_of_nonneg_right he ht.le
    rw [sub_div] at he'
    exact hat.trans_le he'
  · intro a ha
    let b := (H + a) / 2
    have hHb : H < b := by dsimp [b]; linarith
    have hba : b < a := by dsimp [b]; linarith
    have hdec := euclidean_exponential_decay_of_coordinate_upper_rates hupper hHb
    filter_upwards [hv, eventually_gt_atTop (0 : ℝ),
      hdec.eventually_lt_const zero_lt_one] with t hvt ht hdt
    have hN := euclideanNorm_pos hvt
    have hcancel : Real.exp (b * t) * Real.exp (-b * t) = 1 := by
      rw [← Real.exp_add, show b * t + -b * t = 0 by ring, Real.exp_zero]
    have hlt : euclideanNorm (v t) < Real.exp (b * t) := by
      calc
        _ = Real.exp (b * t) * (Real.exp (-b * t) * euclideanNorm (v t)) := by
          rw [← mul_assoc, hcancel, one_mul]
        _ < Real.exp (b * t) * 1 := mul_lt_mul_of_pos_left hdt (Real.exp_pos _)
        _ = _ := mul_one _
    have hlog := (Real.log_lt_iff_lt_exp hN).mpr hlt
    exact ((div_lt_iff₀ ht).mpr hlog).trans hba

end ModifiedCartan
#print axioms ModifiedCartan.euclidean_exponential_decay_of_coordinate_upper_rates
#print axioms ModifiedCartan.vector_log_limit_of_scalar_lower
