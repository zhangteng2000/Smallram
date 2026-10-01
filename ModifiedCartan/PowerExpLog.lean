import ModifiedCartan.RayCompanionAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem log_norm_power_exp_normalization {t b : ℝ} (ht : 0 < t)
    (lam : ℂ) {z : ℂ} (hz : z ≠ 0) :
    Real.log ‖t ^ (-b) • (Complex.exp (-lam * (t : ℂ)) • z)‖ =
      -b * Real.log t - lam.re * t + Real.log ‖z‖ := by
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _),
    Complex.norm_exp, Real.log_mul (Real.rpow_pos_of_pos ht _).ne'
      (mul_ne_zero (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr hz)),
    Real.log_mul (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr hz),
    Real.log_rpow ht, Real.log_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.neg_im, Complex.ofReal_im, mul_zero, sub_zero]
  ring

/-- A genuine nonzero power/exponential normalized scalar limit determines
its logarithmic growth, with no assumed logarithmic asymptotic. -/
theorem log_norm_div_t_tendsto_of_power_exp_limit {f : ℝ → ℂ} {lam c : ℂ} {b : ℝ}
    (hc : c ≠ 0)
    (hf : Tendsto (fun t : ℝ => t ^ (-b) • (Complex.exp (-lam * (t : ℂ)) • f t))
      atTop (𝓝 c)) :
    Tendsto (fun t : ℝ => Real.log ‖f t‖ / t) atTop (𝓝 lam.re) := by
  let u : ℝ → ℂ := fun t => t ^ (-b) • (Complex.exp (-lam * (t : ℂ)) • f t)
  have hlog : Tendsto (fun t => Real.log ‖u t‖) atTop (𝓝 (Real.log ‖c‖)) :=
    (Real.continuousAt_log (norm_ne_zero_iff.mpr hc)).tendsto.comp hf.norm
  have hlogdiv := hlog.div_atTop tendsto_id
  have hsmall : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hlim : Tendsto (fun t : ℝ => Real.log ‖u t‖ / t + b * (Real.log t / t) + lam.re)
      atTop (𝓝 lam.re) := by
    simpa using (hlogdiv.add (hsmall.const_mul b)).add_const lam.re
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ), hf.eventually_ne hc] with t ht hu
  have hft : f t ≠ 0 := by
    intro he
    apply hu
    simp [he]
  change Real.log ‖t ^ (-b) • (Complex.exp (-lam * (t : ℂ)) • f t)‖ / t +
    b * (Real.log t / t) + lam.re = Real.log ‖f t‖ / t
  rw [log_norm_power_exp_normalization ht lam hft]
  field_simp
  <;> ring

end ModifiedCartan
#print axioms ModifiedCartan.log_norm_div_t_tendsto_of_power_exp_limit

