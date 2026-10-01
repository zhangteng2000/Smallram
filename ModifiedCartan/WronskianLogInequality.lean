import ModifiedCartan.WronskianDeterminant
import ModifiedCartan.ScaledLogMeasure

open scoped Topology ENNReal
open Filter MeasureTheory Set

set_option autoImplicit false

namespace ModifiedCartan

/-- The pointwise logarithmic determinant estimate in the proof of `lem:sum`. -/
theorem wronskian_log_sum_lower_bound {n : ℕ} {s : ℝ} (hs : 0 < s)
    {f : FewInflection.Index n → ℂ → ℂ} {z : ℂ} (hf : ∀ j, f j z ≠ 0)
    (hW : FewInflection.wronskian n f z ≠ 0) :
    (s⁻¹ * Real.log ‖FewInflection.wronskian n f z‖) -
      (∑ i : FewInflection.Index n, (i : ℕ)) * s⁻¹ * Real.log s -
      s⁻¹ * logPlusNorm (normalizedWronskian n s f z) ≤
      ∑ j : FewInflection.Index n, s⁻¹ * Real.log ‖f j z‖ := by
  classical
  let κ := ∑ i : FewInflection.Index n, (i : ℕ)
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs)
  have hp : (∏ j, f j z) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hf j)
  have hden : (s : ℂ) ^ κ * ∏ j, f j z ≠ 0 := mul_ne_zero (pow_ne_zero _ hsC) hp
  have hD : normalizedWronskian n s f z ≠ 0 := by
    rw [normalizedWronskian_eq_div]
    exact div_ne_zero hW hden
  have hid : FewInflection.wronskian n f z =
      ((s : ℂ) ^ κ * ∏ j, f j z) * normalizedWronskian n s f z := by
    rw [normalizedWronskian_eq_div]
    exact (mul_div_cancel₀ _ hden).symm
  have hn : ‖FewInflection.wronskian n f z‖ =
      (s ^ κ * ∏ j, ‖f j z‖) * ‖normalizedWronskian n s f z‖ := by
    rw [hid, norm_mul, norm_mul, norm_pow, norm_prod, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have hpR : (∏ j, ‖f j z‖) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => norm_ne_zero_iff.mpr (hf j))
  have hlog := congrArg Real.log hn
  rw [Real.log_mul (mul_ne_zero (pow_ne_zero _ (ne_of_gt hs)) hpR) (norm_ne_zero_iff.mpr hD),
    Real.log_mul (pow_ne_zero _ (ne_of_gt hs)) hpR,
    Real.log_pow, Real.log_prod (fun j _ => norm_ne_zero_iff.mpr (hf j))] at hlog
  have hscale := congrArg (fun x : ℝ => s⁻¹ * x) hlog
  have hplus := mul_le_mul_of_nonneg_left (log_norm_le_logPlusNorm (normalizedWronskian n s f z))
    (le_of_lt (inv_pos.mpr hs))
  rw [← Finset.mul_sum]
  change _ - (κ : ℝ) * s⁻¹ * Real.log s - _ ≤ _
  nlinarith


end ModifiedCartan

