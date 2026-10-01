import ModifiedCartan.MonicQuotientComparison

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem abs_log_sub_le_log_two_of_close {x y : ℝ} (hx : 0 < x)
    (hclose : |y - x| ≤ x / 2) : 0 < y ∧ |Real.log y - Real.log x| ≤ Real.log 2 := by
  have hc := abs_le.mp hclose
  have hy : 0 < y := by linarith
  refine ⟨hy, abs_le.mpr ⟨?_, ?_⟩⟩
  · have hh := Real.log_le_log (half_pos hx) (show x / 2 ≤ y by linarith)
    rw [Real.log_div hx.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hh
    linarith
  · have hh := Real.log_le_log hy (show y ≤ 2 * x by linarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx.ne'] at hh
    linarith

/-- Exponentially close positive norms have the same nonnegative
normalized logarithmic limit. Positivity of the approximating norm is
derived on a tail, not assumed. -/
theorem normalized_log_tendsto_of_exponential_close {x y s : ℕ → ℝ} {A C u : ℝ}
    (hA : 0 < A) (hs : Tendsto s atTop atTop)
    (hx : ∀ᶠ ν in atTop, 0 < x ν)
    (hxlim : Tendsto (fun ν => Real.log (x ν) / s ν) atTop (𝓝 u)) (hu : 0 ≤ u)
    (hclose : ∀ᶠ ν in atTop, |y ν - x ν| ≤ C * Real.exp (-A * s ν)) :
    Tendsto (fun ν => Real.log (y ν) / s ν) atTop (𝓝 u) := by
  have hdec : Tendsto (fun ν => C * Real.exp (-(A / 2) * s ν)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (exponential_decay_of_scale hs (half_pos hA)).const_mul C
  have hevent : ∀ᶠ ν in atTop,
      |Real.log (y ν) / s ν - Real.log (x ν) / s ν| ≤ Real.log 2 / s ν := by
    filter_upwards [hx, hs.eventually_gt_atTop 0, hclose,
      hdec.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      hxlim.eventually (lt_mem_nhds (show -(A / 2) < u by linarith))]
      with ν hxν hsν hcloseν hdecν hlogν
    have hexp : Real.exp (-(A / 2) * s ν) ≤ x ν := by
      rw [← Real.exp_log hxν]
      exact Real.exp_le_exp.mpr ((lt_div_iff₀ hsν).mp hlogν).le
    have hfactor : C * Real.exp (-A * s ν) =
        (C * Real.exp (-(A / 2) * s ν)) * Real.exp (-(A / 2) * s ν) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    have hrelative : |y ν - x ν| ≤ x ν / 2 := by
      calc
        _ ≤ C * Real.exp (-A * s ν) := hcloseν
        _ = _ := hfactor
        _ ≤ (1 / 2) * Real.exp (-(A / 2) * s ν) :=
          mul_le_mul_of_nonneg_right hdecν.le (Real.exp_pos _).le
        _ ≤ x ν / 2 := by nlinarith
    have hlogs := (abs_log_sub_le_log_two_of_close hxν hrelative).2
    rw [← sub_div, abs_div, abs_of_pos hsν]
    exact div_le_div_of_nonneg_right hlogs hsν.le
  have hsmall : Tendsto (fun ν => Real.log 2 / s ν) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, Function.comp_def, mul_zero] using
      (tendsto_inv_atTop_zero.comp hs).const_mul (Real.log 2)
  have hdiff : Tendsto (fun ν => Real.log (y ν) / s ν - Real.log (x ν) / s ν) atTop (𝓝 0) := by
    apply squeeze_zero_norm' hevent hsmall
  have hh := hdiff.add hxlim
  simpa only [sub_add_cancel, zero_add] using hh

end ModifiedCartan
#print axioms ModifiedCartan.normalized_log_tendsto_of_exponential_close
