import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Exp

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The forward decaying / backward bounded kernel in `lem:integrable-system`. -/
noncomputable def dichotomyKernel (a : ℂ) (t s : ℝ) : ℂ :=
  if a.re < 0 then (Iic t).indicator (fun v => Complex.exp (a * ((t - v : ℝ) : ℂ))) s
  else -(Ici t).indicator (fun v => Complex.exp (a * ((t - v : ℝ) : ℂ))) s

theorem dichotomyKernel_norm_le_one (a : ℂ) (t s : ℝ) :
    ‖dichotomyKernel a t s‖ ≤ 1 := by
  unfold dichotomyKernel
  split_ifs with ha
  · by_cases hs : s ≤ t
    · rw [indicator_of_mem (show s ∈ Iic t from hs), Complex.norm_exp, Real.exp_le_one_iff]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg ha.le (sub_nonneg.mpr hs)
    · simp only [indicator_of_notMem (show s ∉ Iic t from hs), norm_zero, zero_le_one]
  · rw [norm_neg]
    by_cases hs : t ≤ s
    · rw [indicator_of_mem (show s ∈ Ici t from hs), Complex.norm_exp, Real.exp_le_one_iff]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_not_gt ha) (sub_nonpos.mpr hs)
    · simp only [indicator_of_notMem (show s ∉ Ici t from hs), norm_zero, zero_le_one]

theorem dichotomyKernel_stronglyMeasurable (a : ℂ) (t : ℝ) :
    StronglyMeasurable (dichotomyKernel a t) := by
  have hc : Continuous (fun s : ℝ => Complex.exp (a * ((t - s : ℝ) : ℂ))) := by fun_prop
  unfold dichotomyKernel
  split_ifs
  · exact hc.stronglyMeasurable.indicator measurableSet_Iic
  · exact (hc.stronglyMeasurable.indicator measurableSet_Ici).neg

theorem dichotomyKernel_tendsto_zero (a : ℂ) (s : ℝ) :
    Tendsto (fun t => dichotomyKernel a t s) atTop (𝓝 0) := by
  by_cases ha : a.re < 0
  · have ht : Tendsto (fun t : ℝ => t - s) atTop atTop := by
      simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-s) tendsto_id
    have he : Tendsto (fun t : ℝ => Complex.exp (a * ((t - s : ℝ) : ℂ))) atTop (𝓝 0) := by
      apply Complex.tendsto_exp_nhds_zero_iff.mpr
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        using ht.const_mul_atTop_of_neg ha
    apply he.congr'
    filter_upwards [eventually_ge_atTop s] with t ht
    simp only [dichotomyKernel, ite_eq_left ha, indicator_of_mem (show s ∈ Iic t from ht)]
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop s] with t ht
    simp only [dichotomyKernel, ite_eq_right ha, indicator_of_notMem (show s ∉ Ici t from not_le.mpr ht), neg_zero]

noncomputable def dichotomyIntegral (a : ℂ) (T : ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ s in Ici T, dichotomyKernel a t s * f s

theorem dichotomyKernel_mul_integrable (a : ℂ) {T : ℝ} {f : ℝ → ℂ}
    (hf : IntegrableOn f (Ici T)) (t : ℝ) :
    IntegrableOn (fun s => dichotomyKernel a t s * f s) (Ici T) := by
  apply Integrable.mono hf ((dichotomyKernel_stronglyMeasurable a t).aestronglyMeasurable.mul hf.1)
  exact Eventually.of_forall (fun s => by
    simp only [Pi.mul_apply, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (dichotomyKernel_norm_le_one a t s))

theorem dichotomyIntegral_norm_le (a : ℂ) {T : ℝ} {f : ℝ → ℂ}
    (hf : IntegrableOn f (Ici T)) (t : ℝ) :
    ‖dichotomyIntegral a T f t‖ ≤ ∫ s in Ici T, ‖f s‖ := by
  apply norm_integral_le_of_norm_le hf.norm
  exact Eventually.of_forall (fun s => by
    simp only [Pi.mul_apply, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (dichotomyKernel_norm_le_one a t s))

/-- Both branches of the actual integral operator tend to zero on every L1 input. -/
theorem dichotomyIntegral_tendsto_zero (a : ℂ) {T : ℝ} {f : ℝ → ℂ}
    (hf : IntegrableOn f (Ici T)) :
    Tendsto (dichotomyIntegral a T f) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (fun s => ‖f s‖)
    (Eventually.of_forall (fun t => (dichotomyKernel_mul_integrable a hf t).1))
    (Eventually.of_forall (fun t => Eventually.of_forall (fun s => by
      simp only [Pi.mul_apply, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (dichotomyKernel_norm_le_one a t s))))
    hf.norm (Eventually.of_forall (fun s => by
      simpa only [zero_mul] using (dichotomyKernel_tendsto_zero a s).mul_const (f s)))
  change Tendsto (fun t => ∫ s in Ici T, dichotomyKernel a t s * f s) atTop (𝓝 0)
  simpa only [integral_zero] using h

theorem dichotomyIntegral_sub (a : ℂ) {T : ℝ} {f g : ℝ → ℂ}
    (hf : IntegrableOn f (Ici T)) (hg : IntegrableOn g (Ici T)) (t : ℝ) :
    dichotomyIntegral a T (fun s => f s - g s) t =
      dichotomyIntegral a T f t - dichotomyIntegral a T g t := by
  unfold dichotomyIntegral
  simp only [mul_sub]
  exact integral_sub (dichotomyKernel_mul_integrable a hf t) (dichotomyKernel_mul_integrable a hg t)

end ModifiedCartan
#print axioms ModifiedCartan.dichotomyIntegral_norm_le
#print axioms ModifiedCartan.dichotomyIntegral_tendsto_zero


