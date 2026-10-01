import ModifiedCartan.RegularizedComplexLog
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open scoped Topology
open Filter Set MeasureTheory ContinuousLinearMap
set_option autoImplicit false
namespace ModifiedCartan

theorem norm_classicalComplexGradient_le (f : ℂ → ℝ) (z : ℂ) :
    ‖classicalComplexGradient f z‖ ≤ 2 * ‖fderiv ℝ f z‖ := by
  rw [classicalComplexGradient]
  calc
    ‖(fderiv ℝ f z 1 : ℂ) - Complex.I * (fderiv ℝ f z Complex.I : ℂ)‖ ≤
        ‖fderiv ℝ f z 1‖ + ‖fderiv ℝ f z Complex.I‖ := by
      simpa only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] using
        norm_sub_le (fderiv ℝ f z 1 : ℂ) (Complex.I * (fderiv ℝ f z Complex.I : ℂ))
    _ ≤ 2 * ‖fderiv ℝ f z‖ := by
      have h₁ := (fderiv ℝ f z).le_opNorm (1 : ℂ)
      have h₂ := (fderiv ℝ f z).le_opNorm Complex.I
      simp only [norm_one, Complex.norm_I, mul_one] at h₁ h₂
      linarith

theorem norm_regularized_clog_le {z : ℂ} {ε M : ℝ}
    (hε : 0 < ε) (hz : z.re ≤ 0) (hM : ‖z‖ ≤ M) :
    ‖Complex.log ((ε : ℂ) - z)‖ ≤ |Real.log ε| + |Real.log (ε + M)| + Real.pi := by
  have hlower : ε ≤ ‖(ε : ℂ) - z‖ := by
    have hh := Complex.re_le_norm ((ε : ℂ) - z)
    simp only [Complex.sub_re, Complex.ofReal_re] at hh
    linarith
  have hupper : ‖(ε : ℂ) - z‖ ≤ ε + M := by
    have hh := norm_sub_le (ε : ℂ) z
    rw [Complex.norm_of_nonneg hε.le] at hh
    linarith
  have hlo := Real.log_le_log hε hlower
  have hhi := Real.log_le_log (hε.trans_le hlower) hupper
  have habs : |Real.log ‖(ε : ℂ) - z‖| ≤ |Real.log ε| + |Real.log (ε + M)| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le (Real.log ε), abs_nonneg (Real.log (ε + M))]
    · linarith [le_abs_self (Real.log (ε + M)), abs_nonneg (Real.log ε)]
  have him : |(Complex.log ((ε : ℂ) - z)).im| ≤ Real.pi :=
    abs_le.mpr ⟨(Complex.neg_pi_lt_log_im _).le, Complex.log_im_le_pi _⟩
  exact (Complex.norm_le_abs_re_add_abs_im _).trans
    (by rw [Complex.log_re]; linarith)

/-- For fixed positive regularization, bounded half-plane-valued gradients
allow passage to every real coordinate of a compact-test logarithm integral. -/
theorem integral_regularized_clog_tendsto {μ : Measure ℂ}
    {g : ℕ → ℂ → ℂ} {g₀ : ℂ → ℂ} {ε M : ℝ} (hε : 0 < ε)
    (hm : ∀ᶠ n in atTop, AEStronglyMeasurable (g n) μ)
    (hb : ∀ᶠ n in atTop, ∀ᵐ z ∂μ, (g n z).re ≤ 0 ∧ ‖g n z‖ ≤ M)
    (h₀ : ∀ᵐ z ∂μ, (g₀ z).re ≤ 0)
    (ht : ∀ᵐ z ∂μ, Tendsto (fun n => g n z) atTop (𝓝 (g₀ z)))
    {ψ : ℂ → ℝ} (hψ : Integrable ψ μ) (L : ℂ →L[ℝ] ℝ) :
    Tendsto (fun n => ∫ z, L (Complex.log ((ε : ℂ) - g n z)) * ψ z ∂μ) atTop
      (𝓝 (∫ z, L (Complex.log ((ε : ℂ) - g₀ z)) * ψ z ∂μ)) := by
  let B : ℝ := |Real.log ε| + |Real.log (ε + M)| + Real.pi
  apply tendsto_integral_filter_of_dominated_convergence (fun z => (‖L‖ * B) * ‖ψ z‖)
  · filter_upwards [hm] with n hn
    exact ((L.continuous.comp_aestronglyMeasurable
      (Complex.measurable_log.comp_aemeasurable (aemeasurable_const.sub hn.aemeasurable)).aestronglyMeasurable).mul
      hψ.aestronglyMeasurable)
  · filter_upwards [hb] with n hn
    filter_upwards [hn] with z hz
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (norm_regularized_clog_le hε hz.1 hz.2) (norm_nonneg _))
  · exact hψ.norm.const_mul _
  · filter_upwards [ht, h₀] with z hz hzr
    have hlog := (continuousAt_clog (regularized_sub_mem_slitPlane hε hzr)).tendsto.comp
      (tendsto_const_nhds.sub hz)
    exact (L.continuous.continuousAt.tendsto.comp hlog).mul_const (ψ z)

end ModifiedCartan
#print axioms ModifiedCartan.integral_regularized_clog_tendsto
