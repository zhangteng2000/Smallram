import ModifiedCartan.AnalyticLogPullback
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

open scoped Topology Real
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

noncomputable def powerChart (a : ℂ) (ρ : ℝ) (w : ℂ) : ℂ := a * w ^ ((ρ⁻¹ : ℝ) : ℂ)
noncomputable def powerChartInverse (a : ℂ) (ρ : ℝ) (z : ℂ) : ℂ := (z / a) ^ (ρ : ℂ)
noncomputable def powerChartDomain (a : ℂ) (ρ : ℝ) : Set ℂ :=
  {w | 0 < w.re} ∩ ball 0 ((4 / ‖a‖) ^ ρ)

theorem powerChartDomain_isOpen (a : ℂ) (ρ : ℝ) : IsOpen (powerChartDomain a ρ) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ball

theorem powerChartDomain_convex (a : ℂ) (ρ : ℝ) : Convex ℝ (powerChartDomain a ρ) :=
  ((convex_Ioi (0 : ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter (convex_ball _ _)

theorem cpow_inv_order_right_halfPlane {ρ : ℝ} (hρ : 1 ≤ ρ) {w : ℂ} (hw : 0 < w.re) :
    (w ^ ((ρ⁻¹ : ℝ) : ℂ)) ^ (ρ : ℂ) = w ∧ 0 < (w ^ ((ρ⁻¹ : ℝ) : ℂ)).re := by
  have hr : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hb : 0 < ρ⁻¹ := inv_pos.mpr hr
  have hble : ρ⁻¹ ≤ 1 := by
    have he := inv_mul_cancel₀ hr.ne'
    nlinarith
  have ha : |w.arg * ρ⁻¹| < Real.pi / 2 := by
    rw [abs_mul, abs_of_pos hb]
    calc
      |w.arg| * ρ⁻¹ ≤ |w.arg| := mul_le_of_le_one_right (abs_nonneg _) hble
      _ < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  have him : (Complex.log w * ((ρ⁻¹ : ℝ) : ℂ)).im = w.arg * ρ⁻¹ := by
    simp only [Complex.mul_im, Complex.ofReal_im, mul_zero, Complex.log_im, Complex.ofReal_re, zero_add]
  have hw0 : w ≠ 0 := by rintro rfl; simpa using hw
  constructor
  · rw [← Complex.cpow_mul (ρ : ℂ) (by rw [him]; linarith [(abs_lt.mp ha).1, Real.pi_pos])
      (by rw [him]; linarith [(abs_lt.mp ha).2, Real.pi_pos])]
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hr.ne', Complex.ofReal_one, Complex.cpow_one]
  · rw [Complex.cpow_ofReal_re]
    exact mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.mpr hw0) _) (Real.cos_pos_of_mem_Ioo (abs_lt.mp ha))

theorem powerChart_inverse {a : ℂ} (ha : a ≠ 0) {ρ : ℝ} (hρ : 1 ≤ ρ)
    {w : ℂ} (hw : w ∈ powerChartDomain a ρ) : powerChartInverse a ρ (powerChart a ρ w) = w := by
  simp only [powerChartInverse, powerChart, mul_div_cancel_left₀ _ ha]
  exact (cpow_inv_order_right_halfPlane hρ hw.1).1

theorem powerChart_analytic (a : ℂ) (ρ : ℝ) :
    AnalyticOnNhd ℂ (powerChart a ρ) (powerChartDomain a ρ) := by
  intro w hw
  exact analyticAt_const.mul (analyticAt_id.cpow analyticAt_const (Complex.mem_slitPlane_iff.mpr (Or.inl hw.1)))

theorem powerChartInverse_analytic {a : ℂ} (ha : a ≠ 0) {ρ : ℝ} (hρ : 1 ≤ ρ) :
    AnalyticOnNhd ℂ (powerChartInverse a ρ) (powerChart a ρ '' powerChartDomain a ρ) := by
  rintro z ⟨w, hw, rfl⟩
  apply (analyticAt_id.div_const (c := a)).cpow analyticAt_const
  apply Complex.mem_slitPlane_iff.mpr
  left
  simpa only [powerChart, id_eq, mul_div_cancel_left₀ _ ha] using (cpow_inv_order_right_halfPlane hρ hw.1).2

theorem powerChart_inverse_jacobian {a : ℂ} (ha : a ≠ 0) {ρ : ℝ} (hρ : 1 ≤ ρ) :
    ∃ D : ℂ → ℂ →L[ℝ] ℂ,
      (∀ z ∈ powerChart a ρ '' powerChartDomain a ρ,
        HasFDerivWithinAt (powerChartInverse a ρ) (D z) (powerChart a ρ '' powerChartDomain a ρ) z) ∧
      ContinuousOn (fun z => |(D z).det|) (powerChart a ρ '' powerChartDomain a ρ) := by
  let D : ℂ → ℂ →L[ℝ] ℂ := fun z => (fderiv ℂ (powerChartInverse a ρ) z).restrictScalars ℝ
  have hφ := powerChartInverse_analytic ha hρ
  refine ⟨D, fun z hz => ((hφ z hz).differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt, ?_⟩
  exact continuous_abs.comp_continuousOn (ContinuousLinearMap.continuous_det.comp_continuousOn
    ((ContinuousLinearMap.continuous_restrictScalars ℝ).comp_continuousOn hφ.fderiv.continuousOn))

theorem powerChart_hasDerivAt {a : ℂ} {ρ : ℝ} {w : ℂ} (hw : w ∈ powerChartDomain a ρ) :
    HasDerivAt (powerChart a ρ) (a * ((ρ⁻¹ : ℝ) : ℂ) * w ^ (((ρ⁻¹ : ℝ) : ℂ) - 1)) w := by
  simpa only [powerChart, mul_assoc] using!
    (Complex.hasStrictDerivAt_cpow_const (c := ((ρ⁻¹ : ℝ) : ℂ))
      (Complex.mem_slitPlane_iff.mpr (Or.inl hw.1))).hasDerivAt.const_mul a

theorem powerChart_real (a : ℂ) (ρ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    powerChart a ρ (t : ℂ) = ((t ^ ρ⁻¹ : ℝ) : ℂ) * a := by
  rw [powerChart, ← Complex.ofReal_cpow ht, mul_comm]

theorem powerChart_continuousAt_zero (a : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ContinuousAt (powerChart a ρ) 0 := by
  exact continuousAt_const.mul (Complex.continuousAt_cpow_const_of_re_pos (Or.inl (by simp))
    (by simpa using inv_pos.mpr hρ))

end ModifiedCartan
#print axioms ModifiedCartan.powerChart_inverse
#print axioms ModifiedCartan.powerChart_inverse_jacobian



