import ModifiedCartan.LocalizedMeasures

open scoped Topology ENNReal ContDiff
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

/-! An explicit smooth radial kernel for the harmonic interior estimates in
`lem:logderivlimit`. Its integral is one, it is nonnegative, and its support is
contained in the closed disk of radius 2R. Radiality is proved from the concrete
inner-product bump formula, without assuming it of an arbitrary bump. -/

noncomputable def radialBump (R : ℝ) (z : ℂ) : ℝ :=
  (ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2 (R⁻¹ • z)

theorem radialBump_contDiff (R : ℝ) : ContDiff ℝ ∞ (radialBump R) := by
  have hg : ContDiff ℝ ∞ (fun z : ℂ => ((2 : ℝ), R⁻¹ • z)) := by fun_prop
  have hh := (ContDiffBumpBase.ofInnerProductSpace ℂ).smooth.comp_contDiff hg
    (fun _ => ⟨by norm_num, mem_univ _⟩)
  convert! hh using 1

theorem radialBump_nonneg (R : ℝ) (z : ℂ) : 0 ≤ radialBump R z :=
  ((ContDiffBumpBase.ofInnerProductSpace ℂ).mem_Icc _ _).1

theorem radialBump_le_one (R : ℝ) (z : ℂ) : radialBump R z ≤ 1 :=
  ((ContDiffBumpBase.ofInnerProductSpace ℂ).mem_Icc _ _).2

theorem radialBump_radial (R : ℝ) (z : ℂ) : radialBump R z = radialBump R (‖z‖ : ℂ) := by
  simp only [radialBump, ContDiffBumpBase.ofInnerProductSpace, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]

theorem radialBump_one {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ ≤ R) :
    radialBump R z = 1 := by
  apply (ContDiffBumpBase.ofInnerProductSpace ℂ).eq_one 2 (by norm_num)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), inv_mul_eq_div]
  exact (div_le_one hR).mpr hz

theorem radialBump_tsupport {R : ℝ} (hR : 0 < R) :
    tsupport (radialBump R) ⊆ closedBall 0 (2 * R) := by
  apply closure_minimal _ isClosed_closedBall
  intro z hz
  have hm : R⁻¹ • z ∈ Function.support ((ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2) := hz
  rw [(ContDiffBumpBase.ofInnerProductSpace ℂ).support 2 (by norm_num)] at hm
  have hn : ‖z‖ / R < 2 := by
    simpa only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hR), inv_mul_eq_div] using hm
  simpa only [mem_closedBall, dist_zero_right] using ((div_lt_iff₀ hR).mp hn).le

theorem radialBump_hasCompactSupport {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (radialBump R) :=
  (isCompact_closedBall (0 : ℂ) (2 * R)).of_isClosed_subset isClosed_closure (radialBump_tsupport hR)

theorem radialBump_integral_pos {R : ℝ} (hR : 0 < R) :
    0 < ∫ z : ℂ, radialBump R z := by
  apply integral_pos_of_integrable_nonneg_nonzero (radialBump_contDiff R).continuous
    ((radialBump_contDiff R).continuous.integrable_of_hasCompactSupport (radialBump_hasCompactSupport hR))
    (radialBump_nonneg R) (x := 0)
  rw [radialBump_one hR (by simpa only [norm_zero] using hR.le)]
  exact one_ne_zero

noncomputable def radialKernel (R : ℝ) (z : ℂ) : ℝ :=
  (∫ w : ℂ, radialBump R w)⁻¹ * radialBump R z

theorem radialKernel_contDiff (R : ℝ) : ContDiff ℝ ∞ (radialKernel R) :=
  contDiff_const.mul (radialBump_contDiff R)

theorem radialKernel_tsupport {R : ℝ} (hR : 0 < R) :
    tsupport (radialKernel R) ⊆ closedBall 0 (2 * R) :=
  tsupport_mul_subset_right.trans (radialBump_tsupport hR)

theorem radialKernel_hasCompactSupport {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (radialKernel R) := (radialBump_hasCompactSupport hR).mul_left

theorem radialKernel_nonneg {R : ℝ} (hR : 0 < R) (z : ℂ) :
    0 ≤ radialKernel R z :=
  mul_nonneg (inv_nonneg.mpr (radialBump_integral_pos hR).le) (radialBump_nonneg R z)

theorem radialKernel_radial (R : ℝ) (z : ℂ) : radialKernel R z = radialKernel R (‖z‖ : ℂ) := by
  unfold radialKernel
  rw [radialBump_radial R z]

theorem radialKernel_integral {R : ℝ} (hR : 0 < R) :
    (∫ z : ℂ, radialKernel R z) = 1 := by
  unfold radialKernel
  rw [integral_const_mul, inv_mul_cancel₀ (radialBump_integral_pos hR).ne']


end ModifiedCartan
