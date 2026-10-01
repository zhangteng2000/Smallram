import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Tactic

open scoped Topology ComplexConjugate
open Filter Set Metric Complex InnerProductSpace
set_option autoImplicit false
namespace ModifiedCartan

theorem harmonic_harnack_le {u : ℂ → ℝ} {R : ℝ}
    (hu : HarmonicOnNhd u (closedBall 0 R))
    (hpos : ∀ z ∈ sphere (0 : ℂ) R, 0 ≤ u z)
    {z : ℂ} (hz : z ∈ ball 0 R) :
    u z ≤ ((R + ‖z‖) / (R - ‖z‖)) * u 0 := by
  have hR : 0 < R := pos_of_mem_ball hz
  have hc : CircleIntegrable u 0 R := by
    exact (hu.continuousOn.mono (by simpa [abs_of_pos hR] using
      (sphere_subset_closedBall : sphere (0 : ℂ) R ⊆ closedBall 0 R))).circleIntegrable'
  have hk := Complex.continuous_re.comp_continuousOn
    (continuousOn_herglotzRieszKernel_sphere hz)
  have hint := hc.continuousOn_smul hk
  have hle := Real.circleAverage_mono hint
    (show CircleIntegrable (fun w => ((R + ‖z‖) / (R - ‖z‖)) * u w) 0 R from
      hc.const_smul) (by
      intro w hw
      have hw' : w ∈ sphere (0 : ℂ) R := by simpa [abs_of_pos hR] using hw
      change (herglotzRieszKernel 0 z w).re * u w ≤ _
      exact mul_le_mul_of_nonneg_right
        (by simpa [herglotzRieszKernel, sub_zero] using
          re_herglotzRieszKernel_le hw' hz) (hpos w hw'))
  rw [hu.circleAverage_re_herglotzRieszKernel_smul hz] at hle
  have hmean : Real.circleAverage u 0 R = u 0 := by
    exact (show HarmonicOnNhd u (closedBall 0 |R|) by simpa [abs_of_pos hR] using hu).circleAverage_eq
  change u z ≤ Real.circleAverage (fun w => ((R + ‖z‖) / (R - ‖z‖)) • u w) 0 R at hle
  rwa [Real.circleAverage_fun_smul, hmean] at hle

/-- The exact factor five used in the upper bound of `prop:representation`. -/
theorem harmonic_harnack_48_32 {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u (closedBall 0 48))
    (hpos : ∀ z ∈ closedBall (0 : ℂ) 48, 0 ≤ u z)
    {z : ℂ} (hz : z ∈ closedBall 0 32) : u z ≤ 5 * u 0 := by
  have hzn : ‖z‖ ≤ 32 := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hz48 : z ∈ ball (0 : ℂ) 48 := by simpa only [mem_ball, dist_zero_right] using
    (show ‖z‖ < (48 : ℝ) by linarith)
  have h := harmonic_harnack_le hu (fun w hw => hpos w (sphere_subset_closedBall hw)) hz48
  have hratio : (48 + ‖z‖) / (48 - ‖z‖) ≤ (5 : ℝ) := by
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < 48 - ‖z‖)).mpr
    linarith
  exact h.trans (mul_le_mul_of_nonneg_right hratio (hpos 0 (mem_closedBall_self (by norm_num))))

theorem harmonic_lower_bound_48_32 {v : ℂ → ℝ} {B : ℝ}
    (hv : HarmonicOnNhd v (closedBall 0 48))
    (hB : ∀ z ∈ closedBall (0 : ℂ) 48, v z ≤ B)
    {z : ℂ} (hz : z ∈ closedBall 0 32) :
    -v z ≤ 4 * B - 5 * v 0 := by
  have hu : HarmonicOnNhd (fun w => B - v w) (closedBall 0 48) :=
    fun w hw => (harmonicAt_const B).sub (hv w hw)
  have h := harmonic_harnack_48_32 hu (fun w hw => sub_nonneg.mpr (hB w hw)) hz
  linarith

theorem norm_canonicalFactor_ge_one {R : ℝ} {a z : ℂ}
    (ha : a ∈ ball 0 R) (hz : z ∈ ball 0 R) (hza : z ≠ a) :
    1 ≤ ‖Complex.canonicalFactor R a z‖ := by
  have hR : 0 < R := pos_of_mem_ball ha
  have han : ‖a‖ < R := by simpa only [mem_ball, dist_zero_right] using ha
  have hzn : ‖z‖ < R := by simpa only [mem_ball, dist_zero_right] using hz
  have hidentity :
      ‖(R : ℂ)^2 - conj a * z‖^2 - R^2 * ‖z-a‖^2 =
        (R^2 - ‖a‖^2) * (R^2 - ‖z‖^2) := by
    simp_rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, sub_re, sub_im,
      mul_re, mul_im, conj_re, conj_im, pow_two, ofReal_re, ofReal_im]
    ring
  have hnum : R * ‖z-a‖ ≤ ‖(R : ℂ)^2 - conj a * z‖ := by
    apply (sq_le_sq₀ (mul_nonneg hR.le (norm_nonneg _)) (norm_nonneg _)).mp
    nlinarith [mul_nonneg
      (show 0 ≤ R^2 - ‖a‖^2 by nlinarith [norm_nonneg a])
      (show 0 ≤ R^2 - ‖z‖^2 by nlinarith [norm_nonneg z])]
  rw [Complex.canonicalFactor, norm_div, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hR]
  exact (le_div_iff₀ (mul_pos hR (norm_pos_iff.mpr (sub_ne_zero.mpr hza)))).mpr
    (by simpa only [one_mul] using hnum)

end ModifiedCartan
#print axioms ModifiedCartan.harmonic_harnack_48_32
#print axioms ModifiedCartan.norm_canonicalFactor_ge_one
