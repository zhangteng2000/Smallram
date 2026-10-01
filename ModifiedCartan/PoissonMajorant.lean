import ModifiedCartan.HarmonicBounds
import FewInflection.Nevanlinna.PoissonJensen
import Mathlib.Analysis.Analytic.Order

open scoped Topology BigOperators
open Filter Set Metric Complex MeromorphicOn
set_option autoImplicit false
namespace ModifiedCartan

theorem poissonKernel_nonneg_on_sphere {R : ℝ} {z w : ℂ}
    (hz : z ∈ ball 0 R) (hw : w ∈ sphere 0 R) : 0 ≤ poissonKernel 0 z w := by
  have hnz : ‖z‖ < R := by simpa only [mem_ball, dist_zero_right] using hz
  have hnw : ‖w‖ = R := by simpa only [mem_sphere, dist_zero_right] using hw
  simp only [poissonKernel_def, sub_zero, hnw]
  apply div_nonneg _ (sq_nonneg _)
  nlinarith [norm_nonneg z]

theorem continuousOn_poissonKernel_sphere {R : ℝ} {z : ℂ} (hz : z ∈ ball 0 R) :
    ContinuousOn (poissonKernel 0 z) (sphere 0 |R|) := by
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  exact Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hz)

theorem log_norm_le_poisson_log_majorant_regular
    {h : ℂ → ℂ} (hh : Differentiable ℂ h) {z : ℂ} (hz0 : h z ≠ 0)
    {U : ℂ → ℝ} (hUc : Continuous U) (hUp : ∀ w, 0 < U w)
    (hbound : ∀ w, ‖h w‖ ≤ U w) {R : ℝ} (hz : z ∈ ball 0 R)
    (hboundary : ∀ w ∈ sphere (0 : ℂ) R, h w ≠ 0) :
    Real.log ‖h z‖ ≤ Real.circleAverage (fun w => poissonKernel 0 z w * Real.log (U w)) 0 R := by
  have hA := Complex.analyticOnNhd_univ_iff_differentiable.mpr hh
  have hAB := hA.mono (subset_univ (ball (0 : ℂ) R))
  have hR : 0 < R := pos_of_mem_ball hz
  have hj := FewInflection.poisson_jensen_log_norm
    (hA.meromorphicOn.mono_set (subset_univ (closedBall (0 : ℂ) R)))
    (fun w hw => ⟨hA w (mem_univ _), hboundary w hw⟩) hz (hA z (mem_univ _)) hz0
  have hsum : 0 ≤ ∑ᶠ a : ℂ, (divisor h (ball 0 R) a : ℝ) *
      Real.log ‖Complex.canonicalFactor R a z‖ := by
    apply finsum_nonneg
    intro a
    by_cases ha : a ∈ ball (0 : ℂ) R
    · by_cases haz : a = z
      · subst a
        have hd : divisor h (ball 0 R) z = 0 := by
          rw [hAB.meromorphicOn.divisor_apply hz, (hA z (mem_univ _)).meromorphicOrderAt_eq,
            (hA z (mem_univ _)).analyticOrderAt_eq_zero.mpr hz0]
          rfl
        simp [hd]
      · exact mul_nonneg (by exact_mod_cast hAB.divisor_nonneg a)
          (Real.log_nonneg (norm_canonicalFactor_ge_one ha hz (Ne.symm haz)))
    · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem (divisor h (ball 0 R)) ha]
  have hint : CircleIntegrable (fun w => Real.log ‖h w‖) 0 R :=
    (hA.meromorphicOn.mono_set (subset_univ (sphere (0 : ℂ) |R|))).circleIntegrable_log_norm
  have hUint : CircleIntegrable (fun w => Real.log (U w)) 0 R :=
    (hUc.log (fun w => (hUp w).ne')).continuousOn.circleIntegrable'
  have hle := Real.circleAverage_mono
    (hint.continuousOn_smul (continuousOn_poissonKernel_sphere hz))
    (hUint.continuousOn_smul (continuousOn_poissonKernel_sphere hz)) (by
      intro w hw
      have hw' : w ∈ sphere (0 : ℂ) R := by simpa [abs_of_pos hR] using hw
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_log (norm_pos_iff.mpr (hboundary w hw')) (hbound w))
        (poissonKernel_nonneg_on_sphere hz hw'))
  change Real.circleAverage (fun w => poissonKernel 0 z w * Real.log ‖h w‖) 0 R ≤
    Real.circleAverage (fun w => poissonKernel 0 z w * Real.log (U w)) 0 R at hle
  linarith

theorem continuous_poisson_log_majorant_mean {U : ℂ → ℝ}
    (hUc : Continuous U) (hUp : ∀ w, 0 < U w) (z : ℂ) :
    ContinuousOn (fun R => Real.circleAverage (fun w => poissonKernel 0 z w * Real.log (U w)) 0 R)
      (Ioi ‖z‖) := by
  apply Real.ContinuousOn.circleAverage _ (fun r hr => (norm_nonneg z).trans hr.le)
  have hden : ∀ w ∈ {w : ℂ | ‖w - 0‖ ∈ Ioi ‖z‖}, w - z ≠ 0 := by
    intro w hw heq
    have hw' : ‖z‖ < ‖w‖ := by simpa using hw
    have he : w = z := sub_eq_zero.mp heq
    rw [he] at hw'
    exact lt_irrefl _ hw'
  have hk : ContinuousOn (fun w : ℂ => (w + z) / (w - z))
      {w : ℂ | ‖w - 0‖ ∈ Ioi ‖z‖} :=
    (by fun_prop : ContinuousOn (fun w : ℂ => w + z) _).div (by fun_prop) hden
  simpa only [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_def, Pi.mul_apply,
    herglotzRieszKernel_def, sub_zero] using!
    (Complex.continuous_re.comp_continuousOn hk).mul
      (hUc.log (fun w => (hUp w).ne')).continuousOn

/-- Scalar Poisson majorization for an entire function, with no regular-boundary
assumption. Finite boundary zero radii are removed before passing to the limit. -/
theorem log_norm_le_poisson_log_majorant
    {h : ℂ → ℂ} (hh : Differentiable ℂ h) {z : ℂ} (hz0 : h z ≠ 0)
    {U : ℂ → ℝ} (hUc : Continuous U) (hUp : ∀ w, 0 < U w)
    (hbound : ∀ w, ‖h w‖ ≤ U w) {R : ℝ} (hz : z ∈ ball 0 R) :
    Real.log ‖h z‖ ≤ Real.circleAverage (fun w => poissonKernel 0 z w * Real.log (U w)) 0 R := by
  have hA := Complex.analyticOnNhd_univ_iff_differentiable.mpr hh
  have hzn : ‖z‖ < R := by simpa only [mem_ball, dist_zero_right] using hz
  let Z : Set ℂ := {w | w ∈ closedBall (0 : ℂ) (R + 1) ∧ h w = 0}
  have hZ : Z.Finite := by
    have hn : ∀ᶠ w in codiscrete ℂ, h w ≠ 0 := hA.preimage_zero_mem_codiscrete hz0
    have hc : h ⁻¹' {0}ᶜ ∈ codiscreteWithin (closedBall (0 : ℂ) (R + 1)) :=
      hn.filter_mono (Filter.codiscreteWithin_mono (subset_univ _))
    convert (isCompact_closedBall (0 : ℂ) (R + 1)).finite_sdiff_of_mem_codiscreteWithin hc using 1
    ext w
    simp [Z]
  let E : Set ℝ := (fun w : ℂ => ‖w‖) '' Z
  have hE : E.Finite := hZ.image _
  have havoid : ∀ᶠ r in 𝓝[≠] R, r ∉ E := by
    apply (nhdsNE_le_cofinite R)
    change ∀ᶠ r in cofinite, r ∉ E
    rw [eventually_cofinite]
    convert hE using 1
    ext r
    simp
  have hnear : ∀ᶠ r in 𝓝[≠] R, ‖z‖ < r ∧ r < R + 1 :=
    nhdsWithin_le_nhds (Ioo_mem_nhds hzn (show R < R + 1 by linarith))
  have hlim : Tendsto (fun r => Real.circleAverage
      (fun w => poissonKernel 0 z w * Real.log (U w)) 0 r) (𝓝[≠] R)
      (𝓝 (Real.circleAverage (fun w => poissonKernel 0 z w * Real.log (U w)) 0 R)) :=
    ((continuous_poisson_log_majorant_mean hUc hUp z).continuousAt
      (isOpen_Ioi.mem_nhds hzn)).tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [havoid, hnear] with r hr hnr
  apply log_norm_le_poisson_log_majorant_regular hh hz0 hUc hUp hbound
    (by simpa only [mem_ball, dist_zero_right] using hnr.1)
  intro w hw hwzero
  have hwn : ‖w‖ = r := by simpa only [mem_sphere, dist_zero_right] using hw
  apply hr
  exact ⟨w, ⟨by simpa only [mem_closedBall, dist_zero_right, hwn] using hnr.2.le, hwzero⟩, hwn⟩

end ModifiedCartan
#print axioms ModifiedCartan.log_norm_le_poisson_log_majorant
