import ModifiedCartan.PoissonMajorant
import Mathlib.Topology.Order.LeftRightNhds

open scoped Topology
open Filter Set Metric Complex MeromorphicOn
set_option autoImplicit false
namespace ModifiedCartan

theorem log_norm_le_local_poisson_majorant_regular {h : ℂ → ℂ} {R : ℝ}
    (hA : AnalyticOnNhd ℂ h (closedBall 0 R)) {z : ℂ} (hz0 : h z ≠ 0)
    {U : ℂ → ℝ} (hUc : ContinuousOn U (closedBall 0 R))
    (hUp : ∀ w ∈ closedBall (0 : ℂ) R, 0 < U w)
    (hbound : ∀ w ∈ closedBall (0 : ℂ) R, ‖h w‖ ≤ U w) (hz : z ∈ ball 0 R)
    (hboundary : ∀ w ∈ sphere (0 : ℂ) R, h w ≠ 0) :
    Real.log ‖h z‖ ≤ Real.circleAverage (fun w => poissonKernel 0 z w * Real.log (U w)) 0 R := by
  have hAB := hA.mono ball_subset_closedBall
  have hR : 0 < R := pos_of_mem_ball hz
  have hj := FewInflection.poisson_jensen_log_norm hA.meromorphicOn
    (fun w hw => ⟨hA w (sphere_subset_closedBall hw), hboundary w hw⟩)
    hz (hA z (ball_subset_closedBall hz)) hz0
  have hsum : 0 ≤ ∑ᶠ a : ℂ, (divisor h (ball 0 R) a : ℝ) *
      Real.log ‖Complex.canonicalFactor R a z‖ := by
    apply finsum_nonneg
    intro a
    by_cases ha : a ∈ ball (0 : ℂ) R
    · by_cases haz : a = z
      · subst a
        have hd : divisor h (ball 0 R) z = 0 := by
          rw [hAB.meromorphicOn.divisor_apply hz, (hAB z hz).meromorphicOrderAt_eq,
            (hAB z hz).analyticOrderAt_eq_zero.mpr hz0]
          rfl
        simp [hd]
      · exact mul_nonneg (by exact_mod_cast hAB.divisor_nonneg a)
          (Real.log_nonneg (norm_canonicalFactor_ge_one ha hz (Ne.symm haz)))
    · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem (divisor h (ball 0 R)) ha]
  have hsp : sphere (0 : ℂ) |R| ⊆ closedBall 0 R := by
    rw [abs_of_pos hR]
    exact sphere_subset_closedBall
  have hint : CircleIntegrable (fun w => Real.log ‖h w‖) 0 R :=
    (hA.meromorphicOn.mono_set hsp).circleIntegrable_log_norm
  have hUint : CircleIntegrable (fun w => Real.log (U w)) 0 R :=
    ((hUc.log (fun w hw => (hUp w hw).ne')).mono hsp).circleIntegrable'
  have hle := Real.circleAverage_mono
    (hint.continuousOn_smul (continuousOn_poissonKernel_sphere hz))
    (hUint.continuousOn_smul (continuousOn_poissonKernel_sphere hz)) (by
      intro w hw
      have hw' : w ∈ sphere (0 : ℂ) R := by simpa [abs_of_pos hR] using hw
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_log (norm_pos_iff.mpr (hboundary w hw')) (hbound w (hsp hw)))
        (poissonKernel_nonneg_on_sphere hz hw'))
  change Real.circleAverage (fun w => poissonKernel 0 z w * Real.log ‖h w‖) 0 R ≤
    Real.circleAverage (fun w => poissonKernel 0 z w * Real.log (U w)) 0 R at hle
  linarith

theorem continuousOn_local_poisson_majorant_mean {U : ℂ → ℝ} {R : ℝ}
    (hUc : ContinuousOn U (closedBall 0 R))
    (hUp : ∀ w ∈ closedBall (0 : ℂ) R, 0 < U w) (z : ℂ) :
    ContinuousOn (fun s => Real.circleAverage (fun w => poissonKernel 0 z w * Real.log (U w)) 0 s)
      (Ioc ‖z‖ R) := by
  apply Real.ContinuousOn.circleAverage _ (fun s hs => (norm_nonneg z).trans hs.1.le)
  let A : Set ℂ := {w : ℂ | ‖w - 0‖ ∈ Ioc ‖z‖ R}
  have hA : A ⊆ closedBall (0 : ℂ) R := by
    intro w hw
    simpa only [mem_closedBall, dist_zero_right, sub_zero] using hw.2
  have hden : ∀ w ∈ A, w - z ≠ 0 := by
    intro w hw he
    have hw' : ‖z‖ < ‖w‖ := by simpa only [sub_zero] using hw.1
    rw [sub_eq_zero.mp he] at hw'
    exact lt_irrefl _ hw'
  have hk : ContinuousOn (fun w : ℂ => (w + z) / (w - z)) A :=
    (by fun_prop : ContinuousOn (fun w : ℂ => w + z) A).div (by fun_prop) hden
  simpa only [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_def,
    herglotzRieszKernel_def, sub_zero, Pi.mul_def, A] using!
    (Complex.continuous_re.comp_continuousOn hk).mul
      ((hUc.log (fun w hw => (hUp w hw).ne')).mono hA)

/-- Local Poisson majorization, with the exceptional boundary radii removed
by a limit from inside the disk. No global analyticity premise is introduced. -/
theorem log_norm_le_local_poisson_majorant {h : ℂ → ℂ} {R : ℝ}
    (hA : AnalyticOnNhd ℂ h (closedBall 0 R)) {z : ℂ} (hz0 : h z ≠ 0)
    {U : ℂ → ℝ} (hUc : ContinuousOn U (closedBall 0 R))
    (hUp : ∀ w ∈ closedBall (0 : ℂ) R, 0 < U w)
    (hbound : ∀ w ∈ closedBall (0 : ℂ) R, ‖h w‖ ≤ U w) (hz : z ∈ ball 0 R) :
    Real.log ‖h z‖ ≤ Real.circleAverage (fun w => poissonKernel 0 z w * Real.log (U w)) 0 R := by
  have hzn : ‖z‖ < R := by simpa only [mem_ball, dist_zero_right] using hz
  have hzC := ball_subset_closedBall hz
  have hord : meromorphicOrderAt h z = 0 := by
    rw [(hA z hzC).meromorphicOrderAt_eq, (hA z hzC).analyticOrderAt_eq_zero.mpr hz0]
    rfl
  have hfinite : ∀ w ∈ closedBall (0 : ℂ) R, meromorphicOrderAt h w ≠ ⊤ := by
    intro w hw
    exact hA.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall (0 : ℂ) R).isPreconnected hzC hw (by simp [hord])
  have hgood := MeromorphicAt.MeromorphicOn.codiscreteWithin_setOfPred_ne_zero hA.meromorphicOn hfinite
  let Z : Set ℂ := closedBall (0 : ℂ) R \ {w : ℂ | h w ≠ 0}
  have hZ : Z.Finite := (isCompact_closedBall (0 : ℂ) R).finite_sdiff_of_mem_codiscreteWithin hgood
  let E : Set ℝ := (fun w : ℂ => ‖w‖) '' Z
  have hE : E.Finite := hZ.image _
  have havoidNE : ∀ᶠ s in 𝓝[≠] R, s ∉ E := by
    apply nhdsNE_le_cofinite R
    change ∀ᶠ s in cofinite, s ∉ E
    rw [eventually_cofinite]
    convert hE using 1
    ext s
    simp
  have havoid : ∀ᶠ s in 𝓝[<] R, s ∉ E :=
    havoidNE.filter_mono (nhdsWithin_mono R (fun _ hs => ne_of_lt hs))
  have hnear : ∀ᶠ s in 𝓝[<] R, ‖z‖ < s := nhdsWithin_le_nhds (Ioi_mem_nhds hzn)
  have hlimLE := (continuousOn_local_poisson_majorant_mean hUc hUp z).continuousWithinAt
    (show R ∈ Ioc ‖z‖ R from ⟨hzn, le_rfl⟩)
  rw [ContinuousWithinAt, nhdsWithin_Ioc_eq_nhdsLE hzn] at hlimLE
  have hlim := hlimLE.mono_left (nhdsWithin_mono R Iio_subset_Iic_self)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [havoid, hnear, self_mem_nhdsWithin] with s hs hzs hsR
  have hsub : closedBall (0 : ℂ) s ⊆ closedBall 0 R := closedBall_subset_closedBall hsR.le
  apply log_norm_le_local_poisson_majorant_regular (hA.mono hsub) hz0 (hUc.mono hsub)
    (fun w hw => hUp w (hsub hw)) (fun w hw => hbound w (hsub hw))
    (by simpa only [mem_ball, dist_zero_right] using hzs)
  intro w hw hw0
  have hwn : ‖w‖ = s := by simpa only [mem_sphere, dist_zero_right] using hw
  apply hs
  exact ⟨w, ⟨hsub (sphere_subset_closedBall hw), by simpa only [Set.mem_setOf_eq, not_not] using hw0⟩, hwn⟩

end ModifiedCartan
#print axioms ModifiedCartan.log_norm_le_local_poisson_majorant

