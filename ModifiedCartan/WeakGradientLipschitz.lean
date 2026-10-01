import ModifiedCartan.WeakGradientSmoothBound
import ModifiedCartan.WeakGradientConstancy

open scoped Topology ContDiff Convolution NNReal
open Filter Set Metric MeasureTheory ContinuousLinearMap
set_option autoImplicit false
namespace ModifiedCartan

/-- A bounded weak gradient supplies a Lipschitz representative on each
strictly smaller disk. This is proved by smoothing and a Lipschitz extension. -/
theorem HasWeakComplexGradient.exists_lipschitz_rep_on_ball
    {U : Set ℂ} {u : ℂ → ℝ} {g : ℂ → ℂ} (hu : HasWeakComplexGradient U u g)
    {c : ℂ} {r R : ℝ} (hrR : r < R) (hball : closedBall c R ⊆ U)
    {C : ℝ≥0} (hg : ∀ᵐ z ∂volume.restrict U, ‖g z‖ ≤ (C : ℝ)) :
    ∃ v : ℂ → ℝ, LipschitzWith C v ∧
      u =ᵐ[volume.restrict (ball c r)] v := by
  classical
  let w : ℂ → ℝ := (closedBall c R).indicator u
  have hw : Integrable w :=
    (hu.function_integrable _ (isCompact_closedBall c R) hball).integrable_indicator
      measurableSet_closedBall
  have hu' : HasWeakComplexGradient (ball c R) u g := hu.restrict (ball_subset_closedBall.trans hball)
  have hw_eq : EqOn w u (ball c R) := fun z hz => indicator_of_mem (ball_subset_closedBall hz) u
  have hg' : ∀ᵐ z ∂volume.restrict (ball c R), ‖g z‖ ≤ (C : ℝ) :=
    hg.filter_mono (ae_mono (Measure.restrict_mono_set _ (ball_subset_closedBall.trans hball)))
  let F : ℕ → ℂ → ℝ := fun ν => w ⋆[lsmul ℝ ℝ, volume] (shrinkingWeakBump ν).normed volume
  have hF : ∀ᶠ ν in atTop, LipschitzOnWith C (F ν) (ball c r) := by
    filter_upwards [shrinkingWeakBump_tendsto.eventually (gt_mem_nhds (sub_pos.mpr hrR))]
      with ν hν
    apply (convex_ball c r).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    · intro x _
      exact ((shrinkingWeakBump ν).hasCompactSupport_normed.hasFDerivAt_convolution_right
        (lsmul ℝ ℝ) hw.locallyIntegrable
        (shrinkingWeakBump ν).contDiff_normed x).differentiableAt
    · intro x hx
      change ‖fderiv ℝ (F ν) x‖ ≤ (C : ℝ)
      apply hu'.norm_fderiv_convolution_le isOpen_ball hw.locallyIntegrable hw_eq
        (shrinkingWeakBump ν).contDiff_normed (shrinkingWeakBump ν).hasCompactSupport_normed
        (shrinkingWeakBump ν).nonneg_normed (shrinkingWeakBump ν).integral_normed
        C.coe_nonneg hg' x
      intro z hz
      have hsmall : dist (x - z) 0 ≤ (shrinkingWeakBump ν).rOut := by
        rw [(shrinkingWeakBump ν).tsupport_normed_eq] at hz
        exact hz
      have hdist : dist z c ≤ dist x c + dist (x - z) 0 := by
        simpa only [dist_zero_right, dist_eq_norm, norm_sub_rev, sub_zero, add_comm] using dist_triangle z x c
      exact mem_ball.mpr (by linarith [mem_ball.mp hx])
  have hratio : ∀ ν, (shrinkingWeakBump ν).rOut ≤ 2 * (shrinkingWeakBump ν).rIn := by
    intro ν
    dsimp only [shrinkingWeakBump]
    linarith
  have hconv := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    shrinkingWeakBump_tendsto (Eventually.of_forall hratio) hw.locallyIntegrable
  have hlim : ∀ᵐ z ∂volume.restrict (ball c r), Tendsto (fun ν => F ν z) atTop (𝓝 (u z)) := by
    filter_upwards [ae_restrict_of_ae hconv, ae_restrict_mem measurableSet_ball] with z hz hzball
    have hwz : w z = u z := indicator_of_mem
      ((ball_subset_closedBall.trans (closedBall_subset_closedBall hrR.le)) hzball) u
    simpa only [F, real_convolution_comm w, hwz] using hz
  let S : Set ℂ := {z | z ∈ ball c r ∧ Tendsto (fun ν => F ν z) atTop (𝓝 (u z))}
  have hS : ∀ᵐ z ∂volume.restrict (ball c r), z ∈ S := by
    filter_upwards [hlim, ae_restrict_mem measurableSet_ball] with z hz hzball
    exact ⟨hzball, hz⟩
  have hLip : LipschitzOnWith C u S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    apply le_of_tendsto (hx.2.dist hy.2)
    filter_upwards [hF] with ν hν
    exact hν.dist_le_mul x hx.1 y hy.1
  obtain ⟨v, hv, heq⟩ := hLip.extend_real
  exact ⟨v, hv, hS.mono (fun z hz => heq hz)⟩

end ModifiedCartan
#print axioms ModifiedCartan.HasWeakComplexGradient.exists_lipschitz_rep_on_ball
