import ModifiedCartan.WeakZeroCutoff
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory ContinuousLinearMap
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

def shrinkingWeakBump (ν : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := (((ν + 1 : ℕ) : ℝ)⁻¹) / 2
  rOut := ((ν + 1 : ℕ) : ℝ)⁻¹
  rIn_pos := half_pos (inv_pos.mpr (by positivity))
  rIn_lt_rOut := half_lt_self (inv_pos.mpr (by positivity))

theorem shrinkingWeakBump_tendsto :
    Tendsto (fun ν => (shrinkingWeakBump ν).rOut) atTop (𝓝 0) := by
  have hsucc : StrictMono (fun ν : ℕ => ν + 1) := fun _ _ h => Nat.add_lt_add_right h 1
  exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hsucc.tendsto_atTop)

/-- The precise zero-gradient constancy consequence needed in Step 2 of
`prop:indices`: a weakly constant function on D4 is AE constant on D3.
Proof by compactly supported smoothing and Lebesgue differentiation. -/
theorem HasWeakComplexGradient.exists_ae_const_on_ball_three {u : ℂ → ℝ}
    (hu : HasWeakComplexGradient (ball (0 : ℂ) 4) u (fun _ => 0)) :
    ∃ c : ℝ, u =ᵐ[volume.restrict (ball (0 : ℂ) 3)] (fun _ => c) := by
  let v := weakZeroCutoff u
  have hv : Integrable v := weakZeroCutoff_integrable hu
  have hratio : ∀ ν, (shrinkingWeakBump ν).rOut ≤ 2 * (shrinkingWeakBump ν).rIn := by
    intro ν
    dsimp only [shrinkingWeakBump]
    linarith
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    shrinkingWeakBump_tendsto (Eventually.of_forall hratio) hv.locallyIntegrable
  have hconv : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 3),
      Tendsto (fun ν => ((shrinkingWeakBump ν).normed volume ⋆[lsmul ℝ ℝ, volume] v) z)
        atTop (𝓝 (v z)) := ae_restrict_of_ae hae
  obtain ⟨a, ha, hca⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (isOpen_ball.measure_ne_zero volume (nonempty_ball.mpr (by norm_num : (0 : ℝ) < 3))) hconv
  have hconst : ∀ᶠ ν in atTop, ∃ c : ℝ, ∀ z ∈ ball (0 : ℂ) 3,
      (v ⋆[lsmul ℝ ℝ, volume] (shrinkingWeakBump ν).normed volume) z = c := by
    filter_upwards [shrinkingWeakBump_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))]
      with ν hν
    apply weak_zero_smooth_constant hu (shrinkingWeakBump ν).contDiff_normed
      (shrinkingWeakBump ν).hasCompactSupport_normed
    rw [(shrinkingWeakBump ν).tsupport_normed_eq]
    exact closedBall_subset_closedBall hν.le
  refine ⟨v a, ?_⟩
  filter_upwards [hconv, ae_restrict_mem measurableSet_ball] with z hcz hz
  have heq : ∀ᶠ ν in atTop,
      ((shrinkingWeakBump ν).normed volume ⋆[lsmul ℝ ℝ, volume] v) z =
        ((shrinkingWeakBump ν).normed volume ⋆[lsmul ℝ ℝ, volume] v) a := by
    filter_upwards [hconst] with ν hν
    obtain ⟨c, hc⟩ := hν
    rw [real_convolution_comm ((shrinkingWeakBump ν).normed volume) v, hc z hz, hc a ha]
  have hzv : v z = u z := weakZeroCutoff_eq
    ((ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num : (3 : ℝ) ≤ 7 / 2))) hz)
  change u z = v a
  rw [← hzv]
  exact tendsto_nhds_unique hcz (hca.congr' (Filter.EventuallyEq.symm heq))

theorem HasWeakComplexGradient.exists_ae_const_of_gradient_ae_zero {u : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : HasWeakComplexGradient (ball (0 : ℂ) 4) u g)
    (hg : g =ᵐ[volume.restrict (ball (0 : ℂ) 4)] (fun _ => 0)) :
    ∃ c : ℝ, u =ᵐ[volume.restrict (ball (0 : ℂ) 3)] (fun _ => c) :=
  (hu.of_gradient_ae_zero isOpen_ball hg).exists_ae_const_on_ball_three

end
end ModifiedCartan
#print axioms ModifiedCartan.HasWeakComplexGradient.exists_ae_const_of_gradient_ae_zero
