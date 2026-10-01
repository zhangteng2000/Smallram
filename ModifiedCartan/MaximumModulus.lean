import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Topology.Order.Compact

open scoped Topology Pointwise
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- The literal maximum modulus on the closed disk, used in
LaTeX `lem:entire-majorant`. For an entire function it equals the
maximum on the boundary circle. -/
noncomputable def maximumModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z => ‖f z‖) '' closedBall 0 r)

theorem maximumModulus_attained {f : ℂ → ℂ} (hf : Continuous f)
    {r : ℝ} (hr : 0 ≤ r) :
    ∃ z ∈ closedBall (0 : ℂ) r, maximumModulus f r = ‖f z‖ :=
  (isCompact_closedBall (0 : ℂ) r).exists_sSup_image_eq
    ⟨0, mem_closedBall_self hr⟩ hf.norm.continuousOn

theorem norm_le_maximumModulus {f : ℂ → ℂ} (hf : Continuous f)
    {r : ℝ} {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) r) :
    ‖f z‖ ≤ maximumModulus f r :=
  le_csSup ((isCompact_closedBall (0 : ℂ) r).bddAbove_image hf.norm.continuousOn)
    (mem_image_of_mem _ hz)

theorem maximumModulus_nonneg {f : ℂ → ℂ} (hf : Continuous f)
    {r : ℝ} (hr : 0 ≤ r) : 0 ≤ maximumModulus f r :=
  (norm_nonneg (f 0)).trans (norm_le_maximumModulus hf (mem_closedBall_self hr))

theorem maximumModulus_le {f : ℂ → ℂ} {r M : ℝ} (hr : 0 ≤ r)
    (hM : ∀ z ∈ closedBall (0 : ℂ) r, ‖f z‖ ≤ M) : maximumModulus f r ≤ M := by
  apply csSup_le ⟨‖f 0‖, mem_image_of_mem (fun z => ‖f z‖) (mem_closedBall_self hr)⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hM z hz

theorem maximumModulus_monotoneOn {f : ℂ → ℂ} (hf : Continuous f) :
    MonotoneOn (maximumModulus f) (Ici 0) := by
  intro r hr s _ hrs
  apply maximumModulus_le hr
  intro z hz
  exact norm_le_maximumModulus hf (closedBall_subset_closedBall hrs hz)

theorem maximumModulus_eq_unitDiskSup (f : ℂ → ℂ) {r : ℝ} (hr : 0 ≤ r) :
    maximumModulus f r = sSup ((fun z : ℂ => ‖f (r • z)‖) '' closedBall 0 1) := by
  have hs : (r • closedBall (0 : ℂ) 1) = closedBall (0 : ℂ) r := by
    simpa only [Real.norm_of_nonneg hr] using (smul_unitClosedBall (E := ℂ) r)
  unfold maximumModulus
  rw [← hs, ← image_smul, image_image]

theorem maximumModulus_continuousOn {f : ℂ → ℂ} (hf : Continuous f) :
    ContinuousOn (maximumModulus f) (Ici 0) := by
  have hc : Continuous (fun r : ℝ =>
      sSup ((fun z : ℂ => ‖f (r • z)‖) '' closedBall 0 1)) :=
    (isCompact_closedBall (0 : ℂ) 1).continuous_sSup
      (hf.comp (continuous_fst.smul continuous_snd)).norm
  apply hc.continuousOn.congr
  intro r hr
  exact maximumModulus_eq_unitDiskSup f hr

theorem maximumModulus_attained_on_sphere {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {r : ℝ} (hr : 0 < r) :
    ∃ z ∈ sphere (0 : ℂ) r, maximumModulus f r = ‖f z‖ := by
  obtain ⟨z, hz, hmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm
    (U := ball (0 : ℂ) r) isBounded_ball ⟨0, mem_ball_self hr⟩ hf.diffContOnCl
  rw [frontier_ball (0 : ℂ) hr.ne'] at hz
  rw [closure_ball (0 : ℂ) hr.ne'] at hmax
  refine ⟨z, hz, le_antisymm (maximumModulus_le hr.le ?_)
    (norm_le_maximumModulus hf.continuous (sphere_subset_closedBall hz))⟩
  intro w hw
  exact hmax hw

theorem maximumModulus_eq_sphereSup {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {r : ℝ} (hr : 0 < r) :
    maximumModulus f r = sSup ((fun z => ‖f z‖) '' sphere (0 : ℂ) r) := by
  obtain ⟨z, hz, he⟩ := maximumModulus_attained_on_sphere hf hr
  apply le_antisymm
  · rw [he]
    exact le_csSup ((isCompact_sphere (0 : ℂ) r).bddAbove_image hf.continuous.norm.continuousOn)
      (mem_image_of_mem _ hz)
  · apply csSup_le ⟨‖f z‖, mem_image_of_mem (fun w => ‖f w‖) hz⟩
    rintro _ ⟨w, hw, rfl⟩
    exact norm_le_maximumModulus hf.continuous (sphere_subset_closedBall hw)

end ModifiedCartan
#print axioms ModifiedCartan.maximumModulus_continuousOn
#print axioms ModifiedCartan.maximumModulus_eq_sphereSup
