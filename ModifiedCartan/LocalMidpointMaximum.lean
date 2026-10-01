import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem le_max_endpoints_of_strict_midpoint {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1))
    (hstrict : ∀ t ∈ Ioo (0 : ℝ) 1, ∃ x ∈ Icc (0 : ℝ) 1, ∃ y ∈ Icc (0 : ℝ) 1,
      f t < (f x + f y) / 2) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    f t ≤ max (f 0) (f 1) := by
  obtain ⟨m, hm, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr zero_le_one) hf
  apply (isMaxOn_iff.mp hmax t ht).trans
  by_cases hm0 : m = 0
  · rw [hm0]; exact le_max_left _ _
  by_cases hm1 : m = 1
  · rw [hm1]; exact le_max_right _ _
  have hm' : m ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hm.1 (Ne.symm hm0), lt_of_le_of_ne hm.2 hm1⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := hstrict m hm'
  have hx' := isMaxOn_iff.mp hmax x hx
  have hy' := isMaxOn_iff.mp hmax y hy
  linarith

/-- The one-dimensional maximum argument needed to pass from local convexity
along a segment to its full chord inequality. -/
theorem le_chord_of_continuous_local_midpoint {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1))
    (hmid : ∀ t ∈ Ioo (0 : ℝ) 1, ∃ δ : ℝ, 0 < δ ∧
      t - δ ∈ Icc (0 : ℝ) 1 ∧ t + δ ∈ Icc (0 : ℝ) 1 ∧
      f t ≤ (f (t - δ) + f (t + δ)) / 2)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : f t ≤ (1 - t) * f 0 + t * f 1 := by
  by_contra hnot
  have hpos : 0 < f t - ((1 - t) * f 0 + t * f 1) := sub_pos.mpr (lt_of_not_ge hnot)
  let ε := (f t - ((1 - t) * f 0 + t * f 1)) / 2
  have hε : 0 < ε := half_pos hpos
  let F : ℝ → ℝ := fun s => f s - ((1 - s) * f 0 + s * f 1) + ε * s ^ 2
  have hFc : ContinuousOn F (Icc 0 1) :=
    (hf.sub ((continuous_const.sub continuous_id).mul continuous_const |>.add
      (continuous_id.mul continuous_const)).continuousOn).add
      (continuous_const.mul (continuous_id.pow 2)).continuousOn
  have hs : ∀ s ∈ Ioo (0 : ℝ) 1, ∃ x ∈ Icc (0 : ℝ) 1, ∃ y ∈ Icc (0 : ℝ) 1,
      F s < (F x + F y) / 2 := by
    intro s hs
    obtain ⟨δ, hδ, hl, hr, hm⟩ := hmid s hs
    refine ⟨s - δ, hl, s + δ, hr, ?_⟩
    have hp : 0 < ε * δ ^ 2 := by positivity
    dsimp only [F]
    nlinarith
  have hmax := le_max_endpoints_of_strict_midpoint hFc hs ht
  have hF0 : F 0 = 0 := by simp [F]
  have hF1 : F 1 = ε := by simp [F]
  rw [hF0, hF1, max_eq_right hε.le] at hmax
  have hnon : 0 ≤ ε * t ^ 2 := mul_nonneg hε.le (sq_nonneg t)
  dsimp only [F, ε] at hmax hnon hε
  linarith

end ModifiedCartan
#print axioms ModifiedCartan.le_chord_of_continuous_local_midpoint
