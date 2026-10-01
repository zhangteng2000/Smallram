import ModifiedCartan.DiskCharacteristic
import Mathlib.Order.Interval.Set.Infinite

open scoped Topology
open Filter Set Metric MeromorphicOn
set_option autoImplicit false
namespace ModifiedCartan

theorem disk_meromorphic_order_ne_top {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : MeromorphicOn f (closedBall 0 R)) (hfa : AnalyticAt ℂ f 0) (h0 : f 0 ≠ 0) :
    ∀ w ∈ closedBall (0 : ℂ) R, meromorphicOrderAt f w ≠ ⊤ := by
  have horder : meromorphicOrderAt f 0 = 0 := by
    rw [hfa.meromorphicOrderAt_eq, hfa.analyticOrderAt_eq_zero.mpr h0]
    rfl
  intro w hw
  exact hf.meromorphicOrderAt_ne_top_of_isPreconnected
    (convex_closedBall (0 : ℂ) R).isPreconnected
    (mem_closedBall_self hR.le) hw (by simp [horder])

/-- The exceptional boundary radii are chosen internally, including any discrete
modifications of the given meromorphic function. A dependency of LaTeX `lem:NH`. -/
theorem exists_regular_radius_between {f : ℂ → ℂ} {a b R : ℝ}
    (ha : 0 < a) (hab : a < b) (hbR : b ≤ R)
    (hf : MeromorphicOn f (closedBall 0 R)) (hfa : AnalyticAt ℂ f 0) (h0 : f 0 ≠ 0) :
    ∃ s : ℝ, a < s ∧ s < b ∧
      ∀ z ∈ sphere (0 : ℂ) s, AnalyticAt ℂ f z ∧ f z ≠ 0 := by
  have hR : 0 < R := (ha.trans hab).trans_le hbR
  let G : Set ℂ := {z | AnalyticAt ℂ f z ∧ f z ≠ 0}
  have hG : G ∈ codiscreteWithin (closedBall (0 : ℂ) R) := by
    filter_upwards [hf.analyticAt_mem_codiscreteWithin,
      MeromorphicAt.MeromorphicOn.codiscreteWithin_setOfPred_ne_zero hf (disk_meromorphic_order_ne_top hR hf hfa h0)] with z hz hz0
    exact ⟨hz, hz0⟩
  have hbad : (closedBall (0 : ℂ) R \ G).Finite :=
    (isCompact_closedBall (0 : ℂ) R).finite_sdiff_of_mem_codiscreteWithin hG
  obtain ⟨s, hs, he⟩ := (Set.Ioo_infinite hab).exists_notMem_finite (hbad.image (fun z : ℂ => ‖z‖))
  refine ⟨s, hs.1, hs.2, fun z hz => ?_⟩
  have hn : ‖z‖ = s := by simpa only [mem_sphere, dist_zero_right] using hz
  have hzR : z ∈ closedBall (0 : ℂ) R := by
    simpa only [mem_closedBall, dist_zero_right, hn] using hs.2.le.trans hbR
  by_contra hzg
  exact he ⟨z, ⟨hzR, hzg⟩, hn⟩

end ModifiedCartan
#print axioms ModifiedCartan.exists_regular_radius_between

