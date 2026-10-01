import ModifiedCartan.QuarterMeanBound
import ModifiedCartan.QuarterDiskIntegral

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The literal disk submean definition forces the classical Laplacian of
a twice continuously differentiable function to be nonnegative. -/
theorem IsSubharmonicOn.laplacian_nonneg_of_contDiff {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℝ} (hu : IsSubharmonicOn U (fun z => (f z : EReal)))
    (hf : ContDiff ℝ 2 f) (c : ℂ) (hc : c ∈ U) : 0 ≤ Laplacian.laplacian f c := by
  by_contra hnot
  have hneg : Laplacian.laplacian f c < 0 := lt_of_not_ge hnot
  let ε : ℝ := -Laplacian.laplacian f c / 8
  have hε : 0 < ε := by dsimp only [ε]; linarith
  obtain ⟨δ, hδ, hd⟩ := exists_quarter_mean_upper_bound hf c hε
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hc)
  let r : ℝ := min δ R / 2
  have hr : 0 < r := half_pos (lt_min hδ hR)
  have hrδ : r < δ := (half_lt_self (lt_min hδ hR)).trans_le (min_le_left _ _)
  have hrR : r < R := (half_lt_self (lt_min hδ hR)).trans_le (min_le_right _ _)
  have hclosed : closedBall c r ⊆ U := (closedBall_subset_ball hrR).trans hRU
  let q : ℂ → ℝ := fun z =>
    f (c + z) + f (c - z) + f (c + Complex.I * z) + f (c - Complex.I * z) - 4 * f c
  have hq : Continuous q := by
    exact ((((hf.continuous.comp (continuous_const.add continuous_id)).add
      (hf.continuous.comp (continuous_const.sub continuous_id))).add
      (hf.continuous.comp (continuous_const.add (continuous_const.mul continuous_id)))).add
      (hf.continuous.comp (continuous_const.sub (continuous_const.mul continuous_id)))).sub continuous_const
  have hqi : IntegrableOn q (ball (0 : ℂ) r) :=
    (hq.continuousOn.integrableOn_compact (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall
  have hbi : IntegrableOn (fun z : ℂ => ‖z‖ ^ 2 * (Laplacian.laplacian f c + 4 * ε)) (ball 0 r) :=
    (((continuous_norm.pow 2).mul continuous_const).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ℂ) r)).mono_set ball_subset_closedBall
  have hb : (∫ z in ball (0 : ℂ) r, q z) ≤
      ∫ z in ball (0 : ℂ) r, ‖z‖ ^ 2 * (Laplacian.laplacian f c + 4 * ε) := by
    apply integral_mono_ae hqi hbi
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact hd z ((show ‖z‖ < r by simpa only [mem_ball, dist_zero_right] using hz).trans hrδ)
  rw [integral_mul_const] at hb
  have hcoef : Laplacian.laplacian f c + 4 * ε < 0 := by dsimp only [ε]; linarith
  have hnegative := mul_neg_of_pos_of_neg (integral_norm_sq_ball_pos hr) hcoef
  have hm := hu.mul_area_le_integral hr hclosed (EReal.coe_ne_bot _)
  simp only [EReal.toReal_coe] at hm
  have hident := integral_quarter_difference hf.continuous c r
  change (∫ z in ball (0 : ℂ) r, q z) = _ at hident
  rw [hident, complex_ball_real_volume 0 hr.le] at hb
  linarith

end ModifiedCartan
#print axioms ModifiedCartan.IsSubharmonicOn.laplacian_nonneg_of_contDiff
