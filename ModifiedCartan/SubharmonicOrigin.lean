import ModifiedCartan.DiskAverages
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The submean step of LaTeX `eq:origin-bound`. A nonnegative
subharmonic function inherits a positive power bound from concentric
disk means, including its value at zero. -/
theorem subharmonic_origin_bound_of_disk_means {U : ℂ → EReal} {v : ℂ → ℝ} {C a : ℝ}
    (hU : IsSubharmonicOn (ball (0 : ℂ) 4) U)
    (hrep : U =ᵐ[volume.restrict (ball (0 : ℂ) 4)] (fun z => (v z : EReal)))
    (hpos : ∀ z ∈ ball (0 : ℂ) 4, 0 ≤ U z)
    (hv : ∀ K, IsCompact K → K ⊆ ball (0 : ℂ) 4 → IntegrableOn v K)
    (hC : 0 < C) (ha : 0 < a)
    (hmean : ∀ R : ℝ, 0 < R → R < 1 → diskAverage R v 0 ≤ C * R ^ a) :
    U 0 = 0 ∧ ∀ z ∈ ball (0 : ℂ) (1 / 4),
      0 ≤ U z ∧ U z ≤ ((4 * C * (2 : ℝ) ^ a * ‖z‖ ^ a : ℝ) : EReal) := by
  have h0 : (0 : ℂ) ∈ ball 0 4 := mem_ball_self (by norm_num)
  have hbot : U 0 ≠ ⊥ := by
    intro hb
    have hh := hpos 0 h0
    simp only [hb, le_bot_iff] at hh
    exact EReal.zero_ne_bot hh
  have h0coe : U 0 = ((U 0).toReal : EReal) := (EReal.coe_toReal (hU.ne_top 0 h0) hbot).symm
  have h0bound (R : ℝ) (hR : 0 < R) (hR1 : R < 1) : (U 0).toReal ≤ C * R ^ a := by
    have hh := hU.le_diskAverage_of_ae_eq hrep hR
      (closedBall_subset_ball (hR1.trans (by norm_num : (1 : ℝ) < 4)))
    rw [← diskAverage_eq hR.le, h0coe, EReal.coe_le_coe_iff] at hh
    exact hh.trans (hmean R hR hR1)
  have hlimit : Tendsto (fun R : ℝ => C * R ^ a) (𝓝[>] 0) (𝓝 0) := by
    have hh := (Real.continuous_rpow_const ha.le).continuousAt.tendsto (x := (0 : ℝ))
    simpa only [Real.zero_rpow ha.ne', mul_zero] using
      (hh.mono_left nhdsWithin_le_nhds).const_mul C
  have h0le : (U 0).toReal ≤ 0 := ge_of_tendsto hlimit (by
    filter_upwards [self_mem_nhdsWithin,
      (gt_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with R hR hR1
    exact h0bound R hR hR1)
  have hzero : U 0 = 0 := le_antisymm (by
    rw [h0coe]
    exact_mod_cast h0le) (hpos 0 h0)
  refine ⟨hzero, ?_⟩
  intro z hz
  have hzN : ‖z‖ < 1 / 4 := by simpa only [mem_ball, dist_zero_right] using hz
  have hz4 : z ∈ ball (0 : ℂ) 4 := (ball_subset_ball (by norm_num : (1 / 4 : ℝ) ≤ 4)) hz
  refine ⟨hpos z hz4, ?_⟩
  by_cases hz0 : z = 0
  · simp only [hz0, hzero, norm_zero, Real.zero_rpow ha.ne', mul_zero, EReal.coe_zero, le_refl]
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have h2r : 0 < 2 * ‖z‖ := by positivity
  have h2r1 : 2 * ‖z‖ < 1 := by linarith
  have hbig : closedBall (0 : ℂ) (2 * ‖z‖) ⊆ ball 0 4 :=
    closedBall_subset_ball (by linarith)
  have hsmall : closedBall z ‖z‖ ⊆ ball (0 : ℂ) 4 :=
    closedBall_subset_ball' (by simp only [dist_zero_right]; linarith)
  have hsubset : ball z ‖z‖ ⊆ ball (0 : ℂ) (2 * ‖z‖) :=
    ball_subset_ball' (by simp only [dist_zero_right]; linarith)
  have hi : IntegrableOn v (ball (0 : ℂ) (2 * ‖z‖)) :=
    (hv _ (isCompact_closedBall _ _) hbig).mono_set ball_subset_closedBall
  have hnonneg : 0 ≤ᵐ[volume.restrict (ball (0 : ℂ) (2 * ‖z‖))] v := by
    filter_upwards [hrep.filter_mono (ae_mono (Measure.restrict_mono_set _
      (ball_subset_closedBall.trans hbig))), ae_restrict_mem measurableSet_ball] with w hw hwB
    have hh := hpos w (hbig (ball_subset_closedBall hwB))
    rw [hw] at hh
    exact_mod_cast hh
  have hIntegral := setIntegral_mono_set hi hnonneg (Eventually.of_forall hsubset)
  have harea : 0 < Real.pi * ‖z‖ ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hr)
  have hcomp : (Real.pi * ‖z‖ ^ 2)⁻¹ * (∫ w in ball z ‖z‖, v w) ≤
      4 * diskAverage (2 * ‖z‖) v 0 := by
    calc
      _ ≤ (Real.pi * ‖z‖ ^ 2)⁻¹ * (∫ w in ball (0 : ℂ) (2 * ‖z‖), v w) :=
        mul_le_mul_of_nonneg_left hIntegral (inv_pos.mpr harea).le
      _ = _ := by rw [diskAverage_eq h2r.le]; field_simp; ring
  have hfinal : (Real.pi * ‖z‖ ^ 2)⁻¹ * (∫ w in ball z ‖z‖, v w) ≤
      4 * C * (2 : ℝ) ^ a * ‖z‖ ^ a := by
    calc
      _ ≤ 4 * (C * (2 * ‖z‖) ^ a) := hcomp.trans
        (mul_le_mul_of_nonneg_left (hmean _ h2r h2r1) (by norm_num))
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr.le]; ring
  exact (hU.le_diskAverage_of_ae_eq hrep hr hsmall).trans (EReal.coe_le_coe_iff.mpr hfinal)

end ModifiedCartan
#print axioms ModifiedCartan.subharmonic_origin_bound_of_disk_means
