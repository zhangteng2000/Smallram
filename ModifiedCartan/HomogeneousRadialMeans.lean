import ModifiedCartan.Homogeneity
import ModifiedCartan.LogAreaJensen

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Circular means of the actual fixed limit inherit `eq:homogeneity`. -/
theorem ArbitraryRadiusLimitData.circleAverage_homogeneous
    {n : ℕ} {f : Curve n} {r : ℕ → ℝ} {ρ : ℝ}
    (hρ : 0 < ρ) (d : ArbitraryRadiusLimitData f r ρ)
    {t : ℝ} (ht : 0 < t) (ht2 : t < 2) :
    Real.circleAverage (fun z => (d.U z).toReal) 0 t =
      t ^ ρ * Real.circleAverage (fun z => (d.U z).toReal) 0 1 := by
  have he (θ : ℝ) : (d.U (circleMap 0 t θ)).toReal =
      t ^ ρ * (d.U (circleMap 0 1 θ)).toReal := by
    have hmap : circleMap 0 t θ = (t : ℂ) * circleMap 0 1 θ := by simp [circleMap]
    have h1 : circleMap 0 1 θ ∈ ball (0 : ℂ) 2 := by
      simp only [mem_ball, dist_zero_right, norm_circleMap_zero]
      norm_num
    have htmem : (t : ℂ) * circleMap 0 1 θ ∈ ball (0 : ℂ) 2 := by
      rw [← hmap, mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos ht]
      exact ht2
    have hh := congrArg EReal.toReal (Paper.prop_homogeneity hρ d ht h1 htmem)
    simpa only [← hmap, EReal.toReal_mul, EReal.toReal_coe] using hh
  have hi : (∫ θ in (0 : ℝ)..2 * Real.pi, (d.U (circleMap 0 t θ)).toReal) =
      t ^ ρ * ∫ θ in (0 : ℝ)..2 * Real.pi, (d.U (circleMap 0 1 θ)).toReal := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun θ _ => he θ)
  simp only [Real.circleAverage_def, smul_eq_mul, hi]
  ring

/-- The polar identity for the actual continuous representative, without
assuming global measurability outside the disk where it is used. -/
theorem integral_ball_eq_radial_mean_of_continuousOn
    {F : ℂ → ℝ} {g : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hF : ContinuousOn F (closedBall (0 : ℂ) R))
    (hmean : ∀ t : ℝ, 0 < t → t < R → Real.circleAverage F 0 t = g t) :
    (∫ z in ball (0 : ℂ) R, F z) =
      2 * Real.pi * ∫ t in (0 : ℝ)..R, t * g t := by
  classical
  let H : ℂ → ℝ := (closedBall (0 : ℂ) R).piecewise F (fun _ => 0)
  have hm : Measurable H := hF.measurable_piecewise continuousOn_const measurableSet_closedBall
  have he : EqOn H F (closedBall (0 : ℂ) R) := fun _ hz => piecewise_eq_of_mem _ _ _ hz
  have hiF : IntegrableOn F (ball (0 : ℂ) R) :=
    (hF.integrableOn_compact (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
  have hiH : IntegrableOn H (ball (0 : ℂ) R) :=
    hiF.congr_fun (fun z hz => (he (ball_subset_closedBall hz)).symm) measurableSet_ball
  have hleft : (∫ z in ball (0 : ℂ) R, F z) = ∫ z in ball (0 : ℂ) R, H z :=
    setIntegral_congr_fun measurableSet_ball (fun z hz => (he (ball_subset_closedBall hz)).symm)
  rw [hleft, integral_ball_eq_circleAverage hm hiH, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hR.le]
  calc
    (∫ t in (0 : ℝ)..R, t * (2 * Real.pi * Real.circleAverage H 0 t)) =
        ∫ t in (0 : ℝ)..R, (2 * Real.pi) * (t * g t) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hR.le
      intro t ht
      have hcircle : Real.circleAverage H 0 t = Real.circleAverage F 0 t := by
        apply Real.circleAverage_congr_sphere
        intro z hz
        apply he
        rw [abs_of_pos ht.1] at hz
        exact (sphere_subset_closedBall.trans (closedBall_subset_closedBall ht.2.le)) hz
      dsimp only
      rw [hcircle, hmean t ht.1 ht.2]
      ring
    _ = _ := intervalIntegral.integral_const_mul _ _

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.circleAverage_homogeneous
#print axioms ModifiedCartan.integral_ball_eq_radial_mean_of_continuousOn

