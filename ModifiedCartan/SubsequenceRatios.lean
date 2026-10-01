import ModifiedCartan.MonotoneWeightedIntegrals
import ModifiedCartan.ArbitraryRadiusConstruction

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem ArbitraryRadiusLimitData.ratio_tendsto_circle_constant
    {n : ℕ} {f : Curve n} {r : ℕ → ℝ} {ρ : ℝ}
    (hρ : 0 < ρ) (d : ArbitraryRadiusLimitData f r ρ)
    (hr : Tendsto r atTop atTop) {t : ℝ} (ht : 0 < t) (ht2 : t < 2) :
    Tendsto (fun ν => characteristic f (t * r (d.subseq ν)) /
      characteristic f (r (d.subseq ν))) atTop
      (𝓝 (Real.circleAverage (fun z => (d.U z).toReal) 0 1 * t ^ ρ)) := by
  apply tendsto_of_monotone_weighted_integrals
    (B := 2) (g := fun t => Real.circleAverage (fun z => (d.U z).toReal) 0 1 * t ^ ρ)
    (F := fun ν t => characteristic f (t * r (d.subseq ν)) / characteristic f (r (d.subseq ν)))
    ?_ ?_ ?_ ?_ t ht ht2
  · exact Eventually.of_forall (fun ν =>
      (((characteristic_continuous f).comp (continuous_id.mul continuous_const)).div_const _).continuousOn)
  · filter_upwards [(hr.comp d.strictMono.tendsto_atTop).eventually_gt_atTop 0] with ν hrν
    intro a ha b hb hab
    exact div_le_div_of_nonneg_right
      (characteristic_monotoneOn f (mul_pos ha.1 hrν) (mul_pos hb.1 hrν)
        (mul_le_mul_of_nonneg_right hab hrν.le)) (d.scale_pos ν).le
  · exact (continuous_const.mul (Real.continuous_rpow_const hρ.le)).continuousOn
  · intro a b ha hab hb
    have he : (∫ t in a..b, t * (Real.circleAverage (fun z => (d.U z).toReal) 0 1 * t ^ ρ)) =
        Real.circleAverage (fun z => (d.U z).toReal) 0 1 * ∫ t in a..b, t * t ^ ρ := by
      have hf : (fun t : ℝ => t * (Real.circleAverage (fun z => (d.U z).toReal) 0 1 * t ^ ρ)) = (fun t => Real.circleAverage (fun z => (d.U z).toReal) 0 1 * (t * t ^ ρ)) := by
        funext t
        ring
      rw [hf]
      rw [intervalIntegral.integral_const_mul]
    rw [he]
    exact d.annular_ratio_tendsto hρ ha hab hb

theorem ArbitraryRadiusLimitData.circleAverage_one
    {n : ℕ} {f : Curve n} {r : ℕ → ℝ} {ρ : ℝ}
    (hρ : 0 < ρ) (d : ArbitraryRadiusLimitData f r ρ) (hr : Tendsto r atTop atTop) :
    Real.circleAverage (fun z => (d.U z).toReal) 0 1 = 1 := by
  have h := d.ratio_tendsto_circle_constant hρ hr (t := 1) (by norm_num) (by norm_num)
  have he : (fun ν => characteristic f (1 * r (d.subseq ν)) /
      characteristic f (r (d.subseq ν))) = (fun _ : ℕ => (1 : ℝ)) := by
    funext ν
    simp only [one_mul, div_self (d.scale_pos ν).ne']
  rw [he, Real.one_rpow, mul_one] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- LaTeX `prop:regular-variation`: the identified subsequence ratio on (0,2). -/
theorem ArbitraryRadiusLimitData.ratio_tendsto
    {n : ℕ} {f : Curve n} {r : ℕ → ℝ} {ρ : ℝ}
    (hρ : 0 < ρ) (d : ArbitraryRadiusLimitData f r ρ)
    (hr : Tendsto r atTop atTop) {t : ℝ} (ht : 0 < t) (ht2 : t < 2) :
    Tendsto (fun ν => characteristic f (t * r (d.subseq ν)) /
      characteristic f (r (d.subseq ν))) atTop (𝓝 (t ^ ρ)) := by
  have h := d.ratio_tendsto_circle_constant hρ hr ht ht2
  rwa [d.circleAverage_one hρ hr, one_mul] at h

/-- LaTeX `prop:regular-variation`: the original curve, without selecting radii. -/
theorem characteristic_ratio_tendsto_of_lt_two {n : ℕ} (f : Curve n)
    (htrans : f.Transcendental) (hlin : f.linearlyNonDegenerate)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 0 < ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {t : ℝ} (ht : 0 < t) (ht2 : t < 2) :
    Tendsto (fun r => characteristic f (t * r) / characteristic f r) atTop (𝓝 (t ^ ρ)) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro r hr
  obtain ⟨B, hB, hnorm, ⟨d⟩⟩ := Paper.exists_arbitrary_radius_limits f hlin htrans hsmall hρ hl hu hr
  refine ⟨d.subseq, ?_⟩
  have h := d.ratio_tendsto hρ hr ht ht2
  rwa [characteristic_matrixGauge_of_euclidean_isometry f B hB hnorm] at h

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.ratio_tendsto
#print axioms ModifiedCartan.characteristic_ratio_tendsto_of_lt_two

