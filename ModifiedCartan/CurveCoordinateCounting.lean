import ModifiedCartan.ScalarCurveBounds
import ModifiedCartan.Counting
import ModifiedCartan.ReciprocalRoots
import ModifiedCartan.EntireOrder

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem characteristic_continuous {n : ℕ} (f : Curve n) :
    Continuous (characteristic f) :=
  (Real.Continuous.circleAverage (curve_log_euclideanNorm_continuous f)).sub continuous_const

theorem order_eventually_characteristic_le_rpow {n : ℕ} (f : Curve n) {β : ℝ}
    (hβ : order f < (β : EReal)) :
    ∀ᶠ r : ℝ in atTop, characteristic f r ≤ r ^ β := by
  filter_upwards [eventually_lt_of_limsup_lt hβ, eventually_ge_atTop (2 : ℝ)] with r hr hr2
  have hr0 : 0 < r := by linarith
  have hlog : 0 < Real.log r := Real.log_pos (by linarith)
  have he : Real.log (characteristic f r) / Real.log r < β := by
    dsimp only [logGrowthRatio] at hr
    exact_mod_cast hr
  exact Real.le_rpow_of_log_le hr0 ((div_lt_iff₀ hlog).mp he).le

theorem order_exists_characteristic_power_bound {n : ℕ} (f : Curve n) {β : ℝ}
    (hβ : order f < (β : EReal)) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r → characteristic f r ≤ C * r ^ β := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp (order_eventually_characteristic_le_rpow f hβ)
  let S : ℝ := max 1 R
  have hcont : ContinuousOn (fun r => characteristic f r / r ^ β) (Icc 1 S) := by
    apply (characteristic_continuous f).continuousOn.div
    · intro r hr
      exact (Real.continuousAt_rpow_const r β (Or.inl (by linarith [hr.1]))).continuousWithinAt
    · intro r hr
      exact (Real.rpow_pos_of_pos (by linarith [hr.1]) β).ne'
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hcont
  refine ⟨max 1 B, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro r hr
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  by_cases hrs : r ≤ S
  · exact (div_le_iff₀ (Real.rpow_pos_of_pos hr0 β)).mp
      ((hB (mem_image_of_mem _ ⟨hr, hrs⟩)).trans (le_max_right _ _))
  · exact (hR r ((le_max_right 1 R).trans (le_of_not_ge hrs))).trans
      (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (le_max_left 1 B) (Real.rpow_nonneg hr0.le β))

/-- Jensen comparison for an actual reduced coordinate. This is Step 1
of LaTeX `lem:small-order-coordinates`. -/
theorem coordinate_logCounting_le_characteristic {n : ℕ} (f : Curve n)
    (j : Index n) (hj : f.coord j 0 ≠ 0) {r : ℝ} (hr : 0 < r) :
    ValueDistribution.logCounting (f.coord j) (0 : WithTop ℂ) r ≤
      characteristic f r + Real.log (euclideanNorm (f.vector 0)) - Real.log ‖f.coord j 0‖ := by
  have hb := scalar_circle_log_le_curve_mean f (f.holomorphic j) ⟨0, hj⟩ zero_lt_one
    (fun z => by
      simpa only [one_mul] using!
        (norm_le_pi_norm (f.vector z) j).trans (norm_le_euclideanNorm _)) hr
  rw [FewInflection.logCounting_zero_eq_circleAverage_sub_const_of_entire
    (f.holomorphic j) hr hj]
  simp only [Real.log_one, zero_add] at hb
  unfold characteristic
  linarith

theorem coordinate_logCounting_power_bound {n : ℕ} (f : Curve n)
    (j : Index n) (hj : f.coord j 0 ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ : order f < (β : EReal)) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
      ValueDistribution.logCounting (f.coord j) (0 : WithTop ℂ) r ≤ C * r ^ β := by
  obtain ⟨D, hD, hbound⟩ := order_exists_characteristic_power_bound f hβ
  let E := |Real.log (euclideanNorm (f.vector 0)) - Real.log ‖f.coord j 0‖|
  refine ⟨D + E, by dsimp only [E]; positivity, ?_⟩
  intro r hr
  have hp : 1 ≤ r ^ β := Real.one_le_rpow hr hβ0
  have he : Real.log (euclideanNorm (f.vector 0)) - Real.log ‖f.coord j 0‖ ≤ E :=
    le_abs_self _
  have hE : 0 ≤ E := abs_nonneg _
  have hEp : E ≤ E * r ^ β := by nlinarith
  have hcount := coordinate_logCounting_le_characteristic f j hj (zero_lt_one.trans_le hr)
  have hT := hbound r hr
  nlinarith

theorem coordinate_zeroCount_power_bound {n : ℕ} (f : Curve n)
    (j : Index n) (hj : f.coord j 0 ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ : order f < (β : EReal)) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r → zeroCount (f.coord j) r ≤ C * r ^ β := by
  obtain ⟨D, hD, hbound⟩ := coordinate_logCounting_power_bound f j hj hβ0 hβ
  refine ⟨D * (2 : ℝ) ^ β / Real.log 2,
    div_pos (mul_pos hD (Real.rpow_pos_of_pos (by norm_num) _)) (Real.log_pos (by norm_num)), ?_⟩
  intro r hr
  have hc := Paper.eq_countbound (f.holomorphic j) hr
  have hb := hbound (2 * r) (by linarith)
  have hpow : (2 * r) ^ β = (2 : ℝ) ^ β * r ^ β :=
    Real.mul_rpow (by norm_num) (zero_le_one.trans hr)
  have hdiv := (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr (hc.trans hb)
  exact hdiv.trans_eq (by rw [hpow]; ring)

theorem coordinate_reciprocal_roots_summable {n : ℕ} (f : Curve n)
    (j : Index n) (hj : f.coord j 0 ≠ 0) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hβ : order f < (β : EReal)) :
    Summable (fun a : entireZeroCopies (f.coord j) => ‖a.1‖⁻¹) := by
  obtain ⟨C, hC, hb⟩ := coordinate_zeroCount_power_bound f j hj hβ0 hβ
  exact entire_reciprocal_roots_summable_of_count_bound (f.holomorphic j) hC.le hβ1 hb

end ModifiedCartan
#print axioms ModifiedCartan.coordinate_logCounting_le_characteristic
#print axioms ModifiedCartan.coordinate_reciprocal_roots_summable
