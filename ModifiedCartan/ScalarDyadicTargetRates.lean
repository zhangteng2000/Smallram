import ModifiedCartan.ScalarDyadicLineTargets

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan.ScalarDyadicPeakTargetData

theorem good_at_rate {f : Curve 1} {a : ℕ → ℂ} {ρ : ℝ}
    (q : ScalarDyadicPeakTargetData f a ρ) (htrans : f.Transcendental)
    {δ : ℝ} (hδ : δ ≤ q.lineRate) :
    ∀ᶠ ν in atTop, q.height ν ∈ Icc ((a ν).im - q.width) ((a ν).im + q.width) ∧
      ∀ t ∈ Icc ((a ν).re - q.width) ((a ν).re + q.width),
        (2 : ℝ) ^ ν * scalarSphericalSpeed f.coord
          ((((2 : ℝ) ^ ν : ℝ) : ℂ) * (⟨t, q.height ν⟩ : ℂ)) ≤
          Real.exp (-δ * characteristic f ((2 : ℝ) ^ ν)) := by
  filter_upwards [q.good] with ν hν
  refine ⟨hν.1, fun t ht => (hν.2 t ht).trans ?_⟩
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg hδ)
    (characteristic_pos_of_transcendental f htrans (pow_pos (by norm_num) _)).le

theorem close_at_rate {f : Curve 1} {a : ℕ → ℂ} {ρ : ℝ}
    (q : ScalarDyadicPeakTargetData f a ρ) (htrans : f.Transcendental)
    {δ : ℝ} (hδ : δ ≤ q.decayRate) :
    ∀ᶠ ν in atTop, ‖q.anchor ν - scalarSphereValue q.target‖ ≤
      2 * Real.exp (-δ * characteristic f ((2 : ℝ) ^ ν)) := by
  filter_upwards [q.close] with ν hν
  apply hν.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg hδ)
    (characteristic_pos_of_transcendental f htrans (pow_pos (by norm_num) _)).le

end ModifiedCartan.ScalarDyadicPeakTargetData
#print axioms ModifiedCartan.ScalarDyadicPeakTargetData.good_at_rate
#print axioms ModifiedCartan.ScalarDyadicPeakTargetData.close_at_rate
