import ModifiedCartan.ScalarSharpScaleBounds
import ModifiedCartan.ScalarDyadicLineTargets

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- The already fixed target and its actual horizontal segment can be made
arbitrarily accurate on the smaller comparable-radius scale by one fixed
dyadic shift. Both the target error and the speed are controlled. -/
theorem ScalarDyadicPeakTargetData.far_target_and_line_bounds
    {f : Curve 1} {a : ℕ → ℂ} {ρ : ℝ} (q : ScalarDyadicPeakTargetData f a ρ)
    (htrans : f.Transcendental) (hlin : f.linearlyNonDegenerate)
    (hsmall : SmallRamification f) (hρ : 0 < ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ᶠ ν in atTop, ∀ c ∈ Icc (1 : ℝ) 2,
      (q.height (ν + K) ∈ Icc ((a (ν + K)).im - q.width) ((a (ν + K)).im + q.width) ∧
        ∀ t ∈ Icc ((a (ν + K)).re - q.width) ((a (ν + K)).re + q.width),
          (2 : ℝ) ^ (ν + K) * scalarSphericalSpeed f.coord
            (((((2 : ℝ) ^ (ν + K)) : ℝ) : ℂ) * (⟨t, q.height (ν + K)⟩ : ℂ)) ≤
              Real.exp (-κ * characteristic f (c * (2 : ℝ) ^ ν))) ∧
      ‖q.anchor (ν + K) - scalarSphereValue q.target‖ ≤
        2 * Real.exp (-κ * characteristic f (c * (2 : ℝ) ^ ν)) := by
  let η := min q.lineRate q.decayRate
  have hη : 0 < η := lt_min q.lineRate_pos q.decayRate_pos
  obtain ⟨K, hK, hlarge⟩ := characteristic_large_dyadic_multiple_eventually
    f htrans hlin hsmall hρ hl hu hη hκ
  have hpow : Tendsto (fun ν : ℕ => (2 : ℝ) ^ ν) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hfar : Tendsto (fun ν : ℕ => (2 : ℝ) ^ (ν + K)) atTop atTop :=
    hpow.comp (tendsto_add_atTop_nat K)
  have hs := (characteristic_tendsto_atTop_of_transcendental f htrans).comp hfar
  refine ⟨K, hK, ?_⟩
  filter_upwards [(tendsto_add_atTop_nat K).eventually q.good,
    (tendsto_add_atTop_nat K).eventually q.close, hpow.eventually hlarge,
    hs.eventually_ge_atTop 0] with ν hgood hclose hbig hsν
  change 0 ≤ characteristic f ((2 : ℝ) ^ (ν + K)) at hsν
  intro c hc
  have hh : κ * characteristic f (c * (2 : ℝ) ^ ν) ≤
      η * characteristic f ((2 : ℝ) ^ (ν + K)) := by
    simpa only [pow_add, mul_comm] using hbig c hc
  have hline : Real.exp (-q.lineRate * characteristic f ((2 : ℝ) ^ (ν + K))) ≤
      Real.exp (-κ * characteristic f (c * (2 : ℝ) ^ ν)) := by
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_right (show η ≤ q.lineRate from min_le_left _ _) hsν
    linarith
  have hdecay : Real.exp (-q.decayRate * characteristic f ((2 : ℝ) ^ (ν + K))) ≤
      Real.exp (-κ * characteristic f (c * (2 : ℝ) ^ ν)) := by
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_right (show η ≤ q.decayRate from min_le_right _ _) hsν
    linarith
  exact ⟨⟨hgood.1, fun t ht => (hgood.2 t ht).trans hline⟩,
    hclose.trans (mul_le_mul_of_nonneg_left hdecay (by norm_num))⟩

end ModifiedCartan
#print axioms ModifiedCartan.ScalarDyadicPeakTargetData.far_target_and_line_bounds
