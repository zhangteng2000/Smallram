import ModifiedCartan.PolynomialCurveGrowth
import ModifiedCartan.ExponentialGauge
import ModifiedCartan.EuclideanJensen
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open scoped Topology
open Filter Set Asymptotics
set_option autoImplicit false
namespace ModifiedCartan

/-- Any actual polynomial representation has logarithmic characteristic growth. -/
theorem characteristic_log_bound_of_polynomial_representation {n : ℕ} (f : Curve n)
    (hf : f.HasPolynomialRepresentation) :
    ∃ A B : ℝ, ∀ r : ℝ, 1 ≤ r → characteristic f r ≤ A + B * Real.log r := by
  obtain ⟨p, a, ha, had, hrep⟩ := hf
  let P : Curve n := {
    coord := fun j z => (p j).eval z
    holomorphic := fun j => (p j).differentiable
    reduced := fun z => by
      obtain ⟨j, hj⟩ := f.reduced z
      refine ⟨j, ?_⟩
      intro hz
      apply hj
      rw [hrep j z, hz, mul_zero] }
  have hchar (r : ℝ) (hr : 0 < r) : characteristic f r = characteristic P r := by
    have hv : f.vector = (P.scalarGauge a ha had).vector := by
      funext z j
      exact hrep j z
    have he : characteristic f r = characteristic (P.scalarGauge a ha had) r := by
      unfold characteristic
      rw [hv]
    exact he.trans (characteristic_scalarGauge P a ha had hr)
  obtain ⟨C, hC, D, hbound⟩ := polynomial_family_euclidean_power_bound p
  refine ⟨Real.log C - Real.log (euclideanNorm (P.vector 0)), (D : ℝ), ?_⟩
  intro r hr
  have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [hchar r hrp]
  have hlog (z : ℂ) (hz : z ∈ Metric.sphere 0 |r|) :
      Real.log (euclideanNorm (P.vector z)) ≤ Real.log C + (D : ℝ) * Real.log r := by
    have hzr : ‖z‖ ≤ r := by
      have he := Metric.mem_sphere.mp hz
      simpa only [dist_zero_right, abs_of_pos hrp] using he.le
    have hh := Real.log_le_log (euclideanNorm_pos (P.vector_ne_zero z)) (hbound r hr z hzr)
    rw [Real.log_mul hC.ne' (pow_pos hrp _).ne', Real.log_pow] at hh
    exact hh
  have hm := Real.circleAverage_mono
    (curve_log_euclideanNorm_continuous P).continuousOn.circleIntegrable'
    (circleIntegrable_const (Real.log C + (D : ℝ) * Real.log r) 0 r) hlog
  rw [Real.circleAverage_const] at hm
  unfold characteristic
  linarith

theorem characteristic_div_power_zero_of_polynomial_representation {n : ℕ}
    (f : Curve n) (hf : f.HasPolynomialRepresentation) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun r : ℝ => characteristic f r / r ^ ρ) atTop (𝓝 0) := by
  obtain ⟨A, B, hB⟩ := characteristic_log_bound_of_polynomial_representation f hf
  have hconst : Tendsto (fun r : ℝ => A / r ^ ρ) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop hρ)
  have hlog : Tendsto (fun r : ℝ => Real.log r / r ^ ρ) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hρ).tendsto_div_nhds_zero
  have hlim : Tendsto (fun r : ℝ => (A + B * Real.log r) / r ^ ρ) atTop (𝓝 0) := by
    simpa only [add_div, mul_div_assoc, mul_zero, add_zero] using hconst.add (hlog.const_mul B)
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact div_nonneg (characteristic_nonneg f hr) (Real.rpow_pos_of_pos hr ρ).le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    exact div_le_div_of_nonneg_right (hB r hr) (Real.rpow_nonneg (by linarith) ρ)

theorem transcendental_of_positive_characteristic_power_limit {n : ℕ} (f : Curve n)
    {ρ C : ℝ} (hρ : 0 < ρ) (hC : 0 < C)
    (hl : Tendsto (fun r : ℝ => characteristic f r / r ^ ρ) atTop (𝓝 C)) :
    f.Transcendental := by
  intro hf
  have hz := characteristic_div_power_zero_of_polynomial_representation f hf hρ
  exact hC.ne' (tendsto_nhds_unique hl hz)

end ModifiedCartan
#print axioms ModifiedCartan.characteristic_log_bound_of_polynomial_representation
#print axioms ModifiedCartan.transcendental_of_positive_characteristic_power_limit
