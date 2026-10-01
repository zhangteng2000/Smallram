import ModifiedCartan.ScalarSectorArcs
import ModifiedCartan.ScalarCosineIntegral

open scoped Topology BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Partition a circular mean into the m explicit equal sector arcs. -/
theorem circleAverage_unit_sector_partition {u : ℂ → ℝ}
    (hu : ContinuousOn u (sphere 0 1)) {a : ℂ} (ha : ‖a‖ = 1)
    {m : ℕ} (hm : 0 < m) :
    Real.circleAverage u 0 1 = (2 * Real.pi)⁻¹ *
      ∑ j : Fin m, ∫ θ in -(Real.pi / (m : ℝ))..Real.pi / (m : ℝ),
        u (scalarSectorCenter a m j * circleMap 0 1 θ) := by
  let h : ℝ → ℝ := fun θ => u (a * circleMap 0 1 θ)
  let δ : ℝ := Real.pi / (m : ℝ)
  let t : ℕ → ℝ := fun k => (k : ℝ) * (2 * δ) - δ
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have haexp : circleMap 0 1 a.arg = a := by
    rw [circleMap_zero, ← ha, Complex.norm_mul_exp_arg_mul_I]
  have hmap (θ : ℝ) : a * circleMap 0 1 θ = circleMap 0 1 (θ + a.arg) := by
    nth_rw 1 [← haexp]
    rw [circleMap_zero_mul, one_mul, add_comm a.arg θ]
  have hc : Continuous h := hu.comp_continuous
    (continuous_const.mul (continuous_circleMap 0 1)) (fun θ => by
      simp only [mem_sphere, dist_zero_right, norm_mul, ha, norm_circleMap_zero, abs_one, mul_one])
  have hp : Function.Periodic h (2 * Real.pi) := by
    intro θ
    dsimp only [h]
    rw [periodic_circleMap 0 1 θ]
  have havg : Real.circleAverage u 0 1 = (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, h θ := by
    rw [Real.circleAverage_eq_integral_add a.arg]
    simp only [smul_eq_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only [h]
    rw [hmap]
  have hend : t m = -δ + 2 * Real.pi := by dsimp [t, δ]; field_simp; ring
  have hstart : t 0 = -δ := by simp [t]
  have hperiod : (∫ θ in (0 : ℝ)..2 * Real.pi, h θ) = ∫ θ in t 0..t m, h θ := by
    rw [hstart, hend]
    simpa only [zero_add] using hp.intervalIntegral_add_eq 0 (-δ)
  have hsum : (∑ j : Fin m, ∫ θ in t j.val..t (j.val + 1), h θ) =
      ∫ θ in t 0..t m, h θ := by
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => ∫ θ in t k..t (k + 1), h θ) m]
    exact intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hc.intervalIntegrable _ _)
  rw [havg, hperiod, ← hsum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  let c : ℝ := (j.val : ℝ) * (2 * Real.pi) / (m : ℝ)
  have he₁ : t j.val = c + (-δ) := by dsimp [t, c, δ]; ring
  have he₂ : t (j.val + 1) = c + δ := by dsimp [t, c, δ]; push_cast; ring
  rw [he₁, he₂, ← intervalIntegral.integral_comp_add_left]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only [h, scalarSectorCenter, scalarSectorRotation]
  rw [mul_assoc, circleMap_zero_mul, one_mul]

/-- A cosine profile on each explicit open sector determines the whole mean.
The endpoints need no separate pointwise assumption. -/
theorem circleAverage_of_sector_cosine_profiles {u : ℂ → ℝ}
    (hu : ContinuousOn u (sphere 0 1)) {a : ℂ} (ha : ‖a‖ = 1)
    {m : ℕ} (hm : 0 < m) {ρ : ℝ} (hρm : ρ = (m : ℝ) / 2)
    (w : Fin m → ℝ)
    (hp : ∀ j : Fin m, ∀ θ : ℝ, ρ * θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) →
      u (scalarSectorCenter a m j * circleMap 0 1 θ) = w j * Real.cos (ρ * θ)) :
    Real.circleAverage u 0 1 = (∑ j : Fin m, w j) / (Real.pi * ρ) := by
  have hrho : 0 < ρ := by rw [hρm]; positivity
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hδ : Real.pi / (m : ℝ) = Real.pi / (2 * ρ) := by rw [hρm]; ring
  have hδpos : 0 < Real.pi / (m : ℝ) := div_pos Real.pi_pos (Nat.cast_pos.mpr hm)
  have he₁ : ρ * (-(Real.pi / (m : ℝ))) = -(Real.pi / 2) := by rw [hρm]; field_simp
  have he₂ : ρ * (Real.pi / (m : ℝ)) = Real.pi / 2 := by rw [hρm]; field_simp
  have hi (j : Fin m) :
      (∫ θ in -(Real.pi / (m : ℝ))..Real.pi / (m : ℝ),
        u (scalarSectorCenter a m j * circleMap 0 1 θ)) = w j * (2 / ρ) := by
    calc
      _ = ∫ θ in -(Real.pi / (m : ℝ))..Real.pi / (m : ℝ), w j * Real.cos (ρ * θ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
        intro θ hθ
        rw [hδ] at hθ
        exact hp j θ (scalar_sector_angle_mem hrho hθ)
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left _ hrho.ne',
          he₁, he₂, integral_cos, Real.sin_neg, Real.sin_pi_div_two, smul_eq_mul]
        ring
  rw [circleAverage_unit_sector_partition hu ha hm]
  simp_rw [hi]
  rw [← Finset.sum_mul]
  field_simp

end ModifiedCartan
#print axioms ModifiedCartan.circleAverage_unit_sector_partition
#print axioms ModifiedCartan.circleAverage_of_sector_cosine_profiles
