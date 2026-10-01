import ModifiedCartan.ScalarSectorIntegrals
import ModifiedCartan.ScalarSectorMultiplicity
import ModifiedCartan.ScalarTargetLogData
import ModifiedCartan.SubsequenceRatios

open scoped Topology BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The exact circular mean defect of a signed sector profile counts its
negative sectors. Auxiliary to LaTeX `thm:A` (b). -/
theorem ScalarTargetLogLimitData.circle_mean_defect_eq_sectorMultiplicity
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} {d : ArbitraryRadiusLimitData f r ρ}
    {β : WithTop ℂ} (e : ScalarTargetLogLimitData d β)
    (hρ : 1 ≤ ρ) (hr : Tendsto r atTop atTop)
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) {a : ℂ} (ha : ‖a‖ = 1)
    (target : Fin m → WithTop ℂ)
    (hroot : ∀ j : Fin m, ((Real.pi / 2 : ℝ) : ℂ) ^ 2 =
      d.scalarQuadratic (scalarSectorCenter a m j))
    (hneg : ∀ j : Fin m, target j = β →
      EqOn (fun z => (e.u z).toReal) (fun z => -(d.U z).toReal)
        (scalarPositiveChart (scalarSectorCenter a m j) ρ ((Real.pi / 2 : ℝ) : ℂ)))
    (hpos : ∀ j : Fin m, target j ≠ β →
      EqOn (fun z => (e.u z).toReal) (fun z => (d.U z).toReal)
        (scalarPositiveChart (scalarSectorCenter a m j) ρ ((Real.pi / 2 : ℝ) : ℂ))) :
    1 - Real.circleAverage (fun z => (e.u z).toReal) 0 1 =
      (scalarSectorMultiplicity target β : ℝ) / ρ := by
  classical
  have hrho : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hm0 : 0 < m := by
    by_contra hn
    have hz : m = 0 := by omega
    simp only [hz, Nat.cast_zero, zero_div] at hm
    linarith
  have hsub : sphere (0 : ℂ) 1 ⊆ ball 0 4 := sphere_subset_ball (by norm_num)
  have hU := d.norm_limit_continuous.2.mono hsub
  have hu := e.regular.2.continuousOn.mono hsub
  let w : Fin m → ℝ := fun j => if target j = β then Real.pi else 0
  have hmean := circleAverage_of_sector_cosine_profiles (hU.sub hu) ha hm0 hm w (by
    intro j θ hθ
    have hj := scalarSectorCenter_norm ha m j
    have hz := unit_arc_mem_scalarPositiveChart hj hrho hθ
    have hval := d.scalar_norm_unit_arc hρ hj (hroot j) hθ
    dsimp only [Pi.sub_apply, w]
    split_ifs with he
    · have hh := hneg j he hz
      dsimp only at hh
      rw [hh, hval]
      ring
    · have hh := hpos j he hz
      dsimp only at hh
      rw [hh]
      ring)
  have hw : (∑ j : Fin m, w j) = (scalarSectorMultiplicity target β : ℝ) * Real.pi := by
    dsimp only [w, scalarSectorMultiplicity]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Real.circleAverage_sub (hU.circleIntegrable (by norm_num)) (hu.circleIntegrable (by norm_num)),
    d.circleAverage_one hrho hr, hw] at hmean
  rw [hmean]
  field_simp

end ModifiedCartan
#print axioms ModifiedCartan.ScalarTargetLogLimitData.circle_mean_defect_eq_sectorMultiplicity
