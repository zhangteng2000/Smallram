import ModifiedCartan.ScalarNormNormalizedProfile

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The actual good centers meet every nonempty open subset of their disk. -/
theorem GoodCenterData.exists_mem_of_isOpen {n : ℕ} {s : ℕ → ℝ}
    {p : ℕ → Index n → Polynomial ℂ}
    {a : (ν : ℕ) → Fin (FewInflection.polynomialWronskian (p ν)).natDegree → ℂ}
    (h : GoodCenterData s p a) {Ω : Set ℂ} (hΩ : IsOpen Ω) (hΩne : Ω.Nonempty)
    (hΩ2 : Ω ⊆ ball (0 : ℂ) 2) : ∃ z ∈ Ω, z ∈ h.centers := by
  exact Measure.exists_mem_of_measure_ne_zero_of_ae (hΩ.measure_ne_zero volume hΩne)
    (h.full_measure.filter_mono (ae_mono (Measure.restrict_mono_set _ hΩ2)))

/-- Every positive point has actual positive good centers arbitrarily nearby. -/
theorem ArbitraryRadiusLimitData.scalar_positive_good_center_near
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    {a : ℂ} (ha : a ∈ ball (0 : ℂ) 2) (hpos : 0 < (d.U a).toReal)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ z ∈ ball a ε, z ∈ d.good_centers.centers ∧ 0 < (d.U z).toReal := by
  have ha4 : a ∈ ball (0 : ℂ) 4 := (ball_subset_ball (by norm_num : (2 : ℝ) ≤ 4)) ha
  have hc := d.norm_limit_continuous.2.continuousAt (isOpen_ball.mem_nhds ha4)
  have hp : ∀ᶠ z in 𝓝 a, 0 < (d.U z).toReal := continuousAt_const.eventually_lt hc hpos
  have hh : ∀ᶠ z in 𝓝 a,
      z ∈ ball a ε ∧ z ∈ ball (0 : ℂ) 2 ∧ 0 < (d.U z).toReal := by
    filter_upwards [ball_mem_nhds a hε, isOpen_ball.mem_nhds ha, hp] with z hz hza hzp
    exact ⟨hz, hza, hzp⟩
  obtain ⟨δ, hδ, hδS⟩ := Metric.mem_nhds_iff.mp hh
  obtain ⟨z, hz, hzg⟩ := d.good_centers.exists_mem_of_isOpen isOpen_ball
    (nonempty_ball.mpr hδ) (fun z hz => (hδS hz).2.1)
  exact ⟨z, (hδS hz).1, hzg, (hδS hz).2.2⟩

/-- The norm profile has a positive good center, proved from the exact
unit-circle normalization rather than presumed in the path construction. -/
theorem ArbitraryRadiusLimitData.scalar_exists_positive_good_center
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) (hr : Tendsto r atTop atTop) :
    ∃ a ∈ d.good_centers.centers, 0 < (d.U a).toReal := by
  obtain ⟨φ, hφ⟩ := d.scalar_norm_polar_profile hρ hr
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  let a : ℂ := circleMap 0 1 (-φ / ρ)
  have ha : a ∈ ball (0 : ℂ) 2 := by
    simp only [a, mem_ball, dist_zero_right, norm_circleMap_zero, abs_one]
    norm_num
  have he : ρ * (-φ / ρ) + φ = 0 := by field_simp; ring
  have hp : 0 < (d.U a).toReal := by
    rw [hφ 1 zero_lt_one (by norm_num) (-φ / ρ), he, Real.cos_zero, abs_one, Real.one_rpow, mul_one, mul_one]
    exact half_pos Real.pi_pos
  obtain ⟨z, _, hz, hpz⟩ := d.scalar_positive_good_center_near ha hp zero_lt_one
  exact ⟨z, hz, hpz⟩

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_exists_positive_good_center
