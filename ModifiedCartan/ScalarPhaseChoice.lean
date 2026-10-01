import ModifiedCartan.ScalarProfileCompactness

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The fixed circle of actual scalar profile coefficients. -/
def scalarPhaseCircle : Set ℂ := sphere 0 ((Real.pi / 2) ^ 2)

theorem scalarPhaseCircle_compact : IsCompact scalarPhaseCircle := isCompact_sphere _ _

theorem scalarPhaseCircle_nonempty : scalarPhaseCircle.Nonempty := by
  refine ⟨(((Real.pi / 2) ^ 2 : ℝ) : ℂ), ?_⟩
  simp only [scalarPhaseCircle, mem_sphere, dist_zero_right, Complex.norm_real,
    Real.norm_of_nonneg (sq_nonneg _)]

theorem mem_scalarPhaseCircle {C : ℂ} : C ∈ scalarPhaseCircle ↔ ‖C‖ = (Real.pi / 2) ^ 2 := by
  simp only [scalarPhaseCircle, mem_sphere, dist_zero_right]

/-- The actual local L1 approximation error on the closed unit disk. -/
noncomputable def scalarProfileError (f : Curve 1) (m : ℕ) (t : ℝ) (C : ℂ) : ℝ :=
  ∫ z in closedBall (0 : ℂ) 1,
    ‖scalarNormalizedSpherePotential f t z - scalarQuadraticProfile m C z‖

theorem scalarProfileError_nonneg (f : Curve 1) (m : ℕ) (t : ℝ) (C : ℂ) :
    0 ≤ scalarProfileError f m t C := integral_nonneg (fun _ => norm_nonneg _)

/-- The actual approximation error is continuous on the compact parameter
circle for every real radius, including initial exceptional radii. -/
theorem scalarProfileError_continuousOn (f : Curve 1) (m : ℕ) (t : ℝ) :
    ContinuousOn (scalarProfileError f m t) scalarPhaseCircle := by
  let K : Set ℂ := closedBall 0 1
  have hK : IsCompact K := isCompact_closedBall _ _
  letI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  have hP := continuous_scalarQuadraticProfile m
  obtain ⟨M, hM⟩ := ((scalarPhaseCircle_compact.prod hK).image hP).isBounded.exists_norm_le
  have hS : IntegrableOn (scalarNormalizedSpherePotential f t) K :=
    (scalarSphericalLogPotential_integrableOn_scaled f t hK).div_const (characteristic f t)
  apply continuousOn_of_dominated (bound := fun z => ‖scalarNormalizedSpherePotential f t z‖ + M)
  · intro C _
    exact ((scalarNormalizedSpherePotential_measurable f t).aestronglyMeasurable.sub
      (hP.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable).norm
  · intro C hC
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    have hbound := hM _ (mem_image_of_mem _ (show (C, z) ∈ scalarPhaseCircle ×ˢ K from ⟨hC, hz⟩))
    simpa only [norm_norm] using (norm_sub_le (scalarNormalizedSpherePotential f t z)
      (scalarQuadraticProfile m C z)).trans (add_le_add le_rfl hbound)
  · exact hS.norm.add (integrable_const M)
  · apply Eventually.of_forall
    intro z
    exact (continuous_const.sub (hP.comp (continuous_id.prodMk continuous_const))).norm.continuousOn

/-- An actual minimizing phase coefficient exists at every radius. -/
theorem exists_scalarProfileError_minimizer (f : Curve 1) (m : ℕ) (t : ℝ) :
    ∃ C : ℂ, ‖C‖ = (Real.pi / 2) ^ 2 ∧ ∀ D : ℂ, ‖D‖ = (Real.pi / 2) ^ 2 →
      scalarProfileError f m t C ≤ scalarProfileError f m t D := by
  obtain ⟨C, hC, hmin⟩ := scalarPhaseCircle_compact.exists_isMinOn scalarPhaseCircle_nonempty
    (scalarProfileError_continuousOn f m t)
  exact ⟨C, mem_scalarPhaseCircle.mp hC, fun D hD => hmin (mem_scalarPhaseCircle.mpr hD)⟩

noncomputable def scalarPhaseCoefficient (f : Curve 1) (m : ℕ) (t : ℝ) : ℂ :=
  Classical.choose (exists_scalarProfileError_minimizer f m t)

theorem scalarPhaseCoefficient_norm (f : Curve 1) (m : ℕ) (t : ℝ) :
    ‖scalarPhaseCoefficient f m t‖ = (Real.pi / 2) ^ 2 :=
  (Classical.choose_spec (exists_scalarProfileError_minimizer f m t)).1

theorem scalarPhaseCoefficient_minimizes (f : Curve 1) (m : ℕ) (t : ℝ)
    {D : ℂ} (hD : ‖D‖ = (Real.pi / 2) ^ 2) :
    scalarProfileError f m t (scalarPhaseCoefficient f m t) ≤ scalarProfileError f m t D :=
  (Classical.choose_spec (exists_scalarProfileError_minimizer f m t)).2 D hD

end ModifiedCartan
#print axioms ModifiedCartan.scalarProfileError_continuousOn
#print axioms ModifiedCartan.exists_scalarProfileError_minimizer
#print axioms ModifiedCartan.scalarPhaseCoefficient_minimizes

