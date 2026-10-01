import ModifiedCartan.ScalarPhaseChoice

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem scalar_potential_sub_profile_integrableOn (f : Curve 1) (m : ℕ) (t : ℝ) (C : ℂ)
    {K : Set ℂ} (hK : IsCompact K) :
    IntegrableOn (fun z => scalarNormalizedSpherePotential f t z - scalarQuadraticProfile m C z) K := by
  have hS : IntegrableOn (scalarNormalizedSpherePotential f t) K :=
    (scalarSphericalLogPotential_integrableOn_scaled f t hK).div_const (characteristic f t)
  exact hS.sub (((continuous_scalarQuadraticProfile m).comp
    (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact hK)

theorem scalarProfileError_eq_eLpNorm (f : Curve 1) (m : ℕ) (t : ℝ) (C : ℂ) :
    ENNReal.ofReal (scalarProfileError f m t C) =
      eLpNorm (fun z => scalarNormalizedSpherePotential f t z - scalarQuadraticProfile m C z)
        1 (volume.restrict (closedBall (0 : ℂ) 1)) := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  exact ofReal_integral_norm_eq_lintegral_enorm
    (scalar_potential_sub_profile_integrableOn f m t C (isCompact_closedBall _ _))

/-- The actual minimum L1 error tends to zero at all large radii. Compactness
of every radius sequence supplies the comparison coefficient; minimization
then gives the same bound for the constructed coefficient. -/
theorem scalarProfileError_best_tendsto_zero
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) :
    Tendsto (fun t => scalarProfileError f m t (scalarPhaseCoefficient f m t)) atTop (𝓝 0) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro r hr
  obtain ⟨ns, _, C, hC, hlim⟩ := scalar_potential_profile_subsequence f hlin htrans hsmall hρ hl hu hm hr
  refine ⟨ns, ?_⟩
  have herr : Tendsto (fun ν => scalarProfileError f m (r (ns ν)) C) atTop (𝓝 0) :=
    hlim.integral_norm_sub_tendsto_zero (isCompact_closedBall (0 : ℂ) 1)
      (closedBall_subset_ball (by norm_num : (1 : ℝ) < 2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds herr
  · intro ν
    exact scalarProfileError_nonneg f m _ _
  · intro ν
    exact scalarPhaseCoefficient_minimizes f m _ hC

/-- The chosen profiles approximate the actual physical potential in local L1
along every radius sequence, with actual integrability at all initial indices. -/
theorem scalarPhaseCoefficient_profile_approximates
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) :
    LocalLpConvergence 1 (ball (0 : ℂ) 1)
      (fun ν z => scalarNormalizedSpherePotential f (r ν) z -
        scalarQuadraticProfile m (scalarPhaseCoefficient f m (r ν)) z) (fun _ => 0) where
  source_mem K hK _ ν := memLp_one_iff_integrable.mpr
    (scalar_potential_sub_profile_integrableOn f m (r ν) _ hK)
  limit_mem _ _ _ := by simp
  tendsto K _ hKU := by
    have herr := (scalarProfileError_best_tendsto_zero f hlin htrans hsmall hρ hl hu hm).comp hr
    have hnn : Tendsto (fun ν => ENNReal.ofReal
        (scalarProfileError f m (r ν) (scalarPhaseCoefficient f m (r ν)))) atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero, Function.comp_def] using
        (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp herr
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hnn (fun _ => bot_le)
    intro ν
    change eLpNorm ((fun z => scalarNormalizedSpherePotential f (r ν) z -
      scalarQuadraticProfile m (scalarPhaseCoefficient f m (r ν)) z) - (0 : ℂ → ℝ))
      1 (volume.restrict K) ≤
        ENNReal.ofReal (scalarProfileError f m (r ν) (scalarPhaseCoefficient f m (r ν)))
    rw [sub_zero, scalarProfileError_eq_eLpNorm]
    exact eLpNorm_mono_measure
      (fun z => scalarNormalizedSpherePotential f (r ν) z -
        scalarQuadraticProfile m (scalarPhaseCoefficient f m (r ν)) z)
      (Measure.restrict_mono_set _ (hKU.trans ball_subset_closedBall))

end ModifiedCartan
#print axioms ModifiedCartan.scalarProfileError_best_tendsto_zero
#print axioms ModifiedCartan.scalarPhaseCoefficient_profile_approximates



