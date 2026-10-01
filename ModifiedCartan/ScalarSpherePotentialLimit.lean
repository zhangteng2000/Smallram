import ModifiedCartan.ScalarSpherePotential
import ModifiedCartan.LocalLpEventualEquality

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The actual physical spherical log potential converges locally in L1 to
twice the actual norm limit. No gauge choice remains in the source function.
Auxiliary to thm:A (b), for comparison of phases at different radii. -/
theorem ArbitraryRadiusLimitData.scalar_spherical_potential_localL1
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) (hρ : 0 < ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    (hr : Tendsto r atTop atTop) :
    LocalLpConvergence 1 (ball (0 : ℂ) 4)
      (fun ν => scalarNormalizedSpherePotential f (r (d.subseq ν)))
      (fun z => 2 * (d.U z).toReal) := by
  let t : ℕ → ℝ := fun ν => r (d.subseq ν)
  let s : ℕ → ℝ := fun ν => characteristic f (t ν)
  let F : ℕ → Index 1 → ℂ → ℂ := fun ν => rescaledRepresentation f (t ν) (d.gauge ν)
  let P : ℕ → Polynomial ℂ := fun ν => rescaledWronskianPolynomial f (t ν)
  have ht : Tendsto t atTop atTop := hr.comp d.strictMono.tendsto_atTop
  obtain ⟨C, hC, hsc⟩ := characteristic_arbitrary_scale_hypotheses f htrans hsmall
    hρ (ε := ρ / 2) (by positivity) (by linarith) hl hu ht
  have hsc1 := hsc 1 zero_lt_one
  simp only [arbitraryScaleWeight_one, one_mul] at hsc1
  have hm := rescaledWronskianPolynomial_degree_small f hlin ht d.scale_tendsto hsc1.2.2.2.2
  have hlogP := (Paper.eq_small_polynomial_log P
    (fun ν => rescaledWronskianPolynomial_monic f (t ν))
    (fun ν a ha => (show ‖a‖ < 64 by simpa only [mem_ball, dist_zero_right] using
      rescaledWronskianPolynomial_roots_mem f (t ν) ha).le) d.scale_tendsto hm).restrict
    (subset_univ (ball (0 : ℂ) 4))
  have hlogt : LocalLpConvergence 1 (ball (0 : ℂ) 4)
      (fun ν _ => Real.log (t ν) / s ν) (fun _ => 0) :=
    localLpConvergence_of_tendstoUniformlyOn 1 (fun _ => continuousOn_const)
      continuousOn_const (hsc1.2.2.1.tendstoUniformlyOn_const _)
  have hmodel := ((d.norm_limit.add le_rfl d.norm_limit).sub le_rfl hlogP).add le_rfl hlogt
  have hmem (K : Set ℂ) (hK : IsCompact K) (_ : K ⊆ ball (0 : ℂ) 4) (ν : ℕ) :
      MemLp (scalarNormalizedSpherePotential f (t ν)) 1 (volume.restrict K) :=
    memLp_one_iff_integrable.mpr
      ((scalarSphericalLogPotential_integrableOn_scaled f (t ν) hK).div_const (s ν))
  have heq : ∀ᶠ ν in atTop,
      (fun z => ((s ν)⁻¹ * Real.log (euclideanNorm (fun j => F ν j z)) +
        (s ν)⁻¹ * Real.log (euclideanNorm (fun j => F ν j z)) -
        Real.log ‖(P ν).eval z‖ / s ν) + Real.log (t ν) / s ν) =ᵐ[volume.restrict (ball (0 : ℂ) 4)]
      scalarNormalizedSpherePotential f (t ν) := by
    filter_upwards [d.replacement.gauge_analytic, d.replacement.gauge_wronskian,
      ht.eventually_gt_atTop 0] with ν hA hW htν
    filter_upwards [ae_restrict_of_ae (monic_polynomial_eval_ne_zero_ae (P ν)
      (rescaledWronskianPolynomial_monic f (t ν))), ae_restrict_mem measurableSet_ball]
      with z hPz hz
    have hz64 := (ball_subset_ball (by norm_num : (4 : ℝ) ≤ 64)) hz
    have hHz := hA z hz64
    have hG : FewInflection.wronskian 1 (F ν) z = (P ν).eval z := hW z hz64
    have hWorig : FewInflection.wronskian 1 f.coord ((t ν : ℂ) * z) ≠ 0 := by
      intro hw
      apply hPz
      rw [← hG]
      change FewInflection.wronskian 1 (rescaledRepresentation f (t ν) (d.gauge ν)) z = 0
      rw [rescaledRepresentation_wronskian f (t ν) hHz, FewInflection.wronskian_dilate, hw,
        mul_zero, mul_zero]
    rw [← hG]
    calc
      _ = (scalarSphericalLogPotential (F ν) z + Real.log (t ν)) / s ν := by
        unfold scalarSphericalLogPotential
        ring
      _ = _ := by
        rw [scalarSphericalLogPotential_rescaled f htν hHz hWorig]
        unfold scalarNormalizedSpherePotential
        ring
  have hphysical := hmodel.congr_eventually_ae hmem heq
  apply hphysical.congr_ae (fun _ => EventuallyEq.rfl)
  filter_upwards [d.representative] with z hz
  rw [hz, EReal.toReal_coe]
  dsimp only [Pi.add_apply, Pi.sub_apply]
  ring

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_spherical_potential_localL1
