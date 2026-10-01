import ModifiedCartan.ScalarComparableBounded
import ModifiedCartan.ScalarSphereIsometry
import ModifiedCartan.ArbitraryRadiusConstruction

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Slow change of the actual physical potential between arbitrary comparable
radii. This conclusion holds for the original curve and every radius sequence,
with no assumed phase selection and no chosen coordinate normalization left.
Auxiliary to the path-gluing step of LaTeX thm:A (b). -/
theorem scalar_potential_comparable_difference_tendsto_zero
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 0 < ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {r c : ℕ → ℝ} (hr : Tendsto r atTop atTop) (hc : ∀ ν, c ν ∈ Icc (1 : ℝ) 2) :
    LocalMeasureConvergence (ball (0 : ℂ) 1)
      (fun ν z => scalarNormalizedSpherePotential f (c ν * r ν) z -
        scalarNormalizedSpherePotential f (r ν) z) (fun _ => 0) := by
  apply localMeasureConvergence_of_subseq
  intro ns hns
  obtain ⟨A, hA, hAnorm, ⟨d⟩⟩ :=
    Paper.exists_arbitrary_radius_limits f hlin htrans hsmall hρ hl hu (hr.comp hns)
  have hT := characteristic_matrixGauge_of_euclidean_isometry f A hA hAnorm
  have hN := FewInflection.Curve.matrixGauge_ramification_eq f A hA
  have hlinA := (f.matrixGauge_linearlyNonDegenerate_iff A hA).mp hlin
  have htransA := (f.matrixGauge_transcendental_iff A hA).mp htrans
  have hsmallA : SmallRamification (f.matrixGauge A hA) := by
    simpa only [SmallRamification, hT, hN] using hsmall
  have hlA : strongLowerIndex (characteristic (f.matrixGauge A hA)) = (ρ : EReal) := by
    simpa only [hT] using hl
  have huA : strongUpperIndex (characteristic (f.matrixGauge A hA)) = (ρ : EReal) := by
    simpa only [hT] using hu
  have hbase := ((d.scalar_spherical_potential_localL1 hlinA htransA hsmallA hρ hlA huA
    (hr.comp hns)).inMeasure (by norm_num)).mono (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 4))
  have hscaled := d.scalar_comparable_potential_limit_bounded hlinA htransA hsmallA hρ hlA huA
    (hr.comp hns) (fun ν => hc (ns (d.subseq ν)))
  have hdiff := hscaled.continuous_map₂ hbase
    (fun K _ _ ν => (scalarNormalizedSpherePotential_measurable (f.matrixGauge A hA) _).aestronglyMeasurable)
    (fun K _ _ ν => (scalarNormalizedSpherePotential_measurable (f.matrixGauge A hA) _).aestronglyMeasurable)
    (continuous_fst.sub continuous_snd)
  refine ⟨d.subseq, ?_⟩
  simpa only [scalarNormalizedSpherePotential_matrixGauge f A hA hAnorm, Pi.sub_apply, sub_self,
    Function.comp_def] using hdiff

end ModifiedCartan
#print axioms ModifiedCartan.scalar_potential_comparable_difference_tendsto_zero

