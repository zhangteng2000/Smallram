import ModifiedCartan.ScalarSharpLevelCrosses
import ModifiedCartan.ScalarPhaseCrosses

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem HasRectangleCrossesAtRate.of_matrixGauge {f : Curve 1}
    (A : Matrix (Index 1) (Index 1) ℂ) (hA : IsUnit A.det)
    (hAnorm : ∀ x, euclideanNorm (fun j => ∑ k, x k * A k j) = euclideanNorm x)
    {r s : ℕ → ℝ} {Ω : Set ℂ} {κ : ℝ}
    (h : HasRectangleCrossesAtRate (f.matrixGauge A hA) r s Ω κ) :
    HasRectangleCrossesAtRate f r s Ω κ := by
  simpa only [HasRectangleCrossesAtRate, ScalarGoodCross,
    scalarSphericalSpeed_matrixGauge f A hA hAnorm] using h

/-- A convergent sequence of actual phase peaks supplies every sharp level
cross estimate for the original curve, on one constructed subsequence. -/
theorem scalar_phase_peak_subsequence_sharp_crosses
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) {r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    {a : ℕ → ℂ} {a₀ : ℂ} (ha : ∀ ν, ‖a ν‖ = 1) (halim : Tendsto a atTop (𝓝 a₀))
    (hpeak : ∀ ν, scalarPhaseCoefficient f m (r ν) * (a ν) ^ m =
      (((Real.pi / 2) ^ 2 : ℝ) : ℂ)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ κ > 0,
      HasRectangleCrossesAtRate f (fun ν => r (ns ν))
        (fun ν => characteristic f (r (ns ν)))
        (scalarLevelChart a₀ ρ ((Real.pi / 2 : ℝ) : ℂ) (κ / 2)) κ := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  obtain ⟨A, hA, hAnorm, ⟨d⟩⟩ := Paper.exists_arbitrary_radius_limits
    f hlin htrans hsmall hρpos hl hu hr
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
  have hroot : ‖a₀‖ = 1 ∧ (((Real.pi / 2 : ℝ) : ℂ)) ^ 2 = d.scalarQuadratic a₀ := by
    apply d.scalar_phase_peak_limit hlinA htransA hsmallA hρ hlA huA hr hm
      (fun ν => ha (d.subseq ν)) (halim.comp d.strictMono.tendsto_atTop)
    intro ν
    simpa only [scalarPhaseCoefficient_matrixGauge f A hA hAnorm, Function.comp_def] using hpeak (d.subseq ν)
  have ha₀ : a₀ ≠ 0 := norm_ne_zero_iff.mp (by rw [hroot.1]; norm_num)
  obtain ⟨ns, hns, hcross⟩ := d.scalar_exists_sharp_level_crosses
    hlinA htransA hsmallA hρ hlA huA hr ha₀ (by rw [hroot.1]; norm_num)
    ((Real.pi / 2 : ℝ) : ℂ) hroot.2 (half_pos Real.pi_pos)
  refine ⟨d.subseq ∘ ns, d.strictMono.comp hns, ?_⟩
  intro κ hκ
  have hh := (hcross κ hκ).of_matrixGauge A hA hAnorm
  simpa only [hT, Function.comp_def] using hh

end ModifiedCartan
#print axioms ModifiedCartan.scalar_phase_peak_subsequence_sharp_crosses
