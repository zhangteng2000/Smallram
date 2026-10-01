import ModifiedCartan.ScalarPhaseIsometry
import ModifiedCartan.ScalarPhasePeakLimits
import ModifiedCartan.ScalarFinitePeakTargets

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Finitely many convergent actual phase peaks give actual exponential cross
bounds on all their limiting full sectors, on one common physical subsequence.
The original curve is retained even if its coordinates vanish at the origin. -/
theorem scalar_phase_peaks_subsequence_crosses
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) {r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    {N : ℕ} {a : Fin N → ℕ → ℂ} {a₀ : Fin N → ℂ}
    (ha : ∀ j ν, ‖a j ν‖ = 1) (halim : ∀ j, Tendsto (a j) atTop (𝓝 (a₀ j)))
    (hpeak : ∀ j ν, scalarPhaseCoefficient f m (r ν) * (a j ν) ^ m =
      (((Real.pi / 2) ^ 2 : ℝ) : ℂ)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ j,
      HasSmallRectangleCrosses f (fun ν => r (ns ν)) (fun ν => characteristic f (r (ns ν)))
        (scalarFullSector (a₀ j) ρ) := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  obtain ⟨A, hA, hAnorm, ⟨d⟩⟩ := Paper.exists_arbitrary_radius_limits f hlin htrans hsmall hρpos hl hu hr
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
  have hroots (j : Fin N) : ‖a₀ j‖ = 1 ∧ (((Real.pi / 2 : ℝ) : ℂ)) ^ 2 = d.scalarQuadratic (a₀ j) := by
    apply d.scalar_phase_peak_limit hlinA htransA hsmallA hρ hlA huA hr hm
      (fun ν => ha j (d.subseq ν)) ((halim j).comp d.strictMono.tendsto_atTop)
    intro ν
    simpa only [scalarPhaseCoefficient_matrixGauge f A hA hAnorm, Function.comp_def] using hpeak j (d.subseq ν)
  obtain ⟨ns, hns, hcross⟩ := d.scalar_finite_peak_crosses hlinA htransA hsmallA hρ hlA huA hr
    a₀ (fun j => (hroots j).1) (fun j => (hroots j).2)
  refine ⟨d.subseq ∘ ns, d.strictMono.comp hns, ?_⟩
  intro j
  have hc := (hcross j).of_matrixGauge A hA hAnorm
  simpa only [hT, Function.comp_def] using hc

end ModifiedCartan
#print axioms ModifiedCartan.scalar_phase_peaks_subsequence_crosses
