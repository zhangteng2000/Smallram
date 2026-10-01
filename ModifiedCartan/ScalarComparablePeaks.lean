import ModifiedCartan.ScalarPeakTracking

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Transport a chosen actual peak to a comparable physical radius using the
constructed phase coefficient and the principal correction near one. -/
noncomputable def scalarComparablePeakCenter (f : Curve 1) (m : ℕ)
    (r c : ℝ) (a : ℂ) : ℂ :=
  a * scalarRootCorrection m (scalarPhaseCoefficient f m r) (scalarPhaseCoefficient f m (c * r))

theorem scalarComparablePeakCenter_norm (f : Curve 1) (m : ℕ) (r c : ℝ)
    {a : ℂ} (ha : ‖a‖ = 1) : ‖scalarComparablePeakCenter f m r c a‖ = 1 := by
  have hD : scalarPhaseCoefficient f m (c * r) ≠ 0 := norm_ne_zero_iff.mp (by
    rw [scalarPhaseCoefficient_norm]
    exact (sq_pos_of_pos (half_pos Real.pi_pos)).ne')
  rw [scalarComparablePeakCenter, norm_mul, ha,
    scalarRootCorrection_norm m hD ((scalarPhaseCoefficient_norm f m r).trans
      (scalarPhaseCoefficient_norm f m (c * r)).symm), one_mul]

theorem scalarComparablePeakCenter_peak (f : Curve 1) {m : ℕ} (hm : m ≠ 0) (r c : ℝ)
    {a : ℂ} (ha : scalarPhaseCoefficient f m r * a ^ m = (((Real.pi / 2) ^ 2 : ℝ) : ℂ)) :
    scalarPhaseCoefficient f m (c * r) * (scalarComparablePeakCenter f m r c a) ^ m =
      (((Real.pi / 2) ^ 2 : ℝ) : ℂ) := by
  have hD : scalarPhaseCoefficient f m (c * r) ≠ 0 := norm_ne_zero_iff.mp (by
    rw [scalarPhaseCoefficient_norm]
    exact (sq_pos_of_pos (half_pos Real.pi_pos)).ne')
  exact scalarRootCorrection_transports_peak hm hD ha

/-- Between arbitrary comparable radii the transported peak stays close to
the original unit peak, including when the peak direction itself rotates. -/
theorem scalarComparablePeakCenter_difference_tendsto_zero
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) {r c : ℕ → ℝ} {a : ℕ → ℂ}
    (hr : Tendsto r atTop atTop) (hc : ∀ ν, c ν ∈ Icc (1 : ℝ) 2) (ha : ∀ ν, ‖a ν‖ = 1) :
    Tendsto (fun ν => scalarComparablePeakCenter f m (r ν) (c ν) (a ν) - a ν) atTop (𝓝 0) := by
  have hslow : Tendsto (fun ν => scalarPhaseCoefficient f m (r ν) -
      scalarPhaseCoefficient f m (c ν * r ν)) atTop (𝓝 0) := by
    simpa only [neg_sub, neg_zero] using
      (scalarPhaseCoefficient_slow_change f hlin htrans hsmall hρ hl hu hm hr hc).neg
  have hcorr := scalarRootCorrection_tendsto_one m (sq_pos_of_pos (half_pos Real.pi_pos))
    (fun ν => scalarPhaseCoefficient_norm f m (c ν * r ν)) hslow
  have he (ν : ℕ) : ‖scalarComparablePeakCenter f m (r ν) (c ν) (a ν) - a ν‖ =
      ‖scalarRootCorrection m (scalarPhaseCoefficient f m (r ν))
        (scalarPhaseCoefficient f m (c ν * r ν)) - 1‖ := by
    have hh : scalarComparablePeakCenter f m (r ν) (c ν) (a ν) - a ν =
        a ν * (scalarRootCorrection m (scalarPhaseCoefficient f m (r ν))
          (scalarPhaseCoefficient f m (c ν * r ν)) - 1) := by
      rw [scalarComparablePeakCenter]; ring
    rw [hh, norm_mul, ha ν, one_mul]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [he, sub_self, norm_zero] using (hcorr.sub_const 1).norm

end ModifiedCartan
#print axioms ModifiedCartan.scalarComparablePeakCenter_peak
#print axioms ModifiedCartan.scalarComparablePeakCenter_difference_tendsto_zero