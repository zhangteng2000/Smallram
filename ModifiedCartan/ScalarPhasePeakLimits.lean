import ModifiedCartan.ScalarPeakTracking

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- The unique continuous-profile coefficient is the actual coefficient of
z^m in the limiting scalar quadratic. -/
theorem ArbitraryRadiusLimitData.scalarQuadratic_eq_of_profile
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) (hr : Tendsto r atTop atTop) {m : ℕ} (hm : ρ = (m : ℝ) / 2)
    {C : ℂ} (hC : ‖C‖ = (Real.pi / 2) ^ 2)
    (hprofile : EqOn (fun z => 2 * (d.U z).toReal) (scalarQuadraticProfile m C) (ball (0 : ℂ) 2))
    (z : ℂ) : d.scalarQuadratic z = C * z ^ m := by
  obtain ⟨k, c, _, hdegree, hcoeff⟩ := d.scalar_coefficient_monomial_nonzero hρ hr
  have hkm : k + 2 = m := by
    have he : ((k + 2 : ℕ) : ℝ) = (m : ℝ) := by push_cast; linarith
    exact_mod_cast he
  let D : ℂ := -(c * ((ρ⁻¹ : ℝ) : ℂ) ^ 2)
  have hD : ‖D‖ = (Real.pi / 2) ^ 2 := by
    obtain ⟨a, ha1, _, hroot⟩ := d.scalar_exists_unit_peak_root hρ hr
    have he := congrArg norm hroot
    change ‖(((Real.pi / 2 : ℝ) : ℂ)) ^ 2‖ = ‖d.scalarQuadratic a‖ at he
    rw [d.scalarQuadratic_eq_monomial hcoeff a] at he
    simp only [norm_mul, norm_pow, ha1, one_pow, mul_one] at he
    simpa only [Complex.norm_real, Real.norm_of_nonneg (half_pos Real.pi_pos).le] using he.symm
  have hDprofile : EqOn (fun z => 2 * (d.U z).toReal)
      (scalarQuadraticProfile m D) (ball (0 : ℂ) 2) := by
    simpa only [hkm] using d.scalar_quadratic_profile_of_monomial hρ hcoeff
  have hDC : D = C := by
    apply scalarQuadraticProfile_injective_of_norm_eq (m := m) (by omega) (hD.trans hC.symm)
    intro w hw
    have hw2 : w ∈ ball (0 : ℂ) 2 := ball_subset_ball (by norm_num) hw
    exact (hDprofile hw2).symm.trans (hprofile hw2)
  rw [d.scalarQuadratic_eq_monomial hcoeff z, hkm]
  exact congrArg (fun b => b * z ^ m) hDC

/-- Any convergent sequence of coherently chosen actual phase peaks is an
actual unit peak root of the arbitrary-radius limit. -/
theorem ArbitraryRadiusLimitData.scalar_phase_peak_limit
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    (hr : Tendsto r atTop atTop) {m : ℕ} (hm : ρ = (m : ℝ) / 2)
    {a : ℕ → ℂ} {a₀ : ℂ} (ha : ∀ ν, ‖a ν‖ = 1) (halim : Tendsto a atTop (𝓝 a₀))
    (hpeak : ∀ ν, scalarPhaseCoefficient f m (r (d.subseq ν)) * (a ν) ^ m =
      (((Real.pi / 2) ^ 2 : ℝ) : ℂ)) :
    ‖a₀‖ = 1 ∧ (((Real.pi / 2 : ℝ) : ℂ)) ^ 2 = d.scalarQuadratic a₀ := by
  obtain ⟨C, hC, hprofile⟩ := d.scalar_exists_quadratic_profile hρ hr hm
  have hphase := d.scalarPhaseCoefficient_tendsto hlin htrans hsmall hρ hl hu hr hm hC hprofile
  have hp := hphase.mul (halim.pow m)
  have hconst : Tendsto
      (fun ν => scalarPhaseCoefficient f m (r (d.subseq ν)) * (a ν) ^ m)
      atTop (𝓝 ((((Real.pi / 2) ^ 2 : ℝ) : ℂ))) := by
    exact (tendsto_congr' (Eventually.of_forall hpeak)).mpr tendsto_const_nhds
  have he := tendsto_nhds_unique hp hconst
  have hn : ‖a₀‖ = 1 := tendsto_nhds_unique halim.norm
    ((tendsto_congr' (Eventually.of_forall ha)).mpr tendsto_const_nhds)
  refine ⟨hn, ?_⟩
  rw [d.scalarQuadratic_eq_of_profile hρ hr hm hC hprofile a₀]
  simpa only [Complex.ofReal_pow] using he.symm

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalarQuadratic_eq_of_profile
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_phase_peak_limit
