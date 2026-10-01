import ModifiedCartan.ScalarSectorRoots

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- A branch-independent continuous representative of the scalar angular
profile. The actual coefficient is constrained to a fixed circle below. -/
noncomputable def scalarQuadraticProfile (m : ℕ) (C z : ℂ) : ℝ :=
  Real.sqrt (2 * (‖C * z ^ m‖ + (C * z ^ m).re))

theorem scalarQuadraticProfile_nonneg (m : ℕ) (C z : ℂ) :
    0 ≤ scalarQuadraticProfile m C z := Real.sqrt_nonneg _

theorem scalarQuadraticProfile_sq (m : ℕ) (C z : ℂ) :
    (scalarQuadraticProfile m C z) ^ 2 = 2 * (‖C * z ^ m‖ + (C * z ^ m).re) := by
  apply Real.sq_sqrt
  have hh := (abs_le.mp (Complex.abs_re_le_norm (C * z ^ m))).1
  linarith

theorem continuous_scalarQuadraticProfile (m : ℕ) :
    Continuous (fun p : ℂ × ℂ => scalarQuadraticProfile m p.1 p.2) := by
  unfold scalarQuadraticProfile
  fun_prop

/-- The previously proved pointwise square formula gives the exact continuous
profile on the full disk, including the origin and zero rays. -/
theorem ArbitraryRadiusLimitData.scalar_quadratic_profile_of_monomial
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) {k : ℕ} {c : ℂ}
    (hcoeff : d.coefficient 0 = fun z => c * z ^ k) :
    EqOn (fun z => 2 * (d.U z).toReal)
      (scalarQuadraticProfile (k + 2) (-(c * ((ρ⁻¹ : ℝ) : ℂ) ^ 2))) (ball (0 : ℂ) 2) := by
  intro z hz
  dsimp only
  by_cases hz0 : z = 0
  · subst z
    simp only [d.origin_zero, EReal.toReal_zero, mul_zero, scalarQuadraticProfile,
      zero_pow (by omega : k + 2 ≠ 0), norm_zero, Complex.zero_re, add_zero, Real.sqrt_zero]
  have hn : ‖z‖ < 2 := by simpa only [mem_ball, dist_zero_right] using hz
  have hsq := d.scalar_norm_square hρ hz0 hn
  change (d.U z).toReal ^ 2 = (‖d.scalarQuadratic z‖ + (d.scalarQuadratic z).re) / 2 at hsq
  rw [d.scalarQuadratic_eq_monomial hcoeff z] at hsq
  obtain ⟨b, _, hU⟩ := d.scalar_norm_value_root hρ hz0 hn
  have hUn : 0 ≤ (d.U z).toReal := by rw [hU]; exact abs_nonneg _
  have hs := scalarQuadraticProfile_sq (k + 2) (-(c * ((ρ⁻¹ : ℝ) : ℂ) ^ 2)) z
  have hp := scalarQuadraticProfile_nonneg (k + 2) (-(c * ((ρ⁻¹ : ℝ) : ℂ) ^ 2)) z
  nlinarith

/-- Every actual scalar norm limit belongs to a single compact family of
continuous profiles. The modulus (pi/2)^2 is forced by the proved normalization. -/
theorem ArbitraryRadiusLimitData.scalar_exists_quadratic_profile
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) (hr : Tendsto r atTop atTop) {m : ℕ} (hm : ρ = (m : ℝ) / 2) :
    ∃ C : ℂ, ‖C‖ = (Real.pi / 2) ^ 2 ∧
      EqOn (fun z => 2 * (d.U z).toReal) (scalarQuadraticProfile m C) (ball (0 : ℂ) 2) := by
  obtain ⟨k, c, _, hdegree, hcoeff⟩ := d.scalar_coefficient_monomial_nonzero hρ hr
  have hkm : k + 2 = m := by
    have he : ((k + 2 : ℕ) : ℝ) = (m : ℝ) := by
      push_cast
      linarith
    exact_mod_cast he
  obtain ⟨a, ha1, _, hroot⟩ := d.scalar_exists_unit_peak_root hρ hr
  let C : ℂ := -(c * ((ρ⁻¹ : ℝ) : ℂ) ^ 2)
  have hC : ‖C‖ = (Real.pi / 2) ^ 2 := by
    have he := congrArg norm hroot
    change ‖(((Real.pi / 2 : ℝ) : ℂ)) ^ 2‖ = ‖d.scalarQuadratic a‖ at he
    rw [d.scalarQuadratic_eq_monomial hcoeff a] at he
    simp only [norm_mul, norm_pow, ha1, one_pow, mul_one] at he
    simpa only [norm_pow, Complex.norm_real, Real.norm_of_nonneg (half_pos Real.pi_pos).le] using he.symm
  refine ⟨C, hC, ?_⟩
  simpa only [hkm] using d.scalar_quadratic_profile_of_monomial hρ hcoeff

end ModifiedCartan
#print axioms ModifiedCartan.continuous_scalarQuadraticProfile
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_exists_quadratic_profile

