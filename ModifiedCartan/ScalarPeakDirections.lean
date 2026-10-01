import ModifiedCartan.ScalarPeakChart

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

noncomputable def scalarSectorRotation (m j : ℕ) : ℂ :=
  circleMap 0 1 ((j : ℝ) * (2 * Real.pi) / (m : ℝ))

noncomputable def scalarSectorCenter (a : ℂ) (m : ℕ) (j : Fin m) : ℂ :=
  a * scalarSectorRotation m j.val

theorem scalarSectorRotation_norm (m j : ℕ) : ‖scalarSectorRotation m j‖ = 1 := by
  simp only [scalarSectorRotation, norm_circleMap_zero, abs_one]

theorem scalarSectorRotation_pow {m : ℕ} (hm : m ≠ 0) (j : ℕ) :
    (scalarSectorRotation m j) ^ m = 1 := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have he : (m : ℝ) * ((j : ℝ) * (2 * Real.pi) / (m : ℝ)) = (j : ℝ) * (2 * Real.pi) := by
    field_simp
  rw [scalarSectorRotation, circleMap_zero_pow, one_pow, he]
  simpa only [circleMap, Complex.ofReal_zero, zero_mul, Complex.exp_zero, Complex.ofReal_one,
    mul_one, zero_add] using (periodic_circleMap (0 : ℂ) 1).nat_mul_eq j

theorem scalarSectorRotation_injective {m : ℕ} (hm : m ≠ 0) :
    Function.Injective (fun j : Fin m => scalarSectorRotation m j.val) := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  have hmem (j : Fin m) : (j.val : ℝ) * (2 * Real.pi) / (m : ℝ) ∈ Ico 0 (2 * Real.pi) := by
    refine ⟨div_nonneg (mul_nonneg (Nat.cast_nonneg _) Real.two_pi_pos.le) hmR.le, ?_⟩
    apply (div_lt_iff₀ hmR).mpr
    have hj : (j.val : ℝ) < (m : ℝ) := by exact_mod_cast j.isLt
    simpa only [mul_comm] using mul_lt_mul_of_pos_right hj Real.two_pi_pos
  intro i j hij
  have he := injOn_circleMap_of_abs_sub_le' (c := (0 : ℂ)) (R := 1)
    (by norm_num : (1 : ℝ) ≠ 0) (by linarith : 2 * Real.pi - 0 ≤ 2 * Real.pi)
    (hmem i) (hmem j) hij
  have hp := (div_left_inj' hmR.ne').mp he
  have hv : (i.val : ℝ) = (j.val : ℝ) := mul_right_cancel₀ Real.two_pi_pos.ne' hp
  apply Fin.ext
  exact_mod_cast hv

theorem scalarSectorCenter_norm {a : ℂ} (ha : ‖a‖ = 1) (m : ℕ) (j : Fin m) :
    ‖scalarSectorCenter a m j‖ = 1 := by
  rw [scalarSectorCenter, norm_mul, ha, scalarSectorRotation_norm, mul_one]

theorem scalarSectorCenter_injective {a : ℂ} (ha : a ≠ 0) {m : ℕ} (hm : m ≠ 0) :
    Function.Injective (scalarSectorCenter a m) := by
  intro i j hij
  exact scalarSectorRotation_injective hm (mul_left_cancel₀ ha hij)

theorem ArbitraryRadiusLimitData.scalar_quadratic_mul_root
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    {k : ℕ} {c a ζ : ℂ} (hcoeff : d.coefficient 0 = fun z => c * z ^ k)
    (hζ : ζ ^ (k + 2) = 1) :
    -(d.coefficient 0 (a * ζ) * (a * ζ * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2) =
      -(d.coefficient 0 a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2) := by
  have hp : ζ ^ k * ζ ^ 2 = 1 := by rw [← pow_add]; exact hζ
  rw [hcoeff]
  dsimp only
  calc
    _ = -(c * a ^ k * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2) * (ζ ^ k * ζ ^ 2) := by
      rw [mul_pow]
      ring
    _ = _ := by rw [hp, mul_one]

/-- The scalar half-integer order supplies exactly m distinct explicit unit
peak centers, all with the actual positive real central root pi/2. -/
theorem ArbitraryRadiusLimitData.scalar_exists_finite_peak_centers
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) (hr : Tendsto r atTop atTop) :
    ∃ (m : ℕ) (a : ℂ), 2 ≤ m ∧ ρ = (m : ℝ) / 2 ∧ ‖a‖ = 1 ∧
      Function.Injective (scalarSectorCenter a m) ∧
      ∀ j : Fin m, ‖scalarSectorCenter a m j‖ = 1 ∧
        (((Real.pi / 2 : ℝ) : ℂ)) ^ 2 =
          -(d.coefficient 0 (scalarSectorCenter a m j) *
            (scalarSectorCenter a m j * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2) := by
  obtain ⟨k, c, _, hdegree, hcoeff⟩ := d.scalar_coefficient_monomial_nonzero hρ hr
  obtain ⟨a, ha1, _, hb⟩ := d.scalar_exists_unit_peak_root hρ hr
  have hm : k + 2 ≠ 0 := by omega
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha1]; norm_num)
  refine ⟨k + 2, a, by omega, ?_, ha1, scalarSectorCenter_injective ha0 hm, ?_⟩
  · simpa only [Nat.cast_add, Nat.cast_ofNat] using hdegree
  · intro j
    refine ⟨scalarSectorCenter_norm ha1 _ j, ?_⟩
    have he := d.scalar_quadratic_mul_root (a := a) hcoeff (scalarSectorRotation_pow hm j.val)
    exact hb.trans he.symm

end ModifiedCartan
#print axioms ModifiedCartan.scalarSectorRotation_injective
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_exists_finite_peak_centers
