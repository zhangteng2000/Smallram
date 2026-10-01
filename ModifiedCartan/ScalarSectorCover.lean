import ModifiedCartan.ScalarSectorGeometry

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Every positive point belongs to one of the explicit full peak charts.
Its positive quadratic root constructs the chart preimage and center. -/
theorem ArbitraryRadiusLimitData.scalar_positive_sector_cover
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) {k : ℕ} {c a : ℂ} (hc : c ≠ 0)
    (hcoeff : d.coefficient 0 = fun z => c * z ^ k)
    (hm : ρ = ((k + 2 : ℕ) : ℝ) / 2) (ha1 : ‖a‖ = 1)
    (hbase : (((Real.pi / 2 : ℝ) : ℂ)) ^ 2 = d.scalarQuadratic a)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 2) (hpos : 0 < (d.U z).toReal) :
    ∃ j : Fin (k + 2), z ∈ scalarFullSector (scalarSectorCenter a (k + 2) j) ρ := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hz2 : ‖z‖ < 2 := by simpa only [mem_ball, dist_zero_right] using hz
  have hz0 : z ≠ 0 := by
    intro he
    simpa only [he, d.origin_zero, EReal.toReal_zero, lt_self_iff_false] using hpos
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha1]; norm_num)
  obtain ⟨q, hq, _, hqpos⟩ := d.scalar_exists_positive_root hρ hz0 hz2 hpos
  let B : ℝ := Real.pi / 2
  have hB : 0 < B := half_pos Real.pi_pos
  have hBc : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hB.ne'
  let w : ℂ := q / (B : ℂ)
  have hwpos : 0 < w.re := by
    simpa only [w, Complex.div_ofReal_re] using div_pos hqpos hB
  have hw0 : w ≠ 0 := by intro he; simpa only [he, Complex.zero_re, lt_self_iff_false] using hwpos
  have hqw : (B : ℂ) ^ 2 * w ^ 2 = d.scalarQuadratic z := by
    dsimp only [w]
    rw [div_pow, hq]
    change (B : ℂ) ^ 2 * (d.scalarQuadratic z / (B : ℂ) ^ 2) = d.scalarQuadratic z
    field_simp
  let A : ℂ := z / w ^ ((ρ⁻¹ : ℝ) : ℂ)
  have ht0 : w ^ ((ρ⁻¹ : ℝ) : ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hw0)
  have htPow := cpow_inverse_half_order hρpos.ne' hm w
  have hQA : d.scalarQuadratic A = (B : ℂ) ^ 2 := by
    rw [d.scalarQuadratic_eq_monomial hcoeff A]
    dsimp only [A]
    rw [div_pow, htPow]
    calc
      _ = d.scalarQuadratic z / w ^ 2 := by
        rw [d.scalarQuadratic_eq_monomial hcoeff z]
        ring
      _ = _ := by rw [← hqw]; field_simp
  obtain ⟨j, hj⟩ := d.scalar_peak_root_exhaust hρpos.ne' hc hcoeff ha0 (hQA.trans hbase)
  have hA1 : ‖A‖ = 1 := by rw [← hj]; exact scalarSectorCenter_norm ha1 _ j
  have hzrep : powerChart A ρ w = z := by
    change (z / w ^ ((ρ⁻¹ : ℝ) : ℂ)) * w ^ ((ρ⁻¹ : ℝ) : ℂ) = z
    exact div_mul_cancel₀ _ ht0
  have hnormz : ‖z‖ = ‖w‖ ^ ρ⁻¹ := by
    rw [← hzrep, powerChart, norm_mul, hA1, one_mul, Complex.norm_cpow_real]
  have hwlt : ‖w‖ < 2 ^ ρ := by
    have hh := Real.rpow_lt_rpow (norm_nonneg z) hz2 hρpos
    rwa [hnormz, Real.rpow_inv_rpow (norm_nonneg w) hρpos.ne'] at hh
  refine ⟨j, w, ⟨hwpos, ?_⟩, ?_⟩
  · simpa only [mem_ball, dist_zero_right, scalarSectorCenter_norm ha1 _ j, div_one] using hwlt
  · rw [hj]
    exact hzrep

/-- Exact finite decomposition of the actual positive norm region into m
disjoint nonempty open connected full charts, with m=2 rho. Auxiliary to thm:A (b).
This is geometry of the actual rescaling limit, not a deficiency assertion. -/
theorem ArbitraryRadiusLimitData.scalar_positive_disk_finite_sector_partition
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) (hr : Tendsto r atTop atTop) :
    ∃ (m : ℕ) (a : ℂ), 2 ≤ m ∧ ρ = (m : ℝ) / 2 ∧ ‖a‖ = 1 ∧
      Function.Injective (scalarSectorCenter a m) ∧
      (∀ j : Fin m, IsOpen (scalarFullSector (scalarSectorCenter a m j) ρ) ∧
        IsConnected (scalarFullSector (scalarSectorCenter a m j) ρ)) ∧
      (∀ i j : Fin m, i ≠ j →
        Disjoint (scalarFullSector (scalarSectorCenter a m i) ρ)
          (scalarFullSector (scalarSectorCenter a m j) ρ)) ∧
      (∀ z : ℂ, (z ∈ ball (0 : ℂ) 2 ∧ 0 < (d.U z).toReal) ↔
        ∃ j : Fin m, z ∈ scalarFullSector (scalarSectorCenter a m j) ρ) := by
  obtain ⟨k, c, hc, hdegree, hcoeff⟩ := d.scalar_coefficient_monomial_nonzero hρ hr
  obtain ⟨a, ha1, _, hbase⟩ := d.scalar_exists_unit_peak_root hρ hr
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hm : k + 2 ≠ 0 := by omega
  have hdegree' : ρ = ((k + 2 : ℕ) : ℝ) / 2 := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hdegree
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha1]; norm_num)
  have hinj := scalarSectorCenter_injective ha0 hm
  have hn (j : Fin (k + 2)) : ‖scalarSectorCenter a (k + 2) j‖ = 1 := scalarSectorCenter_norm ha1 _ j
  have hne (j : Fin (k + 2)) : scalarSectorCenter a (k + 2) j ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [hn j]; norm_num)
  have hroot (j : Fin (k + 2)) :
      (((Real.pi / 2 : ℝ) : ℂ)) ^ 2 = d.scalarQuadratic (scalarSectorCenter a (k + 2) j) :=
    hbase.trans (d.scalar_quadratic_mul_root (a := a) hcoeff (scalarSectorRotation_pow hm j.val)).symm
  refine ⟨k + 2, a, by omega, hdegree', ha1, hinj, ?_, ?_, ?_⟩
  · intro j
    exact ⟨scalarFullSector_isOpen (hne j) hρpos,
      scalarFullSector_isConnected (hne j) (by rw [hn j]; norm_num) hρpos⟩
  · intro i j hij
    exact d.scalarFullSector_disjoint hρpos
      (Complex.ofReal_ne_zero.mpr (half_pos Real.pi_pos).ne') (hroot i) (hroot j)
      (fun he => hij (hinj he))
  · intro z
    constructor
    · rintro ⟨hz, hp⟩
      exact d.scalar_positive_sector_cover hρ hc hcoeff hdegree' ha1 hbase hz hp
    · rintro ⟨j, hj⟩
      exact ⟨scalarFullSector_subset (hne j) hρpos hj,
        d.scalarFullSector_pos hρ (hne j) (half_pos Real.pi_pos) (hroot j) z hj⟩

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_positive_sector_cover
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_positive_disk_finite_sector_partition
