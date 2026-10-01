import ModifiedCartan.ScalarSectorRoots

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

noncomputable def scalarFullSector (a : ℂ) (ρ : ℝ) : Set ℂ :=
  powerChart a ρ '' powerChartInnerDomain a ρ

theorem scalarFullSector_eq_positive {a : ℂ} {ρ c : ℝ} (hc : 0 < c) :
    scalarFullSector a ρ = scalarPositiveChart a ρ (c : ℂ) := by
  unfold scalarFullSector scalarPositiveChart
  rw [positivePowerChartDomain_real hc]

theorem scalarFullSector_isOpen {a : ℂ} (ha : a ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) :
    IsOpen (scalarFullSector a ρ) := by
  rw [scalarFullSector_eq_positive zero_lt_one]
  exact scalarPositiveChart_isOpen ha hρ 1

theorem scalarFullSector_isConnected {a : ℂ} (ha : a ≠ 0) (ha2 : ‖a‖ < 2)
    {ρ : ℝ} (hρ : 0 < ρ) : IsConnected (scalarFullSector a ρ) := by
  rw [scalarFullSector_eq_positive zero_lt_one]
  exact ⟨⟨a, self_mem_scalarPositiveChart ha ha2 hρ (by norm_num)⟩,
    scalarPositiveChart_isPreconnected a hρ 1⟩

theorem scalarFullSector_subset {a : ℂ} (ha : a ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) :
    scalarFullSector a ρ ⊆ ball (0 : ℂ) 2 := by
  rintro z ⟨w, hw, rfl⟩
  exact powerChartInnerDomain_mapsTo ha hρ hw

theorem ArbitraryRadiusLimitData.scalarFullSector_pos
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) {a : ℂ} (ha : a ≠ 0) {c : ℝ} (hc : 0 < c)
    (hroot : (c : ℂ) ^ 2 = d.scalarQuadratic a) :
    ∀ z ∈ scalarFullSector a ρ, 0 < (d.U z).toReal := by
  rw [scalarFullSector_eq_positive hc]
  exact d.scalar_norm_positiveChart_pos hρ ha (c : ℂ) hroot

/-- Distinct centers with the same nonzero quadratic root give disjoint full
positive charts. Equality of squares is resolved by positive real parts. -/
theorem ArbitraryRadiusLimitData.scalarFullSector_disjoint
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 0 < ρ) {a b c : ℂ} (hc : c ≠ 0)
    (ha : c ^ 2 = d.scalarQuadratic a) (hb : c ^ 2 = d.scalarQuadratic b) (hab : a ≠ b) :
    Disjoint (scalarFullSector a ρ) (scalarFullSector b ρ) := by
  apply Set.disjoint_left.mpr
  intro z hza hzb
  obtain ⟨w, hw, hwz⟩ := hza
  obtain ⟨v, hv, hvz⟩ := hzb
  have hQw := d.scalarQuadratic_powerChart hρ.ne' a (powerChartInnerDomain_subset hρ.le hw)
  have hQv := d.scalarQuadratic_powerChart hρ.ne' b (powerChartInnerDomain_subset hρ.le hv)
  rw [hwz, ← ha] at hQw
  rw [hvz, ← hb] at hQv
  have hs : w ^ 2 = v ^ 2 := mul_left_cancel₀ (pow_ne_zero 2 hc) (hQw.symm.trans hQv)
  have hwv : w = v := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with he | he
    · exact he
    · have hre := congrArg Complex.re he
      simp only [Complex.neg_re] at hre
      have hwpos : 0 < w.re := hw.1
      have hvpos : 0 < v.re := hv.1
      linarith
  have hw0 : w ≠ 0 := by intro he; rw [he] at hw; simpa using hw.1
  have hp0 : w ^ ((ρ⁻¹ : ℝ) : ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hw0)
  have he : a * w ^ ((ρ⁻¹ : ℝ) : ℂ) = b * w ^ ((ρ⁻¹ : ℝ) : ℂ) := by
    calc
      _ = z := hwz
      _ = b * v ^ ((ρ⁻¹ : ℝ) : ℂ) := hvz.symm
      _ = _ := by rw [hwv]
  exact hab (mul_right_cancel₀ hp0 he)

/-- Integer powers remove the half-order chart exponent without branch
ambiguity; this uses the exact natural-power complex identity. -/
theorem cpow_inverse_half_order {m : ℕ} {ρ : ℝ} (hρ : ρ ≠ 0)
    (hm : ρ = (m : ℝ) / 2) (w : ℂ) :
    (w ^ ((ρ⁻¹ : ℝ) : ℂ)) ^ m = w ^ 2 := by
  have hrel : (m : ℝ) = 2 * ρ := by linarith
  have heR : ρ⁻¹ * (m : ℝ) = 2 := by rw [hrel]; field_simp
  have he : ((ρ⁻¹ : ℝ) : ℂ) * (m : ℂ) = 2 := by exact_mod_cast heR
  rw [← Complex.cpow_mul_nat, he]
  exact Complex.cpow_natCast w 2

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalarFullSector_disjoint
#print axioms ModifiedCartan.cpow_inverse_half_order
