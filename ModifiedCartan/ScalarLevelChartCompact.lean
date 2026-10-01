import ModifiedCartan.ScalarLevelChart
import ModifiedCartan.ScalarPeakDisks

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem scalarLevelChart_antitone (a b : ℂ) (ρ : ℝ) :
    Antitone (scalarLevelChart a ρ b) := by
  intro ℓ t hℓt z hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact ⟨w, ⟨hw.1, hℓt.trans_lt hw.2⟩, rfl⟩

/-- A compact subset of the positive chart has a strictly positive level
margin. This uses its proved open directed cover by strict level regions. -/
theorem scalarPositiveChart_compact_level_margin {a b : ℂ} {ρ : ℝ}
    (ha : a ≠ 0) (hρ : 0 < ρ) {K : Set ℂ} (hK : IsCompact K)
    (hKΩ : K ⊆ scalarPositiveChart a ρ b) :
    ∃ ℓ > 0, K ⊆ scalarLevelChart a ρ b ℓ := by
  letI : Nonempty {ℓ : ℝ // 0 < ℓ} := ⟨⟨1, zero_lt_one⟩⟩
  let U : {ℓ : ℝ // 0 < ℓ} → Set ℂ := fun ℓ => scalarLevelChart a ρ b ℓ.val
  have hcover : K ⊆ ⋃ ℓ, U ℓ := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hKΩ hz
    refine mem_iUnion.mpr ⟨⟨(b * w).re / 2, half_pos hw.2⟩, w, ?_, rfl⟩
    refine ⟨hw.1, ?_⟩
    change (b * w).re / 2 < (b * w).re
    have hh : 0 < (b * w).re := hw.2
    linarith
  have hdir : Directed (· ⊆ ·) U := by
    intro ℓ t
    refine ⟨⟨min ℓ.val t.val, lt_min ℓ.property t.property⟩, ?_, ?_⟩
    · exact scalarLevelChart_antitone a b ρ (min_le_left _ _)
    · exact scalarLevelChart_antitone a b ρ (min_le_right _ _)
  obtain ⟨ℓ, hℓ⟩ := hK.elim_directed_cover U
    (fun ℓ => scalarLevelChart_isOpen ha hρ b ℓ.val) hcover hdir
  exact ⟨ℓ.val, ℓ.property, hℓ⟩

theorem scalarLevelChart_mul_mem {a z : ℂ} (ha : ‖a‖ = 1) {ρ ℓ : ℝ} {b : ℂ}
    (hz : z ∈ scalarLevelChart 1 ρ b ℓ) : a * z ∈ scalarLevelChart a ρ b ℓ := by
  obtain ⟨w, hw, rfl⟩ := hz
  refine ⟨w, ?_, ?_⟩
  · simpa only [levelPowerChartDomain, powerChartInnerDomain, ha, norm_one] using hw
  · simp only [powerChart, one_mul]

/-- Any fixed disk width admissible at every unit peak has one positive level
margin valid at every unit direction. In particular this applies to the
already constructed dyadic target data without altering its width or target. -/
theorem scalar_peak_disks_have_uniform_level_margin {ρ ε c : ℝ}
    (hρ : 0 < ρ) (hc : 0 < c)
    (hdisks : ∀ a : ℂ, ‖a‖ = 1 → closedBall a (4 * ε) ⊆ scalarFullSector a ρ) :
    ∃ ℓ > 0, ∀ a : ℂ, ‖a‖ = 1 →
      closedBall a (4 * ε) ⊆ scalarLevelChart a ρ (c : ℂ) ℓ := by
  have hK : closedBall (1 : ℂ) (4 * ε) ⊆ scalarPositiveChart 1 ρ (c : ℂ) := by
    rw [← scalarFullSector_eq_positive hc]
    exact hdisks 1 norm_one
  obtain ⟨ℓ, hℓ, hKℓ⟩ := scalarPositiveChart_compact_level_margin one_ne_zero hρ
    (isCompact_closedBall (1 : ℂ) (4 * ε)) hK
  refine ⟨ℓ, hℓ, ?_⟩
  intro a ha z hz
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha]; norm_num)
  have hz' : z / a ∈ closedBall (1 : ℂ) (4 * ε) := by
    rw [mem_closedBall, dist_eq_norm]
    have he : z / a - 1 = (z - a) / a := by field_simp
    rw [he, norm_div, ha, div_one]
    simpa only [mem_closedBall, dist_eq_norm] using hz
  have hh := scalarLevelChart_mul_mem ha (hKℓ hz')
  simpa only [mul_div_cancel₀ _ ha0] using hh

end ModifiedCartan
#print axioms ModifiedCartan.scalarPositiveChart_compact_level_margin
#print axioms ModifiedCartan.scalar_peak_disks_have_uniform_level_margin
