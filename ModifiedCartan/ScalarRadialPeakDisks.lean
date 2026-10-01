import ModifiedCartan.ScalarPeakDisks

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- A whole compact positive radial interval has one uniform sector
neighborhood, in every unit direction. This supplies geometry for arbitrary
radii between consecutive dyadic scales. -/
theorem scalarFullSector_uniform_radial_disks {ρ L U : ℝ} (hρ : 0 < ρ)
    (hL : 0 < L) (hU : U < 2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : ℂ, ‖a‖ = 1 → ∀ t ∈ Icc L U,
      closedBall ((t : ℂ) * a) (4 * ε) ⊆ scalarFullSector a ρ := by
  let K : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Icc L U
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hKΩ : K ⊆ scalarFullSector 1 ρ := by
    rintro z ⟨t, ht, rfl⟩
    exact scalarFullSector_real_mem hρ (hL.trans_le ht.1) (ht.2.trans_lt hU)
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open
    (scalarFullSector_isOpen (a := (1 : ℂ)) one_ne_zero hρ) hKΩ
  refine ⟨δ / 4, by positivity, ?_⟩
  intro a ha t ht z hz
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha]; norm_num)
  have hz' : z / a ∈ cthickening δ K := by
    apply mem_cthickening_of_dist_le (z / a) (t : ℂ) δ K ⟨t, ht, rfl⟩
    rw [dist_eq_norm]
    have he : z / a - (t : ℂ) = (z - (t : ℂ) * a) / a := by field_simp
    rw [he, norm_div, ha, div_one]
    have hh : ‖z - (t : ℂ) * a‖ ≤ 4 * (δ / 4) := by
      simpa only [mem_closedBall, dist_eq_norm] using hz
    linarith
  have hh := scalarFullSector_mul_mem ha (hδΩ hz')
  simpa only [mul_div_cancel₀ _ ha0] using hh

end ModifiedCartan
#print axioms ModifiedCartan.scalarFullSector_uniform_radial_disks