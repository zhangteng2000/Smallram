import ModifiedCartan.ScalarSectorGeometry
import ModifiedCartan.ComplexRect
import Mathlib.Topology.MetricSpace.Thickening

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Positive radii below two belong to the unit-centered full sector. -/
theorem scalarFullSector_real_mem {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t)
    (ht2 : t < 2) : (t : ℂ) ∈ scalarFullSector 1 ρ := by
  refine ⟨((t ^ ρ : ℝ) : ℂ), ?_, ?_⟩
  · constructor
    · exact Real.rpow_pos_of_pos ht ρ
    · simp only [powerChartInnerDomain, mem_ball, dist_zero_right, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg ht.le ρ), norm_one, div_one]
      exact Real.rpow_lt_rpow ht.le ht2 hρ
  · simpa only [powerChart_real 1 ρ (Real.rpow_nonneg ht.le ρ),
      Real.rpow_rpow_inv ht.le hρ.ne', mul_one]

/-- Rotating the unit peak rotates its entire full sector. -/
theorem scalarFullSector_mul_mem {a z : ℂ} (ha : ‖a‖ = 1) {ρ : ℝ}
    (hz : z ∈ scalarFullSector 1 ρ) : a * z ∈ scalarFullSector a ρ := by
  obtain ⟨w, hw, rfl⟩ := hz
  refine ⟨w, ?_, ?_⟩
  · simpa only [powerChartInnerDomain, ha, norm_one] using hw
  · simp only [powerChart, one_mul]

/-- A uniform disk size works at the unit peak and at its half-radius point,
for every unit center. This is pure geometry, independent of limit data. -/
theorem scalarFullSector_uniform_peak_disks {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : ℂ, ‖a‖ = 1 →
      closedBall a (4 * ε) ⊆ scalarFullSector a ρ ∧
      closedBall ((1 / 2 : ℂ) * a) (4 * ε) ⊆ scalarFullSector a ρ := by
  have ho := scalarFullSector_isOpen (a := (1 : ℂ)) one_ne_zero hρ
  have h1 : (1 : ℂ) ∈ scalarFullSector 1 ρ := by
    exact_mod_cast scalarFullSector_real_mem hρ zero_lt_one (by norm_num : (1 : ℝ) < 2)
  have hhalf : (1 / 2 : ℂ) ∈ scalarFullSector 1 ρ := by
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using scalarFullSector_real_mem hρ (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 2)
  obtain ⟨d₁, hd₁, hb₁⟩ := (isCompact_singleton (x := (1 : ℂ))).exists_cthickening_subset_open ho
    (singleton_subset_iff.mpr h1)
  obtain ⟨d₂, hd₂, hb₂⟩ := (isCompact_singleton (x := (1 / 2 : ℂ))).exists_cthickening_subset_open ho
    (singleton_subset_iff.mpr hhalf)
  let ε := min d₁ d₂ / 4
  have hε : 0 < ε := div_pos (lt_min hd₁ hd₂) (by norm_num)
  have hle₁ : 4 * ε ≤ d₁ := by dsimp only [ε]; linarith [min_le_left d₁ d₂]
  have hle₂ : 4 * ε ≤ d₂ := by dsimp only [ε]; linarith [min_le_right d₁ d₂]
  refine ⟨ε, hε, ?_⟩
  intro a ha
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha]; norm_num)
  have hrotate (c : ℂ) {d : ℝ} (hcd : closedBall c d ⊆ scalarFullSector 1 ρ)
      (hεd : 4 * ε ≤ d) : closedBall (c * a) (4 * ε) ⊆ scalarFullSector a ρ := by
    intro z hz
    have hh : z / a ∈ closedBall c d := by
      rw [mem_closedBall, dist_eq_norm]
      have he : z / a - c = (z - c * a) / a := by field_simp
      rw [he, norm_div, ha, div_one]
      exact (show ‖z - c * a‖ ≤ 4 * ε by simpa only [mem_closedBall, dist_eq_norm] using hz).trans hεd
    have hh' := scalarFullSector_mul_mem ha (hcd hh)
    simpa only [mul_div_cancel₀ _ ha0] using hh'
  constructor
  · simpa only [one_mul] using hrotate 1
      ((closedBall_subset_cthickening_singleton 1 d₁).trans hb₁) hle₁
  · exact hrotate (1 / 2) ((closedBall_subset_cthickening_singleton _ d₂).trans hb₂) hle₂

namespace ComplexRect

/-- An axis-aligned box with independently prescribed positive half-widths. -/
def box (a : ℂ) (w h : ℝ) (hw : 0 < w) (hh : 0 < h) : ComplexRect where
  left := a.re - w
  right := a.re + w
  bottom := a.im - h
  top := a.im + h
  horizontal_pos := by linarith
  vertical_pos := by linarith

theorem box_closed_subset_closedBall (a : ℂ) {w h : ℝ} (hw : 0 < w) (hh : 0 < h) :
    (box a w h hw hh).closed ⊆ closedBall a (w + h) := by
  intro z hz
  change (a.re - w ≤ z.re ∧ z.re ≤ a.re + w) ∧
    (a.im - h ≤ z.im ∧ z.im ≤ a.im + h) at hz
  rw [mem_closedBall, dist_eq_norm]
  have hre : |(z - a).re| ≤ w := by
    rw [Complex.sub_re, abs_le]; constructor <;> linarith [hz.1.1, hz.1.2]
  have him : |(z - a).im| ≤ h := by
    rw [Complex.sub_im, abs_le]; constructor <;> linarith [hz.2.1, hz.2.2]
  exact (Complex.norm_le_abs_re_add_abs_im (z - a)).trans (add_le_add hre him)

end ComplexRect
end ModifiedCartan
#print axioms ModifiedCartan.scalarFullSector_uniform_peak_disks
#print axioms ModifiedCartan.ComplexRect.box_closed_subset_closedBall