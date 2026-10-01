import ModifiedCartan.NHElementaryBounds
import ModifiedCartan.DiskRegularRadius

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem inverse_le_four_control {δ x B : ℝ} (hδ : 0 < δ) (hx : δ / 4 ≤ x) (hB : δ⁻¹ ≤ B) :
    x⁻¹ ≤ 4 * B := by
  have hh := one_div_le_one_div_of_le (div_pos hδ (by norm_num : (0 : ℝ) < 4)) hx
  have he : x⁻¹ ≤ 4 * δ⁻¹ := by
    simp only [one_div] at hh
    rw [inv_div, div_eq_mul_inv] at hh
    exact hh
  linarith

/-- Quantitative internal boundary selection for LaTeX `lem:NH`. -/
theorem exists_NH_regular_radius {f : ℂ → ℂ} {r ρ B : ℝ}
    (hr : 0 < r) (hrρ : r < ρ) (hρB : ρ ≤ B) (hδB : (ρ - r)⁻¹ ≤ B)
    (hf : MeromorphicOn f (closedBall 0 ρ)) (hfa : AnalyticAt ℂ f 0) (h0 : f 0 ≠ 0) :
    ∃ R s : ℝ, r < R ∧ R < ρ ∧ r < s ∧ s < R ∧ R ≤ B ∧
      (R - s)⁻¹ ≤ 4 * B ∧ (s - r)⁻¹ ≤ 4 * B ∧
      (Real.log (ρ / R))⁻¹ ≤ 4 * B ^ 2 ∧
      ∀ w ∈ sphere (0 : ℂ) R, AnalyticAt ℂ f w ∧ f w ≠ 0 := by
  obtain ⟨R, hRl, hRu, hb⟩ := exists_regular_radius_between
    (a := (r + ρ) / 2) (b := (r + 3 * ρ) / 4)
    (by linarith) (by linarith) (by linarith) hf hfa h0
  have hrR : r < R := by linarith
  have hRρ : R < ρ := by linarith
  have hR := hr.trans hrR
  have hB := (hr.trans hrρ).trans_le hρB
  let s := (r + R) / 2
  have hrs : r < s := by dsimp [s]; linarith
  have hsR : s < R := by dsimp [s]; linarith
  have hRs : (R - s)⁻¹ ≤ 4 * B :=
    inverse_le_four_control (sub_pos.mpr hrρ) (by dsimp [s]; linarith) hδB
  have hsr : (s - r)⁻¹ ≤ 4 * B :=
    inverse_le_four_control (sub_pos.mpr hrρ) (by dsimp [s]; linarith) hδB
  have hρR : (ρ - R)⁻¹ ≤ 4 * B :=
    inverse_le_four_control (sub_pos.mpr hrρ) (by linarith) hδB
  refine ⟨R, s, hrR, hRρ, hrs, hsR, hRρ.le.trans hρB, hRs, hsr, ?_, hb⟩
  calc
    _ ≤ ρ / (ρ - R) := inverse_log_ratio_le hR hRρ
    _ = ρ * (ρ - R)⁻¹ := div_eq_mul_inv _ _
    _ ≤ B * (4 * B) := mul_le_mul hρB hρR (inv_nonneg.mpr (sub_pos.mpr hRρ).le) hB.le
    _ = 4 * B ^ 2 := by ring

end ModifiedCartan
#print axioms ModifiedCartan.exists_NH_regular_radius


