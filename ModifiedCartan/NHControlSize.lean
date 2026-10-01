import ModifiedCartan.DiskBoundaryMean

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

noncomputable def nhControl (f : ℂ → ℂ) (r ρ : ℝ) : ℝ :=
  1 + ρ + (ρ - r)⁻¹ + r⁻¹ + diskCharacteristic f ρ + Real.posLog (1 / ‖f 0‖)

/-- The exact five logarithmic contributions in LaTeX `lem:NH`, including
the positive logarithm of the negative central logarithm. -/
noncomputable def nhLogarithmicSize (f : ℂ → ℂ) (r ρ : ℝ) : ℝ :=
  1 + Real.posLog (diskCharacteristic f ρ) + Real.posLog (Real.posLog (1 / ‖f 0‖)) +
    Real.posLog ρ + Real.posLog (1 / (ρ - r)) + Real.posLog (1 / r)

theorem nhControl_bounds {f : ℂ → ℂ} {r ρ : ℝ} (hr : 0 < r) (hrρ : r < ρ)
    (hf : MeromorphicOn f (closedBall 0 ρ)) (hfa : AnalyticAt ℂ f 0) (h0 : f 0 ≠ 0) :
    1 ≤ nhControl f r ρ ∧ ρ ≤ nhControl f r ρ ∧ (ρ - r)⁻¹ ≤ nhControl f r ρ ∧
      r⁻¹ ≤ nhControl f r ρ ∧ diskCharacteristic f ρ ≤ nhControl f r ρ ∧
      Real.posLog (1 / ‖f 0‖) ≤ nhControl f r ρ := by
  have hρ := hr.trans hrρ
  have hT := diskCharacteristic_nonneg_of_regular_center hρ
    (by simpa only [abs_of_pos hρ] using hf) hfa h0
  have hδ : 0 ≤ (ρ - r)⁻¹ := inv_nonneg.mpr (sub_pos.mpr hrρ).le
  have hri : 0 ≤ r⁻¹ := inv_nonneg.mpr hr.le
  have hcentral : 0 ≤ Real.posLog (1 / ‖f 0‖) := Real.posLog_nonneg
  dsimp only [nhControl]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem nhLogarithmicSize_ge_one (f : ℂ → ℂ) (r ρ : ℝ) :
    1 ≤ nhLogarithmicSize f r ρ := by
  have h1 : 0 ≤ Real.posLog (diskCharacteristic f ρ) := Real.posLog_nonneg
  have h2 : 0 ≤ Real.posLog (Real.posLog (1 / ‖f 0‖)) := Real.posLog_nonneg
  have h3 : 0 ≤ Real.posLog ρ := Real.posLog_nonneg
  have h4 : 0 ≤ Real.posLog (1 / (ρ - r)) := Real.posLog_nonneg
  have h5 : 0 ≤ Real.posLog (1 / r) := Real.posLog_nonneg
  dsimp only [nhLogarithmicSize]
  linarith

theorem log_nhControl_le (f : ℂ → ℂ) (r ρ : ℝ) :
    Real.log (nhControl f r ρ) ≤ Real.log 6 + nhLogarithmicSize f r ρ - 1 := by
  have hh := Real.posLog_sum Finset.univ
    ![(1 : ℝ), ρ, (ρ - r)⁻¹, r⁻¹, diskCharacteristic f ρ, Real.posLog (1 / ‖f 0‖)]
  have he : (∑ i : Fin 6,
      ![(1 : ℝ), ρ, (ρ - r)⁻¹, r⁻¹, diskCharacteristic f ρ, Real.posLog (1 / ‖f 0‖)] i) =
      nhControl f r ρ := by simp [nhControl, Fin.sum_univ_succ, add_assoc]
  rw [he] at hh
  have hlog : Real.log (nhControl f r ρ) ≤ Real.posLog (nhControl f r ρ) := le_max_right _ _
  have h := hlog.trans hh
  simp only [Finset.card_univ, Fintype.card_fin] at h
  norm_num [Fin.sum_univ_succ] at h
  dsimp only [nhLogarithmicSize]
  simp only [one_div] at *
  linarith

theorem one_add_log_nhControl_le (f : ℂ → ℂ) (r ρ : ℝ) :
    1 + Real.log (nhControl f r ρ) ≤ (1 + Real.log 6) * nhLogarithmicSize f r ρ := by
  have hh := log_nhControl_le f r ρ
  have hs := nhLogarithmicSize_ge_one f r ρ
  have h6 : 0 ≤ Real.log (6 : ℝ) := Real.log_nonneg (by norm_num)
  nlinarith [mul_nonneg h6 (sub_nonneg.mpr hs)]

end ModifiedCartan
#print axioms ModifiedCartan.one_add_log_nhControl_le
