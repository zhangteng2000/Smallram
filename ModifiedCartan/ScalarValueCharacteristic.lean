import ModifiedCartan.ScalarTheoremGrowth
import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem

open scoped Topology
open Filter Set Asymptotics
set_option autoImplicit false
namespace ModifiedCartan

/-- The actual scalar characteristic diverges for a transcendental meromorphic
function. Context: LaTeX `thm:A`; no order or ramification premise is needed. -/
theorem scalarCharacteristic_tendsto_atTop {f : ℂ → ℂ} (hf : Meromorphic f)
    (htrans : ScalarTranscendental f) : Tendsto (scalarCharacteristic f) atTop atTop := by
  obtain ⟨F, hFt, hFl, he, _, hD⟩ := exists_scalar_curve_lift hf htrans
  exact (scalarCharacteristic_isEquivalent_lift hf F hFt hFl he hD).symm.tendsto_atTop
    (characteristic_tendsto_atTop_of_transcendental F hFt)

/-- A finite target is represented exactly by the inverse shifted function. -/
theorem scalarValueCharacteristic_coe (f : ℂ → ℂ) (a : ℂ) :
    ValueDistribution.characteristic f (a : WithTop ℂ) =
      ValueDistribution.characteristic (f - fun _ => a)⁻¹ ⊤ := by
  simp only [ValueDistribution.characteristic,
    ValueDistribution.proximity_coe_eq_proximity_sub_const_zero,
    ValueDistribution.logCounting_coe_eq_logCounting_sub_const_zero,
    ValueDistribution.proximity_inv, ValueDistribution.logCounting_inv]

/-- Uniform first-main-theorem comparison for every value, including infinity
and every radius. Context: LaTeX `thm:A`, conclusion (b). -/
theorem scalarValueCharacteristic_abs_sub_le {f : ℂ → ℂ} (hf : Meromorphic f)
    (a : WithTop ℂ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ,
      |ValueDistribution.characteristic f a r - scalarCharacteristic f r| ≤ C := by
  induction a using WithTop.recTopCoe with
  | top => exact ⟨0, le_rfl, fun r => by simp⟩
  | coe a =>
    let g : ℂ → ℂ := f - fun _ => a
    have hg : Meromorphic g := hf.sub (Meromorphic.const a)
    let C₁ := Real.posLog ‖a‖ + Real.log 2
    let C₂ := max |Real.log ‖g 0‖| |Real.log ‖meromorphicTrailingCoeffAt g 0‖|
    refine ⟨C₁ + C₂, add_nonneg (add_nonneg Real.posLog_nonneg (Real.log_nonneg (by norm_num)))
      (le_trans (abs_nonneg _) (le_max_left _ _)), fun r => ?_⟩
    rw [scalarValueCharacteristic_coe]
    change |ValueDistribution.characteristic g⁻¹ ⊤ r - scalarCharacteristic f r| ≤ C₁ + C₂
    have h₁ := ValueDistribution.abs_characteristic_sub_characteristic_shift_le
      (a₀ := a) (r := r) hf
    have h₂ := ValueDistribution.characteristic_sub_characteristic_inv_le (R := r) hg
    calc
      |ValueDistribution.characteristic g⁻¹ ⊤ r - scalarCharacteristic f r| =
          |(ValueDistribution.characteristic g⁻¹ ⊤ r - ValueDistribution.characteristic g ⊤ r) +
            (ValueDistribution.characteristic g ⊤ r - scalarCharacteristic f r)| := by
              rw [sub_add_sub_cancel]
      _ ≤ |ValueDistribution.characteristic g⁻¹ ⊤ r - ValueDistribution.characteristic g ⊤ r| +
            |ValueDistribution.characteristic g ⊤ r - scalarCharacteristic f r| := abs_add_le _ _
      _ ≤ C₂ + C₁ := add_le_add
        (by simpa only [abs_sub_comm] using h₂)
        (by simpa only [g, C₁, scalarCharacteristic, Pi.sub_apply, abs_sub_comm] using! h₁)
      _ = C₁ + C₂ := add_comm _ _
/-- First main theorem normalized by the actual scalar characteristic. -/
theorem scalarValueCharacteristic_ratio_tendsto_one {f : ℂ → ℂ} (hf : Meromorphic f)
    (htrans : ScalarTranscendental f) (a : WithTop ℂ) :
    Tendsto (fun r => ValueDistribution.characteristic f a r / scalarCharacteristic f r)
      atTop (𝓝 1) := by
  obtain ⟨C, _, hC⟩ := scalarValueCharacteristic_abs_sub_le hf a
  have hT := scalarCharacteristic_tendsto_atTop hf htrans
  have he := isEquivalent_of_bounded_difference hT (Filter.Eventually.of_forall hC)
  exact (isEquivalent_iff_tendsto_one
    ((hT.eventually (eventually_gt_atTop 0)).mono fun _ hr => hr.ne')).mp he

end ModifiedCartan
#print axioms ModifiedCartan.scalarValueCharacteristic_ratio_tendsto_one


