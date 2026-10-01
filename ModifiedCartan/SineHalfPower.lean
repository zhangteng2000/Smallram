import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Data.Set.Countable

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem ae_sin_ne_zero : ∀ᵐ θ : ℝ, Real.sin θ ≠ 0 := by
  have he := (countable_range (fun j : ℤ => (j : ℝ) * Real.pi)).ae_notMem volume
  filter_upwards [he] with θ hθ
  intro hz
  obtain ⟨j, hj⟩ := Real.sin_eq_zero_iff.mp hz
  exact hθ ⟨j, hj⟩

theorem sine_half_power_bound {θ : ℝ} (hθ : 0 < θ) (hπ : θ ≤ Real.pi / 2) :
    |Real.sin θ| ^ (-(1 / 2 : ℝ)) ≤
      (2 / Real.pi) ^ (-(1 / 2 : ℝ)) * θ ^ (-(1 / 2 : ℝ)) := by
  have hpos : 0 < 2 / Real.pi * θ := mul_pos (div_pos (by norm_num) Real.pi_pos) hθ
  have hsin := Real.mul_le_sin hθ.le hπ
  have hsinpos : 0 < Real.sin θ := hpos.trans_le hsin
  rw [abs_of_pos hsinpos]
  have he := Real.rpow_le_rpow_of_nonpos hpos hsin (by norm_num : -(1 / 2 : ℝ) ≤ 0)
  rwa [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 / Real.pi) hθ.le] at he

theorem sine_half_power_periodic :
    Function.Periodic (fun θ : ℝ => |Real.sin θ| ^ (-(1 / 2 : ℝ))) Real.pi := by
  intro θ
  simp only [Real.sin_add_pi, abs_neg]

theorem sine_half_power_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun θ : ℝ => |Real.sin θ| ^ (-(1 / 2 : ℝ))) volume a b := by
  have hm : Measurable (fun θ : ℝ => |Real.sin θ| ^ (-(1 / 2 : ℝ))) := by fun_prop
  have hquarter : IntervalIntegrable (fun θ : ℝ => |Real.sin θ| ^ (-(1 / 2 : ℝ)))
      volume 0 (Real.pi / 2) := by
    apply ((intervalIntegral.intervalIntegrable_rpow' (by norm_num : -(1 : ℝ) < -(1 / 2 : ℝ))).const_mul
      ((2 / Real.pi) ^ (-(1 / 2 : ℝ)))).mono_fun' hm.aestronglyMeasurable
    filter_upwards [self_mem_ae_restrict (measurableSet_uIoc : MeasurableSet (uIoc (0 : ℝ) (Real.pi / 2)))]
      with θ hθ
    rw [uIoc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact sine_half_power_bound hθ.1 hθ.2
  have hquarter' := hquarter.comp_sub_left Real.pi
  have he : Real.pi - Real.pi / 2 = Real.pi / 2 := by ring
  simp only [sub_zero, he, Real.sin_pi_sub] at hquarter'
  have hhalf : IntervalIntegrable (fun θ : ℝ => |Real.sin θ| ^ (-(1 / 2 : ℝ)))
      volume 0 Real.pi := hquarter.trans hquarter'.symm
  apply sine_half_power_periodic.intervalIntegrable Real.pi_ne_zero (t := 0) _ a b
  simpa only [zero_add] using hhalf

end ModifiedCartan
#print axioms ModifiedCartan.sine_half_power_intervalIntegrable
