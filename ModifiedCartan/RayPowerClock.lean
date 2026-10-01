import ModifiedCartan.FirstOrderGaugeSolutions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

noncomputable def rayTime (ρ r : ℝ) : ℝ := r ^ ρ / ρ
noncomputable def rayRadius (ρ t : ℝ) : ℝ := (ρ * t) ^ ρ⁻¹

theorem rayRadius_pos {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) :
    0 < rayRadius ρ t := Real.rpow_pos_of_pos (mul_pos hρ ht) _

theorem rayTime_pos {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) :
    0 < rayTime ρ r := div_pos (Real.rpow_pos_of_pos hr _) hρ

theorem rayRadius_pow_order {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) :
    rayRadius ρ t ^ ρ = ρ * t :=
  Real.rpow_inv_rpow (mul_pos hρ ht).le hρ.ne'

theorem rayTime_radius {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) :
    rayTime ρ (rayRadius ρ t) = t := by
  rw [rayTime, rayRadius_pow_order hρ ht, mul_div_cancel_left₀ _ hρ.ne']

theorem rayRadius_time {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) :
    rayRadius ρ (rayTime ρ r) = r := by
  rw [rayRadius, rayTime, mul_div_cancel₀ _ hρ.ne', Real.rpow_rpow_inv hr.le hρ.ne']

theorem rayTime_hasDerivAt {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) :
    HasDerivAt (rayTime ρ) (r ^ (ρ - 1)) r := by
  have hd := (Real.hasDerivAt_rpow_const (p := ρ) (Or.inl hr.ne')).div_const ρ
  simpa only [rayTime, mul_div_cancel_left₀ _ hρ.ne'] using! hd

theorem rayRadius_hasDerivAt {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) :
    HasDerivAt (rayRadius ρ) (rayRadius ρ t ^ (1 - ρ)) t := by
  have hm : HasDerivAt (fun u : ℝ => ρ * u) ρ t := by
    simpa only [id_eq, mul_one] using! (hasDerivAt_id t).const_mul ρ
  have hd := (Real.hasDerivAt_rpow_const (p := ρ⁻¹) (Or.inl (mul_pos hρ ht).ne')).comp t hm
  have he : ρ⁻¹ * (ρ * t) ^ (ρ⁻¹ - 1) * ρ = rayRadius ρ t ^ (1 - ρ) := by
    rw [rayRadius, ← Real.rpow_mul (mul_pos hρ ht).le,
      show ρ⁻¹ * (1 - ρ) = ρ⁻¹ - 1 by field_simp]
    field_simp
  simpa only [Function.comp_apply, he, rayRadius] using! hd

theorem rayTime_tendsto {ρ : ℝ} (hρ : 0 < ρ) : Tendsto (rayTime ρ) atTop atTop := by
  unfold rayTime
  exact (tendsto_rpow_atTop hρ).atTop_div_const hρ

theorem rayRadius_tendsto {ρ : ℝ} (hρ : 0 < ρ) : Tendsto (rayRadius ρ) atTop atTop := by
  unfold rayRadius
  exact (tendsto_rpow_atTop (inv_pos.mpr hρ)).comp (tendsto_id.const_mul_atTop hρ)

theorem rayRadius_power_hasDerivAt {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) (a : ℝ) :
    HasDerivAt (fun u => rayRadius ρ u ^ a)
      ((a / (ρ * t)) * rayRadius ρ t ^ a) t := by
  have hr := rayRadius_pos hρ ht
  have hd := (Real.hasDerivAt_rpow_const (p := a) (Or.inl hr.ne')).comp t
    (rayRadius_hasDerivAt hρ ht)
  apply hd.congr_deriv
  calc
    _ = a * (rayRadius ρ t ^ (a - 1) * rayRadius ρ t ^ (1 - ρ)) := by ring
    _ = a * rayRadius ρ t ^ (a - ρ) := by rw [← Real.rpow_add hr]; congr 2; ring
    _ = a * (rayRadius ρ t ^ a / rayRadius ρ t ^ ρ) := by rw [Real.rpow_sub hr]
    _ = _ := by rw [rayRadius_pow_order hρ ht]; ring

end ModifiedCartan
#print axioms ModifiedCartan.rayRadius_hasDerivAt
#print axioms ModifiedCartan.rayRadius_power_hasDerivAt

