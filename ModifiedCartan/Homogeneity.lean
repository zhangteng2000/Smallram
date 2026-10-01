import ModifiedCartan.GoodCenterHomogeneity
import ModifiedCartan.SmallExponentNorm

open scoped Topology BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem ArbitraryRadiusLimitData.norm_limit_dilation_le_one
    {n : ℕ} {f : Curve n} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 2) :
    d.U ((s : ℂ) * z) = ((s ^ ρ : ℝ) : EReal) * d.U z := by
  have h24 : ball (0 : ℂ) 2 ⊆ ball 0 4 := ball_subset_ball (by norm_num)
  have hmap : MapsTo (fun x : ℂ => (s : ℂ) * x) (ball (0 : ℂ) 2) (ball 0 4) := by
    intro x hx
    have hnx : ‖x‖ < 2 := by simpa only [mem_ball, dist_zero_right] using hx
    rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    calc
      s * ‖x‖ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
      _ < 4 := by linarith
  obtain ⟨hfinite, hc⟩ := d.norm_limit_continuous
  have he : (fun x => (d.U ((s : ℂ) * x)).toReal) =ᵐ[volume.restrict (ball (0 : ℂ) 2)]
      (fun x => s ^ ρ * (d.U x).toReal) := by
    filter_upwards [d.good_centers.full_measure, ae_restrict_mem measurableSet_ball] with x hx hx2
    have hh := d.norm_limit_dilation_at_good_center hρ hx hs hs1
    rw [hfinite _ (hmap hx2), hfinite x (h24 hx2), ← EReal.coe_mul] at hh
    exact_mod_cast hh
  have hpoint := Measure.eqOn_open_of_ae_eq he isOpen_ball
    (hc.comp (continuous_const.mul continuous_id).continuousOn hmap)
    (continuousOn_const.mul (hc.mono h24))
  rw [hfinite _ (hmap hz), hfinite z (h24 hz), ← EReal.coe_mul]
  exact congrArg (fun x : ℝ => (x : EReal)) (hpoint hz)

namespace Paper

/-- LaTeX labels `prop:homogeneity` and `eq:homogeneity`.
The fixed norm limit from the actual arbitrary-radius construction is homogeneous
at every admissible radius, with no extra regularity or conformal assumptions. -/
theorem prop_homogeneity {n : ℕ} {f : Curve n} {r : ℕ → ℝ} {ρ : ℝ}
    (hρ : 0 < ρ) (d : ArbitraryRadiusLimitData f r ρ)
    {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 2) (htz : (t : ℂ) * z ∈ ball (0 : ℂ) 2) :
    d.U ((t : ℂ) * z) = ((t ^ ρ : ℝ) : EReal) * d.U z := by
  have h24 : ball (0 : ℂ) 2 ⊆ ball 0 4 := ball_subset_ball (by norm_num)
  rcases lt_or_ge ρ 1 with hsmall | hlarge
  · rw [d.norm_limit_eq_zero_of_order_lt_one hsmall _ (h24 htz),
      d.norm_limit_eq_zero_of_order_lt_one hsmall z (h24 hz), mul_zero]
  · by_cases ht1 : t ≤ 1
    · exact d.norm_limit_dilation_le_one hlarge ht ht1 hz
    · have hi : 0 < t⁻¹ := inv_pos.mpr ht
      have hi1 : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (le_of_lt (lt_of_not_ge ht1))
      have hrev := d.norm_limit_dilation_le_one hlarge hi hi1 htz
      have hcancel : ((t⁻¹ : ℝ) : ℂ) * ((t : ℂ) * z) = z := by
        rw [Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr ht.ne'), one_mul]
      obtain ⟨hfinite, _⟩ := d.norm_limit_continuous
      rw [hcancel, hfinite z (h24 hz), hfinite _ (h24 htz), ← EReal.coe_mul] at hrev
      have hreal : (d.U z).toReal = (t⁻¹) ^ ρ * (d.U ((t : ℂ) * z)).toReal := by exact_mod_cast hrev
      have hprod : t ^ ρ * (t⁻¹) ^ ρ = 1 := by
        rw [Real.inv_rpow ht.le ρ, mul_inv_cancel₀ (Real.rpow_pos_of_pos ht ρ).ne']
      rw [hfinite _ (h24 htz), hfinite z (h24 hz), ← EReal.coe_mul]
      apply congrArg (fun x : ℝ => (x : EReal))
      rw [hreal, ← mul_assoc, hprod, one_mul]

end Paper
end ModifiedCartan
#print axioms ModifiedCartan.Paper.prop_homogeneity
