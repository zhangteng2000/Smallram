import ModifiedCartan.SubsequenceRatios

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- LaTeX `prop:regular-variation`: every positive multiplier.
For large multipliers the proved small-multiplier limit is applied to its reciprocal. -/
theorem characteristic_ratio_tendsto {n : ℕ} (f : Curve n)
    (htrans : f.Transcendental) (hlin : f.linearlyNonDegenerate)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 0 < ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun r => characteristic f (t * r) / characteristic f r) atTop (𝓝 (t ^ ρ)) := by
  by_cases ht2 : t < 2
  · exact characteristic_ratio_tendsto_of_lt_two f htrans hlin hsmall hρ hl hu ht ht2
  have hit : 0 < t⁻¹ := inv_pos.mpr ht
  have hit2 : t⁻¹ < 2 := (inv_lt_one_of_one_lt₀ (by linarith : (1 : ℝ) < t)).trans (by norm_num)
  have hs := characteristic_ratio_tendsto_of_lt_two f htrans hlin hsmall hρ hl hu hit hit2
  have hc : Tendsto (fun r : ℝ => t * r) atTop atTop := Tendsto.const_mul_atTop ht tendsto_id
  have h := (hs.comp hc).inv₀ (Real.rpow_pos_of_pos hit ρ).ne'
  simpa only [Function.comp_def, ← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul,
    inv_div, Real.inv_rpow ht.le, inv_inv] using! h

end ModifiedCartan
#print axioms ModifiedCartan.characteristic_ratio_tendsto
