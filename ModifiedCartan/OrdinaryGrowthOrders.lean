import ModifiedCartan.StrongGrowthIndices

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- The literal logarithmic quotient underlying `eq:index-order-bounds`.
There is no cutoff in either the numerator or the denominator. -/
def ordinaryGrowthRatio (T : ℝ → ℝ) (r : ℝ) : EReal :=
  (Real.log (T r) / Real.log r : ℝ)

def upperGrowthOrder (T : ℝ → ℝ) : EReal := limsup (ordinaryGrowthRatio T) atTop

def lowerGrowthOrder (T : ℝ → ℝ) : EReal := liminf (ordinaryGrowthRatio T) atTop

theorem upperGrowthOrder_characteristic {n : ℕ} (f : Curve n) :
    upperGrowthOrder (characteristic f) = order f := rfl

theorem lowerGrowthOrder_characteristic {n : ℕ} (f : Curve n) :
    lowerGrowthOrder (characteristic f) = lowerOrder f := rfl

theorem lowerGrowthOrder_le_upperGrowthOrder (T : ℝ → ℝ) :
    lowerGrowthOrder T ≤ upperGrowthOrder T := liminf_le_limsup

theorem upperGrowthOrder_le_of_log_upper (T : ℝ → ℝ) {p C : ℝ}
    (hb : ∀ᶠ r : ℝ in atTop, Real.log (T r) ≤ p * Real.log r + C) :
    upperGrowthOrder T ≤ (p : EReal) := by
  have hc : Tendsto (fun r : ℝ => p + C / Real.log r) atTop (𝓝 p) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add (Real.tendsto_log_atTop.const_div_atTop C))
  have he : ∀ᶠ r : ℝ in atTop, ordinaryGrowthRatio T r ≤ ((p + C / Real.log r : ℝ) : EReal) := by
    filter_upwards [hb, eventually_ge_atTop (2 : ℝ)] with r hr hr2
    have hlog : 0 < Real.log r := Real.log_pos (by linarith)
    have hreal : Real.log (T r) / Real.log r ≤ p + C / Real.log r := by
      apply (div_le_iff₀ hlog).mpr
      have hcancel : (p + C / Real.log r) * Real.log r = p * Real.log r + C := by
        rw [add_mul, div_mul_cancel₀ C hlog.ne']
      rwa [hcancel]
    dsimp only [ordinaryGrowthRatio]
    exact_mod_cast hreal
  have hi := limsup_le_limsup he
  rw [(EReal.tendsto_coe.mpr hc).limsup_eq] at hi
  exact hi

theorem le_lowerGrowthOrder_of_log_lower (T : ℝ → ℝ) {p C : ℝ}
    (hb : ∀ᶠ r : ℝ in atTop, p * Real.log r + C ≤ Real.log (T r)) :
    (p : EReal) ≤ lowerGrowthOrder T := by
  have hc : Tendsto (fun r : ℝ => p + C / Real.log r) atTop (𝓝 p) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add (Real.tendsto_log_atTop.const_div_atTop C))
  have he : ∀ᶠ r : ℝ in atTop, ((p + C / Real.log r : ℝ) : EReal) ≤ ordinaryGrowthRatio T r := by
    filter_upwards [hb, eventually_ge_atTop (2 : ℝ)] with r hr hr2
    have hlog : 0 < Real.log r := Real.log_pos (by linarith)
    have hreal : p + C / Real.log r ≤ Real.log (T r) / Real.log r := by
      apply (le_div_iff₀ hlog).mpr
      have hcancel : (p + C / Real.log r) * Real.log r = p * Real.log r + C := by
        rw [add_mul, div_mul_cancel₀ C hlog.ne']
      rwa [hcancel]
    dsimp only [ordinaryGrowthRatio]
    exact_mod_cast hreal
  have hi := liminf_le_liminf he
  rw [(EReal.tendsto_coe.mpr hc).liminf_eq] at hi
  exact hi

end
end ModifiedCartan
#print axioms ModifiedCartan.upperGrowthOrder_le_of_log_upper
#print axioms ModifiedCartan.le_lowerGrowthOrder_of_log_lower
