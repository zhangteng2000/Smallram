import ModifiedCartan.StrongGrowthIndices

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- Uniform power growth controls the actual upper strong index.
This is a converse estimate used to exclude an interval without peaks. -/
theorem strongUpperIndex_le_of_uniform_upper (T : ℝ → ℝ)
    (hT : ∀ r, 0 < r → 0 < T r) {p C X r0 : ℝ}
    (hC : 0 < C) (hX : 1 ≤ X) (hr0 : 1 ≤ r0)
    (hb : ∀ x r, X ≤ x → r0 ≤ r → T (x * r) ≤ C * x ^ p * T r) :
    strongUpperIndex T ≤ (p : EReal) := by
  unfold strongUpperIndex
  apply sSup_le
  rintro z ⟨q, hq, rfl⟩
  by_contra hqp
  change ¬ (q : EReal) ≤ (p : EReal) at hqp
  have hpq : p < q := by exact_mod_cast lt_of_not_ge hqp
  have he : ∀ᶠ xt : ℝ × ℝ in atTop, growthScaleRatio T q xt ≤ (C : EReal) := by
    filter_upwards [eventually_ge_atTop ((X, r0) : ℝ × ℝ)] with xt hxt
    have hx1 := hX.trans hxt.1
    have hr1 := hr0.trans hxt.2
    have hx0 := zero_lt_one.trans_le hx1
    have hrpos := zero_lt_one.trans_le hr1
    have hTr := hT xt.2 hrpos
    have hpows := Real.rpow_le_rpow_of_exponent_le hx1 hpq.le
    have hnum : T (xt.1 * xt.2) ≤ C * (xt.1 ^ q * T xt.2) := by
      have hle := (hb xt.1 xt.2 hxt.1 hxt.2).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpows hC.le) hTr.le)
      simpa only [mul_assoc] using hle
    have hd := mul_pos (Real.rpow_pos_of_pos hx0 q) hTr
    have hreal := (div_le_iff₀ hd).mpr hnum
    dsimp only [growthScaleRatio]
    exact_mod_cast hreal
  have hl : limsup (growthScaleRatio T q) atTop ≤ (C : EReal) := limsup_le_of_le (h := he)
  have hq' : limsup (growthScaleRatio T q) atTop = ⊤ := hq
  rw [hq'] at hl
  simp at hl

/-- A uniform positive lower power estimate controls the actual lower
strong index, directly from its joint liminf definition. -/
theorem le_strongLowerIndex_of_uniform_lower (T : ℝ → ℝ)
    (hT : ∀ r, 0 < r → 0 < T r) {p c X r0 : ℝ}
    (hc : 0 < c) (hX : 1 ≤ X) (hr0 : 1 ≤ r0)
    (hb : ∀ x r, X ≤ x → r0 ≤ r → c * x ^ p * T r ≤ T (x * r)) :
    (p : EReal) ≤ strongLowerIndex T := by
  unfold strongLowerIndex
  apply le_sInf
  rintro z ⟨q, hq, rfl⟩
  by_contra hpq
  change ¬ (p : EReal) ≤ (q : EReal) at hpq
  have hqp : q < p := by exact_mod_cast lt_of_not_ge hpq
  have he : ∀ᶠ xt : ℝ × ℝ in atTop, (c : EReal) ≤ growthScaleRatio T q xt := by
    filter_upwards [eventually_ge_atTop ((X, r0) : ℝ × ℝ)] with xt hxt
    have hx1 := hX.trans hxt.1
    have hr1 := hr0.trans hxt.2
    have hx0 := zero_lt_one.trans_le hx1
    have hrpos := zero_lt_one.trans_le hr1
    have hTr := hT xt.2 hrpos
    have hpows := Real.rpow_le_rpow_of_exponent_le hx1 hqp.le
    have hnum : c * (xt.1 ^ q * T xt.2) ≤ T (xt.1 * xt.2) := by
      have hle := (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpows hc.le) hTr.le).trans
        (hb xt.1 xt.2 hxt.1 hxt.2)
      simpa only [mul_assoc] using hle
    have hd := mul_pos (Real.rpow_pos_of_pos hx0 q) hTr
    have hreal := (le_div_iff₀ hd).mpr hnum
    dsimp only [growthScaleRatio]
    exact_mod_cast hreal
  have hl : (c : EReal) ≤ liminf (growthScaleRatio T q) atTop := le_liminf_of_le (h := he)
  have hq' : liminf (growthScaleRatio T q) atTop = 0 := hq
  rw [hq'] at hl
  have hreal : c ≤ 0 := by exact_mod_cast hl
  exact (not_le_of_gt hc) hreal

end
end ModifiedCartan
#print axioms ModifiedCartan.strongUpperIndex_le_of_uniform_upper
#print axioms ModifiedCartan.le_strongLowerIndex_of_uniform_lower
