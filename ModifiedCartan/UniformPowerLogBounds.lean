import ModifiedCartan.StrongIndexPowerBounds

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem log_upper_of_uniform_power_upper (T : ℝ → ℝ)
    (hT : ∀ r, 0 < r → 0 < T r) {p C X r0 : ℝ}
    (hC : 0 < C) (hX : 1 ≤ X) (hr0 : 1 ≤ r0)
    (hb : ∀ x r, X ≤ x → r0 ≤ r → T (x * r) ≤ C * x ^ p * T r) :
    ∃ K : ℝ, ∀ᶠ r : ℝ in atTop, Real.log (T r) ≤ p * Real.log r + K := by
  have hr0pos : 0 < r0 := zero_lt_one.trans_le hr0
  refine ⟨Real.log C - p * Real.log r0 + Real.log (T r0), ?_⟩
  filter_upwards [eventually_ge_atTop (max 2 (X * r0))] with r hr
  have hr2 : 2 ≤ r := (le_max_left _ _).trans hr
  have hrpos : 0 < r := by linarith
  have hx : X ≤ r / r0 := (le_div_iff₀ hr0pos).mpr ((le_max_right _ _).trans hr)
  have hxpos := div_pos hrpos hr0pos
  have hb' := hb (r / r0) r0 hx le_rfl
  rw [div_mul_cancel₀ r hr0pos.ne'] at hb'
  have hl := Real.log_le_log (hT r hrpos) hb'
  rw [Real.log_mul (mul_pos hC (Real.rpow_pos_of_pos hxpos p)).ne' (hT r0 hr0pos).ne',
    Real.log_mul hC.ne' (Real.rpow_pos_of_pos hxpos p).ne', Real.log_rpow hxpos,
    Real.log_div hrpos.ne' hr0pos.ne'] at hl
  nlinarith

theorem log_lower_of_uniform_power_lower (T : ℝ → ℝ)
    (hT : ∀ r, 0 < r → 0 < T r) {p c X r0 : ℝ}
    (hc : 0 < c) (hX : 1 ≤ X) (hr0 : 1 ≤ r0)
    (hb : ∀ x r, X ≤ x → r0 ≤ r → c * x ^ p * T r ≤ T (x * r)) :
    ∃ K : ℝ, ∀ᶠ r : ℝ in atTop, p * Real.log r + K ≤ Real.log (T r) := by
  have hr0pos : 0 < r0 := zero_lt_one.trans_le hr0
  refine ⟨Real.log c - p * Real.log r0 + Real.log (T r0), ?_⟩
  filter_upwards [eventually_ge_atTop (max 2 (X * r0))] with r hr
  have hr2 : 2 ≤ r := (le_max_left _ _).trans hr
  have hrpos : 0 < r := by linarith
  have hx : X ≤ r / r0 := (le_div_iff₀ hr0pos).mpr ((le_max_right _ _).trans hr)
  have hxpos := div_pos hrpos hr0pos
  have hb' := hb (r / r0) r0 hx le_rfl
  rw [div_mul_cancel₀ r hr0pos.ne'] at hb'
  have hl := Real.log_le_log (mul_pos (mul_pos hc (Real.rpow_pos_of_pos hxpos p))
    (hT r0 hr0pos)) hb'
  rw [Real.log_mul (mul_pos hc (Real.rpow_pos_of_pos hxpos p)).ne' (hT r0 hr0pos).ne',
    Real.log_mul hc.ne' (Real.rpow_pos_of_pos hxpos p).ne', Real.log_rpow hxpos,
    Real.log_div hrpos.ne' hr0pos.ne'] at hl
  nlinarith

theorem strongLowerIndex_nonneg (T : ℝ → ℝ)
    (hT : ∀ r, 0 < r → 0 < T r) (hm : MonotoneOn T (Ioi 0)) :
    0 ≤ strongLowerIndex T := by
  have he : ((0 : ℝ) : EReal) ≤ strongLowerIndex T := by
    apply le_strongLowerIndex_of_uniform_lower T hT
      (p := 0) (c := 1) (X := 1) (r0 := 1) zero_lt_one le_rfl le_rfl
    intro x r hx hr
    have hxpos : 0 < x := zero_lt_one.trans_le hx
    have hrpos : 0 < r := zero_lt_one.trans_le hr
    simp only [Real.rpow_zero, one_mul]
    exact hm hrpos (mul_pos hxpos hrpos) (by nlinarith)
  simpa only [EReal.coe_zero] using he

end
end ModifiedCartan
#print axioms ModifiedCartan.log_upper_of_uniform_power_upper
#print axioms ModifiedCartan.log_lower_of_uniform_power_lower
#print axioms ModifiedCartan.strongLowerIndex_nonneg
