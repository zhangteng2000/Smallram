import ModifiedCartan.RationalCharacteristicGrowth

open scoped Topology
open Filter Set Asymptotics
set_option autoImplicit false
namespace ModifiedCartan

theorem quadratic_log_ratio_tendsto (a b c : ℝ) :
    Tendsto (fun r : ℝ =>
      (a * (Real.log r) ^ 2 + b * Real.log r + c) / (Real.log r) ^ 2)
      atTop (𝓝 a) := by
  have hb := Real.tendsto_log_atTop.const_div_atTop b
  have hc := (Real.tendsto_log_atTop.const_div_atTop c).div_atTop Real.tendsto_log_atTop
  have ht : Tendsto (fun r : ℝ => a + b / Real.log r + c / Real.log r / Real.log r)
      atTop (𝓝 a) := by simpa using (hb.const_add a).add hc
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
  have hn : Real.log r ≠ 0 := (Real.log_pos (by linarith : 1 < r)).ne'
  field_simp
  <;> ring

theorem tendsto_of_quadratic_log_bounds {T : ℝ → ℝ} {a b c d e : ℝ}
    (hb : ∀ᶠ r : ℝ in atTop,
      a * (Real.log r) ^ 2 + b * Real.log r + c ≤ T r ∧
      T r ≤ a * (Real.log r) ^ 2 + d * Real.log r + e) :
    Tendsto (fun r : ℝ => T r / (Real.log r) ^ 2) atTop (𝓝 a) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (quadratic_log_ratio_tendsto a b c) (quadratic_log_ratio_tendsto a d e)
  · filter_upwards [hb] with r hr
    exact div_le_div_of_nonneg_right hr.1 (sq_nonneg _)
  · filter_upwards [hb] with r hr
    exact div_le_div_of_nonneg_right hr.2 (sq_nonneg _)

theorem log_growth_zero_of_logsquare_limit {T : ℝ → ℝ} {c : ℝ} (hc : c ≠ 0)
    (ht : Tendsto (fun r : ℝ => T r / (Real.log r) ^ 2) atTop (𝓝 c)) :
    Tendsto (fun r : ℝ => Real.log (T r) / Real.log r) atTop (𝓝 0) := by
  have hsmall : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have hl := (ht.log hc).div_atTop Real.tendsto_log_atTop
  have hh := (hsmall.comp Real.tendsto_log_atTop).const_mul 2
  have hm : Tendsto (fun r : ℝ => Real.log (T r / (Real.log r) ^ 2) / Real.log r +
      2 * (Real.log (Real.log r) / Real.log r)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero, add_zero] using hl.add hh
  apply hm.congr'
  filter_upwards [ht.eventually_ne hc, eventually_ge_atTop (2 : ℝ)] with r hr hr2
  have hT : T r ≠ 0 := by intro he; exact hr (by simp [he])
  have hlog : Real.log r ≠ 0 := (Real.log_pos (by linarith : 1 < r)).ne'
  rw [Real.log_div hT (pow_ne_zero _ hlog), Real.log_pow]
  ring

theorem characteristic_logsquare_zero_of_polynomial_representation {n : ℕ} (f : Curve n)
    (hf : f.HasPolynomialRepresentation) :
    Tendsto (fun r : ℝ => characteristic f r / (Real.log r) ^ 2) atTop (𝓝 0) := by
  obtain ⟨A, B, hb⟩ := characteristic_log_bound_of_polynomial_representation f hf
  apply tendsto_of_quadratic_log_bounds (a := 0) (b := 0) (c := 0) (d := B) (e := A)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  constructor
  · simpa using characteristic_nonneg f (zero_lt_one.trans_le hr)
  · simpa only [zero_mul, zero_add, add_comm] using hb r hr

theorem transcendental_of_positive_characteristic_logsquare_limit {n : ℕ} (f : Curve n)
    {c : ℝ} (hc : 0 < c)
    (ht : Tendsto (fun r : ℝ => characteristic f r / (Real.log r) ^ 2) atTop (𝓝 c)) :
    f.Transcendental := by
  intro hp
  exact hc.ne' (tendsto_nhds_unique ht (characteristic_logsquare_zero_of_polynomial_representation f hp))

end ModifiedCartan
#print axioms ModifiedCartan.log_growth_zero_of_logsquare_limit
#print axioms ModifiedCartan.transcendental_of_positive_characteristic_logsquare_limit
