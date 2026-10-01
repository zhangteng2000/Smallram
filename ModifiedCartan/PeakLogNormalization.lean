import ModifiedCartan.PeakScaleBounds

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem tendsto_atTop_of_logarithmic_lower_bound (T : ℝ → ℝ) {C : ℝ}
    (hb : ∀ r, 1 ≤ r → Real.log r - C ≤ T r) : Tendsto T atTop atTop := by
  have ht : Tendsto (fun r : ℝ => Real.log r - C) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-C) Real.tendsto_log_atTop
  exact tendsto_atTop_mono' atTop ((eventually_ge_atTop 1).mono (fun r hr => hb r hr)) ht

/-- The exact log-radius normalization required for the representation at
positive-order peaks. A logarithmic lower bound suffices; a global rationality
criterion is not required. This alternative is recorded in FORMALIZATION_MAP.md. -/
theorem peak_log_radius_div_scale_tendsto_zero (T : ℝ → ℝ)
    (hT : ∀ r, 0 < r → 0 < T r) {r ε : ℕ → ℝ} {μ C : ℝ}
    (hrpos : ∀ n, 0 < r n) (hr : Tendsto r atTop atTop)
    (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0)) (hμ : 0 < μ)
    (hpeak : ∀ n t, ε n ≤ t → t ≤ (ε n)⁻¹ →
      T (t * r n) ≤ (1 + ε n) * t ^ μ * T (r n))
    (hlower : ∀ x, 1 ≤ x → Real.log x - C ≤ T x) :
    Tendsto (fun n => Real.log (r n) / T (r n)) atTop (𝓝 0) := by
  have hS : Tendsto (fun n => T (r n)) atTop atTop :=
    (tendsto_atTop_of_logarithmic_lower_bound T hlower).comp hr
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [hr.eventually_ge_atTop 1] with n hn
    exact ha.trans_le (div_nonneg (Real.log_nonneg hn) (hT _ (hrpos n)).le)
  · intro δ hδ
    let a := Real.exp (Real.log (δ / 8) / μ)
    have ha : 0 < a := Real.exp_pos _
    have hpow : a ^ μ = δ / 8 := by
      rw [Real.rpow_def_of_pos ha, Real.log_exp,
        div_mul_cancel₀ _ hμ.ne', Real.exp_log (by positivity : 0 < δ / 8)]
    have hc : Tendsto (fun n => (C - Real.log a) / T (r n)) atTop (𝓝 0) :=
      hS.const_div_atTop (C - Real.log a)
    filter_upwards [peak_fixed_scale_eventual_bound T hT hrpos hεpos hε hpeak ha,
      hr.eventually_ge_atTop (1 / a), hc.eventually_lt_const (by linarith : 0 < δ / 2)]
      with n hn hnbase hnerr
    have hbase : 1 ≤ a * r n := by
      have he := (div_le_iff₀ ha).mp hnbase
      nlinarith
    have hl := hlower (a * r n) hbase
    rw [Real.log_mul ha.ne' (hrpos n).ne'] at hl
    have hnum : Real.log (r n) ≤ (2 * a ^ μ) * T (r n) + (C - Real.log a) := by linarith
    have hratio : Real.log (r n) / T (r n) ≤ 2 * a ^ μ + (C - Real.log a) / T (r n) := by
      apply (div_le_iff₀ (hT _ (hrpos n))).mpr
      rw [add_mul, div_mul_cancel₀ _ (hT _ (hrpos n)).ne']
      exact hnum
    rw [hpow] at hratio
    linarith

end
end ModifiedCartan
#print axioms ModifiedCartan.peak_log_radius_div_scale_tendsto_zero
