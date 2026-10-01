import ModifiedCartan.PolyaPeaks

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem monotoneOn_unbounded_tendsto_atTop (T : ℝ → ℝ)
    (hm : MonotoneOn T (Ioi 0)) (hunbounded : ∀ M, ∃ r, 0 < r ∧ M < T r) :
    Tendsto T atTop atTop := by
  apply tendsto_atTop.mpr
  intro M
  obtain ⟨r, hr, hMr⟩ := hunbounded M
  filter_upwards [eventually_ge_atTop r] with s hs
  exact hMr.le.trans (hm hr (hr.trans_le hs) hs)

theorem peak_window_eventually_contains {ε : ℕ → ℝ}
    (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0)) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n in atTop, ε n ≤ a ∧ a ≤ (ε n)⁻¹ := by
  filter_upwards [hε.eventually_lt_const ha,
    hε.eventually_lt_const (one_div_pos.mpr ha)] with n hn0 hn1
  refine ⟨hn0.le, ?_⟩
  have he : ε n * a ≤ 1 := (le_div_iff₀ ha).mp hn1.le
  have he' : a ≤ 1 / ε n := (le_div_iff₀ (hεpos n)).mpr (by nlinarith)
  simpa only [one_div] using he'

theorem peak_fixed_scale_eventual_bound (T : ℝ → ℝ)
    (hT : ∀ r, 0 < r → 0 < T r) {r ε : ℕ → ℝ} {μ : ℝ}
    (hr : ∀ n, 0 < r n) (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hpeak : ∀ n t, ε n ≤ t → t ≤ (ε n)⁻¹ →
      T (t * r n) ≤ (1 + ε n) * t ^ μ * T (r n))
    {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n in atTop, T (a * r n) ≤ 2 * a ^ μ * T (r n) := by
  filter_upwards [peak_window_eventually_contains hεpos hε ha,
    hε.eventually_lt_const zero_lt_one] with n hn hεn
  have hp := hpeak n a hn.1 hn.2
  exact hp.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith : 1 + ε n ≤ 2)
      (Real.rpow_pos_of_pos ha μ).le) (hT _ (hr n)).le)

/-- The fixed-multiplier limsup consequence immediately following LaTeX
`lem:peaks`, with exactly the peak exponent. -/
theorem peak_fixed_scale_ratio_limsup (T : ℝ → ℝ)
    (hT : ∀ r, 0 < r → 0 < T r) {r ε : ℕ → ℝ} {μ : ℝ}
    (hr : ∀ n, 0 < r n) (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hpeak : ∀ n t, ε n ≤ t → t ≤ (ε n)⁻¹ →
      T (t * r n) ≤ (1 + ε n) * t ^ μ * T (r n))
    {a : ℝ} (ha : 0 < a) :
    limsup (fun n => ((T (a * r n) / T (r n) : ℝ) : EReal)) atTop ≤ (a ^ μ : ℝ) := by
  have he : ∀ᶠ n in atTop,
      ((T (a * r n) / T (r n) : ℝ) : EReal) ≤ (((1 + ε n) * a ^ μ : ℝ) : EReal) := by
    filter_upwards [peak_window_eventually_contains hεpos hε ha] with n hn
    have hreal := (div_le_iff₀ (hT _ (hr n))).mpr (hpeak n a hn.1 hn.2)
    exact_mod_cast hreal
  have ht : Tendsto (fun n => (1 + ε n) * a ^ μ) atTop (𝓝 (a ^ μ)) := by
    have hsum : Tendsto (fun n => 1 + ε n) atTop (𝓝 (1 + (0 : ℝ))) :=
      tendsto_const_nhds.add hε
    simpa only [add_zero, one_mul] using hsum.mul_const (a ^ μ)
  have hi := limsup_le_limsup he
  rw [(EReal.tendsto_coe.mpr ht).limsup_eq] at hi
  exact hi

end
end ModifiedCartan
#print axioms ModifiedCartan.peak_fixed_scale_eventual_bound
#print axioms ModifiedCartan.peak_fixed_scale_ratio_limsup
