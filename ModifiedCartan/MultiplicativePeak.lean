import ModifiedCartan.LogGrowthProfile

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- Exponentiating an additive approximate peak gives exactly the
manuscript's multiplicative error factor, with no error in the exponent. -/
theorem multiplicative_peak_of_logarithmic_peak (T : ℝ → ℝ)
    (hT : ∀ r, 0 < r → 0 < T r) {μ x H ε : ℝ} (hε : 0 < ε)
    (hpeak : ∀ y, x - H ≤ y → y ≤ x + H →
      logGrowthProfile T y - μ * y ≤
        logGrowthProfile T x - μ * x + Real.log (1 + ε))
    {t : ℝ} (ht : 0 < t) (ht0 : -H ≤ Real.log t) (ht1 : Real.log t ≤ H) :
    T (t * Real.exp x) ≤ (1 + ε) * t ^ μ * T (Real.exp x) := by
  have hs := hpeak (Real.log t + x) (by linarith) (by linarith)
  simp only [logGrowthProfile, Real.exp_add, Real.exp_log ht] at hs
  have hl : Real.log (T (t * Real.exp x)) ≤
      Real.log (1 + ε) + Real.log t * μ + Real.log (T (Real.exp x)) := by
    nlinarith
  have he := Real.exp_le_exp.mpr hl
  rw [Real.exp_add, Real.exp_add, Real.exp_log (hT _ (mul_pos ht (Real.exp_pos x))),
    Real.exp_log (hT _ (Real.exp_pos x)), Real.exp_log (by linarith : 0 < 1 + ε),
    ← Real.rpow_def_of_pos ht μ] at he
  exact he

/-- An explicit strictly decreasing error sequence for LaTeX `lem:peaks`. -/
def polyaPeakEpsilon (n : ℕ) : ℝ := Real.exp (-((n : ℝ) + 1))

theorem polyaPeakEpsilon_pos (n : ℕ) : 0 < polyaPeakEpsilon n := Real.exp_pos _

theorem polyaPeakEpsilon_strictAnti : StrictAnti polyaPeakEpsilon := by
  intro i j hij
  apply Real.exp_lt_exp.mpr
  have hij' : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
  linarith

theorem polyaPeakEpsilon_tendsto : Tendsto polyaPeakEpsilon atTop (𝓝 0) := by
  exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_atTop_add_const_right atTop 1
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))

theorem logarithmic_window_of_polyaPeakEpsilon {n : ℕ} {t : ℝ}
    (ht0 : polyaPeakEpsilon n ≤ t) (ht1 : t ≤ (polyaPeakEpsilon n)⁻¹) :
    0 < t ∧ -((n : ℝ) + 1) ≤ Real.log t ∧ Real.log t ≤ (n : ℝ) + 1 := by
  have ht := (polyaPeakEpsilon_pos n).trans_le ht0
  refine ⟨ht, ?_, ?_⟩
  · have hl := Real.log_le_log (polyaPeakEpsilon_pos n) ht0
    simpa only [polyaPeakEpsilon, Real.log_exp] using hl
  · have he : (polyaPeakEpsilon n)⁻¹ = Real.exp ((n : ℝ) + 1) := by
      rw [polyaPeakEpsilon, Real.exp_neg, inv_inv]
    rw [he] at ht1
    have hl := Real.log_le_log ht ht1
    simpa only [Real.log_exp] using hl

end
end ModifiedCartan
#print axioms ModifiedCartan.multiplicative_peak_of_logarithmic_peak
#print axioms ModifiedCartan.polyaPeakEpsilon_tendsto
