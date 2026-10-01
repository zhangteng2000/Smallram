import ModifiedCartan.ZeroSharpMajorant
import ModifiedCartan.Counting
import Mathlib.Analysis.Complex.Liouville

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem quadratic_log_bound_iteratedDeriv {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hb : ∀ r : ℝ, 1 ≤ r → ∀ z : ℂ, ‖z‖ ≤ r →
      ‖f z‖ ≤ Real.exp ((Real.log r) ^ 2 / 2 + A * Real.log r + B)) (m : ℕ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ r : ℝ, 1 ≤ r → ∀ z : ℂ, ‖z‖ ≤ r →
      ‖iteratedDeriv m f z‖ ≤ Real.exp ((Real.log r) ^ 2 / 2 + C * Real.log r + D) := by
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hlf : 0 ≤ Real.log (m.factorial : ℝ) := Real.log_nonneg (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m))
  refine ⟨A + Real.log 2, B + A * Real.log 2 + (Real.log 2) ^ 2 / 2 +
    Real.log (m.factorial : ℝ), by positivity, by positivity, ?_⟩
  intro r hr z hz
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m hr0
    hf.diffContOnCl (C := Real.exp ((Real.log (2 * r)) ^ 2 / 2 + A * Real.log (2 * r) + B))
    (fun w hw => hb (2 * r) (by linarith) w (by
      have hdist : ‖w - z‖ = r := by simpa only [mem_sphere, dist_eq_norm] using hw
      have ht : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
        simpa only [sub_add_cancel] using norm_add_le (w - z) z
      linarith))
  have hp : 1 ≤ r ^ m := one_le_pow₀ hr
  apply hc.trans
  calc
    _ ≤ (m.factorial : ℝ) * Real.exp ((Real.log (2 * r)) ^ 2 / 2 + A * Real.log (2 * r) + B) :=
      div_le_self (by positivity) hp
    _ = _ := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hr0.ne']
      rw [← Real.exp_log hfac, ← Real.exp_add]
      simp only [Real.log_exp]
      congr 1
      ring

theorem logCounting_upper_of_quadratic_log_bound {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hb : ∀ r : ℝ, 1 ≤ r → ∀ z : ℂ, ‖z‖ ≤ r →
      ‖f z‖ ≤ Real.exp ((Real.log r) ^ 2 / 2 + A * Real.log r + B)) :
    ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r →
      ValueDistribution.logCounting f (0 : WithTop ℂ) r ≤
        (Real.log r) ^ 2 / 2 + A * Real.log r + C := by
  refine ⟨B - Real.log ‖meromorphicTrailingCoeffAt f 0‖, fun r hr => ?_⟩
  have hr0 := zero_lt_one.trans_le hr
  have hlog (z : ℂ) (hz : z ∈ sphere 0 |r|) :
      Real.log ‖f z‖ ≤ (Real.log r) ^ 2 / 2 + A * Real.log r + B := by
    by_cases hfz : f z = 0
    · simp only [hfz, norm_zero, Real.log_zero]
      exact add_nonneg (add_nonneg (by positivity) (mul_nonneg hA (Real.log_nonneg hr))) hB
    · apply (Real.log_le_iff_le_exp (norm_pos_iff.mpr hfz)).mpr
      apply hb r hr z
      simpa only [mem_sphere, dist_zero_right, abs_of_pos hr0] using hz.le
  have hint : CircleIntegrable (fun z => Real.log ‖f z‖) 0 r :=
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr hf).meromorphicOn.mono_set
      (Set.subset_univ _)).circleIntegrable_log_norm
  have hm := Real.circleAverage_mono hint
    (circleIntegrable_const ((Real.log r) ^ 2 / 2 + A * Real.log r + B) 0 r) hlog
  rw [Real.circleAverage_const, Paper.eq_zerojensen hf hr0.ne'] at hm
  linarith

end ModifiedCartan
#print axioms ModifiedCartan.quadratic_log_bound_iteratedDeriv
#print axioms ModifiedCartan.logCounting_upper_of_quadratic_log_bound
