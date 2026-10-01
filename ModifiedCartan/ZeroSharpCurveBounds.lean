import ModifiedCartan.ZeroSharpWronskian
import ModifiedCartan.ZeroSharpCountingLower
import ModifiedCartan.QuadraticLogDerivative
import ModifiedCartan.CurveCoordinateCounting

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem zeroSharpCurve_characteristic_quadratic_bounds (n : ℕ) (hn : 1 ≤ n) :
    ∃ A B C : ℝ, ∀ r : ℝ, 1 ≤ r →
      (Real.log r) ^ 2 / 2 - Real.log r - B ≤ characteristic (zeroSharpCurve n hn) r ∧
      characteristic (zeroSharpCurve n hn) r ≤ (Real.log r) ^ 2 / 2 + A * Real.log r + C := by
  obtain ⟨A, B, hA, hB, hbound⟩ := zeroSharp_norm_quadratic_log_bound
  let f := zeroSharpCurve n hn
  let L := Real.log (euclideanNorm (f.vector 0))
  refine ⟨A + n, 1 + L, B + Real.log (Real.sqrt (n + 1 : ℝ)) - L, fun r hr => ⟨?_, ?_⟩⟩
  · have hg : f.coord (Fin.last n) = zeroSharpFunction := zeroSharpCoordinates_last n
    have hl := coordinate_logCounting_le_characteristic f (Fin.last n)
      (by rw [hg, zeroSharpFunction_zero]; exact one_ne_zero) (zero_lt_one.trans_le hr)
    rw [hg, zeroSharpFunction_zero, norm_one, Real.log_one, sub_zero] at hl
    have hlow := zeroSharp_derivative_logCounting_lower 0 hr
    simp only [iteratedDeriv_zero, Nat.cast_zero, zero_add, one_mul] at hlow
    dsimp only [L]
    linarith
  · have hr0 : 0 < r := zero_lt_one.trans_le hr
    have hlr : 0 ≤ Real.log r := Real.log_nonneg hr
    let E := (Real.log r) ^ 2 / 2 + (A + (n : ℝ)) * Real.log r + B
    have hv (z : ℂ) (hz : ‖z‖ ≤ r) : ‖f.vector z‖ ≤ Real.exp E := by
      apply (pi_norm_le_iff_of_nonneg (Real.exp_nonneg E)).mpr
      intro j
      change ‖zeroSharpCoordinates n j z‖ ≤ _
      unfold zeroSharpCoordinates
      split_ifs with hj
      · rw [norm_pow]
        apply (pow_le_pow_left₀ (norm_nonneg z) hz j.val).trans
        have hp : r ^ j.val = Real.exp ((j.val : ℝ) * Real.log r) := by
          rw [Real.exp_nat_mul, Real.exp_log hr0]
        rw [hp]
        apply Real.exp_le_exp.mpr
        have hjr : (j.val : ℝ) ≤ n := by exact_mod_cast hj.le
        have hm := mul_nonneg (show 0 ≤ A + (n : ℝ) - j.val by linarith) hlr
        dsimp only [E]
        nlinarith [sq_nonneg (Real.log r)]
      · apply (hbound r hr z hz).trans
        apply Real.exp_le_exp.mpr
        have hm := mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hlr
        dsimp only [E]
        nlinarith
    have hlog (z : ℂ) (hz : z ∈ Metric.sphere 0 |r|) :
        Real.log (euclideanNorm (f.vector z)) ≤ Real.log (Real.sqrt (n + 1 : ℝ)) + E := by
      have hzr : ‖z‖ ≤ r := by
        have he := Metric.mem_sphere.mp hz
        simpa only [dist_zero_right, abs_of_pos hr0] using he.le
      have he := (euclideanNorm_le (f.vector z)).trans
        (mul_le_mul_of_nonneg_left (hv z hzr) (Real.sqrt_nonneg _))
      have hh := Real.log_le_log (euclideanNorm_pos (f.vector_ne_zero z)) he
      simpa only [Real.log_mul (by positivity : Real.sqrt (n + 1 : ℝ) ≠ 0)
        (Real.exp_ne_zero E), Real.log_exp] using hh
    have hm := Real.circleAverage_mono
      (curve_log_euclideanNorm_continuous f).continuousOn.circleIntegrable'
      (circleIntegrable_const (Real.log (Real.sqrt (n + 1 : ℝ)) + E) 0 r) hlog
    rw [Real.circleAverage_const] at hm
    change characteristic f r ≤ _
    unfold characteristic
    dsimp only [E, L] at *
    linarith

theorem zeroSharp_derivative_logCounting_quadratic_bounds (m : ℕ) :
    ∃ A B : ℝ, ∀ r : ℝ, 1 ≤ r →
      (Real.log r) ^ 2 / 2 - ((m : ℝ) + 1) * Real.log r - 1 ≤
        ValueDistribution.logCounting (iteratedDeriv m zeroSharpFunction) (0 : WithTop ℂ) r ∧
      ValueDistribution.logCounting (iteratedDeriv m zeroSharpFunction) (0 : WithTop ℂ) r ≤
        (Real.log r) ^ 2 / 2 + A * Real.log r + B := by
  obtain ⟨A, B, hA, hB, hb⟩ := zeroSharp_norm_quadratic_log_bound
  obtain ⟨C, D, hC, hD, hd⟩ := quadratic_log_bound_iteratedDeriv
    zeroSharpFunction_differentiable hA hB hb m
  obtain ⟨E, hE⟩ := logCounting_upper_of_quadratic_log_bound
    (zeroSharpFunction_iteratedDeriv_entire m) hC hD hd
  exact ⟨C, E, fun r hr => ⟨zeroSharp_derivative_logCounting_lower m hr, hE r hr⟩⟩

end ModifiedCartan
#print axioms ModifiedCartan.zeroSharpCurve_characteristic_quadratic_bounds
#print axioms ModifiedCartan.zeroSharp_derivative_logCounting_quadratic_bounds
