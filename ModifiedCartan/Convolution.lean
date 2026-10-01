import ModifiedCartan.EntireMajorant
import ModifiedCartan.SystemMaximum

open scoped Topology BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The actual Wronskian counting function N_y in `cor:convolution`. -/
noncomputable def systemCounting {n : ℕ} (y : Fin (n + 1) → ℂ → ℂ) (r : ℝ) : ℝ :=
  ValueDistribution.logCounting (FewInflection.wronskian n y) (0 : WithTop ℂ) r

theorem log_initial_monomial_le {n : ℕ} (j : Fin (n + 1)) {r : ℝ} (hr : 0 < r) :
    Real.log (r ^ j.val / (j.val.factorial : ℝ)) ≤ (n : ℝ) * Real.posLog r := by
  have hfact : 0 < (j.val.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j.val
  have hfact1 : (1 : ℝ) ≤ j.val.factorial := by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos j.val)
  have hjn : (j.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.le_of_lt_succ j.isLt
  rw [Real.log_div (pow_pos hr _).ne' hfact.ne', Real.log_pow]
  have hlog := Real.log_nonneg hfact1
  have h1 : (j.val : ℝ) * Real.log r ≤ (j.val : ℝ) * Real.posLog r :=
    mul_le_mul_of_nonneg_left (le_max_right 0 _) (Nat.cast_nonneg _)
  have h2 := mul_le_mul_of_nonneg_right hjn (@Real.posLog_nonneg r)
  linarith

namespace Paper

/-- LaTeX `cor:convolution`, equation `eq:convolution`, with the literal
maximum modulus H_y and actual Wronskian logarithmic count N_y. -/
theorem cor_convolution {n : ℕ}
    {y : Fin (n + 1) → ℂ → ℂ} (hy : ∀ j, Differentiable ℂ (y j))
    (horder : ∀ j, entireOrder (y j) < 1)
    (hjets : ∀ i j : Fin (n + 1), iteratedDeriv i.val (y j) 0 = if i = j then 1 else 0)
    {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t => systemCounting y t / (r + t) ^ 2) (Ioi 0) ∧
      systemLogMaximum y r ≤ (n : ℝ) * Real.posLog r +
        r * ∫ t in Ioi 0, systemCounting y t / (r + t) ^ 2 := by
  obtain ⟨hs, hmajor⟩ := lem_entire_majorant hy horder hjets
  have hkernel := normalized_wronskian_product_convolution hy horder hjets hr
  refine ⟨hkernel.1, ?_⟩
  have h0 : y 0 0 = 1 := by simpa using hjets 0 0
  have hpos : 0 < systemMaximum y r :=
    zero_lt_one.trans_le (one_le_systemMaximum (fun j => (hy j).continuous) h0 hr.le)
  obtain ⟨j, hj⟩ := systemMaximum_attained y r
  obtain ⟨z, hz, he⟩ := maximumModulus_attained_on_sphere (hy j) hr
  have hnorm : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right] using hz
  have hb := hmajor j z
  rw [hnorm, ← he, ← hj] at hb
  have hl := Real.log_le_log hpos hb
  rw [Real.log_mul (div_pos (pow_pos hr _) (by positivity)).ne'
    (rootMajorantProduct_pos hs hr.le).ne'] at hl
  have hout : Real.log (systemMaximum y r) ≤ (n : ℝ) * Real.posLog r +
      Real.log (rootMajorantProduct (FewInflection.wronskian n y) r) := by
    linarith [log_initial_monomial_le j hr]
  rw [hkernel.2] at hout
  exact hout

end Paper
end ModifiedCartan
#print axioms ModifiedCartan.Paper.cor_convolution
