import ModifiedCartan.PolynomialNormalizedMajorant
import ModifiedCartan.PolynomialRootLogCounting

open scoped Topology BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The polynomial majorant in the integral form needed for the
limit in LaTeX `lem:entire-majorant`. -/
theorem normalized_polynomial_tuple_integral_majorant {n : ℕ}
    (p : Fin (n + 1) → Polynomial ℂ)
    (hjets : ∀ i j : Fin (n + 1),
      iteratedDeriv i.val (fun z => (p j).eval z) 0 = if i = j then 1 else 0)
    (j : Fin (n + 1)) {z : ℂ} (hz : z ≠ 0) :
    ‖(p j).eval z‖ ≤ (‖z‖ ^ j.val / (j.val.factorial : ℝ)) *
      Real.exp (‖z‖ * ∫ t in Ioi 0, ValueDistribution.logCounting
        (FewInflection.wronskian n (fun j w => (p j).eval w)) (0 : WithTop ℂ) t / (‖z‖ + t) ^ 2) := by
  obtain ⟨a, ha, hzero, hb⟩ := normalized_polynomial_tuple_majorant p hjets
  have he : (fun w => (FewInflection.polynomialWronskian p).eval w) =
      FewInflection.wronskian n (fun j w => (p j).eval w) := by
    funext w
    exact FewInflection.polynomialWronskian_eval p w
  have hk := polynomial_root_list_kernel_integral (FewInflection.polynomialWronskian p) a ha hzero
    (norm_pos_iff.mpr hz)
  rw [he] at hk
  rw [hk, Real.exp_sum]
  have hfactors : (∏ i, Real.exp (Real.log (1 + ‖z‖ / ‖a i‖))) =
      ∏ i, (1 + ‖z‖ / ‖a i‖) := by
    apply Finset.prod_congr rfl
    intro i _
    exact Real.exp_log (by positivity)
  rw [hfactors]
  exact hb j z

end ModifiedCartan
#print axioms ModifiedCartan.normalized_polynomial_tuple_integral_majorant
