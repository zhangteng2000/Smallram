import ModifiedCartan.AllScaleCauchyBounds
import FewInflection.Results

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- The discrete-order conclusion from a nonzero coefficient among the
actual scale models. Nonvanishing is a separate analytic lemma, not an
additional assumption of the final `prop:indices`. -/
theorem admissibleOrder_of_nonzero_scale_model {n : ℕ} {μ K : ℝ}
    (i : Fin n) {a : ℂ → ℂ} (ha : AnalyticOnNhd ℂ a (ball 0 4))
    (hne : ∃ z ∈ ball (0 : ℂ) 4, a z ≠ 0)
    (hscale : ∀ R : ℝ, 0 < R → ∃ b : ℂ → ℂ, AnalyticOnNhd ℂ b (ball 0 4) ∧
      (∀ z ∈ ball (0 : ℂ) 1, ‖b z‖ ≤ K) ∧
      (fun z : ℂ => a ((R : ℂ) * z)) =ᶠ[𝓝 0]
        (fun z => (R ^ (((n + 1 - i.val : ℕ) : ℝ) * (μ - 1)) : ℝ) * b z)) :
    FewInflection.AdmissibleOrder n μ := by
  obtain ⟨m, hm, _⟩ := dilation_weight_eq_nat_of_uniform_local_bounds ha hne hscale
  have hq2 : 2 ≤ n + 1 - i.val := by omega
  have hqn : n + 1 - i.val ≤ n + 1 := Nat.sub_le _ _
  have hq : (0 : ℝ) < (n + 1 - i.val : ℕ) := by exact_mod_cast (by omega : 0 < n + 1 - i.val)
  refine ⟨m, n + 1 - i.val, hq2, hqn, ?_⟩
  have he : μ - 1 = (m : ℝ) / (n + 1 - i.val : ℕ) := by
    apply (eq_div_iff hq.ne').mpr
    nlinarith [hm]
  linarith

end ModifiedCartan
#print axioms ModifiedCartan.admissibleOrder_of_nonzero_scale_model
