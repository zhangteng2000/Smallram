import ModifiedCartan.MonomialGerms
import Mathlib.Analysis.Analytic.IsolatedZeros

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- The exact alternatives in LaTeX `eq:monomial-coefficients`.
Natural exponents are used on the complex plane. -/
def IsWeightedMonomial (p : ℝ) (a : ℂ → ℂ) : Prop :=
  (∃ m : ℕ, p = m ∧ ∃ c : ℂ, a = fun z => c * z ^ m) ∨
  ((¬ ∃ m : ℕ, p = m) ∧ a = 0)

theorem exists_entire_weighted_monomial_extension {a : ℂ → ℂ} {p : ℝ}
    (ha : AnalyticOnNhd ℂ a (ball 0 4))
    (hsupport : ∀ m : ℕ, iteratedDeriv m a 0 ≠ 0 → p = m) :
    ∃ A : ℂ → ℂ, AnalyticOnNhd ℂ A univ ∧
      EqOn a A (ball 0 4) ∧ IsWeightedMonomial p A := by
  rcases analytic_eq_monomial_of_deriv_support ha hsupport with
    ⟨m, hm, c, hc⟩ | ⟨hp, hz⟩
  · refine ⟨fun z => c * z ^ m, ?_, hc, Or.inl ⟨m, hm, c, rfl⟩⟩
    intro z _
    fun_prop
  · exact ⟨0, analyticOnNhd_const, hz, Or.inr ⟨hp, rfl⟩⟩

/-- Analytic continuation identifies every scale model on its full disk. -/
theorem entire_dilation_model_eqOn {A b : ℂ → ℂ} {R : ℝ} {c : ℂ}
    (hA : AnalyticOnNhd ℂ A univ) (hb : AnalyticOnNhd ℂ b (ball 0 4))
    (hrel : (fun z : ℂ => A ((R : ℂ) * z)) =ᶠ[𝓝 0] (fun z => c * b z)) :
    EqOn (fun z : ℂ => A ((R : ℂ) * z)) (fun z => c * b z) (ball 0 4) := by
  have hleft : AnalyticOnNhd ℂ (fun z : ℂ => A ((R : ℂ) * z)) (ball 0 4) := by
    intro z _
    exact (hA _ (mem_univ _)).comp (analyticAt_const.mul analyticAt_id)
  exact hleft.eqOn_of_preconnected_of_eventuallyEq (analyticOnNhd_const.mul hb)
    (convex_ball (0 : ℂ) 4).isPreconnected (mem_ball_self (by norm_num)) hrel

/-- The scale bound extends to the closed unit disk by continuity. -/
theorem norm_le_closed_unit_ball_of_open_bound {b : ℂ → ℂ} {K : ℝ}
    (hb : AnalyticOnNhd ℂ b (ball 0 4))
    (hbound : ∀ z ∈ ball (0 : ℂ) 1, ‖b z‖ ≤ K) :
    ∀ z ∈ closedBall (0 : ℂ) 1, ‖b z‖ ≤ K := by
  have hclosure : closure (ball (0 : ℂ) 1) ⊆ ball 0 4 := by
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact closedBall_subset_ball (by norm_num)
  have hh := le_on_closure hbound
    (hb.continuousOn.norm.mono hclosure) continuousOn_const
  simpa only [closure_ball (0 : ℂ) one_ne_zero] using hh

end ModifiedCartan
#print axioms ModifiedCartan.exists_entire_weighted_monomial_extension
#print axioms ModifiedCartan.entire_dilation_model_eqOn
