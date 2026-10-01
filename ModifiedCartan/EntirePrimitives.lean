import ModifiedCartan.EntireSeries
import Mathlib.Analysis.Complex.HasPrimitives

open scoped Topology
open Set
set_option autoImplicit false
namespace ModifiedCartan

theorem iteratedDeriv_add_orders (m k : ℕ) (f : ℂ → ℂ) :
    iteratedDeriv (m + k) f = iteratedDeriv m (iteratedDeriv k f) := by
  simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]

/-- Entire repeated primitives with every lower initial jet equal to zero. -/
theorem entire_iteratedPrimitive_exists {f : ℂ → ℂ} (hf : Differentiable ℂ f) (m : ℕ) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ iteratedDeriv m F = f ∧
      ∀ i : ℕ, i < m → iteratedDeriv i F 0 = 0 := by
  induction m with
  | zero => exact ⟨f, hf, by simp, by intro i hi; omega⟩
  | succ m ih =>
    obtain ⟨G, hG, hGm, hG0⟩ := ih
    obtain ⟨F, hF0, hFd⟩ := hG.isExactOn_univ.with_val_at 0 0
    have hF : Differentiable ℂ F := fun z => (hFd z (mem_univ z)).differentiableAt
    have hderiv : deriv F = G := funext (fun z => (hFd z (mem_univ z)).deriv)
    refine ⟨F, hF, ?_, ?_⟩
    · rw [iteratedDeriv_succ', hderiv, hGm]
    · intro i hi
      cases i with
      | zero => simpa only [iteratedDeriv_zero] using hF0
      | succ i =>
        rw [iteratedDeriv_succ', hderiv]
        exact hG0 i (by omega)

end ModifiedCartan
#print axioms ModifiedCartan.entire_iteratedPrimitive_exists
