import ModifiedCartan.CyclicCentralizer
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem hasPolynomialCyclicVector_of_simple_eigenbasis {ι V : Type*}
    [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis ι ℂ V) (T : Module.End ℂ V) (w : ι → ℂ)
    (hw : Function.Injective w) (hT : ∀ i, T (b i) = w i • b i) :
    HasPolynomialCyclicVector T (∑ i, b i) := by
  intro v
  refine ⟨Lagrange.interpolate Finset.univ w (fun i => b.repr v i), ?_⟩
  rw [map_sum]
  calc
    _ = ∑ i, b.repr v i • b i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Module.End.aeval_apply_of_mem_apply_eq_smul (hT i),
        Lagrange.eval_interpolate_at_node _ (fun x _ y _ h => hw h) (Finset.mem_univ i)]
    _ = _ := b.sum_repr v

end
end ModifiedCartan


