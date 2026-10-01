import ModifiedCartan.SimpleEigenbasisCyclic
import Mathlib.LinearAlgebra.Dimension.Constructions

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {ι V : Type*} {W : ι → Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup V] [Module ℂ V] [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

def blockSumLinearMap (F : ∀ i, W i →ₗ[ℂ] V) : (∀ i, W i) →ₗ[ℂ] V where
  toFun v := ∑ i, F i (v i)
  map_add' u v := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c v := by simp only [Pi.smul_apply, map_smul, Finset.smul_sum]; rfl

theorem eigenblock_polynomial_projection (F : ∀ i, W i →ₗ[ℂ] V)
    (T : Module.End ℂ V) (e : ι → ℂ) (he : Function.Injective e)
    (hT : ∀ i v, T (F i v) = e i • F i v) (i : ι) (v : ∀ i, W i) :
    Polynomial.aeval T (Lagrange.basis Finset.univ e i) (blockSumLinearMap F v) = F i (v i) := by
  change Polynomial.aeval T (Lagrange.basis Finset.univ e i) (∑ j, F j (v j)) = _
  rw [map_sum, Finset.sum_eq_single i]
  · rw [Module.End.aeval_apply_of_mem_apply_eq_smul (hT i (v i)),
      Lagrange.eval_basis_self (fun x _ y _ h => he h) (Finset.mem_univ i), one_smul]
  · intro j _ hji
    rw [Module.End.aeval_apply_of_mem_apply_eq_smul (hT j (v j)),
      Lagrange.eval_basis_of_ne (Ne.symm hji) (Finset.mem_univ j), zero_smul]
  · simp

theorem blockSumLinearMap_injective_of_eigenvalues (F : ∀ i, W i →ₗ[ℂ] V)
    (hF : ∀ i, Function.Injective (F i)) (T : Module.End ℂ V)
    (e : ι → ℂ) (he : Function.Injective e) (hT : ∀ i v, T (F i v) = e i • F i v) :
    Function.Injective (blockSumLinearMap F) := by
  intro v w h
  funext i
  apply hF i
  have hh := congrArg (Polynomial.aeval T (Lagrange.basis Finset.univ e i)) h
  simpa only [eigenblock_polynomial_projection F T e he hT] using hh

def eigenblockSumEquiv [FiniteDimensional ℂ V] [∀ i, FiniteDimensional ℂ (W i)]
    (F : ∀ i, W i →ₗ[ℂ] V) (hF : ∀ i, Function.Injective (F i))
    (T : Module.End ℂ V) (e : ι → ℂ) (he : Function.Injective e)
    (hT : ∀ i v, T (F i v) = e i • F i v)
    (hd : (∑ i, Module.finrank ℂ (W i)) = Module.finrank ℂ V) :
    (∀ i, W i) ≃ₗ[ℂ] V :=
  LinearEquiv.ofInjectiveOfFinrankEq (blockSumLinearMap F)
    (blockSumLinearMap_injective_of_eigenvalues F hF T e he hT)
    ((Module.finrank_pi_fintype ℂ).trans hd)

end
end ModifiedCartan


