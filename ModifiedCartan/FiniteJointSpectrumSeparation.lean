import ModifiedCartan.CyclicCentralizer
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.StdBasis

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem exists_separating_linearFunctional {ι J : Type*} [Fintype ι]
    (e : ι → (J → ℂ)) (he : Function.Injective e) :
    ∃ L : Module.Dual ℂ (J → ℂ), Function.Injective (fun i => L (e i)) := by
  let P := {q : ι × ι // q.1 ≠ q.2}
  let f : P → Module.Dual ℂ (Module.Dual ℂ (J → ℂ)) := fun q =>
    { toFun := fun L => L (e q.val.1 - e q.val.2)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hex (q : P) : ∃ L, f q L ≠ 0 := by
    obtain ⟨j, hj⟩ : ∃ j : J, e q.val.1 j ≠ e q.val.2 j := by
      by_contra hn
      have hh : e q.val.1 = e q.val.2 := by
        funext j
        by_contra h
        exact hn ⟨j, h⟩
      exact q.property (he hh)
    let L : Module.Dual ℂ (J → ℂ) :=
      { toFun := fun x => x j
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }
    refine ⟨L, ?_⟩
    change e q.val.1 j - e q.val.2 j ≠ 0
    exact sub_ne_zero.mpr hj
  obtain ⟨L, hL⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f hex
  refine ⟨L, ?_⟩
  intro i j hij
  change L (e i) = L (e j) at hij
  by_contra hn
  apply hL ⟨(i, j), hn⟩
  change L (e i - e j) = 0
  rw [map_sub, hij, sub_self]

theorem exists_separating_finite_weights {ι J : Type*} [Fintype ι] [Fintype J]
    (e : ι → (J → ℂ)) (he : Function.Injective e) :
    ∃ t : J → ℂ, Function.Injective (fun i => ∑ j : J, t j * e i j) := by
  obtain ⟨L, hL⟩ := exists_separating_linearFunctional e he
  let t : J → ℂ := fun j => L (Pi.basisFun ℂ J j)
  have hh (i : ι) : (∑ j : J, t j * e i j) = L (e i) := by
    have h := congrArg L ((Pi.basisFun ℂ J).sum_repr (e i))
    simpa only [map_sum, map_smul, Pi.basisFun_repr, smul_eq_mul, t, mul_comm] using h
  refine ⟨t, ?_⟩
  intro i j hij
  apply hL
  change L (e i) = L (e j)
  rw [← hh i, ← hh j]
  exact hij

end
end ModifiedCartan


