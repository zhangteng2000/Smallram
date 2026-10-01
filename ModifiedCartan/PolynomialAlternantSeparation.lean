import ModifiedCartan.PartitionAlternatingDualForm
import ModifiedCartan.PolynomialJetDegreeProfile
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem alternatingMap_zero_of_coordinate_eq_first {M : Type*}
    [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (F : M [⋀^Fin (n + 1)]→ₗ[ℂ] ℂ) (l : M)
    (h : ∀ v, v 0 = l → F v = 0) (v : Fin (n + 1) → M)
    (j : Fin (n + 1)) (hj : v j = l) : F v = 0 := by
  by_cases he : j = 0
  · exact h v (he ▸ hj)
  · have hh := h (v ∘ Equiv.swap 0 j) (by
      simpa only [Function.comp_apply, Equiv.swap_apply_left] using hj)
    rw [F.map_swap v (Ne.symm he)] at hh
    exact neg_eq_zero.mp hh

theorem polynomialBasis_annihilator_of_alternating_first_zero {n : ℕ}
    (V : Submodule ℂ (Polynomial ℂ)) (b : Module.Basis (Fin (n + 1)) ℂ V)
    (l : Module.Dual ℂ (Polynomial ℂ))
    (h : ∀ v, v 0 = l → polynomialAlternatingDualForm (fun j => (b j).val) v = 0) :
    ∀ p ∈ V, l p = 0 := by
  let v : Fin (n + 1) → Module.Dual ℂ (Polynomial ℂ) := fun i =>
    Subspace.dualLift V (b.dualBasis i)
  have hv (i j : Fin (n + 1)) : v i (b j).val = if i = j then 1 else 0 := by
    simp only [v, Subspace.dualLift_of_subtype, Module.Basis.dualBasis_apply_self]
    simp only [eq_comm]
  have hb (j : Fin (n + 1)) : l (b j).val = 0 := by
    have hz := alternatingMap_zero_of_coordinate_eq_first
      (polynomialAlternatingDualForm (fun k => (b k).val)) l h
      (Function.update v j l) j (Function.update_self j l v)
    rw [polynomialAlternatingDualForm_apply] at hz
    have hM : (fun i k : Fin (n + 1) => (Function.update v j l) i (b k).val) =
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).updateRow j (fun k => l (b k).val) := by
      funext i k
      by_cases hi : i = j
      · subst i
        simp only [Function.update_self, Matrix.updateRow_self]
      · simp only [Function.update_of_ne hi, Matrix.updateRow_ne hi, hv, Matrix.one_apply]
    erw [hM, matrix_det_updateRow_one] at hz
    exact hz
  intro p hp
  have he := congrArg (fun q : V => l q.val) (b.sum_repr (⟨p, hp⟩ : V))
  simpa only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul,
    hb, smul_zero, Finset.sum_const_zero] using he.symm

/-- Proportional determinant polynomials of two actual bases determine exactly
    the same polynomial subspace. Auxiliary to coordinate injectivity for
    manuscript `lem:KP-correspondence`. -/
theorem polynomialBasis_subspace_eq_of_alternant_eq {n : ℕ}
    (V W : Submodule ℂ (Polynomial ℂ))
    (b : Module.Basis (Fin (n + 1)) ℂ V) (d : Module.Basis (Fin (n + 1)) ℂ W)
    (c : ℂ) (hc : c ≠ 0)
    (h : polynomialAlternant (fun j => (b j).val) =
      MvPolynomial.C c * polynomialAlternant (fun j => (d j).val)) : V = W := by
  have he (v : Fin (n + 1) → Module.Dual ℂ (Polynomial ℂ)) :
      polynomialAlternatingDualForm (fun j => (b j).val) v =
        c * polynomialAlternatingDualForm (fun j => (d j).val) v := by
    have ht := congrArg (polynomialTensorFunctional v) h
    simpa only [polynomialTensorFunctional_C_mul, polynomialTensorFunctional_alternant,
      polynomialAlternatingDualForm_apply] using ht
  apply le_antisymm
  · intro p hp
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W p).mp
    intro l hl
    apply polynomialBasis_annihilator_of_alternating_first_zero V b l _ p hp
    intro v hv
    rw [he, polynomialAlternatingDualForm_apply]
    have hz : Matrix.det (fun i j : Fin (n + 1) => v i (d j).val) = 0 := by
      apply Matrix.det_eq_zero_of_row_eq_zero (0 : Fin (n + 1))
      intro j
      rw [hv]
      exact (Submodule.mem_dualAnnihilator l).mp hl (d j).val (d j).property
    rw [hz, mul_zero]
  · intro p hp
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff V p).mp
    intro l hl
    apply polynomialBasis_annihilator_of_alternating_first_zero W d l _ p hp
    intro v hv
    have hz : polynomialAlternatingDualForm (fun j => (b j).val) v = 0 := by
      rw [polynomialAlternatingDualForm_apply]
      apply Matrix.det_eq_zero_of_row_eq_zero (0 : Fin (n + 1))
      intro j
      rw [hv]
      exact (Submodule.mem_dualAnnihilator l).mp hl (b j).val (b j).property
    rw [he] at hz
    exact (mul_eq_zero.mp hz).resolve_left hc

end
end ModifiedCartan

#print axioms ModifiedCartan.polynomialBasis_subspace_eq_of_alternant_eq