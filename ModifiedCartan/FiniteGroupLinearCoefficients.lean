import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Data.Complex.Basic

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

theorem finiteGroupAlgebra_linear_coeff {G : Type*} [Fintype G]
    (L : MonoidAlgebra ℂ G →ₗ[ℂ] ℂ) (x : MonoidAlgebra ℂ G) :
    L x = ∑ g : G, x.coeff g * L (MonoidAlgebra.single g 1) := by
  have hx : (∑ g : G, x.coeff g • (MonoidAlgebra.single g 1 : MonoidAlgebra ℂ G)) = x := by
    ext g
    simp [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_smul_apply,
      MonoidAlgebra.coeff_single, Finsupp.finsetSum_apply, Finsupp.single_apply]
  calc
    L x = L (∑ g : G, x.coeff g • MonoidAlgebra.single g 1) := congrArg L hx.symm
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]

theorem subalgebraCharacter_exists_linear_extension {R : Type*} [Ring R] [Algebra ℂ R]
    (S : Subalgebra ℂ R) (φ : S →ₐ[ℂ] ℂ) :
    ∃ L : R →ₗ[ℂ] ℂ, ∀ x : S, L x.val = φ x := by
  obtain ⟨L, hL⟩ := (φ.toLinearMap.comp S.toSubmoduleEquiv.toLinearMap).exists_extend
  refine ⟨L, fun x => ?_⟩
  exact congrArg (fun f : S.toSubmodule →ₗ[ℂ] ℂ => f ⟨x.val, x.property⟩) hL

/-- A polynomial identity in every finite group coefficient remains true
    under any linear functional. Auxiliary to paper `lem:KP-correspondence`. -/
theorem finiteGroup_polynomial_relation_linear {G I B : Type*} [Fintype G] [Fintype I]
    (L : MonoidAlgebra ℂ G →ₗ[ℂ] ℂ) (c : I → MonoidAlgebra ℂ G)
    (P : I → MvPolynomial B ℂ)
    (h : ∀ g : G, (∑ i : I, MvPolynomial.C ((c i).coeff g) * P i) = 0) :
    (∑ i : I, MvPolynomial.C (L (c i)) * P i) = 0 := by
  calc
    _ = ∑ i : I, ∑ g : G, MvPolynomial.C ((c i).coeff g) *
        MvPolynomial.C (L (MonoidAlgebra.single g 1)) * P i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [finiteGroupAlgebra_linear_coeff L (c i)]
      simp only [map_sum, map_mul, Finset.sum_mul]
    _ = ∑ g : G, ∑ i : I, MvPolynomial.C ((c i).coeff g) *
        MvPolynomial.C (L (MonoidAlgebra.single g 1)) * P i := Finset.sum_comm
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro g hg
      calc
        _ = MvPolynomial.C (L (MonoidAlgebra.single g 1)) *
            (∑ i : I, MvPolynomial.C ((c i).coeff g) * P i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = 0 := by rw [h, mul_zero]

end
end ModifiedCartan

#print axioms ModifiedCartan.finiteGroup_polynomial_relation_linear
