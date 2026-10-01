import ModifiedCartan.AlternatingDualDescent
import Mathlib.LinearAlgebra.Determinant

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- After descent to an equally dimensional subspace, a nonzero alternating
    form is exactly a nonzero scalar times the evaluation determinant.
    Auxiliary to manuscript `lem:KP-correspondence`. -/
theorem alternatingDual_eq_scalar_det {M : Type*} [AddCommGroup M] [Module ℂ M]
    {n : ℕ} (V : Submodule ℂ M) (b : Module.Basis (Fin (n + 1)) ℂ V)
    (F : (Module.Dual ℂ M) [⋀^Fin (n + 1)]→ₗ[ℂ] ℂ)
    (hF : ∀ v, (∀ p ∈ V, v 0 p = 0) → F v = 0) (hne : F ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ v : Fin (n + 1) → Module.Dual ℂ M,
      F v = c * Matrix.det (fun i j : Fin (n + 1) => v i (b j).val) := by
  let G := F.compLinearMap (Subspace.dualLift V)
  have hG : G ≠ 0 := alternatingDual_descent_ne_zero V F hF hne
  refine ⟨G b.dualBasis, (G.map_basis_ne_zero_iff b.dualBasis).mpr hG, ?_⟩
  intro v
  have he := AlternatingMap.congr_fun (alternatingDual_descent V F hF) v
  change F v = G (fun i => V.dualRestrict (v i)) at he
  rw [he]
  have hd := AlternatingMap.congr_fun (G.eq_smul_basis_det b.dualBasis)
    (fun i => V.dualRestrict (v i))
  calc
    _ = G b.dualBasis * b.dualBasis.det (fun i => V.dualRestrict (v i)) := hd
    _ = _ := by
      congr 1
      rw [Module.Basis.det_apply]
      have hM : b.dualBasis.toMatrix (fun i => V.dualRestrict (v i)) =
          (fun i j : Fin (n + 1) => v j (b i).val) := by
        funext i j
        simp only [Module.Basis.toMatrix_apply, Module.Basis.dualBasis_repr,
          Submodule.dualRestrict_apply]
      rw [hM]
      exact Matrix.det_transpose (fun i j : Fin (n + 1) => v i (b j).val)

end
end ModifiedCartan

#print axioms ModifiedCartan.alternatingDual_eq_scalar_det
