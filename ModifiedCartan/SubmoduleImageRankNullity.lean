import ModifiedCartan.YoungSpechtModule
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace ModifiedCartan
noncomputable section

/-- Rank-nullity for a linear map restricted to a submodule, with its actual
kernel identified inside the ambient space. -/
theorem submodule_finrank_map_add_of_kernel {M N : Type*}
    [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    [AddCommGroup N] [Module ℂ N] (f : M →ₗ[ℂ] N) (U V : Submodule ℂ M)
    (hUV : U ≤ V) (hker : ∀ v ∈ V, f v = 0 ↔ v ∈ U) :
    Module.finrank ℂ (V.map f) + Module.finrank ℂ U = Module.finrank ℂ V := by
  have hK : LinearMap.ker (f.domRestrict V) = U.comap V.subtype := by
    ext v
    change f v.val = 0 ↔ v.val ∈ U
    exact hker v.val v.property
  have hdim : Module.finrank ℂ (LinearMap.ker (f.domRestrict V)) = Module.finrank ℂ U :=
    ((LinearEquiv.ofEq _ _ hK).trans (Submodule.comapSubtypeEquivOfLe hUV)).finrank_eq
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict V)
  rw [LinearMap.range_domRestrict, hdim] at h
  exact h

end
end ModifiedCartan


