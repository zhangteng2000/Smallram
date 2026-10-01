import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace ModifiedCartan

theorem nested_submodule_invariant
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U W : Submodule K V) (T : V →ₗ[K] V)
    (hU : ∀ v ∈ U, T v ∈ U) (hW : ∀ v ∈ W, T v ∈ W) :
    ∀ v ∈ U.comap W.subtype, T.restrict hW v ∈ U.comap W.subtype := by
  intro v hv
  exact hU v.val hv

/-- Restricting to a nested subspace has the same trace as restricting directly. -/
theorem trace_restrict_nested
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (U W : Submodule K V) (hUW : U ≤ W) (T : V →ₗ[K] V)
    (hU : ∀ v ∈ U, T v ∈ U) (hW : ∀ v ∈ W, T v ∈ W) :
    LinearMap.trace K (U.comap W.subtype)
      ((T.restrict hW).restrict (nested_submodule_invariant U W T hU hW)) =
      LinearMap.trace K U (T.restrict hU) := by
  let e := Submodule.comapSubtypeEquivOfLe hUW
  have he : e.conj ((T.restrict hW).restrict
      (nested_submodule_invariant U W T hU hW)) = T.restrict hU := by
    ext v
    rfl
  rw [← he, LinearMap.trace_conj']

end ModifiedCartan


