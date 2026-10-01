import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace ModifiedCartan

/-- Trace additivity for an actual surjective intertwining linear map. -/
theorem trace_eq_kernel_add_of_surjective
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (f : V →ₗ[K] W) (hf : Function.Surjective f)
    (T : V →ₗ[K] V) (S : W →ₗ[K] W)
    (hT : ∀ v, f (T v) = S (f v))
    (hker : ∀ v ∈ LinearMap.ker f, T v ∈ LinearMap.ker f) :
    LinearMap.trace K V T =
      LinearMap.trace K (LinearMap.ker f) (T.restrict hker) + LinearMap.trace K W S := by
  classical
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  have hs_apply (w : W) : f (s w) = w := LinearMap.congr_fun hs w
  let p : V →ₗ[K] LinearMap.ker f :=
    LinearMap.codRestrict (LinearMap.ker f) (LinearMap.id - s.comp f) (by
      intro v
      change f (v - s (f v)) = 0
      rw [map_sub, hs_apply, sub_self])
  have hp_apply (v : V) : (p v).val = v - s (f v) := rfl
  have hpker (v : LinearMap.ker f) : p v.val = v := by
    apply Subtype.ext
    change v.val - s (f v.val) = v.val
    rw [show f v.val = 0 from v.property, map_zero, sub_zero]
  have hpT : (p.comp T).comp (LinearMap.ker f).subtype = T.restrict hker := by
    ext v
    exact congrArg Subtype.val (hpker ⟨T v.val, hker v.val v.property⟩)
  have hfT : (f.comp T).comp s = S := by
    ext w
    change f (T (s w)) = S w
    rw [hT, hs_apply]
  have hsplit : T = ((T.comp (LinearMap.ker f).subtype).comp p) + (T.comp s).comp f := by
    ext v
    change T v = T (p v).val + T (s (f v))
    rw [hp_apply, map_sub, sub_add_cancel]
  calc
    LinearMap.trace K V T =
        LinearMap.trace K V ((T.comp (LinearMap.ker f).subtype).comp p) +
          LinearMap.trace K V ((T.comp s).comp f) := by rw [← map_add, ← hsplit]
    _ = LinearMap.trace K (LinearMap.ker f) (T.restrict hker) + LinearMap.trace K W S := by
      rw [LinearMap.trace_comp_comm', LinearMap.trace_comp_comm' f (T.comp s)]
      rw [← LinearMap.comp_assoc, hpT, ← LinearMap.comp_assoc, hfT]

 /-- The same additivity formula with an explicitly identified kernel subspace. -/
theorem trace_eq_submodule_add_of_surjective
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (f : V →ₗ[K] W) (hf : Function.Surjective f)
    (T : V →ₗ[K] V) (S : W →ₗ[K] W)
    (hT : ∀ v, f (T v) = S (f v))
    (U : Submodule K V) (hU : ∀ v ∈ U, T v ∈ U) (hker : LinearMap.ker f = U) :
    LinearMap.trace K V T =
      LinearMap.trace K U (T.restrict hU) + LinearMap.trace K W S := by
  subst U
  exact trace_eq_kernel_add_of_surjective f hf T S hT hU

end ModifiedCartan


