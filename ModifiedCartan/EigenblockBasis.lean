import ModifiedCartan.EigenblockSum
import Mathlib.LinearAlgebra.StdBasis

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {ι V : Type*} {W : ι → Type*} {κ : ι → Type*}
  [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℂ V]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  [FiniteDimensional ℂ V] [∀ i, FiniteDimensional ℂ (W i)]

def eigenblockBasis (b : ∀ i, Module.Basis (κ i) ℂ (W i))
    (F : ∀ i, W i →ₗ[ℂ] V) (hF : ∀ i, Function.Injective (F i))
    (T : Module.End ℂ V) (e : ι → ℂ) (he : Function.Injective e)
    (hT : ∀ i v, T (F i v) = e i • F i v)
    (hd : (∑ i, Module.finrank ℂ (W i)) = Module.finrank ℂ V) :
    Module.Basis (Σ i, κ i) ℂ V :=
  (Pi.basis b).map (eigenblockSumEquiv F hF T e he hT hd)

theorem eigenblockBasis_apply (b : ∀ i, Module.Basis (κ i) ℂ (W i))
    (F : ∀ i, W i →ₗ[ℂ] V) (hF : ∀ i, Function.Injective (F i))
    (T : Module.End ℂ V) (e : ι → ℂ) (he : Function.Injective e)
    (hT : ∀ i v, T (F i v) = e i • F i v)
    (hd : (∑ i, Module.finrank ℂ (W i)) = Module.finrank ℂ V) (p : Σ i, κ i) :
    eigenblockBasis b F hF T e he hT hd p = F p.1 (b p.1 p.2) := by
  rw [eigenblockBasis, Module.Basis.map_apply, Pi.basis_apply]
  change (∑ i, F i ((Pi.single p.1 (b p.1 p.2)) i)) = _
  rw [Finset.sum_eq_single p.1]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

end
end ModifiedCartan


