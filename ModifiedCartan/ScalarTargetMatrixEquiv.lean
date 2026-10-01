import ModifiedCartan.ScalarLinearTargetClassification

open scoped Topology Matrix
open Filter Set Matrix
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem scalarTargetCoordinateMap_comp_vecMul_ne_zero
    (B : Matrix (Index 1) (Index 1) ℂ) (hB : IsUnit B.det) (β : WithTop ℂ) :
    (scalarTargetCoordinateMap β).comp B.vecMulLinear ≠ 0 := by
  intro h
  apply scalarTargetCoordinateMap_ne_zero β
  apply LinearMap.ext
  intro v
  change scalarTargetCoordinateMap β v = 0
  obtain ⟨w, hw⟩ := (Matrix.vecMul_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det B).mpr hB)) v
  have he := congrArg (fun L : (Index 1 → ℂ) →ₗ[ℂ] ℂ => L w) h
  change scalarTargetCoordinateMap β (w ᵥ* B) = 0 at he
  dsimp only at hw
  rw [hw] at he
  exact he

/-- An invertible homogeneous coordinate change induces a proved bijection of
all targets, and its normalized target forms differ by nonzero constants.
Auxiliary to LaTeX `thm:A` (b). -/
theorem exists_scalar_target_equiv_matrix
    (B : Matrix (Index 1) (Index 1) ℂ) (hB : IsUnit B.det) :
    ∃ e : WithTop ℂ ≃ WithTop ℂ, ∀ β : WithTop ℂ, ∃ c : ℂ, c ≠ 0 ∧
      ∀ v : Index 1 → ℂ,
        scalarTargetCoordinateMap β (v ᵥ* B) = c * scalarTargetCoordinateMap (e β) v := by
  classical
  have hex (β : WithTop ℂ) := exists_scalar_target_coordinate_form
    ((scalarTargetCoordinateMap β).comp B.vecMulLinear)
    (scalarTargetCoordinateMap_comp_vecMul_ne_zero B hB β)
  choose g c hc he using hex
  have hinj : Function.Injective g := by
    intro α β hab
    by_contra hαβ
    obtain ⟨v, hv, hz⟩ := scalarTargetCoordinateMap_exists_kernel (g α)
    have hα : scalarTargetCoordinateMap α (v ᵥ* B) = 0 := by
      calc
        _ = c α * scalarTargetCoordinateMap (g α) v := he α v
        _ = 0 := by rw [hz, mul_zero]
    have hβ : scalarTargetCoordinateMap β (v ᵥ* B) = 0 := by
      calc
        _ = c β * scalarTargetCoordinateMap (g β) v := he β v
        _ = 0 := by rw [← hab, hz, mul_zero]
    have hh := scalarTargetCoordinateMap_common_zero hαβ hα hβ
    apply hv
    apply (Matrix.vecMul_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det B).mpr hB))
    simpa only [Matrix.zero_vecMul] using hh
  have hsurj : Function.Surjective g := by
    intro α
    obtain ⟨β, k, hk, hβ⟩ := exists_scalar_target_coordinate_form
      ((scalarTargetCoordinateMap α).comp B⁻¹.vecMulLinear)
      (scalarTargetCoordinateMap_comp_vecMul_ne_zero B⁻¹ (B.isUnit_nonsing_inv_det hB) α)
    refine ⟨β, ?_⟩
    apply Eq.symm
    apply scalarTargetCoordinateMap_unique (mul_ne_zero hk (hc β))
    intro v
    have hh := hβ (v ᵥ* B)
    change scalarTargetCoordinateMap α ((v ᵥ* B) ᵥ* B⁻¹) =
      k * scalarTargetCoordinateMap β (v ᵥ* B) at hh
    rw [Matrix.vecMul_vecMul, B.mul_nonsing_inv hB, Matrix.vecMul_one] at hh
    calc
      scalarTargetCoordinateMap α v = k * scalarTargetCoordinateMap β (v ᵥ* B) := hh
      _ = k * (c β * scalarTargetCoordinateMap (g β) v) := by rw [← he β v]; rfl
      _ = (k * c β) * scalarTargetCoordinateMap (g β) v := by ring
  exact ⟨Equiv.ofBijective g ⟨hinj, hsurj⟩, fun β => ⟨c β, hc β, he β⟩⟩

end
end ModifiedCartan
#print axioms ModifiedCartan.exists_scalar_target_equiv_matrix
