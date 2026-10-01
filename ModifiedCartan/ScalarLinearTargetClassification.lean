import ModifiedCartan.ScalarDistinctTargetBounds

open scoped Topology Matrix
open Filter Set Matrix
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- Every scalar target form is nonzero, including infinity. -/
theorem scalarTargetCoordinateMap_ne_zero (β : WithTop ℂ) :
    scalarTargetCoordinateMap β ≠ 0 := by
  intro h
  induction β using WithTop.recTopCoe with
  | top =>
    have he := congrArg (fun L : (Index 1 → ℂ) →ₗ[ℂ] ℂ => L ![1, 0]) h
    change (1 : ℂ) / 1 = 0 at he
    norm_num at he
  | coe b =>
    have he := congrArg (fun L : (Index 1 → ℂ) →ₗ[ℂ] ℂ => L ![0, 1]) h
    change ((1 : ℂ) - b * 0) / (scalarTargetNormalizingSize (b : WithTop ℂ) : ℂ) = 0 at he
    have hd := Complex.ofReal_ne_zero.mpr (scalarTargetNormalizingSize_pos (b : WithTop ℂ)).ne'
    simpa [hd] using he

/-- Each target form has a nonzero homogeneous vector in its kernel. -/
theorem scalarTargetCoordinateMap_exists_kernel (β : WithTop ℂ) :
    ∃ v : Index 1 → ℂ, v ≠ 0 ∧ scalarTargetCoordinateMap β v = 0 := by
  induction β using WithTop.recTopCoe with
  | top =>
    refine ⟨![0, 1], ?_, ?_⟩
    · intro h
      have he := congrFun h 1
      norm_num at he
    · change (0 : ℂ) / 1 = 0
      ring
  | coe b =>
    refine ⟨![1, b], ?_, ?_⟩
    · intro h
      have he := congrFun h 0
      norm_num at he
    · change (b - b * 1) / _ = 0
      ring

theorem scalarTargetCoordinateMap_common_zero {α β : WithTop ℂ} (hab : α ≠ β)
    {v : Index 1 → ℂ} (hα : scalarTargetCoordinateMap α v = 0)
    (hβ : scalarTargetCoordinateMap β v = 0) : v = 0 := by
  change scalarTargetLinearForm α (v 0) (v 1) / (scalarTargetNormalizingSize α : ℂ) = 0 at hα
  change scalarTargetLinearForm β (v 0) (v 1) / (scalarTargetNormalizingSize β : ℂ) = 0 at hβ
  have hnα := Complex.ofReal_ne_zero.mpr (scalarTargetNormalizingSize_pos α).ne'
  have hnβ := Complex.ofReal_ne_zero.mpr (scalarTargetNormalizingSize_pos β).ne'
  obtain ⟨h₀, h₁⟩ := scalarTargetLinearForm_common_zero hab
    ((div_eq_zero_iff).mp hα |>.resolve_right hnα)
    ((div_eq_zero_iff).mp hβ |>.resolve_right hnβ)
  ext j
  fin_cases j
  · exact h₀
  · exact h₁

/-- A nonzero factor cannot identify two different projective targets. -/
theorem scalarTargetCoordinateMap_unique {α β : WithTop ℂ} {c : ℂ} (hc : c ≠ 0)
    (he : ∀ v, scalarTargetCoordinateMap α v = c * scalarTargetCoordinateMap β v) : α = β := by
  by_contra hab
  obtain ⟨v, hv, hα⟩ := scalarTargetCoordinateMap_exists_kernel α
  have hβ : scalarTargetCoordinateMap β v = 0 := by
    have hh := he v
    rw [hα] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left hc
  exact hv (scalarTargetCoordinateMap_common_zero hab hα hβ)

/-- Every nonzero complex linear functional in dimension two is a nonzero
multiple of exactly one of the manuscript's target forms. -/
theorem exists_scalar_target_coordinate_form (L : (Index 1 → ℂ) →ₗ[ℂ] ℂ) (hL : L ≠ 0) :
    ∃ β : WithTop ℂ, ∃ c : ℂ, c ≠ 0 ∧ ∀ v, L v = c * scalarTargetCoordinateMap β v := by
  let a : ℂ := L ![1, 0]
  let b : ℂ := L ![0, 1]
  have hdecomp (v : Index 1 → ℂ) : L v = a * v 0 + b * v 1 := by
    have hv : v = v 0 • ![1, 0] + v 1 • ![0, 1] := by
      ext j
      fin_cases j <;> simp
    calc
      _ = L (v 0 • ![1, 0] + v 1 • ![0, 1]) := congrArg L hv
      _ = _ := by rw [map_add, map_smul, map_smul]; change v 0 * a + v 1 * b = _; ring
  by_cases hb : b = 0
  · have ha : a ≠ 0 := by
      intro ha
      apply hL
      apply LinearMap.ext
      intro v
      change L v = 0
      rw [hdecomp, ha, hb]
      simp
    refine ⟨⊤, a, ha, fun v => ?_⟩
    rw [hdecomp, hb, zero_mul, add_zero]
    change a * v 0 = a * (v 0 / 1)
    ring
  · let β : WithTop ℂ := ((-a / b : ℂ) : WithTop ℂ)
    let D : ℂ := (scalarTargetNormalizingSize β : ℂ)
    have hD : D ≠ 0 := Complex.ofReal_ne_zero.mpr (scalarTargetNormalizingSize_pos β).ne'
    refine ⟨β, b * D, mul_ne_zero hb hD, fun v => ?_⟩
    rw [hdecomp]
    change a * v 0 + b * v 1 = (b * D) * ((v 1 - (-a / b) * v 0) / D)
    field_simp
    ring

end
end ModifiedCartan
#print axioms ModifiedCartan.exists_scalar_target_coordinate_form
#print axioms ModifiedCartan.scalarTargetCoordinateMap_unique
