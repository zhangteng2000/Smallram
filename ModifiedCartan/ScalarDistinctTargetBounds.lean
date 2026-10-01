import ModifiedCartan.ScalarTargetUnitary
import Mathlib.Analysis.Normed.Module.FiniteDimension

open scoped Topology Matrix
open Filter Set Matrix
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- Distinct projective targets have linearly independent vanishing forms. -/
theorem scalarTargetLinearForm_common_zero {α β : WithTop ℂ} (hab : α ≠ β)
    {q p : ℂ} (ha : scalarTargetLinearForm α q p = 0)
    (hb : scalarTargetLinearForm β q p = 0) : q = 0 ∧ p = 0 := by
  induction α using WithTop.recTopCoe with
  | top =>
    induction β using WithTop.recTopCoe with
    | top => exact (hab rfl).elim
    | coe b =>
      change q = 0 at ha
      change p - b * q = 0 at hb
      exact ⟨ha, by simpa only [ha, mul_zero, sub_zero] using hb⟩
  | coe a =>
    induction β using WithTop.recTopCoe with
    | top =>
      change q = 0 at hb
      change p - a * q = 0 at ha
      exact ⟨hb, by simpa only [hb, mul_zero, sub_zero] using ha⟩
    | coe b =>
      change p - a * q = 0 at ha
      change p - b * q = 0 at hb
      have hne : a ≠ b := fun he => hab (congrArg (fun x : ℂ => (x : WithTop ℂ)) he)
      have he : (a - b) * q = 0 := by
        calc
          _ = (p - b * q) - (p - a * q) := by ring
          _ = 0 := by rw [ha, hb, sub_self]
      have hq := (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hne)
      exact ⟨hq, by simpa only [hq, mul_zero, sub_zero] using ha⟩

def scalarTargetCoordinateMap (β : WithTop ℂ) : (Index 1 → ℂ) →ₗ[ℂ] ℂ where
  toFun v := scalarTargetLinearForm β (v 0) (v 1) / (scalarTargetNormalizingSize β : ℂ)
  map_add' v w := by
    induction β using WithTop.recTopCoe with
    | top => change (v 0 + w 0) / 1 = v 0 / 1 + w 0 / 1; ring
    | coe b =>
      change ((v 1 + w 1) - b * (v 0 + w 0)) / _ =
        (v 1 - b * v 0) / _ + (w 1 - b * w 0) / _
      ring
  map_smul' t v := by
    induction β using WithTop.recTopCoe with
    | top => change (t * v 0) / 1 = t * (v 0 / 1); ring
    | coe b =>
      change (t * v 1 - b * (t * v 0)) / _ = t * ((v 1 - b * v 0) / _)
      ring

theorem scalarTargetCoordinateMap_apply (β : WithTop ℂ) (v : Index 1 → ℂ) :
    scalarTargetCoordinateMap β v =
      (v ᵥ* (scalarTargetUnitary β : Matrix (Index 1) (Index 1) ℂ)) 0 :=
  (scalarTargetUnitary_first β v).symm

/-- The actual Euclidean norm is controlled by the two fixed target
coordinates. The constant is constructed from their proved independence. -/
theorem scalar_distinct_target_norm_bound {α β : WithTop ℂ} (hab : α ≠ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : Index 1 → ℂ,
      euclideanNorm v ≤ C * max
        ‖(v ᵥ* (scalarTargetUnitary α : Matrix (Index 1) (Index 1) ℂ)) 0‖
        ‖(v ᵥ* (scalarTargetUnitary β : Matrix (Index 1) (Index 1) ℂ)) 0‖ := by
  let L := (scalarTargetCoordinateMap α).prod (scalarTargetCoordinateMap β)
  have hker : LinearMap.ker L = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have hα := congrArg Prod.fst hv
    have hβ := congrArg Prod.snd hv
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
  obtain ⟨K, hK, hbound⟩ := L.exists_antilipschitzWith hker
  refine ⟨Real.sqrt 2 * (K : ℝ), mul_pos (Real.sqrt_pos.mpr (by norm_num)) hK, ?_⟩
  intro v
  have hh := hbound.le_mul_dist v 0
  rw [map_zero, dist_zero_right, dist_zero_right] at hh
  have hv : ‖L v‖ = max
      ‖(v ᵥ* (scalarTargetUnitary α : Matrix (Index 1) (Index 1) ℂ)) 0‖
      ‖(v ᵥ* (scalarTargetUnitary β : Matrix (Index 1) (Index 1) ℂ)) 0‖ := by
    change max ‖scalarTargetCoordinateMap α v‖ ‖scalarTargetCoordinateMap β v‖ = _
    rw [scalarTargetCoordinateMap_apply, scalarTargetCoordinateMap_apply]
  rw [hv] at hh
  calc
    euclideanNorm v ≤ Real.sqrt 2 * ‖v‖ := by simpa only [Nat.cast_one, one_add_one_eq_two] using euclideanNorm_le v
    _ ≤ Real.sqrt 2 * ((K : ℝ) * _) := mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg _)
    _ = _ := by ring

end
end ModifiedCartan
#print axioms ModifiedCartan.scalarTargetLinearForm_common_zero
#print axioms ModifiedCartan.scalar_distinct_target_norm_bound
