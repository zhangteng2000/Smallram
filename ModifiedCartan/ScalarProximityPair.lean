import ModifiedCartan.ScalarTargetGaugeMean
import ModifiedCartan.ScalarCharacteristicBridge

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- Numerator of the scalar expression used in proximity to a target. -/
def scalarProximityNumerator (β : WithTop ℂ) (q p : ℂ) : ℂ :=
  β.recTopCoe p (fun _ => q)

def scalarProximityPairNorm (β : WithTop ℂ) (v : Index 1 → ℂ) : ℝ :=
  max ‖scalarProximityNumerator β (v 0) (v 1)‖ ‖scalarTargetLinearForm β (v 0) (v 1)‖

def scalarTargetRawFunction (f : Curve 1) (β : WithTop ℂ) (z : ℂ) : ℂ :=
  scalarTargetLinearForm β (f.coord 0 z) (f.coord 1 z)

theorem scalarTargetFunction_eq_raw_div (f : Curve 1) (β : WithTop ℂ) (z : ℂ) :
    scalarTargetFunction f β z = scalarTargetRawFunction f β z / (scalarTargetNormalizingSize β : ℂ) := rfl

theorem scalarTargetRawFunction_differentiable (f : Curve 1) (β : WithTop ℂ) :
    Differentiable ℂ (scalarTargetRawFunction f β) := by
  induction β using WithTop.recTopCoe with
  | top => exact f.holomorphic 0
  | coe b => exact (f.holomorphic 1).sub ((f.holomorphic 0).const_mul b)

theorem scalarTargetRawFunction_nontrivial (f : Curve 1) (hlin : f.linearlyNonDegenerate)
    (β : WithTop ℂ) : ∃ z, scalarTargetRawFunction f β z ≠ 0 := by
  obtain ⟨z, hz⟩ := scalarTargetFunction_nontrivial f hlin β
  refine ⟨z, fun he => hz ?_⟩
  rw [scalarTargetFunction_eq_raw_div, he, zero_div]

theorem scalarTargetLinearSize_one_le (β : WithTop ℂ) : 1 ≤ scalarTargetLinearSize β := by
  induction β using WithTop.recTopCoe with
  | top => exact le_rfl
  | coe b => change 1 ≤ 1 + ‖b‖; linarith [norm_nonneg b]

/-- Explicit norm comparison for the actual numerator/target pair. -/
theorem scalarProximityPairNorm_compare (β : WithTop ℂ) (v : Index 1 → ℂ) :
    scalarProximityPairNorm β v ≤ (2 * scalarTargetLinearSize β) * euclideanNorm v ∧
      euclideanNorm v ≤ (2 * scalarTargetLinearSize β) * scalarProximityPairNorm β v := by
  have hN := euclideanNorm_nonneg v
  have hq : ‖v 0‖ ≤ euclideanNorm v := (norm_le_pi_norm v 0).trans (norm_le_euclideanNorm v)
  have hp : ‖v 1‖ ≤ euclideanNorm v := (norm_le_pi_norm v 1).trans (norm_le_euclideanNorm v)
  have hS := scalarTargetLinearSize_one_le β
  have hM : 0 ≤ scalarProximityPairNorm β v := (norm_nonneg _).trans (le_max_left _ _)
  have hupper : scalarProximityPairNorm β v ≤ scalarTargetLinearSize β * euclideanNorm v := by
    induction β using WithTop.recTopCoe with
    | top => change max ‖v 1‖ ‖v 0‖ ≤ 1 * _; simpa only [one_mul] using max_le hp hq
    | coe b =>
      change max ‖v 0‖ ‖v 1 - b * v 0‖ ≤ (1 + ‖b‖) * euclideanNorm v
      apply max_le
      · nlinarith [mul_nonneg (norm_nonneg b) hN]
      · calc
          _ ≤ ‖v 1‖ + ‖b‖ * ‖v 0‖ := by simpa only [norm_mul] using norm_sub_le (v 1) (b * v 0)
          _ ≤ euclideanNorm v + ‖b‖ * euclideanNorm v :=
            add_le_add hp (mul_le_mul_of_nonneg_left hq (norm_nonneg b))
          _ = _ := by ring
  have hlower : ‖v‖ ≤ scalarTargetLinearSize β * scalarProximityPairNorm β v := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (scalarTargetLinearSize_pos β).le hM)).mpr
    intro j
    induction β using WithTop.recTopCoe with
    | top =>
      change ‖v j‖ ≤ 1 * max ‖v 1‖ ‖v 0‖
      rw [one_mul]
      fin_cases j
      · exact le_max_right _ _
      · exact le_max_left _ _
    | coe b =>
      change ‖v j‖ ≤ (1 + ‖b‖) * max ‖v 0‖ ‖v 1 - b * v 0‖
      have hqM := le_max_left ‖v 0‖ ‖v 1 - b * v 0‖
      have hLM := le_max_right ‖v 0‖ ‖v 1 - b * v 0‖
      have hM0 : 0 ≤ max ‖v 0‖ ‖v 1 - b * v 0‖ := (norm_nonneg _).trans hqM
      fin_cases j
      · change ‖v 0‖ ≤ (1 + ‖b‖) * max ‖v 0‖ ‖v 1 - b * v 0‖
        nlinarith [mul_nonneg (norm_nonneg b) hM0]
      · calc
          ‖v 1‖ = ‖(v 1 - b * v 0) + b * v 0‖ := by rw [sub_add_cancel]
          _ ≤ ‖v 1 - b * v 0‖ + ‖b‖ * ‖v 0‖ := by simpa only [norm_mul] using norm_add_le (v 1 - b * v 0) (b * v 0)
          _ ≤ max ‖v 0‖ ‖v 1 - b * v 0‖ + ‖b‖ * max ‖v 0‖ ‖v 1 - b * v 0‖ :=
            add_le_add hLM (mul_le_mul_of_nonneg_left hqM (norm_nonneg b))
          _ = _ := by ring
  have hsqrt : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  refine ⟨hupper.trans ?_, ?_⟩
  · nlinarith [mul_nonneg (scalarTargetLinearSize_pos β).le hN]
  · calc
      euclideanNorm v ≤ Real.sqrt 2 * ‖v‖ := by simpa only [Nat.cast_one, one_add_one_eq_two] using euclideanNorm_le v
      _ ≤ 2 * ‖v‖ := mul_le_mul_of_nonneg_right hsqrt (norm_nonneg v)
      _ ≤ 2 * (scalarTargetLinearSize β * scalarProximityPairNorm β v) := mul_le_mul_of_nonneg_left hlower (by norm_num)
      _ = _ := by ring

theorem scalarProximityPairNorm_pos (β : WithTop ℂ) {v : Index 1 → ℂ} (hv : v ≠ 0) :
    0 < scalarProximityPairNorm β v := by
  have h := (scalarProximityPairNorm_compare β v).2
  have hpos := euclideanNorm_pos hv
  have hS := scalarTargetLinearSize_pos β
  by_contra hn
  have hM := le_of_not_gt hn
  have hh := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 2 * scalarTargetLinearSize β by positivity) hM
  linarith

theorem scalarProximityPairNorm_continuous (f : Curve 1) (β : WithTop ℂ) :
    Continuous (fun z => scalarProximityPairNorm β (f.vector z)) := by
  induction β using WithTop.recTopCoe with
  | top => exact (f.holomorphic 1).continuous.norm.max (f.holomorphic 0).continuous.norm
  | coe b =>
    exact (f.holomorphic 0).continuous.norm.max
      (((f.holomorphic 1).continuous.sub ((f.holomorphic 0).continuous.const_mul b)).norm)

theorem scalarProximityPairLog_continuous (f : Curve 1) (β : WithTop ℂ) :
    Continuous (fun z => Real.log (scalarProximityPairNorm β (f.vector z))) :=
  (scalarProximityPairNorm_continuous f β).log
    (fun z => (scalarProximityPairNorm_pos β (f.vector_ne_zero z)).ne')

end
end ModifiedCartan
#print axioms ModifiedCartan.scalarProximityPairNorm_compare
