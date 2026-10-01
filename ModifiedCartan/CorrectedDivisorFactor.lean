import ModifiedCartan.CorrectedLinearFactor
import ModifiedCartan.GenusZeroMultiplicity

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- A correction chosen separately at each accuracy 2^(-n); the choice is
justified by the preceding polynomial approximation theorem. -/
noncomputable def divisorCorrectionPolynomial (n : ℕ) : Polynomial ℂ :=
  (exists_corrected_linear_factor (ε := (1 / 2 : ℝ) ^ n) (by positivity)).choose

theorem divisorCorrectionPolynomial_bound (n : ℕ) {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖(1 - w) * Complex.exp ((divisorCorrectionPolynomial n).eval w) - 1‖ ≤
      (1 / 2 : ℝ) ^ n :=
  (exists_corrected_linear_factor (ε := (1 / 2 : ℝ) ^ n) (by positivity)).choose_spec w hw

/-- The actual simple-zero factor, also defined at the origin. -/
noncomputable def correctedDivisorFactor (n : ℕ) (a z : ℂ) : ℂ :=
  if a = 0 then z else
    (1 - z / a) * Complex.exp ((divisorCorrectionPolynomial n).eval (z / a))

theorem correctedDivisorFactor_differentiable (n : ℕ) (a : ℂ) :
    Differentiable ℂ (correctedDivisorFactor n a) := by
  unfold correctedDivisorFactor
  split_ifs <;> fun_prop

theorem correctedDivisorFactor_eq_zero_iff (n : ℕ) (a z : ℂ) :
    correctedDivisorFactor n a z = 0 ↔ z = a := by
  by_cases ha : a = 0
  · simp [correctedDivisorFactor, ha]
  · simp only [correctedDivisorFactor, if_neg ha, mul_eq_zero, Complex.exp_ne_zero,
      or_false, sub_eq_zero]
    exact eq_comm.trans (div_eq_one_iff_eq ha)

theorem correctedDivisorFactor_analyticOrderAt (n : ℕ) (a : ℂ) :
    analyticOrderAt (correctedDivisorFactor n a) a = 1 := by
  by_cases ha : a = 0
  · subst a
    have he : correctedDivisorFactor n (0 : ℂ) = id := by
      funext z
      simp [correctedDivisorFactor]
    rw [he]
    exact analyticOrderAt_id
  · have hA : AnalyticAt ℂ (fun z : ℂ => 1 - z / a) a := by fun_prop
    have hB : AnalyticAt ℂ
        (fun z : ℂ => Complex.exp ((divisorCorrectionPolynomial n).eval (z / a))) a :=
      (show Differentiable ℂ (fun z : ℂ => Complex.exp ((divisorCorrectionPolynomial n).eval (z / a))) from by fun_prop).analyticAt a
    have he : correctedDivisorFactor n a =
        (fun z : ℂ => 1 - z / a) *
        (fun z : ℂ => Complex.exp ((divisorCorrectionPolynomial n).eval (z / a))) := by
      ext z
      simp only [correctedDivisorFactor, if_neg ha, Pi.mul_apply]
    rw [he, analyticOrderAt_mul hA hB, analyticOrderAt_genusZeroFactor ha,
      hB.analyticOrderAt_eq_zero.mpr (Complex.exp_ne_zero _), add_zero]

theorem correctedDivisorFactor_half_disk_bound (n : ℕ) {a z : ℂ}
    (ha : a ≠ 0) (hz : ‖z‖ ≤ ‖a‖ / 2) :
    ‖correctedDivisorFactor n a z - 1‖ ≤ (1 / 2 : ℝ) ^ n := by
  rw [correctedDivisorFactor, if_neg ha]
  apply divisorCorrectionPolynomial_bound
  rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr ha)]
  linarith

end ModifiedCartan
#print axioms ModifiedCartan.correctedDivisorFactor_analyticOrderAt
#print axioms ModifiedCartan.correctedDivisorFactor_half_disk_bound


