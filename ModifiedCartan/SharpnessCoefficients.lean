import ModifiedCartan.Targets
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Factorial.Basic

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- Actual coefficients for the initial monomial solution of y^(q)=z^k*y. -/
noncomputable def sharpnessBaseCoeff (q k j : ℕ) : ℕ → ℝ
  | 0 => ((j.factorial : ℕ) : ℝ)⁻¹
  | l + 1 => sharpnessBaseCoeff q k j l /
      ((j + (q + k) * (l + 1)).descFactorial q : ℝ)

theorem sharpness_denominator_ge {q : ℕ} (hq : 1 ≤ q) (k j l : ℕ) :
    l + 1 ≤ (j + (q + k) * (l + 1)).descFactorial q := by
  have hm := Nat.mul_le_mul_right l hq
  have hn : l + q ≤ j + (q + k) * (l + 1) := by nlinarith
  have hb : l + 1 ≤ j + (q + k) * (l + 1) + 1 - q := by omega
  exact hb.trans ((le_self_pow₀ (by omega) (by omega : q ≠ 0)).trans
    (Nat.pow_sub_le_descFactorial _ q))

theorem sharpnessBaseCoeff_pos {q : ℕ} (hq : 1 ≤ q) (k j l : ℕ) :
    0 < sharpnessBaseCoeff q k j l := by
  induction l with
  | zero => simp only [sharpnessBaseCoeff]; positivity
  | succ l ih =>
    apply div_pos ih
    exact_mod_cast (lt_of_lt_of_le (Nat.succ_pos l) (sharpness_denominator_ge hq k j l))

theorem sharpnessBaseCoeff_recurrence {q : ℕ} (hq : 1 ≤ q) (k j l : ℕ) :
    sharpnessBaseCoeff q k j (l + 1) *
      ((j + (q + k) * (l + 1)).descFactorial q : ℝ) = sharpnessBaseCoeff q k j l := by
  have hd : (0 : ℝ) < ((j + (q + k) * (l + 1)).descFactorial q : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (Nat.succ_pos l) (sharpness_denominator_ge hq k j l))
  exact div_mul_cancel₀ _ hd.ne'

/-- Every fixed disk has an actual summable majorant for the solution series. -/
theorem sharpnessBaseCoeff_weighted_summable {q : ℕ} (hq : 1 ≤ q)
    (k j : ℕ) {R : ℝ} (hR : 0 < R) :
    Summable (fun l : ℕ => sharpnessBaseCoeff q k j l * R ^ (j + (q + k) * l)) := by
  have hp (l : ℕ) : 0 ≤ sharpnessBaseCoeff q k j l * R ^ (j + (q + k) * l) :=
    (mul_pos (sharpnessBaseCoeff_pos hq k j l) (pow_pos hR _)).le
  apply summable_of_ratio_norm_eventually_le (r := (1 / 2 : ℝ)) (by norm_num)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 * R ^ (q + k))] with l hl
  have hd : (0 : ℝ) < ((j + (q + k) * (l + 1)).descFactorial q : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (Nat.succ_pos l) (sharpness_denominator_ge hq k j l))
  have hdge : (l : ℝ) + 1 ≤ ((j + (q + k) * (l + 1)).descFactorial q : ℝ) := by
    exact_mod_cast sharpness_denominator_ge hq k j l
  have hratio : R ^ (q + k) / ((j + (q + k) * (l + 1)).descFactorial q : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hd).mpr
    linarith
  have he : sharpnessBaseCoeff q k j (l + 1) * R ^ (j + (q + k) * (l + 1)) =
      (R ^ (q + k) / ((j + (q + k) * (l + 1)).descFactorial q : ℝ)) *
        (sharpnessBaseCoeff q k j l * R ^ (j + (q + k) * l)) := by
    rw [sharpnessBaseCoeff, show j + (q + k) * (l + 1) = (j + (q + k) * l) + (q + k) by ring,
      pow_add]
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (hp (l + 1)), Real.norm_eq_abs, abs_of_nonneg (hp l), he]
  exact mul_le_mul_of_nonneg_right hratio (hp l)

end ModifiedCartan
#print axioms ModifiedCartan.sharpnessBaseCoeff_recurrence
#print axioms ModifiedCartan.sharpnessBaseCoeff_weighted_summable
