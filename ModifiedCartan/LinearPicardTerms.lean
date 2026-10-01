import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped Topology Interval
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Actual successive-integral terms for a continuous linear differential equation. -/
noncomputable def linearPicardTerm (B : ℝ → V →L[ℝ] V) (v : V) : ℕ → ℝ → V
  | 0, _ => v
  | n + 1, t => ∫ s in (0 : ℝ)..t, B s (linearPicardTerm B v n s)

theorem linearPicardTerm_continuous {B : ℝ → V →L[ℝ] V}
    (hB : Continuous B) (v : V) (n : ℕ) : Continuous (linearPicardTerm B v n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact (intervalIntegral.differentiable_integral_of_continuous (hB.clm_apply ih)).continuous

theorem linearPicardTerm_succ_hasDerivAt {B : ℝ → V →L[ℝ] V}
    (hB : Continuous B) (v : V) (n : ℕ) (t : ℝ) :
    HasDerivAt (linearPicardTerm B v (n + 1)) (B t (linearPicardTerm B v n t)) t := by
  have hc := hB.clm_apply (linearPicardTerm_continuous hB v n)
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem linearPicardTerm_succ_zero (B : ℝ → V →L[ℝ] V) (v : V) (n : ℕ) :
    linearPicardTerm B v (n + 1) 0 = 0 := by
  simp only [linearPicardTerm, intervalIntegral.integral_same]

/-- The factorial estimate holds in both time directions, by the exact integral
of |s|^n over the unordered interval between zero and t. -/
theorem linearPicardTerm_norm_le {B : ℝ → V →L[ℝ] V} {M : ℝ}
    (hM : 0 ≤ M) (hB : ∀ t, ‖B t‖ ≤ M) (v : V) (n : ℕ) (t : ℝ) :
    ‖linearPicardTerm B v n t‖ ≤ (‖v‖ * M ^ n / (n.factorial : ℝ)) * |t| ^ n := by
  induction n generalizing t with
  | zero => simp [linearPicardTerm]
  | succ n ih =>
    let c : ℝ := M * (‖v‖ * M ^ n / (n.factorial : ℝ))
    have hc : Continuous (fun s : ℝ => c * |s| ^ n) := by fun_prop
    have hi : IntegrableOn (fun s : ℝ => c * |s| ^ n) (Ι (0 : ℝ) t) :=
      (hc.intervalIntegrable 0 t).def'
    have hbound (s : ℝ) : ‖B s (linearPicardTerm B v n s)‖ ≤ c * |s| ^ n := by
      calc
        _ ≤ ‖B s‖ * ‖linearPicardTerm B v n s‖ := (B s).le_opNorm _
        _ ≤ M * ((‖v‖ * M ^ n / (n.factorial : ℝ)) * |s| ^ n) :=
          mul_le_mul (hB s) (ih s) (norm_nonneg _) hM
        _ = _ := by dsimp [c]; ring
    have hp : (∫ s in Ι (0 : ℝ) t, |s| ^ n) = |t| ^ (n + 1) / ((n : ℝ) + 1) := by
      simpa only [sub_zero] using integral_pow_abs_sub_uIoc (a := 0) (b := t) n
    calc
      ‖linearPicardTerm B v (n + 1) t‖ =
          ‖∫ s in Ι (0 : ℝ) t, B s (linearPicardTerm B v n s)‖ :=
        intervalIntegral.norm_intervalIntegral_eq _ _ _ _
      _ ≤ ∫ s in Ι (0 : ℝ) t, c * |s| ^ n :=
        norm_integral_le_of_norm_le hi (Eventually.of_forall hbound)
      _ = c * (|t| ^ (n + 1) / ((n : ℝ) + 1)) := by rw [integral_const_mul, hp]
      _ = (‖v‖ * M ^ (n + 1) / ((n + 1).factorial : ℝ)) * |t| ^ (n + 1) := by
        dsimp [c]
        rw [Nat.factorial_succ, pow_succ]
        push_cast
        have hn : (n : ℝ) + 1 ≠ 0 := by positivity
        field_simp [hn, Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)] <;> ring

theorem linearPicardTerm_summable {B : ℝ → V →L[ℝ] V} {M : ℝ}
    (hM : 0 ≤ M) (hB : ∀ t, ‖B t‖ ≤ M) (v : V) (t : ℝ) :
    Summable (fun n => linearPicardTerm B v n t) := by
  apply ((Real.summable_pow_div_factorial (M * |t|)).mul_left ‖v‖).of_norm_bounded
  intro n
  have h := linearPicardTerm_norm_le hM hB v n t
  simpa only [mul_pow, mul_div_assoc, div_mul_eq_mul_div, mul_assoc] using h

end ModifiedCartan
#print axioms ModifiedCartan.linearPicardTerm_norm_le
#print axioms ModifiedCartan.linearPicardTerm_summable

