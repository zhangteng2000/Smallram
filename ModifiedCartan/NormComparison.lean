import FewInflection.Definitions
import Mathlib.Analysis.Real.Sqrt

open scoped BigOperators Topology
open Filter Asymptotics

namespace ModifiedCartan

noncomputable section

abbrev Index := FewInflection.Index
abbrev Curve := FewInflection.Curve

/-- Euclidean norm in the manuscript, preceding LaTeX label `cartan`. -/
def euclideanNorm {n : ℕ} (v : Index n → ℂ) : ℝ :=
  Real.sqrt (∑ j, ‖v j‖ ^ 2)

theorem euclideanNorm_nonneg {n : ℕ} (v : Index n → ℂ) :
    0 ≤ euclideanNorm v := Real.sqrt_nonneg _

theorem norm_le_euclideanNorm {n : ℕ} (v : Index n → ℂ) :
    ‖v‖ ≤ euclideanNorm v := by
  apply (pi_norm_le_iff_of_nonneg (euclideanNorm_nonneg v)).mpr
  intro j
  apply Real.le_sqrt_of_sq_le
  exact Finset.single_le_sum (fun i _ => sq_nonneg ‖v i‖) (Finset.mem_univ j)

theorem euclideanNorm_le {n : ℕ} (v : Index n → ℂ) :
    euclideanNorm v ≤ Real.sqrt (n + 1) * ‖v‖ := by
  have hsum : (∑ j : Index n, ‖v j‖ ^ 2) ≤ (n + 1 : ℝ) * ‖v‖ ^ 2 := by
    calc
      _ ≤ ∑ _j : Index n, ‖v‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        gcongr
        exact norm_le_pi_norm v j
      _ = _ := by simp [Index, FewInflection.Index]
  have hsqrt := Real.sqrt_le_sqrt hsum
  simpa only [euclideanNorm, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ n + 1),
    Real.sqrt_sq (norm_nonneg v)] using hsqrt

theorem euclideanNorm_pos {n : ℕ} {v : Index n → ℂ} (hv : v ≠ 0) :
    0 < euclideanNorm v :=
  (norm_pos_iff.mpr hv).trans_le (norm_le_euclideanNorm v)

theorem euclideanNorm_continuous {n : ℕ} :
    Continuous (euclideanNorm (n := n)) := by
  unfold euclideanNorm
  fun_prop

theorem curve_log_euclideanNorm_continuous {n : ℕ} (f : Curve n) :
    Continuous (fun z => Real.log (euclideanNorm (f.vector z))) := by
  apply (euclideanNorm_continuous.comp
    (continuous_pi (fun j => (f.holomorphic j).continuous))).log
  intro z
  exact (euclideanNorm_pos (f.vector_ne_zero z)).ne'

theorem curve_log_norm_continuous {n : ℕ} (f : Curve n) :
    Continuous (fun z => Real.log ‖f.vector z‖) := by
  apply (continuous_pi (fun j => (f.holomorphic j).continuous)).norm.log
  intro z
  exact norm_ne_zero_iff.mpr (f.vector_ne_zero z)

theorem log_norm_le_log_euclideanNorm {n : ℕ} {v : Index n → ℂ}
    (hv : v ≠ 0) : Real.log ‖v‖ ≤ Real.log (euclideanNorm v) :=
  Real.log_le_log (norm_pos_iff.mpr hv) (norm_le_euclideanNorm v)

theorem log_euclideanNorm_le {n : ℕ} {v : Index n → ℂ}
    (hv : v ≠ 0) :
    Real.log (euclideanNorm v) ≤ Real.log (Real.sqrt (n + 1)) + Real.log ‖v‖ := by
  have h := Real.log_le_log (euclideanNorm_pos hv) (euclideanNorm_le v)
  rwa [Real.log_mul (by positivity : Real.sqrt (n + 1 : ℝ) ≠ 0)
    (norm_ne_zero_iff.mpr hv)] at h

/-- The manuscript's characteristic, using its Euclidean norm.
LaTeX context: the Introduction, preceding `cartan`. -/
def characteristic {n : ℕ} (f : Curve n) (r : ℝ) : ℝ :=
  Real.circleAverage (fun z => Real.log (euclideanNorm (f.vector z))) 0 r -
    Real.log (euclideanNorm (f.vector 0))

theorem characteristic_eq_circleAverage {n : ℕ} (f : Curve n) (r : ℝ) :
    characteristic f r =
      Real.circleAverage (fun z => Real.log (euclideanNorm (f.vector z))) 0 r -
        Real.log (euclideanNorm (f.vector 0)) := rfl

theorem characteristic_zero {n : ℕ} (f : Curve n) :
    characteristic f 0 = 0 := by simp [characteristic]

theorem circleAverage_log_norm_le {n : ℕ} (f : Curve n) (r : ℝ) :
    Real.circleAverage (fun z => Real.log ‖f.vector z‖) 0 r ≤
      Real.circleAverage (fun z => Real.log (euclideanNorm (f.vector z))) 0 r := by
  apply Real.circleAverage_mono
    (curve_log_norm_continuous f).continuousOn.circleIntegrable'
    (curve_log_euclideanNorm_continuous f).continuousOn.circleIntegrable'
  intro z _
  exact log_norm_le_log_euclideanNorm (f.vector_ne_zero z)

theorem circleAverage_log_euclideanNorm_le {n : ℕ} (f : Curve n) (r : ℝ) :
    Real.circleAverage (fun z => Real.log (euclideanNorm (f.vector z))) 0 r ≤
      Real.log (Real.sqrt (n + 1)) +
        Real.circleAverage (fun z => Real.log ‖f.vector z‖) 0 r := by
  have h := Real.circleAverage_mono
    (curve_log_euclideanNorm_continuous f).continuousOn.circleIntegrable'
    (continuous_const.add (curve_log_norm_continuous f)).continuousOn.circleIntegrable'
    (fun z _ => log_euclideanNorm_le (f.vector_ne_zero z)) (c := 0) (R := r)
  change Real.circleAverage (fun z => Real.log (euclideanNorm (f.vector z))) 0 r ≤
    Real.circleAverage (fun z => Real.log (Real.sqrt (n + 1)) +
      Real.log ‖f.vector z‖) 0 r at h
  rwa [Real.circleAverage_fun_add (circleIntegrable_const _ _ _)
    (curve_log_norm_continuous f).continuousOn.circleIntegrable',
    Real.circleAverage_const] at h

/-- Explicit norm-convention bridge for the paper's characteristic.
This is an elementary additional proof, recorded in FORMALIZATION_MAP.md. -/
theorem characteristic_abs_sub_le {n : ℕ} (f : Curve n) (r : ℝ) :
    |characteristic f r - FewInflection.characteristic f r| ≤
      Real.log (Real.sqrt (n + 1)) := by
  have h₁ := circleAverage_log_norm_le f r
  have h₂ := circleAverage_log_euclideanNorm_le f r
  have h₃ := log_norm_le_log_euclideanNorm (f.vector_ne_zero 0)
  have h₄ := log_euclideanNorm_le (f.vector_ne_zero 0)
  rw [abs_le]
  unfold characteristic FewInflection.characteristic
  constructor <;> linarith

/-- LaTeX label `eq:zero-count-definition`, specialized to the Wronskian. -/
abbrev ramification {n : ℕ} (f : Curve n) : ℝ → ℝ := FewInflection.ramification f

/-- The literal logarithmic quotient from the Introduction, with no cutoff. -/
def logGrowthRatio {n : ℕ} (f : Curve n) (r : ℝ) : EReal :=
  (Real.log (characteristic f r) / Real.log r : ℝ)

def order {n : ℕ} (f : Curve n) : EReal := limsup (logGrowthRatio f) atTop
def lowerOrder {n : ℕ} (f : Curve n) : EReal := liminf (logGrowthRatio f) atTop
def FiniteLowerOrder {n : ℕ} (f : Curve n) : Prop := lowerOrder f < ⊤

/-- LaTeX label `eq:mainhyp`. -/
def SmallRamification {n : ℕ} (f : Curve n) : Prop :=
  ramification f =o[atTop] characteristic f

end
end ModifiedCartan

