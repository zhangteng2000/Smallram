import ModifiedCartan.ScalarSphereValues
import Mathlib.Analysis.SpecificLimits.Basic

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem halving_weight_iterate {w : ℕ → ℝ}
    (hw : ∀ n, w (n + 1) ≤ (1 / 2 : ℝ) * w n) (n k : ℕ) :
    w (n + k) ≤ w n * (1 / 2 : ℝ) ^ k := by
  induction k with
  | zero => simp only [Nat.add_zero, pow_zero, mul_one, le_refl]
  | succ k ih =>
    calc
      _ ≤ (1 / 2 : ℝ) * w (n + k) := hw (n + k)
      _ ≤ (1 / 2 : ℝ) * (w n * (1 / 2 : ℝ) ^ k) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

/-- Quantitative gluing of sphere target values, including infinity. This
auxiliary lemma does not assert the still separate physical-path hypotheses. -/
theorem scalarSphereValue_limit_of_halving_steps (a : ℕ → WithTop ℂ) {w : ℕ → ℝ}
    (hw : ∀ n, w (n + 1) ≤ (1 / 2 : ℝ) * w n)
    (hstep : ∀ n, ‖scalarSphereValue (a n) - scalarSphereValue (a (n + 1))‖ ≤ w n) :
    ∃ b : WithTop ℂ,
      Tendsto (fun n => scalarSphereValue (a n)) atTop (𝓝 (scalarSphereValue b)) ∧
      ∀ n, ‖scalarSphereValue (a n) - scalarSphereValue b‖ ≤ 2 * w n := by
  have hbound (n k : ℕ) :
      dist (scalarSphereValue (a (n + k))) (scalarSphereValue (a (n + (k + 1)))) ≤
        w n * (1 / 2 : ℝ) ^ k := by
    rw [dist_eq_norm]
    exact (hstep (n + k)).trans (halving_weight_iterate hw n k)
  have hC : CauchySeq (fun n => scalarSphereValue (a n)) :=
    cauchySeq_of_le_geometric (1 / 2 : ℝ) (w 0) (by norm_num)
      (fun n => by simpa only [Nat.zero_add] using hbound 0 n)
  obtain ⟨v, ht⟩ := cauchySeq_tendsto_of_complete hC
  have hv : v ∈ scalarSphereImage := scalarSphereImage_isCompact.isClosed.mem_of_tendsto ht
    (Eventually.of_forall (fun n => scalarSphereValue_mem (a n)))
  rw [scalarSphereImage_eq_range] at hv
  obtain ⟨b, rfl⟩ := hv
  refine ⟨b, ht, ?_⟩
  intro n
  have hshift : Tendsto (fun k => scalarSphereValue (a (n + k))) atTop (𝓝 (scalarSphereValue b)) := by
    simpa only [Function.comp_def, Nat.add_comm] using ht.comp (tendsto_add_atTop_nat n)
  have hh := dist_le_of_le_geometric_of_tendsto₀ (1 / 2 : ℝ) (w n) (by norm_num) (hbound n) hshift
  have hden : w n / (1 - (1 / 2 : ℝ)) = 2 * w n := by ring
  simpa only [Nat.add_zero, dist_eq_norm, hden] using hh

theorem exp_neg_scale_halving {s : ℕ → ℝ} {δ : ℝ}
    (hs : ∀ n, Real.log 2 ≤ δ * (s (n + 1) - s n)) :
    ∀ n, Real.exp (-δ * s (n + 1)) ≤ (1 / 2 : ℝ) * Real.exp (-δ * s n) := by
  intro n
  calc
    _ ≤ Real.exp (-δ * s n - Real.log 2) := Real.exp_le_exp.mpr (by nlinarith [hs n])
    _ = _ := by rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; ring

/-- Exponential error is preserved when consecutive scales have the proved
additive separation. Applying it to the curve requires the geometric connection. -/
theorem scalarSphereValue_limit_of_exponential_steps (a : ℕ → WithTop ℂ) {s : ℕ → ℝ} {δ : ℝ}
    (hs : ∀ n, Real.log 2 ≤ δ * (s (n + 1) - s n))
    (hstep : ∀ n, ‖scalarSphereValue (a n) - scalarSphereValue (a (n + 1))‖ ≤
      Real.exp (-δ * s n)) :
    ∃ b : WithTop ℂ,
      Tendsto (fun n => scalarSphereValue (a n)) atTop (𝓝 (scalarSphereValue b)) ∧
      ∀ n, ‖scalarSphereValue (a n) - scalarSphereValue b‖ ≤ 2 * Real.exp (-δ * s n) :=
  scalarSphereValue_limit_of_halving_steps a (exp_neg_scale_halving hs) hstep

end ModifiedCartan
#print axioms ModifiedCartan.scalarSphereValue_limit_of_halving_steps
#print axioms ModifiedCartan.scalarSphereValue_limit_of_exponential_steps
