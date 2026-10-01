import ModifiedCartan.CurveOrderBasic
import ModifiedCartan.TaylorWronskianGrowth

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- A translated constant linear combination of entire coordinates,
used in the actual inverse-jet construction of `lem:small-order-coordinates`. -/
noncomputable def shiftedCombination {n : ℕ} (g : Index n → ℂ → ℂ)
    (c : Index n → ℂ) (b z : ℂ) : ℂ := ∑ k, c k * g k (b + z)

theorem shiftedCombination_differentiable {n : ℕ} {g : Index n → ℂ → ℂ}
    (hg : ∀ j, Differentiable ℂ (g j)) (c : Index n → ℂ) (b : ℂ) :
    Differentiable ℂ (shiftedCombination g c b) := by
  unfold shiftedCombination
  fun_prop

theorem shiftedCombination_power_bound {n : ℕ} {g : Index n → ℂ → ℂ}
    (hg : ∀ j, Differentiable ℂ (g j)) (c : Index n → ℂ) (b : ℂ)
    {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 < C)
    (hc : ∀ j r, 1 ≤ r → Real.posLog (maximumModulus (g j) r) ≤ C * r ^ β) :
    ∃ D : ℝ, 0 < D ∧ ∀ r, 1 ≤ r →
      Real.posLog (maximumModulus (shiftedCombination g c b) r) ≤ D * r ^ β := by
  classical
  let S : ℝ := 1 + ∑ k, ‖c k‖
  let A : ℝ := C * (1 + ‖b‖) ^ β
  have hS : 1 ≤ S := by
    have hn : 0 ≤ ∑ k, ‖c k‖ := Finset.sum_nonneg (fun k _ => norm_nonneg (c k))
    dsimp only [S]
    linarith
  have hSp : 0 < S := zero_lt_one.trans_le hS
  have hA : 0 < A := mul_pos hC (Real.rpow_pos_of_pos (by positivity) _)
  have hlogS : 0 ≤ Real.log S := Real.log_nonneg hS
  refine ⟨Real.log S + A, by positivity, ?_⟩
  intro r hr
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hpow : 1 ≤ r ^ β := Real.one_le_rpow hr hβ
  have hR : r + ‖b‖ ≤ (1 + ‖b‖) * r := by nlinarith [norm_nonneg b]
  have hpowR : (r + ‖b‖) ^ β ≤ (1 + ‖b‖) ^ β * r ^ β := by
    rw [← Real.mul_rpow (by positivity : (0 : ℝ) ≤ 1 + ‖b‖) hr0.le]
    exact Real.rpow_le_rpow (by positivity) hR hβ
  have hM (k : Index n) : maximumModulus (g k) (r + ‖b‖) ≤ Real.exp (A * r ^ β) := by
    apply Real.le_exp_of_log_le
    have hh := (le_max_right 0 (Real.log (maximumModulus (g k) (r + ‖b‖)))).trans
      (hc k (r + ‖b‖) (by linarith [norm_nonneg b]))
    exact hh.trans (by dsimp only [A]; nlinarith)
  have hmax : maximumModulus (shiftedCombination g c b) r ≤
      Real.exp ((Real.log S + A) * r ^ β) := by
    apply maximumModulus_le hr0.le
    intro z hz
    have hnz : ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz
    have hgz (k : Index n) : ‖g k (b + z)‖ ≤ Real.exp (A * r ^ β) := by
      apply (norm_le_maximumModulus (hg k).continuous ?_).trans (hM k)
      rw [mem_closedBall, dist_zero_right]
      exact (norm_add_le b z).trans (by linarith)
    calc
      ‖shiftedCombination g c b z‖ ≤ ∑ k, ‖c k‖ * ‖g k (b + z)‖ := by
        simpa only [shiftedCombination, norm_mul] using norm_sum_le (s := Finset.univ)
          (f := fun k => c k * g k (b + z))
      _ ≤ ∑ k, ‖c k‖ * Real.exp (A * r ^ β) :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hgz k) (norm_nonneg _))
      _ = (∑ k, ‖c k‖) * Real.exp (A * r ^ β) := (Finset.sum_mul ..).symm
      _ ≤ S * Real.exp (A * r ^ β) := by dsimp only [S]; nlinarith [Real.exp_pos (A * r ^ β)]
      _ = Real.exp (Real.log S + A * r ^ β) := by rw [Real.exp_add, Real.exp_log hSp]
      _ ≤ Real.exp ((Real.log S + A) * r ^ β) := Real.exp_le_exp.mpr (by nlinarith)
  have hp := Real.posLog_le_posLog
    (maximumModulus_nonneg (shiftedCombination_differentiable hg c b).continuous hr0.le) hmax
  have hD : 0 ≤ (Real.log S + A) * r ^ β := by positivity
  simpa only [Real.posLog, Real.log_exp, max_eq_right hD] using hp

theorem shiftedCombination_entireOrder_le {n : ℕ} {g : Index n → ℂ → ℂ}
    (hg : ∀ j, Differentiable ℂ (g j)) (c : Index n → ℂ) (b : ℂ)
    {ρ : EReal} (hρ : 0 ≤ ρ) (ho : ∀ j, entireOrder (g j) ≤ ρ) :
    entireOrder (shiftedCombination g c b) ≤ ρ := by
  apply EReal.le_of_forall_lt_iff_le.mp
  intro β hβ
  have hβ0 : 0 ≤ β := by exact_mod_cast hρ.trans hβ.le
  obtain ⟨C, hC, hc⟩ := finite_entireOrder_common_power_bound (fun j => (hg j).continuous)
    (fun j => (ho j).trans_lt hβ)
  obtain ⟨D, hD, hd⟩ := shiftedCombination_power_bound hg c b hβ0 hC hc
  exact entireOrder_le_of_posLog_power_bound hβ0 hD hd

end ModifiedCartan
#print axioms ModifiedCartan.shiftedCombination_entireOrder_le
