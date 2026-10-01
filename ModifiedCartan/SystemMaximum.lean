import ModifiedCartan.EntireOrder
import ModifiedCartan.QuantitativeTaylor
import Mathlib.Topology.Order.Lattice

open scoped Topology BigOperators
open Filter Set Metric Asymptotics
set_option autoImplicit false
namespace ModifiedCartan

/-- Largest component maximum modulus in LaTeX `cor:convolution`. -/
noncomputable def systemMaximum {n : ℕ} (y : Fin (n + 1) → ℂ → ℂ) (r : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => maximumModulus (y j) r)

/-- The literal H_y in LaTeX `cor:convolution`; no logarithmic cutoff. -/
noncomputable def systemLogMaximum {n : ℕ} (y : Fin (n + 1) → ℂ → ℂ) (r : ℝ) : ℝ :=
  Real.log (systemMaximum y r)

theorem maximumModulus_le_systemMaximum {n : ℕ} (y : Fin (n + 1) → ℂ → ℂ)
    (r : ℝ) (j : Fin (n + 1)) : maximumModulus (y j) r ≤ systemMaximum y r :=
  Finset.le_sup' (fun k => maximumModulus (y k) r) (Finset.mem_univ j)

theorem systemMaximum_attained {n : ℕ} (y : Fin (n + 1) → ℂ → ℂ) (r : ℝ) :
    ∃ j, systemMaximum y r = maximumModulus (y j) r := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty
    (fun j => maximumModulus (y j) r)
  exact ⟨j, hj⟩

theorem systemMaximum_continuousOn {n : ℕ} {y : Fin (n + 1) → ℂ → ℂ}
    (hy : ∀ j, Continuous (y j)) : ContinuousOn (systemMaximum y) (Ici 0) :=
  ContinuousOn.finset_sup'_apply Finset.univ_nonempty
    (fun j _ => maximumModulus_continuousOn (hy j))

theorem systemMaximum_monotoneOn {n : ℕ} {y : Fin (n + 1) → ℂ → ℂ}
    (hy : ∀ j, Continuous (y j)) : MonotoneOn (systemMaximum y) (Ici 0) := by
  intro r hr s hs hrs
  apply Finset.sup'_le
  intro j _
  exact ((maximumModulus_monotoneOn (hy j)) hr hs hrs).trans
    (maximumModulus_le_systemMaximum y s j)

theorem one_le_systemMaximum {n : ℕ} {y : Fin (n + 1) → ℂ → ℂ}
    (hy : ∀ j, Continuous (y j)) (h0 : y 0 0 = 1) {r : ℝ} (hr : 0 ≤ r) :
    1 ≤ systemMaximum y r := by
  have hh := (norm_le_maximumModulus (hy 0) (mem_closedBall_self hr)).trans
    (maximumModulus_le_systemMaximum y r 0)
  simpa only [h0, norm_one] using hh

theorem systemLogMaximum_nonneg {n : ℕ} {y : Fin (n + 1) → ℂ → ℂ}
    (hy : ∀ j, Continuous (y j)) (h0 : y 0 0 = 1) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ systemLogMaximum y r := Real.log_nonneg (one_le_systemMaximum hy h0 hr)

theorem systemLogMaximum_continuousOn {n : ℕ} {y : Fin (n + 1) → ℂ → ℂ}
    (hy : ∀ j, Continuous (y j)) (h0 : y 0 0 = 1) :
    ContinuousOn (systemLogMaximum y) (Ici 0) :=
  (systemMaximum_continuousOn hy).log (fun _ hr =>
    (zero_lt_one.trans_le (one_le_systemMaximum hy h0 hr)).ne')

theorem systemLogMaximum_monotoneOn {n : ℕ} {y : Fin (n + 1) → ℂ → ℂ}
    (hy : ∀ j, Continuous (y j)) (h0 : y 0 0 = 1) :
    MonotoneOn (systemLogMaximum y) (Ici 0) := by
  intro r hr s hs hrs
  exact Real.log_le_log (zero_lt_one.trans_le (one_le_systemMaximum hy h0 hr))
    (systemMaximum_monotoneOn hy hr hs hrs)

theorem systemLogMaximum_le_sum_posLog {n : ℕ} (y : Fin (n + 1) → ℂ → ℂ) (r : ℝ) :
    systemLogMaximum y r ≤ ∑ j, Real.posLog (maximumModulus (y j) r) := by
  obtain ⟨j, hj⟩ := systemMaximum_attained y r
  unfold systemLogMaximum
  rw [hj]
  exact (le_max_right 0 _).trans (Finset.single_le_sum
    (fun i _ => @Real.posLog_nonneg (maximumModulus (y i) r))
    (Finset.mem_univ j))

/-- The hypothesis needed to apply `lem:envelope` follows from the
literal component orders, as in Step 2 of `prop:small-order`. -/
theorem systemLogMaximum_isLittleO {n : ℕ} {y : Fin (n + 1) → ℂ → ℂ}
    (hy : ∀ j, Continuous (y j)) (h0 : y 0 0 = 1) {α : ℝ}
    (horder : ∀ j, entireOrder (y j) < (α : EReal)) :
    systemLogMaximum y =o[atTop] (fun r => r ^ α) := by
  have hs : (fun r => ∑ j, Real.posLog (maximumModulus (y j) r)) =o[atTop] (fun r => r ^ α) := by
    convert! (IsLittleO.sum (s := Finset.univ)
      (fun j _ => entireOrder_posLog_isLittleO (horder j))) using 1
    funext r
    simp only [Finset.sum_apply]
  apply IsBigO.trans_isLittleO (g := fun r => ∑ j, Real.posLog (maximumModulus (y j) r)) ?_ hs
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  rw [Real.norm_of_nonneg (systemLogMaximum_nonneg hy h0 hr),
    Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => Real.posLog_nonneg)), one_mul]
  exact systemLogMaximum_le_sum_posLog y r

/-- The initial first derivative forces H_y(r)>=log r, as used after
LaTeX `eq:translated-count`. -/
theorem log_le_systemLogMaximum_of_deriv_one {n : ℕ} {y : Fin (n + 1) → ℂ → ℂ}
    (hy : ∀ j, Differentiable ℂ (y j)) {j : Fin (n + 1)} (hj : deriv (y j) 0 = 1)
    {r : ℝ} (hr : 0 < r) : Real.log r ≤ systemLogMaximum y r := by
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1 hr
    (hy j).diffContOnCl (fun z hz => norm_le_maximumModulus (hy j).continuous
      (sphere_subset_closedBall hz))
  have hratio : 1 ≤ maximumModulus (y j) r / r := by
    simpa only [iteratedDeriv_one, hj, norm_one, Nat.factorial_one, Nat.cast_one,
      one_mul, pow_one] using hc
  have hM : r ≤ maximumModulus (y j) r := by
    simpa only [one_mul] using (le_div_iff₀ hr).mp hratio
  have hb : r ≤ systemMaximum y r := hM.trans (maximumModulus_le_systemMaximum y r j)
  exact Real.log_le_log hr hb

theorem systemLogMaximum_eventually_pos_of_deriv_one {n : ℕ}
    {y : Fin (n + 1) → ℂ → ℂ} (hy : ∀ j, Differentiable ℂ (y j))
    {j : Fin (n + 1)} (hj : deriv (y j) 0 = 1) :
    ∀ᶠ r : ℝ in atTop, 0 < systemLogMaximum y r := by
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
  have hr0 : 0 < r := by linarith
  exact (Real.log_pos (by linarith)).trans_le (log_le_systemLogMaximum_of_deriv_one hy hj hr0)

end ModifiedCartan
#print axioms ModifiedCartan.systemLogMaximum_isLittleO
