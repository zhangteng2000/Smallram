import ModifiedCartan.EntireOrder
import ModifiedCartan.EntireTaylorBounds
import ModifiedCartan.LocalJetDeterminantBounds
import FewInflection.TaylorLimits
import Mathlib.Data.Finset.Lattice.Fold

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem finite_entireOrder_exists_exponent_lt_one {n : ℕ}
    {y : Fin (n + 1) → ℂ → ℂ} (horder : ∀ j, entireOrder (y j) < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∀ j, entireOrder (y j) < (σ : EReal) := by
  choose β hβ hβ1 using fun j => EReal.exists_between_coe_real (horder j)
  let S : ℝ := Finset.univ.sup' Finset.univ_nonempty β
  have hS : S < 1 := by
    dsimp only [S]
    rw [Finset.sup'_lt_iff]
    intro j _
    exact_mod_cast hβ1 j
  refine ⟨max (1 / 2) S, lt_of_lt_of_le (by norm_num) (le_max_left _ _),
    max_lt (by norm_num) hS, ?_⟩
  intro j
  have hj : β j ≤ max (1 / 2) S :=
    (Finset.le_sup' β (Finset.mem_univ j)).trans (le_max_right _ _)
  exact (hβ j).trans_le (by exact_mod_cast hj)

theorem finite_entireOrder_common_power_bound {n : ℕ}
    {y : Fin (n + 1) → ℂ → ℂ} (hy : ∀ j, Continuous (y j)) {σ : ℝ}
    (horder : ∀ j, entireOrder (y j) < (σ : EReal)) :
    ∃ C : ℝ, 0 < C ∧ ∀ j r, 1 ≤ r → Real.posLog (maximumModulus (y j) r) ≤ C * r ^ σ := by
  choose C hC hb using fun j => entireOrder_exists_posLog_power_bound (hy j) (horder j)
  have hle (j : Fin (n + 1)) : C j ≤ ∑ i, C i :=
    Finset.single_le_sum (fun i _ => (hC i).le) (Finset.mem_univ j)
  refine ⟨∑ j, C j, (hC 0).trans_le (hle 0), ?_⟩
  intro j r hr
  exact (hb j r hr).trans (mul_le_mul_of_nonneg_right (hle j)
    (Real.rpow_nonneg (zero_le_one.trans hr) σ))

theorem taylor_jet_bound_from_common_power_bound {n : ℕ}
    {y : Fin (n + 1) → ℂ → ℂ} (hy : ∀ j, Differentiable ℂ (y j))
    {σ C r : ℝ} (hC : 0 < C)
    (hb : ∀ j t, 1 ≤ t → Real.posLog (maximumModulus (y j) t) ≤ C * t ^ σ)
    (hr : 1 ≤ r) (N : ℕ) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) r)
    (j : Fin (n + 1)) {k : ℕ} (hk : k ≤ n + 1) :
    ‖iteratedDeriv k (fun w => (FewInflection.taylorPolynomial (y j) 0 N).eval w) z‖ ≤
      (2 * ((n + 1).factorial : ℝ)) * Real.exp ((C * (4 : ℝ) ^ σ) * r ^ σ) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hf : (k.factorial : ℝ) ≤ (n + 1).factorial := by exact_mod_cast Nat.factorial_le hk
  have hM : maximumModulus (y j) (4 * r) ≤ Real.exp ((C * (4 : ℝ) ^ σ) * r ^ σ) := by
    apply Real.le_exp_of_log_le
    have hh := (le_max_right 0 (Real.log (maximumModulus (y j) (4 * r)))).trans
      (hb j (4 * r) (by linarith))
    simpa only [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hr0.le, mul_assoc] using hh
  calc
    _ ≤ (k.factorial : ℝ) * (2 * maximumModulus (y j) (4 * r)) / r ^ k :=
      entire_taylorPolynomial_iteratedDeriv_le (hy j) hr0 N k hz
    _ ≤ (k.factorial : ℝ) * (2 * maximumModulus (y j) (4 * r)) :=
      div_le_self (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num)
        (maximumModulus_nonneg (hy j).continuous (by positivity)))) (one_le_pow₀ hr)
    _ ≤ ((n + 1).factorial : ℝ) * (2 * Real.exp ((C * (4 : ℝ) ^ σ) * r ^ σ)) := by
      gcongr
      exact mul_nonneg (by norm_num) (maximumModulus_nonneg (hy j).continuous (by positivity))
    _ = _ := by ring

/-- Uniform Wronskian growth in LaTeX `eq:WN-growth`. The coefficient
C is obtained from the literal component orders and is independent of N. -/
theorem entire_taylorWronskian_posLog_bound {n : ℕ}
    {y : Fin (n + 1) → ℂ → ℂ} (hy : ∀ j, Differentiable ℂ (y j))
    {σ : ℝ} (hσ : 0 ≤ σ) (horder : ∀ j, entireOrder (y j) < (σ : EReal)) :
    ∃ D : ℝ, 0 < D ∧ ∀ N r, 1 ≤ r → ∀ z ∈ closedBall (0 : ℂ) r,
      Real.posLog ‖FewInflection.wronskian n
        (fun j w => (FewInflection.taylorPolynomial (y j) 0 N).eval w) z‖ ≤ D * r ^ σ := by
  obtain ⟨C, hC, hb⟩ := finite_entireOrder_common_power_bound (fun j => (hy j).continuous) horder
  let F : ℝ := (n + 1).factorial
  let A : ℝ := 2 * F
  let B : ℝ := C * (4 : ℝ) ^ σ
  let K : ℝ := Real.posLog F + (n + 1 : ℝ) * Real.posLog A
  have hB : 0 < B := mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _)
  have hK : 0 ≤ K := add_nonneg Real.posLog_nonneg (mul_nonneg (by positivity) Real.posLog_nonneg)
  refine ⟨K + (n + 1 : ℝ) * B + 1, by positivity, ?_⟩
  intro N r hr z hz
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hpow : 1 ≤ r ^ σ := Real.one_le_rpow hr hσ
  have he : 0 ≤ B * r ^ σ := mul_nonneg hB.le (Real.rpow_nonneg hr0.le _)
  have hW := norm_wronskian_le_of_jet_bound
    (fun j w => (FewInflection.taylorPolynomial (y j) 0 N).eval w) z
    (by dsimp [A, F]; positivity : 0 ≤ A * Real.exp (B * r ^ σ))
    (fun j k hk => taylor_jet_bound_from_common_power_bound hy hC hb hr N hz j hk)
  have hexp : Real.posLog (Real.exp (B * r ^ σ)) = B * r ^ σ := by
    rw [Real.posLog_apply, Real.log_exp, max_eq_right he]
  have hlog : Real.posLog ‖FewInflection.wronskian n
      (fun j w => (FewInflection.taylorPolynomial (y j) 0 N).eval w) z‖ ≤
      Real.posLog F + (n + 1 : ℝ) * (Real.posLog A + B * r ^ σ) := by
    calc
      _ ≤ Real.posLog (F * (A * Real.exp (B * r ^ σ)) ^ (n + 1)) :=
        Real.posLog_le_posLog (norm_nonneg _) hW
      _ ≤ Real.posLog F + Real.posLog ((A * Real.exp (B * r ^ σ)) ^ (n + 1)) := Real.posLog_mul
      _ = Real.posLog F + (n + 1 : ℝ) * Real.posLog (A * Real.exp (B * r ^ σ)) := by
        rw [Real.posLog_pow, Nat.cast_add, Nat.cast_one]
      _ ≤ _ := by
        apply add_le_add le_rfl (mul_le_mul_of_nonneg_left _ (by positivity))
        have hh := @Real.posLog_mul A (Real.exp (B * r ^ σ))
        rwa [hexp] at hh
  have hKmul : K ≤ K * r ^ σ := le_mul_of_one_le_right hK hpow
  exact hlog.trans (by dsimp [K] at hKmul ⊢; nlinarith)

/-- The same bound for the actual entire Wronskian follows from the
already proved convergence of Taylor jets and continuity of determinant. -/
theorem entire_wronskian_posLog_bound {n : ℕ}
    {y : Fin (n + 1) → ℂ → ℂ} (hy : ∀ j, Differentiable ℂ (y j))
    {σ : ℝ} (hσ : 0 ≤ σ) (horder : ∀ j, entireOrder (y j) < (σ : EReal)) :
    ∃ D : ℝ, 0 < D ∧ ∀ r, 1 ≤ r → ∀ z ∈ closedBall (0 : ℂ) r,
      Real.posLog ‖FewInflection.wronskian n y z‖ ≤ D * r ^ σ := by
  obtain ⟨D, hD, hb⟩ := entire_taylorWronskian_posLog_bound hy hσ horder
  refine ⟨D, hD, ?_⟩
  intro r hr z hz
  have ht := (FewInflection.tendsto_taylorPolynomial_wronskian_of_entire hy 0 z).norm
  exact le_of_tendsto (Real.continuous_posLog.continuousAt.tendsto.comp ht)
    (Eventually.of_forall (fun N => hb N r hr z hz))

end ModifiedCartan
#print axioms ModifiedCartan.entire_taylorWronskian_posLog_bound
#print axioms ModifiedCartan.entire_wronskian_posLog_bound
