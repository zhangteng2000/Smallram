import ModifiedCartan.NormalizedFundamentalODE

open scoped Topology BigOperators NNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- A specialized monic root bound for the weak-gradient equation in
`prop:homogeneity`, proved directly from the equation. -/
theorem norm_le_of_monic_equation {n : ℕ} (a : Index n → ℂ) {z : ℂ}
    (hz : z ^ (n + 1) + ∑ i : Index n, a i * z ^ i.val = 0) :
    ‖z‖ ≤ max 1 (∑ i : Index n, ‖a i‖) := by
  by_cases hsmall : ‖z‖ ≤ 1
  · exact hsmall.trans (le_max_left _ _)
  have hlarge : 1 < ‖z‖ := lt_of_not_ge hsmall
  have hpos : 0 < ‖z‖ ^ n := pow_pos (zero_lt_one.trans hlarge) _
  have hnorm : ‖z‖ ^ (n + 1) = ‖∑ i : Index n, a i * z ^ i.val‖ := by
    have he : z ^ (n + 1) = -(∑ i : Index n, a i * z ^ i.val) := eq_neg_of_add_eq_zero_left hz
    simpa only [norm_pow, norm_neg] using congrArg norm he
  have hle : ‖z‖ ^ n * ‖z‖ ≤ (∑ i : Index n, ‖a i‖) * ‖z‖ ^ n := by
    rw [← pow_succ, hnorm, Finset.sum_mul]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlarge.le (Nat.le_of_lt_succ i.isLt)) (norm_nonneg _)
  have hzle : ‖z‖ ≤ ∑ i : Index n, ‖a i‖ :=
    (mul_le_mul_iff_right₀ hpos).mp (by simpa only [mul_comm] using hle)
  exact hzle.trans (le_max_right _ _)

theorem monic_equation_gradient_bound_on_compact {n : ℕ} {U K : Set ℂ}
    (hK : IsCompact K) (hKU : K ⊆ U) {a : Index n → ℂ → ℂ}
    (ha : ∀ i, ContinuousOn (a i) U) {g : ℂ → ℂ}
    (heq : ∀ᵐ z ∂volume.restrict U, g z ^ (n + 1) + ∑ i : Index n, a i z * g z ^ i.val = 0) :
    ∃ C : ℝ≥0, ∀ᵐ z ∂volume.restrict K, ‖g z‖ ≤ (C : ℝ) := by
  have hcont : ContinuousOn (fun z => ∑ i : Index n, ‖a i z‖) K :=
    continuousOn_finset_sum Finset.univ (fun i _ => ((ha i).mono hKU).norm)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
  let C : ℝ≥0 := ⟨max 1 M, (by positivity)⟩
  refine ⟨C, ?_⟩
  filter_upwards [heq.filter_mono (ae_mono (Measure.restrict_mono_set _ hKU)),
    ae_restrict_mem hK.measurableSet] with z hz hzK
  apply (norm_le_of_monic_equation (fun i => a i z) hz).trans
  have hm : (∑ i : Index n, ‖a i z‖) ≤ M := by
    have hh := hM z hzK
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg (a i z)))] using hh
  exact max_le_max_left 1 hm

end ModifiedCartan
#print axioms ModifiedCartan.norm_le_of_monic_equation
#print axioms ModifiedCartan.monic_equation_gradient_bound_on_compact
