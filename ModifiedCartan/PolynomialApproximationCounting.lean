import ModifiedCartan.LocalPolynomialApproximation
import FewInflection.Nevanlinna.CountingBounds

open scoped Topology BigOperators
open Filter Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem norm_polynomial_coeff_le_unit_circle (P : Polynomial ℂ) {M : ℝ}
    (hM : ∀ z ∈ sphere (0 : ℂ) 1, ‖P.eval z‖ ≤ M) (k : ℕ) : ‖P.coeff k‖ ≤ M := by
  have he := norm_taylor_coefficient_le (by norm_num : (0 : ℝ) < 1)
    P.differentiable.differentiableOn hM k
  have hcoeff : (k.factorial : ℂ)⁻¹ * iteratedDeriv k (fun z => P.eval z) 0 = P.coeff k := by
    rw [FewInflection.polynomial_coeff_eq_jet]
    ring
  simpa only [hcoeff, one_pow, div_one] using he

noncomputable def polynomialDiskGrowthFactor (m : ℕ) : ℝ := (m + 1) * 12 ^ m

theorem one_le_polynomialDiskGrowthFactor (m : ℕ) : 1 ≤ polynomialDiskGrowthFactor m := by
  have hp : (1 : ℝ) ≤ 12 ^ m := one_le_pow₀ (by norm_num)
  dsimp [polynomialDiskGrowthFactor]
  nlinarith

theorem log_polynomialDiskGrowthFactor_le (m : ℕ) :
    Real.log (polynomialDiskGrowthFactor m) ≤ (1 + Real.log 12) * m := by
  rw [polynomialDiskGrowthFactor, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < m + 1 by positivity)
  linarith

theorem norm_polynomial_on_disk_le (P : Polynomial ℂ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ sphere (0 : ℂ) 1, ‖P.eval z‖ ≤ M)
    {z : ℂ} (hz : z ∈ closedBall 0 12) :
    ‖P.eval z‖ ≤ polynomialDiskGrowthFactor P.natDegree * M := by
  have hz' : ‖z‖ ≤ 12 := by simpa only [mem_closedBall, dist_zero_right] using hz
  rw [Polynomial.eval_eq_sum_range]
  calc
    _ ≤ ∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k * z ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range (P.natDegree + 1), M * (12 : ℝ) ^ P.natDegree := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' : k ≤ P.natDegree := by have := Finset.mem_range.mp hk; omega
      rw [norm_mul, norm_pow]
      calc
        _ ≤ M * (12 : ℝ) ^ k := by
          gcongr
          exact norm_polynomial_coeff_le_unit_circle P hM k
        _ ≤ M * (12 : ℝ) ^ P.natDegree := by
          gcongr
          norm_num
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, polynomialDiskGrowthFactor,
        Nat.cast_add, Nat.cast_one]
      ring

/-- A maximizing point supplies the relative growth bound needed for a
specialized Jensen proof of the o(s) interior root count in `prop:localcompact`. -/
theorem exists_monic_polynomial_growth_center (P : Polynomial ℂ) (hP : P.Monic) :
    ∃ a : ℂ, a ∈ closedBall 0 1 ∧ 1 ≤ ‖P.eval a‖ ∧
      ∀ z ∈ closedBall (0 : ℂ) 12,
        ‖P.eval z‖ ≤ polynomialDiskGrowthFactor P.natDegree * ‖P.eval a‖ := by
  obtain ⟨a, ha, hmax⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_isMaxOn
    ⟨0, mem_closedBall_self (by norm_num)⟩ P.continuous.norm.continuousOn
  have hbound : ∀ z ∈ sphere (0 : ℂ) 1, ‖P.eval z‖ ≤ ‖P.eval a‖ :=
    fun z hz => hmax (sphere_subset_closedBall hz)
  have hMa : 1 ≤ ‖P.eval a‖ := by
    by_contra h
    exact monic_polynomial_not_uniformly_small P hP (lt_of_not_ge h) hbound
  refine ⟨a, ha, hMa, ?_⟩
  intro z hz
  exact norm_polynomial_on_disk_le P (norm_nonneg _) hbound hz

theorem polynomial_approximation_growth_center (P R : Polynomial ℂ) (hP : P.Monic)
    (herr : ∀ z ∈ closedBall (0 : ℂ) 12, ‖R.eval z - P.eval z‖ ≤ 1 / 2) :
    ∃ a : ℂ, a ∈ closedBall 0 1 ∧ 1 ≤ ‖P.eval a‖ ∧
      ‖P.eval a‖ / 2 ≤ ‖R.eval a‖ ∧
      ∀ z ∈ closedBall (0 : ℂ) 12,
        ‖R.eval z‖ ≤ 2 * polynomialDiskGrowthFactor P.natDegree * ‖P.eval a‖ := by
  obtain ⟨a, ha, hMa, hgrowth⟩ := exists_monic_polynomial_growth_center P hP
  have ha12 : a ∈ closedBall (0 : ℂ) 12 :=
    closedBall_subset_closedBall (by norm_num) ha
  have hG := one_le_polynomialDiskGrowthFactor P.natDegree
  refine ⟨a, ha, hMa, ?_, ?_⟩
  · have ht := norm_sub_norm_le (P.eval a) (R.eval a)
    rw [norm_sub_rev] at ht
    have he := herr a ha12
    linarith
  · intro z hz
    have ht := norm_sub_norm_le (R.eval z) (P.eval z)
    have he := herr z hz
    have hg := hgrowth z hz
    have hGM : 1 ≤ polynomialDiskGrowthFactor P.natDegree * ‖P.eval a‖ := by nlinarith
    nlinarith

noncomputable def localRootCountBound (m : ℕ) : ℝ :=
  (Real.log 4 + (1 + Real.log 12) * m) / Real.log (10 / 9)

theorem polynomial_approximation_centered_divisor_count_le (P R : Polynomial ℂ)
    (hP : P.Monic)
    (herr : ∀ z ∈ closedBall (0 : ℂ) 12, ‖R.eval z - P.eval z‖ ≤ 1 / 2) :
    ∃ a : ℂ, a ∈ closedBall 0 1 ∧
      (∑ᶠ z : ℂ, ((MeromorphicOn.divisor (fun w => R.eval w)
        (closedBall a 9)) z : ℝ)) ≤ localRootCountBound P.natDegree := by
  obtain ⟨a, ha, hMa, hRa, hbound⟩ := polynomial_approximation_growth_center P R hP herr
  have hG := one_le_polynomialDiskGrowthFactor P.natDegree
  have hM : 1 ≤ 2 * polynomialDiskGrowthFactor P.natDegree * ‖P.eval a‖ := by nlinarith
  have hRpos : 0 < ‖R.eval a‖ := by linarith
  have ha' : ‖a‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using ha
  have hsub : closedBall a (10 : ℝ) ⊆ closedBall 0 12 := by
    apply closedBall_subset_closedBall'
    simp only [dist_zero_right]
    linarith
  have hhol : AnalyticOnNhd ℂ (fun z => R.eval z) (closedBall a |(10 : ℝ)|) :=
    fun z _ => AnalyticOnNhd.eval_polynomial R z (mem_univ z)
  have hc := FewInflection.analytic_divisor_count_le
    (r := (9 : ℝ)) (R := (10 : ℝ)) (by norm_num) (by norm_num) hM hhol
    (norm_pos_iff.mp hRpos) (fun z hz => hbound z (hsub (sphere_subset_closedBall (by
      simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 10)] using hz))))
  refine ⟨a, ha, ?_⟩
  have habs : |(9 : ℝ)| = 9 := by norm_num
  rw [habs] at hc
  apply hc.trans
  have hratio : 2 * polynomialDiskGrowthFactor P.natDegree * ‖P.eval a‖ / ‖R.eval a‖ ≤
      4 * polynomialDiskGrowthFactor P.natDegree := by
    apply (div_le_iff₀ hRpos).mpr
    nlinarith
  have hratioPos : 0 < 2 * polynomialDiskGrowthFactor P.natDegree * ‖P.eval a‖ / ‖R.eval a‖ :=
    div_pos (by linarith) hRpos
  have hlog := Real.log_le_log hratioPos hratio
  rw [Real.log_mul (by norm_num) (by linarith : polynomialDiskGrowthFactor P.natDegree ≠ 0)] at hlog
  have hgrowth := log_polynomialDiskGrowthFactor_le P.natDegree
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 10 / 9))
  linarith

theorem analytic_divisor_count_mono {f : ℂ → ℂ} {K L : Set ℂ}
    (hK : IsCompact K) (hL : IsCompact L) (hsub : K ⊆ L)
    (hf : AnalyticOnNhd ℂ f L) :
    (∑ᶠ z : ℂ, ((MeromorphicOn.divisor f K) z : ℝ)) ≤
      ∑ᶠ z : ℂ, ((MeromorphicOn.divisor f L) z : ℝ) := by
  have hfK : AnalyticOnNhd ℂ f K := fun z hz => hf z (hsub hz)
  refine finsum_le_finsum' ?_ ?_ (fun z => ?_)
  · exact ((MeromorphicOn.divisor f K).finiteSupport hK).subset
      (fun _ _ => by simp_all)
  · exact ((MeromorphicOn.divisor f L).finiteSupport hL).subset
      (fun _ _ => by simp_all)
  · by_cases hz : z ∈ K
    · rw [hfK.meromorphicOn.divisor_apply hz, hf.meromorphicOn.divisor_apply (hsub hz)]
    · simp only [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz, Int.cast_zero]
      exact Int.cast_nonneg (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf z)

/-- Interior root-count input for `prop:localcompact`, proved by Jensen instead
of the manuscript's stronger Rouché equality `eq:rouche-root-count`. -/
theorem polynomial_approximation_divisor_count_le (P R : Polynomial ℂ)
    (hP : P.Monic)
    (herr : ∀ z ∈ closedBall (0 : ℂ) 12, ‖R.eval z - P.eval z‖ ≤ 1 / 2) :
    (∑ᶠ z : ℂ, ((MeromorphicOn.divisor (fun w => R.eval w)
      (closedBall 0 8)) z : ℝ)) ≤ localRootCountBound P.natDegree := by
  obtain ⟨a, ha, hcount⟩ := polynomial_approximation_centered_divisor_count_le P R hP herr
  apply le_trans (analytic_divisor_count_mono (isCompact_closedBall 0 8)
    (isCompact_closedBall a 9) ?_ (fun z _ => AnalyticOnNhd.eval_polynomial R z (mem_univ z))) hcount
  apply closedBall_subset_closedBall'
  have ha' : ‖a‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using ha
  simp only [dist_zero_left]
  linarith

end ModifiedCartan

#print axioms ModifiedCartan.exists_monic_polynomial_growth_center
#print axioms ModifiedCartan.polynomial_approximation_divisor_count_le
