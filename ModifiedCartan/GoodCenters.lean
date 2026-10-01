import ModifiedCartan.ReplacementSubsequence
import ModifiedCartan.AnalyticWeakGradient

open scoped Topology ENNReal BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem polynomial_eval_ne_zero_ae (P : Polynomial ℂ) (hP : P ≠ 0) :
    ∀ᵐ z : ℂ, P.eval z ≠ 0 := by
  have hn : ∃ z ∈ (univ : Set ℂ), P.eval z ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hP
    apply Polynomial.funext
    intro z
    simpa only [Polynomial.eval_zero] using hh z (mem_univ z)
  simpa only [Measure.restrict_univ] using analytic_ae_ne_zero isOpen_univ isPreconnected_univ
    (AnalyticOnNhd.eval_polynomial P) hn

theorem reciprocalDistanceSum_split_at {M : ℕ} (a : Fin M → ℂ) (η : ℝ)
    (hsep : ∀ i, ‖a i‖ ≠ η) (z : ℂ) :
    reciprocalDistanceSum Finset.univ a z =
      reciprocalDistanceSum (Finset.univ.filter (fun i => ‖a i‖ < η)) a z +
      reciprocalDistanceSum (Finset.univ.filter (fun i => η < ‖a i‖)) a z := by
  have he (i : Fin M) : ¬ ‖a i‖ < η ↔ η < ‖a i‖ := by
    constructor
    · intro hi
      exact lt_of_le_of_ne (le_of_not_gt hi) (hsep i).symm
    · exact fun hi => not_lt.mpr hi.le
  simpa only [reciprocalDistanceSum, he] using
    (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => ‖a i‖ < η)
      (fun i => ‖z - a i‖⁻¹)).symm

/-- LaTeX `eq:good-centers`, with an explicit eventual bound for the
full reciprocal sum over the actual Wronskian roots with multiplicity. -/
theorem PolynomialReplacementData.exists_good_centers {n : ℕ} {f : Curve n}
    {t s : ℕ → ℝ} {C A L : ℝ} {H : ℕ → ℂ → ℂ}
    {p : ℕ → Index n → Polynomial ℂ}
    {a : (ν : ℕ) → Fin (FewInflection.polynomialWronskian (p ν)).natDegree → ℂ}
    {η : ℕ → ℝ} (h : PolynomialReplacementData f t s C A L H p a η) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ E : Set ℂ,
      E ⊆ ball (0 : ℂ) 2 \ {0} ∧ (∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 2), z ∈ E) ∧
      ∀ z ∈ E,
        (∀ ν, (FewInflection.polynomialWronskian (p (ns ν))).eval z ≠ 0) ∧
        Tendsto (fun ν => Real.log ‖(FewInflection.polynomialWronskian (p (ns ν))).eval z‖ /
          s (ns ν)) atTop (𝓝 0) ∧
        ∃ B : ℝ, 0 < B ∧ ∀ᶠ ν in atTop,
          reciprocalDistanceSum Finset.univ (a (ns ν)) z / s (ns ν) ≤ B := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h.wronskian_nonzero
  let τ : ℕ → ℕ := fun ν => ν + N
  have hτ : StrictMono τ := fun _ _ h => Nat.add_lt_add_right h N
  obtain ⟨ι, hι, hlog⟩ := (h.log_wronskian.comp_tendsto hτ.tendsto_atTop).exists_seq_tendsto_ae
    one_ne_zero isOpen_ball
  obtain ⟨σ, hσ, hinner⟩ :=
    (((h.inner_sum_measure.comp hτ.tendsto_atTop).comp hι.tendsto_atTop).exists_seq_tendsto_ae isOpen_ball)
  let ns := τ ∘ ι ∘ σ
  have hns : StrictMono ns := hτ.comp (hι.comp hσ)
  have hzeros : ∀ᵐ z : ℂ, ∀ ν, (FewInflection.polynomialWronskian (p (ns ν))).eval z ≠ 0 := by
    apply ae_all_iff.mpr
    intro ν
    apply polynomial_eval_ne_zero_ae
    exact hN _ (by dsimp only [ns, τ, Function.comp_def]; omega)
  have hnonzero : ∀ᵐ z : ℂ, z ≠ 0 := by
    simpa only [Polynomial.eval_X] using polynomial_eval_ne_zero_ae Polynomial.X (by simp)
  let E : Set ℂ := {z | z ∈ ball (0 : ℂ) 2 ∧ z ≠ 0 ∧
    (∀ ν, (FewInflection.polynomialWronskian (p (ns ν))).eval z ≠ 0) ∧
    Tendsto (fun ν => Real.log ‖(FewInflection.polynomialWronskian (p (ns ν))).eval z‖ /
      s (ns ν)) atTop (𝓝 0) ∧
    Tendsto (fun ν => reciprocalDistanceSum
      (Finset.univ.filter (fun i => ‖a (ns ν) i‖ < η (ns ν))) (a (ns ν)) z / s (ns ν)) atTop (𝓝 0)}
  refine ⟨ns, hns, E, ?_, ?_, ?_⟩
  · exact fun z hz => ⟨hz.1, hz.2.1⟩
  · filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hnonzero,
      ae_restrict_of_ae hzeros,
      hlog.filter_mono (ae_mono (Measure.restrict_mono_set _
        (ball_subset_ball (by norm_num : (2 : ℝ) ≤ 4)))),
      hinner.filter_mono (ae_mono (Measure.restrict_mono_set _
        (ball_subset_ball (by norm_num : (2 : ℝ) ≤ 6))))] with z hz hz0 hzW hzl hzi
    exact ⟨hz, hz0, hzW, hzl.comp hσ.tendsto_atTop, hzi⟩
  · intro z hz
    refine ⟨hz.2.2.1, hz.2.2.2.1, max (((n + 1) * (L + 1)) / 2) 0 + 1, by positivity, ?_⟩
    filter_upwards [hz.2.2.2.2.eventually (gt_mem_nhds zero_lt_one),
      hns.tendsto_atTop.eventually h.outer_sum] with ν hν hout
    rw [reciprocalDistanceSum_split_at (a (ns ν)) (η (ns ν))
      (h.separating_radii (ns ν)).2.2.1 z, add_div]
    have hb := hout z ((ball_subset_ball (by norm_num : (2 : ℝ) ≤ 6)) hz.1)
    have hmax := le_max_left (((n + 1) * (L + 1)) / 2) 0
    linarith

end ModifiedCartan
#print axioms ModifiedCartan.PolynomialReplacementData.exists_good_centers
