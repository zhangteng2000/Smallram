import ModifiedCartan.LocalPolynomialApproximation
import ModifiedCartan.MonicQuotientComparison

open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan.Paper

/-- LaTeX `eq:cramercomparison`. The polynomials and their nonzero Wronskians
are constructed from the manuscript's original hypotheses. The comparison
is for the actual fundamental coefficients, with no approximation assumption. -/
theorem eq_cramercomparison (n : ℕ) (C : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∃ L : ℝ, 0 < L ∧
      ∀ (g : ℕ → Index n → ℂ → ℂ) (s : ℕ → ℝ) (P : ℕ → Polynomial ℂ),
        Tendsto s atTop atTop →
        (∀ ν j, AnalyticOnNhd ℂ (g ν j) (ball 0 32)) →
        (∀ ν z, z ∈ ball (0 : ℂ) 32 →
          euclideanNorm (fun j => g ν j z) ≤ Real.exp (C * s ν)) →
        (∀ ν, (P ν).Monic) →
        (∀ ν z, z ∈ ball (0 : ℂ) 32 → FewInflection.wronskian n (g ν) z = (P ν).eval z) →
        Tendsto (fun ν => ((P ν).natDegree : ℝ) / s ν) atTop (𝓝 0) →
        ∃ p : ℕ → Index n → Polynomial ℂ,
          (∀ᶠ ν in atTop,
            ((FewInflection.polynomialWronskian (p ν)).natDegree : ℝ) ≤ L * s ν ∧
            FewInflection.polynomialWronskian (p ν) ≠ 0 ∧
            ∀ z ∈ closedBall (0 : ℂ) 12,
              ‖(FewInflection.polynomialWronskian (p ν)).eval z - (P ν).eval z‖ ≤
                Real.exp (-B * s ν)) ∧
          ∀ i, LocalMeasureConvergence (ball (0 : ℂ) 12)
            (fun ν z => FewInflection.fundamentalCoefficients n (fun j w => (p ν j).eval w) z i -
              FewInflection.fundamentalCoefficients n (g ν) z i) (fun _ => 0) := by
  obtain ⟨C2, hC2, hnumbound⟩ := exists_fundamentalNumerator_exponential_bound n C
  let B : ℝ := C2 + 3
  have hB : 0 < B := by dsimp [B]; linarith
  have hB1 : 1 < B := by dsimp [B]; linarith
  have hBC : C2 + 2 < B := by dsimp [B]; linarith
  obtain ⟨L, hL, happrox⟩ := eq_wronskiapprox n C B hB
  refine ⟨B, hB, L, hL, ?_⟩
  intro g s P hs hg hnorm hP hW hm
  obtain ⟨p, hp⟩ := happrox g s P hs hg hnorm hP hW
  have hn := hnumbound g s hs hg hnorm
  refine ⟨p, ?_, ?_⟩
  · filter_upwards [hp] with ν hν
    exact ⟨hν.1, hν.2.1, hν.2.2.1⟩
  · intro i
    have hden : ∀ᶠ ν in atTop, ∀ z ∈ ball (0 : ℂ) 12,
        ‖(FewInflection.polynomialWronskian (p ν)).eval z - (P ν).eval z‖ ≤
          Real.exp (-B * s ν) := by
      filter_upwards [hp] with ν hν z hz
      exact hν.2.2.1 z (ball_subset_closedBall hz)
    have hnum : ∀ᶠ ν in atTop, ∀ z ∈ ball (0 : ℂ) 12,
        ‖FewInflection.fundamentalNumerator n (fun j w => (p ν j).eval w) i z -
          FewInflection.fundamentalNumerator n (g ν) i z‖ ≤ Real.exp (-B * s ν) := by
      filter_upwards [hp] with ν hν z hz
      exact hν.2.2.2 i z (ball_subset_closedBall hz)
    have hv : ∀ᶠ ν in atTop, ∀ z ∈ ball (0 : ℂ) 12,
        ‖FewInflection.fundamentalNumerator n (g ν) i z‖ ≤ Real.exp (C2 * s ν) := by
      filter_upwards [hn] with ν hν z hz
      exact hν i z ((closedBall_subset_closedBall (by norm_num : (12 : ℝ) ≤ 16))
        (ball_subset_closedBall hz))
    have hconv := monic_quotient_comparison_localMeasure P hP hs hm hB1 hBC hden hnum hv
    intro K hK hKU
    apply TendstoInMeasure.congr _ EventuallyEq.rfl (hconv K hK hKU)
    intro ν
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    have hz32 : z ∈ ball (0 : ℂ) 32 := (ball_subset_ball (by norm_num : (12 : ℝ) ≤ 32)) (hKU hz)
    simp only [FewInflection.fundamentalCoefficients_eq_quotient,
      polynomialWronskian_eval_eq_wronskian, hW ν z hz32]

end ModifiedCartan.Paper
