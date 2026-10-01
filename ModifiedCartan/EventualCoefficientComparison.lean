import ModifiedCartan.LocalCompactness
import ModifiedCartan.LocalCramerComparison
import ModifiedCartan.MeasureLimitTransfer

open scoped Topology BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The numerator bound is unchanged by deleting a finite initial segment. -/
theorem exists_fundamentalNumerator_exponential_bound_eventual (n : ℕ) (C : ℝ) :
    ∃ C2 : ℝ, 0 < C2 ∧
      ∀ (g : ℕ → Index n → ℂ → ℂ) (s : ℕ → ℝ), Tendsto s atTop atTop →
        (∀ᶠ ν in atTop,
          (∀ j, AnalyticOnNhd ℂ (g ν j) (ball 0 32)) ∧
          (∀ z ∈ ball (0 : ℂ) 32, euclideanNorm (fun j => g ν j z) ≤ Real.exp (C * s ν))) →
        ∀ᶠ ν in atTop, ∀ i z, z ∈ closedBall (0 : ℂ) 16 →
          ‖FewInflection.fundamentalNumerator n (g ν) i z‖ ≤ Real.exp (C2 * s ν) := by
  obtain ⟨C2, hC2, hb⟩ := exists_fundamentalNumerator_exponential_bound n C
  refine ⟨C2, hC2, ?_⟩
  intro g s hs hd
  obtain ⟨N, hN⟩ := eventually_atTop.mp hd
  let k : ℕ → ℕ := fun ν => max ν N
  have he : k =ᶠ[atTop] id := by
    filter_upwards [eventually_ge_atTop N] with ν hν
    exact max_eq_left hν
  have hk : Tendsto k atTop atTop := (tendsto_congr' he).mpr tendsto_id
  have hdata (ν : ℕ) := hN (k ν) (le_max_right ν N)
  have hbound := hb (fun ν => g (k ν)) (fun ν => s (k ν)) (hs.comp hk)
    (fun ν => (hdata ν).1) (fun ν => (hdata ν).2)
  filter_upwards [hbound, he] with ν hbν heν
  simpa only [heν, id_eq] using hbν

/-- LaTeX `eq:gaugecomparison` with precisely the eventual local hypotheses
supplied by the rescaled representation. -/
theorem Paper.eq_gaugecomparison_eventual {n : ℕ} (C : ℝ)
    (g : ℕ → Index n → ℂ → ℂ) (s : ℕ → ℝ) (P : ℕ → Polynomial ℂ)
    (hs : Tendsto s atTop atTop)
    (hm : Tendsto (fun ν => ((P ν).natDegree : ℝ) / s ν) atTop (𝓝 0))
    (hd : ∀ᶠ ν in atTop,
      (∀ j, AnalyticOnNhd ℂ (g ν j) (ball 0 32)) ∧ (P ν).Monic ∧
      (∀ z ∈ ball (0 : ℂ) 32, FewInflection.wronskian n (g ν) z = (P ν).eval z) ∧
      (∀ z ∈ ball (0 : ℂ) 32, euclideanNorm (fun j => g ν j z) ≤ Real.exp (C * s ν))) :
    ∀ i, LocalMeasureConvergence (ball (0 : ℂ) 4)
      (fun ν z => (canonicalCoefficient n (g ν) i z -
        FewInflection.fundamentalCoefficients n (g ν) z i) /
          (s ν : ℂ) ^ (n + 1 - i.val)) (fun _ => 0) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hd
  let k : ℕ → ℕ := fun ν => max ν N
  have he : k =ᶠ[atTop] id := by
    filter_upwards [eventually_ge_atTop N] with ν hν
    exact max_eq_left hν
  have hk : Tendsto k atTop atTop := (tendsto_congr' he).mpr tendsto_id
  have hdata (ν : ℕ) := hN (k ν) (le_max_right ν N)
  have hcomp := eq_gaugecomparison C (fun ν => g (k ν)) (fun ν => s (k ν))
    (fun ν => P (k ν)) (fun ν => (hdata ν).1) (hs.comp hk)
    (fun ν => (hdata ν).2.1) (fun ν => (hdata ν).2.2.1)
    (fun ν => (hdata ν).2.2.2) (hm.comp hk)
  intro i
  apply (hcomp i).congr_ae
  filter_upwards [he] with ν heν
  rw [heν]
  exact EventuallyEq.rfl

/-- Cramer comparison for a specified sequence of polynomial vectors.
Its hypotheses are the quantitative determinant estimates, not the desired
coefficient convergence; the final replacement construction proves them. -/
theorem cramer_comparison_of_polynomial_approximation {n : ℕ}
    (g : ℕ → Index n → ℂ → ℂ) (p : ℕ → Index n → Polynomial ℂ)
    (P : ℕ → Polynomial ℂ) (hP : ∀ ν, (P ν).Monic)
    {s : ℕ → ℝ} (hs : Tendsto s atTop atTop)
    (hm : Tendsto (fun ν => ((P ν).natDegree : ℝ) / s ν) atTop (𝓝 0))
    {B C2 : ℝ} (hB : 1 < B) (hBC : C2 + 2 < B)
    (hW : ∀ᶠ ν in atTop, ∀ z ∈ ball (0 : ℂ) 12,
      FewInflection.wronskian n (g ν) z = (P ν).eval z)
    (hd : ∀ᶠ ν in atTop, ∀ z ∈ ball (0 : ℂ) 12,
      ‖(FewInflection.polynomialWronskian (p ν)).eval z - (P ν).eval z‖ ≤ Real.exp (-B * s ν))
    (hn : ∀ᶠ ν in atTop, ∀ i z, z ∈ ball (0 : ℂ) 12 →
      ‖FewInflection.fundamentalNumerator n (fun j w => (p ν j).eval w) i z -
        FewInflection.fundamentalNumerator n (g ν) i z‖ ≤ Real.exp (-B * s ν))
    (hv : ∀ᶠ ν in atTop, ∀ i z, z ∈ ball (0 : ℂ) 12 →
      ‖FewInflection.fundamentalNumerator n (g ν) i z‖ ≤ Real.exp (C2 * s ν)) :
    ∀ i, LocalMeasureConvergence (ball (0 : ℂ) 12)
      (fun ν z => FewInflection.fundamentalCoefficients n (fun j w => (p ν j).eval w) z i -
        FewInflection.fundamentalCoefficients n (g ν) z i) (fun _ => 0) := by
  intro i
  have hn' := hn.mono (fun _ h => h i)
  have hv' := hv.mono (fun _ h => h i)
  have hconv := monic_quotient_comparison_localMeasure P hP hs hm hB hBC hd hn' hv'
  intro K hK hKU
  apply (hconv K hK hKU).congr' _ EventuallyEq.rfl
  filter_upwards [hW] with ν hWν
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  simp only [FewInflection.fundamentalCoefficients_eq_quotient,
    polynomialWronskian_eval_eq_wronskian, hWν z (hKU hz)]

end ModifiedCartan
#print axioms ModifiedCartan.Paper.eq_gaugecomparison_eventual
#print axioms ModifiedCartan.cramer_comparison_of_polynomial_approximation
