import ModifiedCartan.ExponentialTaylorApproximation
import ModifiedCartan.ExponentialJetApproximation

open scoped Topology BigOperators
open Filter Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem monic_polynomial_not_uniformly_small (P : Polynomial ℂ) (hP : P.Monic)
    {δ : ℝ} (hδ : δ < 1) :
    ¬ ∀ z ∈ sphere (0 : ℂ) 1, ‖P.eval z‖ ≤ δ := by
  intro hbound
  have he := norm_taylor_coefficient_le (by norm_num : (0 : ℝ) < 1)
    P.differentiable.differentiableOn hbound P.natDegree
  have hcoeff : (P.natDegree.factorial : ℂ)⁻¹ *
      iteratedDeriv P.natDegree (fun z => P.eval z) 0 = P.coeff P.natDegree := by
    rw [FewInflection.polynomial_coeff_eq_jet]
    ring
  rw [hcoeff, hP.coeff_natDegree] at he
  norm_num at he
  linarith

theorem polynomial_ne_zero_of_small_error_monic (P R : Polynomial ℂ) (hP : P.Monic)
    {δ : ℝ} (hδ : δ < 1)
    (herror : ∀ z ∈ sphere (0 : ℂ) 1, ‖R.eval z - P.eval z‖ ≤ δ) : R ≠ 0 := by
  intro hR
  apply monic_polynomial_not_uniformly_small P hP hδ
  intro z hz
  simpa only [hR, Polynomial.eval_zero, zero_sub, norm_neg] using herror z hz

theorem polynomialWronskian_eval_eq_wronskian {n : ℕ} (p : Index n → Polynomial ℂ) (z : ℂ) :
    (FewInflection.polynomialWronskian p).eval z =
      FewInflection.wronskian n (fun j w => (p j).eval w) z :=
  FewInflection.polynomialWronskian_eval p z

theorem polynomialWronskian_natDegree_le_real {n : ℕ} (p : Index n → Polynomial ℂ)
    {M : ℝ} (hp : ∀ j, ((p j).natDegree : ℝ) ≤ M) :
    ((FewInflection.polynomialWronskian p).natDegree : ℝ) ≤ (n + 1) * M := by
  have he : ((FewInflection.polynomialWronskian p).natDegree : ℝ) ≤
      ∑ j : Index n, ((p j).natDegree : ℝ) := by
    exact_mod_cast FewInflection.polynomialWronskian_natDegree_le p
  calc
    _ ≤ ∑ j : Index n, ((p j).natDegree : ℝ) := he
    _ ≤ ∑ _j : Index n, M := Finset.sum_le_sum (fun j _ => hp j)
    _ = _ := by simp [Index, FewInflection.Index]

namespace Paper

/-- LaTeX `eq:wronskiapprox`, together with the difference estimate in
`eq:cramer-numerator-approx`. The nonzero polynomial Wronskians are constructed
from the local curve; their degree and errors are proved from its norm bound. -/
theorem eq_wronskiapprox (n : ℕ) (C B : ℝ) (hB : 0 < B) :
    ∃ L : ℝ, 0 < L ∧
      ∀ (g : ℕ → Index n → ℂ → ℂ) (s : ℕ → ℝ) (P : ℕ → Polynomial ℂ),
        Tendsto s atTop atTop →
        (∀ ν j, AnalyticOnNhd ℂ (g ν j) (ball 0 32)) →
        (∀ ν z, z ∈ ball (0 : ℂ) 32 →
          euclideanNorm (fun j => g ν j z) ≤ Real.exp (C * s ν)) →
        (∀ ν, (P ν).Monic) →
        (∀ ν z, z ∈ ball (0 : ℂ) 32 → FewInflection.wronskian n (g ν) z = (P ν).eval z) →
        ∃ p : ℕ → Index n → Polynomial ℂ,
          ∀ᶠ ν in atTop,
            ((FewInflection.polynomialWronskian (p ν)).natDegree : ℝ) ≤ L * s ν ∧
            FewInflection.polynomialWronskian (p ν) ≠ 0 ∧
            (∀ z ∈ closedBall (0 : ℂ) 12,
              ‖(FewInflection.polynomialWronskian (p ν)).eval z - (P ν).eval z‖ ≤
                Real.exp (-B * s ν)) ∧
            (∀ i z, z ∈ closedBall (0 : ℂ) 12 →
              ‖FewInflection.fundamentalNumerator n (fun j w => (p ν j).eval w) i z -
                  FewInflection.fundamentalNumerator n (g ν) i z‖ ≤ Real.exp (-B * s ν)) := by
  obtain ⟨L, hL, happrox⟩ := exists_polynomial_determinant_approximation n C B hB
  refine ⟨(n + 1) * L, by positivity, ?_⟩
  intro g s P hs hg hnorm hP hW
  obtain ⟨p, hp⟩ := happrox g s hs hg hnorm
  refine ⟨p, ?_⟩
  filter_upwards [hp, hs.eventually_gt_atTop 0] with ν hν hsν
  have herror (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 12) :
      ‖(FewInflection.polynomialWronskian (p ν)).eval z - (P ν).eval z‖ ≤
        Real.exp (-B * s ν) := by
    rw [polynomialWronskian_eval_eq_wronskian,
      ← hW ν z ((closedBall_subset_ball (by norm_num)) hz)]
    exact (hν.2 z ((closedBall_subset_closedBall (by norm_num : (12 : ℝ) ≤ 16)) hz)).1
  have hsmall : Real.exp (-B * s ν) < 1 := by
    have he : -B * s ν < 0 := mul_neg_of_neg_of_pos (neg_lt_zero.mpr hB) hsν
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr he
  refine ⟨?_, ?_, herror, ?_⟩
  · calc
      _ ≤ (n + 1) * (L * s ν) := polynomialWronskian_natDegree_le_real (p ν) hν.1
      _ = _ := by ring
  · apply polynomial_ne_zero_of_small_error_monic (P ν) _ (hP ν) hsmall
    intro z hz
    exact herror z ((closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 12))
      (sphere_subset_closedBall hz))
  · intro i z hz
    exact (hν.2 z ((closedBall_subset_closedBall (by norm_num : (12 : ℝ) ≤ 16)) hz)).2 i

end Paper

end ModifiedCartan
