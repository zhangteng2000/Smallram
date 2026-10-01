import ModifiedCartan.EventualTaylor
import ModifiedCartan.EventualCoefficientComparison

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- Actual Taylor truncations for `lem:replacement`, preserving all jet,
Wronskian, degree and Cramer comparison conclusions for the same polynomials.
Every threshold and truncation constant is chosen before the sequence data. -/
theorem replacement_taylor_data (n : ℕ) (C : ℝ) :
    ∃ A0 : ℝ, 0 < A0 ∧ ∀ A : ℝ, A0 ≤ A → ∃ L : ℝ, 0 < L ∧
      ∀ (g : ℕ → Index n → ℂ → ℂ) (s : ℕ → ℝ) (P : ℕ → Polynomial ℂ),
        Tendsto s atTop atTop → (∀ ν, (P ν).Monic) →
        Tendsto (fun ν => ((P ν).natDegree : ℝ) / s ν) atTop (𝓝 0) →
        (∀ᶠ ν in atTop,
          (∀ j, AnalyticOnNhd ℂ (g ν j) (ball 0 32)) ∧
          (∀ z ∈ ball (0 : ℂ) 32, FewInflection.wronskian n (g ν) z = (P ν).eval z) ∧
          (∀ z ∈ ball (0 : ℂ) 32, euclideanNorm (fun j => g ν j z) ≤ Real.exp (C * s ν))) →
        ∃ p : ℕ → Index n → Polynomial ℂ,
          (∀ ν j, p ν j = FewInflection.taylorPolynomial (g ν j) 0 (Nat.ceil (L * s ν))) ∧
          (∀ᶠ ν in atTop,
            (∀ j, ((p ν j).natDegree : ℝ) ≤ (L + 1) * s ν) ∧
            ((FewInflection.polynomialWronskian (p ν)).natDegree : ℝ) ≤ (n + 1) * (L + 1) * s ν ∧
            FewInflection.polynomialWronskian (p ν) ≠ 0 ∧
            (∀ j k, k ≤ n + 1 → ∀ z ∈ closedBall (0 : ℂ) 16,
              ‖iteratedDeriv k (fun w => (p ν j).eval w) z - iteratedDeriv k (g ν j) z‖ ≤
                Real.exp (-A * s ν)) ∧
            (∀ z ∈ closedBall (0 : ℂ) 12,
              ‖(FewInflection.polynomialWronskian (p ν)).eval z - (P ν).eval z‖ ≤ 1 / 2)) ∧
          ∀ i, LocalMeasureConvergence (ball (0 : ℂ) 12)
            (fun ν z => FewInflection.fundamentalCoefficients n (fun j w => (p ν j).eval w) z i -
              FewInflection.fundamentalCoefficients n (g ν) z i) (fun _ => 0) := by
  obtain ⟨C2, hC2, hnumbound⟩ := exists_fundamentalNumerator_exponential_bound_eventual n C
  let B : ℝ := C2 + 3
  have hB : 0 < B := by dsimp [B]; linarith
  let A0 : ℝ := B + (n + 1) * (|C| + 1) + 1
  have hA0 : 0 < A0 := by dsimp [A0]; positivity
  refine ⟨A0, hA0, ?_⟩
  intro A hA
  obtain ⟨L, hL, htaylor⟩ := Paper.eq_taylorerror_eventual n A C
  refine ⟨L, hL, ?_⟩
  intro g s P hs hP hm hd
  have hg := hd.mono (fun _ h => h.1)
  have hnorm := hd.mono (fun _ h => h.2.2)
  obtain ⟨p, hpTaylor, _, hp⟩ := htaylor g s hs hg hnorm
  have hdet : ∀ᶠ ν in atTop,
      (∀ z ∈ closedBall (0 : ℂ) 12,
        ‖(FewInflection.polynomialWronskian (p ν)).eval z - (P ν).eval z‖ ≤ Real.exp (-B * s ν)) ∧
      (∀ i z, z ∈ closedBall (0 : ℂ) 12 →
        ‖FewInflection.fundamentalNumerator n (fun j w => (p ν j).eval w) i z -
          FewInflection.fundamentalNumerator n (g ν) i z‖ ≤ Real.exp (-B * s ν)) := by
    filter_upwards [hd, hp, hs.eventually_ge_atTop 0,
      hs.eventually_ge_atTop (Real.log (((n + 1).factorial : ℝ) + 1)),
      hs.eventually_ge_atTop (Real.log (((n + 1).factorial : ℝ) * (n + 1)))]
      with ν hdν hpν hs0 hsjet hsfac
    have he (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 12) :=
      determinant_error_of_taylor_jets hB hA hdν.1 hdν.2.2 hs0 hsjet hsfac
        ((closedBall_subset_closedBall (by norm_num : (12 : ℝ) ≤ 16)) hz)
        (fun j k hk => hpν.2 j k hk z ((closedBall_subset_closedBall (by norm_num : (12 : ℝ) ≤ 16)) hz))
    constructor
    · intro z hz
      rw [polynomialWronskian_eval_eq_wronskian,
        ← hdν.2.1 z ((closedBall_subset_ball (by norm_num : (12 : ℝ) < 32)) hz)]
      exact (he z hz).1
    · intro i z hz
      exact (he z hz).2 i
  have hhalf : ∀ᶠ ν in atTop, ∀ z ∈ closedBall (0 : ℂ) 12,
      ‖(FewInflection.polynomialWronskian (p ν)).eval z - (P ν).eval z‖ ≤ 1 / 2 := by
    filter_upwards [hdet, (exponential_decay_of_scale hs hB).eventually_lt_const
      (by norm_num : (0 : ℝ) < 1 / 2)] with ν hν heν z hz
    exact (hν.1 z hz).trans heν.le
  have hnb := hnumbound g s hs (hd.mono (fun _ h => ⟨h.1, h.2.2⟩))
  refine ⟨p, hpTaylor, ?_, ?_⟩
  · filter_upwards [hp, hhalf] with ν hpν heν
    refine ⟨hpν.1, ?_, ?_, hpν.2, heν⟩
    · calc
        _ ≤ (n + 1) * ((L + 1) * s ν) := polynomialWronskian_natDegree_le_real (p ν) hpν.1
        _ = _ := by ring
    · apply polynomial_ne_zero_of_small_error_monic (P ν) _ (hP ν)
        (by norm_num : (1 / 2 : ℝ) < 1)
      intro z hz
      exact heν z ((closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 12))
        (sphere_subset_closedBall hz))
  · apply cramer_comparison_of_polynomial_approximation g p P hP hs hm
      (show 1 < B by dsimp [B]; linarith) (show C2 + 2 < B by dsimp [B]; linarith)
    · filter_upwards [hd] with ν hν z hz
      exact hν.2.1 z ((ball_subset_ball (by norm_num : (12 : ℝ) ≤ 32)) hz)
    · filter_upwards [hdet] with ν hν z hz
      exact hν.1 z (ball_subset_closedBall hz)
    · filter_upwards [hdet] with ν hν i z hz
      exact hν.2 i z (ball_subset_closedBall hz)
    · filter_upwards [hnb] with ν hν i z hz
      exact hν i z ((closedBall_subset_closedBall (by norm_num : (12 : ℝ) ≤ 16))
        (ball_subset_closedBall hz))

end
end ModifiedCartan
#print axioms ModifiedCartan.replacement_taylor_data
