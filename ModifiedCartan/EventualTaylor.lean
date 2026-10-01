import ModifiedCartan.ExponentialJetApproximation

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- LaTeX `eq:taylorerror`, with eventual hypotheses and the actual Taylor
polynomials at every index. Finite initial terms require no assumptions. -/
theorem Paper.eq_taylorerror_eventual (n : ℕ) (A C : ℝ) :
    ∃ L : ℝ, 0 < L ∧
      ∀ (g : ℕ → Index n → ℂ → ℂ) (s : ℕ → ℝ),
        Tendsto s atTop atTop →
        (∀ᶠ ν in atTop, ∀ j, AnalyticOnNhd ℂ (g ν j) (ball 0 32)) →
        (∀ᶠ ν in atTop, ∀ z, z ∈ ball (0 : ℂ) 32 →
          euclideanNorm (fun j => g ν j z) ≤ Real.exp (C * s ν)) →
        ∃ p : ℕ → Index n → Polynomial ℂ,
          (∀ ν j, p ν j = FewInflection.taylorPolynomial (g ν j) 0 (Nat.ceil (L * s ν))) ∧
          (∀ ν j, (p ν j).natDegree ≤ Nat.ceil (L * s ν)) ∧
          ∀ᶠ ν in atTop,
            (∀ j, ((p ν j).natDegree : ℝ) ≤ (L + 1) * s ν) ∧
            (∀ j k, k ≤ n + 1 → ∀ z ∈ closedBall (0 : ℂ) 16,
              ‖iteratedDeriv k (fun w => (p ν j).eval w) z - iteratedDeriv k (g ν j) z‖ ≤
                Real.exp (-A * s ν)) := by
  let K : ℝ := 6 * (n + 1).factorial
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨L, hL, hcutoff⟩ := exists_geometric_linear_cutoff A C K hK
  refine ⟨L, hL, ?_⟩
  intro g s hs hg hnorm
  let p : ℕ → Index n → Polynomial ℂ := fun ν j =>
    FewInflection.taylorPolynomial (g ν j) 0 (Nat.ceil (L * s ν))
  have hdegree (ν : ℕ) (j : Index n) : (p ν j).natDegree ≤ Nat.ceil (L * s ν) :=
    taylorPolynomial_natDegree_le _ _ _
  refine ⟨p, fun _ _ => rfl, hdegree, ?_⟩
  filter_upwards [hg, hnorm, hs.eventually_ge_atTop (max 1 (Real.log K))] with ν hgν hnormν hν
  have hcoordinate (j : Index n) (z : ℂ) (hz : z ∈ ball (0 : ℂ) 32) :
      ‖g ν j z‖ ≤ Real.exp (C * s ν) :=
    (norm_le_pi_norm (fun i => g ν i z) j).trans
      ((norm_le_euclideanNorm (fun i => g ν i z)).trans (hnormν z hz))
  constructor
  · intro j
    exact (show ((p ν j).natDegree : ℝ) ≤ Nat.ceil (L * s ν) by
      exact_mod_cast hdegree ν j).trans (hcutoff (s ν) hν).1
  · intro j k hk z hz
    exact (norm_taylor_derivative_remainder_le_factorial (Real.exp_nonneg _)
      (hgν j) (hcoordinate j) hz (Nat.ceil (L * s ν)) hk).trans (hcutoff (s ν) hν).2


/-- Determinant errors for the same prescribed Taylor jets. This retains the
jet data needed by `lem:replacement`, including the actual truncation choice. -/
theorem determinant_error_of_taylor_jets {n : ℕ} {g p : Index n → ℂ → ℂ}
    {C A B t : ℝ} (hB : 0 < B)
    (hA : B + (n + 1) * (|C| + 1) + 1 ≤ A)
    (hg : ∀ j, AnalyticOnNhd ℂ (g j) (ball 0 32))
    (hnorm : ∀ z ∈ ball (0 : ℂ) 32, euclideanNorm (fun j => g j z) ≤ Real.exp (C * t))
    (ht0 : 0 ≤ t)
    (htjet : Real.log (((n + 1).factorial : ℝ) + 1) ≤ t)
    (htfac : Real.log (((n + 1).factorial : ℝ) * (n + 1)) ≤ t)
    {z : ℂ} (hz : z ∈ closedBall 0 16)
    (herr : ∀ j k, k ≤ n + 1 →
      ‖iteratedDeriv k (p j) z - iteratedDeriv k (g j) z‖ ≤ Real.exp (-A * t)) :
    ‖FewInflection.wronskian n p z - FewInflection.wronskian n g z‖ ≤ Real.exp (-B * t) ∧
    ∀ i, ‖FewInflection.fundamentalNumerator n p i z -
      FewInflection.fundamentalNumerator n g i z‖ ≤ Real.exp (-B * t) := by
  let C1 : ℝ := |C| + 1
  let A0 : ℝ := B + (n + 1) * C1 + 1
  have hC1 : 0 < C1 := by dsimp [C1]; positivity
  have hA0 : 0 < A0 := by dsimp [A0]; positivity
  have hcoordinate (j : Index n) (w : ℂ) (hw : w ∈ ball (0 : ℂ) 32) :
      ‖g j w‖ ≤ Real.exp (C * t) :=
    (norm_le_pi_norm (fun l => g l w) j).trans
      ((norm_le_euclideanNorm (fun l => g l w)).trans (hnorm w hw))
  have hmargin (j : Index n) (k : ℕ) (hk : k ≤ n + 1) :
      ‖iteratedDeriv k (g j) z‖ + 1 ≤ Real.exp (C1 * t) :=
    local_jet_exponential_margin (hg j) (hcoordinate j) ht0 htjet hz hk
  have hjg (j : Index n) (k : ℕ) (hk : k ≤ n + 1) :
      ‖iteratedDeriv k (g j) z‖ ≤ Real.exp (C1 * t) := by
    linarith [hmargin j k hk]
  have herr0 (j : Index n) (k : ℕ) (hk : k ≤ n + 1) :
      ‖iteratedDeriv k (p j) z - iteratedDeriv k (g j) z‖ ≤ Real.exp (-A0 * t) := by
    apply (herr j k hk).trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg hA) ht0
  have herr1 : Real.exp (-A0 * t) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hA0.le) ht0)
  have hjp (j : Index n) (k : ℕ) (hk : k ≤ n + 1) :
      ‖iteratedDeriv k (p j) z‖ ≤ Real.exp (C1 * t) :=
    norm_le_of_unit_error (hmargin j k hk) ((herr0 j k hk).trans herr1)
  have hM1 : 1 ≤ Real.exp (C1 * t) := Real.one_le_exp_iff.mpr (mul_nonneg hC1.le ht0)
  constructor
  · exact (norm_wronskian_sub_le_of_jet_error p g z hM1 (Real.exp_nonneg _) hjp hjg herr0).trans
      (factorial_exponential_error_le n B C1 t htfac)
  · intro i
    exact (norm_fundamentalNumerator_sub_le_of_jet_error p g z i hM1
      (Real.exp_nonneg _) hjp hjg herr0).trans (factorial_exponential_error_le n B C1 t htfac)

end ModifiedCartan
#print axioms ModifiedCartan.Paper.eq_taylorerror_eventual
#print axioms ModifiedCartan.determinant_error_of_taylor_jets