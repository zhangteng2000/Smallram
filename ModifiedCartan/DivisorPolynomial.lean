import ModifiedCartan.LogRiesz
import FewInflection.AnalyticLogBranch
import Mathlib.Algebra.Polynomial.BigOperators

open scoped Topology BigOperators Classical
open Filter MeasureTheory Set Metric MeromorphicOn Function
set_option autoImplicit false

namespace ModifiedCartan
noncomputable section

/-- The monic polynomial associated with a finite nonnegative divisor.
This is the polynomial used in Step 1 of LaTeX `prop:representation`. -/
def finiteDivisorPolynomial {U : Set ℂ} (D : locallyFinsuppWithin U ℤ)
    (hD : D.support.Finite) : Polynomial ℂ :=
  ∏ a ∈ hD.toFinset, (Polynomial.X - Polynomial.C a) ^ (D a).toNat

theorem finiteDivisorPolynomial_monic {U : Set ℂ} (D : locallyFinsuppWithin U ℤ)
    (hD : D.support.Finite) : (finiteDivisorPolynomial D hD).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun a _ => (Polynomial.monic_X_sub_C a).pow _)

theorem finiteDivisorPolynomial_natDegree {U : Set ℂ} (D : locallyFinsuppWithin U ℤ)
    (hD : D.support.Finite) :
    (finiteDivisorPolynomial D hD).natDegree = ∑ a ∈ hD.toFinset, (D a).toNat := by
  rw [finiteDivisorPolynomial, Polynomial.natDegree_prod_of_monic _ _
    (fun a _ => (Polynomial.monic_X_sub_C a).pow _)]
  simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]

theorem finiteDivisorPolynomial_eval {U : Set ℂ} (D : locallyFinsuppWithin U ℤ)
    (hD : D.support.Finite) (z : ℂ) :
    (finiteDivisorPolynomial D hD).eval z =
      ∏ a ∈ hD.toFinset, (z - a) ^ (D a).toNat := by
  simp only [finiteDivisorPolynomial, Polynomial.eval_prod, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

theorem finiteDivisorPolynomial_roots_mem {U : Set ℂ} (D : locallyFinsuppWithin U ℤ)
    (hD : D.support.Finite) {z : ℂ}
    (hz : (finiteDivisorPolynomial D hD).eval z = 0) : z ∈ U := by
  rw [finiteDivisorPolynomial_eval] at hz
  obtain ⟨a, ha, haz⟩ := Finset.prod_eq_zero_iff.mp hz
  have hza : z = a := by
    by_contra hne
    exact (pow_ne_zero _ (sub_ne_zero.mpr hne)) haz
  subst z
  exact D.supportWithinDomain (hD.mem_toFinset.mp ha)

theorem finiteDivisorPolynomial_eval_eq_factorized {U : Set ℂ}
    (D : locallyFinsuppWithin U ℤ) (hD : D.support.Finite) (hD0 : 0 ≤ D) :
    (fun z => (finiteDivisorPolynomial D hD).eval z) =
      ∏ᶠ a, (fun z : ℂ => z - a) ^ D a := by
  rw [finprod_eq_prod_of_mulSupport_subset (s := hD.toFinset) _ (by
    rw [Function.FactorizedRational.mulSupport]
    exact hD.coe_toFinset.symm.subset)]
  funext z
  rw [finiteDivisorPolynomial_eval]
  simp only [Finset.prod_apply, Pi.pow_apply]
  apply Finset.prod_congr rfl
  intro a _
  rw [← zpow_natCast, Int.toNat_of_nonneg (hD0 a)]

theorem finiteDivisorPolynomial_natDegree_cast {U : Set ℂ}
    (D : locallyFinsuppWithin U ℤ) (hD : D.support.Finite) (hD0 : 0 ≤ D) :
    ((finiteDivisorPolynomial D hD).natDegree : ℝ) = ∑ᶠ a : ℂ, (D a : ℝ) := by
  rw [finsum_eq_sum_of_support_subset _ (s := hD.toFinset) (by
    intro a ha
    apply hD.mem_toFinset.mpr
    simpa only [mem_support, ne_eq, Int.cast_eq_zero] using ha)]
  rw [finiteDivisorPolynomial_natDegree, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact_mod_cast Int.toNat_of_nonneg (hD0 a)

theorem exists_monic_polynomial_nonzero_factor {U : Set ℂ} (hU : IsOpen U)
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U)
    (horder : ∀ z : U, meromorphicOrderAt F z ≠ ⊤)
    (hfinite : (divisor F U).support.Finite) :
    ∃ v : ℂ → ℂ, AnalyticOnNhd ℂ v U ∧ (∀ z ∈ U, v z ≠ 0) ∧
      ∀ z ∈ U, F z = (finiteDivisorPolynomial (divisor F U) hfinite).eval z * v z := by
  obtain ⟨v, hv, hv0, heq⟩ := hF.meromorphicOn.extract_zeros_poles horder hfinite
  rw [← finiteDivisorPolynomial_eval_eq_factorized _ hfinite hF.divisor_nonneg] at heq
  have hae : F =ᵐ[volume.restrict U]
      (fun z => (finiteDivisorPolynomial (divisor F U) hfinite).eval z * v z) := by
    exact ae_restrict_le_codiscreteWithin (μ := volume) hU.measurableSet heq
  have hp : ContinuousOn
      (fun z => (finiteDivisorPolynomial (divisor F U) hfinite).eval z * v z) U := by
    apply ContinuousOn.mul _ hv.continuousOn
    fun_prop
  exact ⟨v, hv, fun z hz => hv0 ⟨z, hz⟩,
    fun z hz => Measure.eqOn_open_of_ae_eq hae hU hF.continuousOn hp hz⟩

theorem entire_meromorphicOrder_ne_top {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hF0 : ∃ z, F z ≠ 0) (z : ℂ) : meromorphicOrderAt F z ≠ ⊤ := by
  have hA := Complex.analyticOnNhd_univ_iff_differentiable.mpr hF
  obtain ⟨a, ha⟩ := hF0
  have hoa : meromorphicOrderAt F a ≠ ⊤ := by
    rw [(hA a (mem_univ _)).meromorphicOrderAt_eq,
      (hA a (mem_univ _)).analyticOrderAt_eq_zero.mpr ha]
    simp
  exact hA.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ a) (mem_univ z) hoa

/-- Exact analytic factorization on an open disk, including all zeros.
Lowest analytic construction for LaTeX `eq:localgauge`. -/
theorem exists_monic_polynomial_exp_factor_on_ball
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hF0 : ∃ z, F z ≠ 0) {R : ℝ} (hR : 0 < R) :
    ∃ (P : Polynomial ℂ) (L : ℂ → ℂ),
      P.Monic ∧ AnalyticOnNhd ℂ L (ball 0 R) ∧
      (∀ z, P.eval z = 0 → z ∈ ball (0 : ℂ) R) ∧
      (∀ z ∈ ball (0 : ℂ) R, F z = P.eval z * Complex.exp (L z)) ∧
      ((P.natDegree : ℝ) = ∑ᶠ a : ℂ, (divisor F (ball 0 R) a : ℝ)) := by
  have hA := Complex.analyticOnNhd_univ_iff_differentiable.mpr hF
  have hfinite := (hA.meromorphicOn.mono_set (subset_univ (closedBall (0 : ℂ) R))).divisor_ball_support_finite
  let P := finiteDivisorPolynomial (divisor F (ball 0 R)) hfinite
  obtain ⟨v, hv, hv0, heq⟩ := exists_monic_polynomial_nonzero_factor isOpen_ball
    (hA.mono (subset_univ _)) (fun z => entire_meromorphicOrder_ne_top hF hF0 z) hfinite
  let : ContractibleSpace (ball (0 : ℂ) R) :=
    (convex_ball (0 : ℂ) R).contractibleSpace ⟨0, mem_ball_self hR⟩
  have hsim : IsSimplyConnected (ball (0 : ℂ) R) := SimplyConnectedSpace.ofContractible _
  obtain ⟨L, hL, heL⟩ := FewInflection.exists_analyticOnNhd_log hsim isOpen_ball hv hv0
  refine ⟨P, L, finiteDivisorPolynomial_monic _ _, hL,
    fun z hz => finiteDivisorPolynomial_roots_mem _ _ hz, ?_,
    finiteDivisorPolynomial_natDegree_cast _ _ (hA.mono (subset_univ _)).divisor_nonneg⟩
  intro z hz
  rw [heL z hz]
  exact heq z hz

end
end ModifiedCartan
#print axioms ModifiedCartan.exists_monic_polynomial_exp_factor_on_ball
