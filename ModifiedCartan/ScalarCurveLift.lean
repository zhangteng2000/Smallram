import ModifiedCartan.GlobalMeromorphicPair
import ModifiedCartan.ScalarDefinitions
import ModifiedCartan.DivisorPolynomial

open scoped Topology BigOperators
open Filter Set MeromorphicOn
set_option autoImplicit false
namespace ModifiedCartan

/-- The actual homogeneous lift [q:p] of the quotient p/q. -/
noncomputable def curveOfReducedPair (p q : ℂ → ℂ)
    (hp : Differentiable ℂ p) (hq : Differentiable ℂ q)
    (hred : ∀ z, p z ≠ 0 ∨ q z ≠ 0) : Curve 1 where
  coord := ![q, p]
  holomorphic := by intro j; fin_cases j <;> simpa using ‹_›
  reduced := by
    intro z
    rcases hred z with h | h
    · exact ⟨1, h⟩
    · exact ⟨0, h⟩

theorem curveOfReducedPair_transcendental {f p q : ℂ → ℂ}
    (hp : Differentiable ℂ p) (hq : Differentiable ℂ q)
    (hred : ∀ z, p z ≠ 0 ∨ q z ≠ 0) (hqn : ∃ z, q z ≠ 0)
    (he : f =ᶠ[codiscreteWithin (univ : Set ℂ)] (fun z => p z / q z))
    (htrans : ScalarTranscendental f) : (curveOfReducedPair p q hp hq hred).Transcendental := by
  rintro ⟨P, g, hg, _, hP⟩
  apply htrans
  have hP0 : P 0 ≠ 0 := by
    intro hzero
    obtain ⟨z, hz⟩ := hqn
    have hh := hP 0 z
    change q z = g z * (P 0).eval z at hh
    rw [hzero, Polynomial.eval_zero, mul_zero] at hh
    exact hz hh
  refine ⟨P 1, P 0, hP0, ?_⟩
  filter_upwards [he] with z hz
  have hqz := hP 0 z
  have hpz := hP 1 z
  change q z = g z * (P 0).eval z at hqz
  change p z = g z * (P 1).eval z at hpz
  rw [hz, hpz, hqz]
  exact mul_div_mul_left _ _ (hg z)

theorem curveOfReducedPair_linearlyNonDegenerate {f p q : ℂ → ℂ}
    (hp : Differentiable ℂ p) (hq : Differentiable ℂ q)
    (hred : ∀ z, p z ≠ 0 ∨ q z ≠ 0) (hqn : ∃ z, q z ≠ 0)
    (he : f =ᶠ[codiscreteWithin (univ : Set ℂ)] (fun z => p z / q z))
    (htrans : ScalarTranscendental f) :
    (curveOfReducedPair p q hp hq hred).linearlyNonDegenerate := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  have hcz (z : ℂ) : c 0 * q z + c 1 * p z = 0 := by
    have h := congrFun hc z
    simpa [Index, FewInflection.Index, curveOfReducedPair, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] using h
  have hc1 : c 1 = 0 := by
    by_contra h1
    apply htrans
    apply scalarIsRational_of_codiscrete_const (a := -(c 0) / c 1)
    have hqU : MeromorphicOn q univ := fun z _ => (hq.analyticAt z).meromorphicAt
    have hne := MeromorphicAt.MeromorphicOn.codiscreteWithin_setOfPred_ne_zero hqU
      (fun z _ => entire_meromorphicOrder_ne_top hq hqn z)
    filter_upwards [he, hne] with z hz hzq
    rw [hz]
    apply (div_eq_div_iff hzq h1).mpr
    linear_combination hcz z
  have hc0 : c 0 = 0 := by
    obtain ⟨z, hz⟩ := hqn
    have h := hcz z
    rw [hc1, zero_mul, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_right hz
  fin_cases j <;> assumption

/-- A transcendental scalar meromorphic function supplies all representation
and nondegeneracy hypotheses of the n=1 curve theorem; none are assumed. -/
theorem exists_scalar_curve_lift {f : ℂ → ℂ} (hf : Meromorphic f)
    (htrans : ScalarTranscendental f) :
    ∃ F : Curve 1, F.Transcendental ∧ F.linearlyNonDegenerate ∧
      f =ᶠ[codiscreteWithin (univ : Set ℂ)] (fun z => F.coord 1 z / F.coord 0 z) ∧
      divisor (F.coord 1) univ = (divisor f univ)⁺ ∧
      divisor (F.coord 0) univ = (divisor f univ)⁻ := by
  obtain ⟨p, q, hp, hq, hred, he, hpD, hqD, _, hqfin⟩ :=
    global_reduced_pair_of_finite_orders hf (scalarTranscendental_finite_orders hf htrans)
  have hqn : ∃ z, q z ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hqzero : q = 0 := funext hn
    have hh := hqfin 0
    simp [hqzero] at hh
  refine ⟨curveOfReducedPair p q hp hq hred,
    curveOfReducedPair_transcendental hp hq hred hqn he htrans,
    curveOfReducedPair_linearlyNonDegenerate hp hq hred hqn he htrans, he, hpD, hqD⟩

end ModifiedCartan
#print axioms ModifiedCartan.exists_scalar_curve_lift


