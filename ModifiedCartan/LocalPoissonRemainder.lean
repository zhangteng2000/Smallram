import ModifiedCartan.LocalKernelBounds
import FewInflection.Nevanlinna.CharacteristicMassBound

open scoped Topology ComplexConjugate
open Filter Set Metric Complex Function MeromorphicOn
set_option autoImplicit false
namespace ModifiedCartan

noncomputable def poissonJensenRemainder {ι : Type*} (S : Finset ι)
    (a c : ι → ℂ) (f : ℂ → ℂ) (R : ℝ) (z : ℂ) : ℂ :=
  (∑ i ∈ S, c i * (conj (a i) / ((R : ℂ) ^ 2 - conj (a i) * z))) +
    localPoissonLogDerivative f R z

theorem poissonJensenRemainder_analytic {ι : Type*} (S : Finset ι) (a c : ι → ℂ)
    {f : ℂ → ℂ} {R : ℝ} (ha : ∀ i ∈ S, ‖a i‖ ≤ R)
    (hf : MeromorphicOn f (sphere 0 |R|)) :
    AnalyticOnNhd ℂ (poissonJensenRemainder S a c f R) (ball 0 R) := by
  have hsum : AnalyticOnNhd ℂ (fun z : ℂ =>
      ∑ i ∈ S, c i * (conj (a i) / ((R : ℂ) ^ 2 - conj (a i) * z))) (ball 0 R) := by
    apply Finset.analyticOnNhd_fun_sum
    intro i hi z hz
    have hzR : ‖z‖ < R := by simpa only [mem_ball, dist_zero_right] using hz
    have hd : (R : ℂ) ^ 2 - conj (a i) * z ≠ 0 := by
      apply norm_pos_iff.mp
      exact (mul_pos (pos_of_mem_ball hz) (sub_pos.mpr hzR)).trans_le
        (reflected_denominator_lower_bound (norm_nonneg z) hzR (ha i hi) le_rfl)
    fun_prop
  exact hsum.add (localPoissonLogDerivative_analytic hf)

theorem poissonJensenRemainder_bound {ι : Type*} (S : Finset ι) (a c : ι → ℂ)
    {f : ℂ → ℂ} {r R : ℝ} {z : ℂ} (hr : 0 ≤ r) (hrR : r < R)
    (ha : ∀ i ∈ S, ‖a i‖ ≤ R) (hf : MeromorphicOn f (sphere 0 |R|)) (hz : ‖z‖ ≤ r) :
    ‖poissonJensenRemainder S a c f R z‖ ≤
      (R - r)⁻¹ * ∑ i ∈ S, ‖c i‖ +
        (2 * R / (R - r) ^ 2) * Real.circleAverage (fun ζ => |Real.log ‖f ζ‖|) 0 R := by
  have hs : ‖∑ i ∈ S, c i * (conj (a i) / ((R : ℂ) ^ 2 - conj (a i) * z))‖ ≤
      (R - r)⁻¹ * ∑ i ∈ S, ‖c i‖ := by
    rw [Finset.mul_sum]
    apply norm_sum_le_of_le
    intro i hi
    rw [norm_mul, mul_comm ((R - r)⁻¹)]
    exact mul_le_mul_of_nonneg_left (reflected_kernel_bound_general hr hrR (ha i hi) hz)
      (norm_nonneg _)
  exact (norm_add_le _ _).trans (add_le_add hs (localPoissonLogDerivative_bound hr hrR hz hf))

theorem poissonJensenRemainder_iteratedDeriv_bound {ι : Type*} (S : Finset ι) (a c : ι → ℂ)
    {f : ℂ → ℂ} {r s R : ℝ} {z : ℂ} (hr : 0 ≤ r) (hrs : r < s) (hsR : s < R)
    (ha : ∀ i ∈ S, ‖a i‖ ≤ R) (hf : MeromorphicOn f (sphere 0 |R|)) (hz : ‖z‖ ≤ r) (m : ℕ) :
    ‖iteratedDeriv m (poissonJensenRemainder S a c f R) z‖ ≤
      (m.factorial : ℝ) * ((R - s)⁻¹ * ∑ i ∈ S, ‖c i‖ +
        (2 * R / (R - s) ^ 2) * Real.circleAverage (fun ζ => |Real.log ‖f ζ‖|) 0 R) /
          (s - r) ^ m := by
  apply local_cauchy_derivative_bound hr hrs hsR (poissonJensenRemainder_analytic S a c ha hf) _ m hz
  intro w hw
  exact poissonJensenRemainder_bound S a c (hr.trans hrs.le) hsR ha hf
    (by simpa only [mem_closedBall, dist_zero_right] using hw)

theorem logDeriv_eq_singular_add_remainder {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : MeromorphicOn f (closedBall 0 R))
    (hfa : AnalyticAt ℂ f 0) (h0 : f 0 ≠ 0)
    (hb : ∀ w ∈ sphere (0 : ℂ) R, AnalyticAt ℂ f w ∧ f w ≠ 0)
    (S : Finset ℂ) (hs : support (divisor f (ball 0 R)) ⊆ (S : Set ℂ)) :
    logDeriv f =ᶠ[codiscreteWithin (ball 0 R)] (fun z =>
      (∑ a ∈ S, (divisor f (ball 0 R) a : ℂ) * (z - a)⁻¹) +
        poissonJensenRemainder S id (fun a => (divisor f (ball 0 R) a : ℂ)) f R z) := by
  filter_upwards [FewInflection.logDeriv_poisson_jensen_eventuallyEq hR hf hfa h0 hb] with z hz
  have hsum : (∑ᶠ a : ℂ, (divisor f (ball 0 R) a : ℂ) *
      ((z - a)⁻¹ + conj a / ((R : ℂ) ^ 2 - conj a * z))) =
      ∑ a ∈ S, (divisor f (ball 0 R) a : ℂ) *
        ((z - a)⁻¹ + conj a / ((R : ℂ) ^ 2 - conj a * z)) := by
    apply finsum_eq_sum_of_support_subset
    intro a ha
    apply hs
    intro he
    exact ha (by simp [he])
  rw [hz, hsum]
  simp only [mul_add, Finset.sum_add_distrib, poissonJensenRemainder,
    localPoissonLogDerivative, id_eq, add_assoc]

end ModifiedCartan
#print axioms ModifiedCartan.poissonJensenRemainder_iteratedDeriv_bound
#print axioms ModifiedCartan.logDeriv_eq_singular_add_remainder
