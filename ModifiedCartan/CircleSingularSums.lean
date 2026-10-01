import ModifiedCartan.CircleSingularHalfPower
import ModifiedCartan.CircleMomentProximity
import ModifiedCartan.SingularPowerEstimate

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem circleIntegrable_pole_fractional_moment (w a : ℂ) {r α : ℝ} {q : ℕ}
    (hr : 0 < r) (hpow : (q : ℝ) * α = 1 / 2) :
    CircleIntegrable (fun z : ℂ => ‖w / (z - a) ^ q‖ ^ α) 0 r := by
  simp_rw [norm_div_pow_rpow, neg_mul, hpow]
  change IntervalIntegrable _ _ _ _
  exact (circle_singular_half_power_integrable hr a).const_mul _

theorem circleIntegrable_weighted_poles_fractional_moment {ι : Type*}
    (S : Finset ι) (a w : ι → ℂ) {r α : ℝ} {q : ℕ}
    (hr : 0 < r) (hα : 0 < α) (hα1 : α ≤ 1) (hpow : (q : ℝ) * α = 1 / 2) :
    CircleIntegrable (fun z : ℂ => ‖∑ i ∈ S, w i / (z - a i) ^ q‖ ^ α) 0 r := by
  have hterm (i : ι) (_hi : i ∈ S) :=
    circleIntegrable_pole_fractional_moment (w i) (a i) hr hpow
  have hsum : CircleIntegrable (fun z : ℂ => ∑ i ∈ S, ‖w i / (z - a i) ^ q‖ ^ α) 0 r := by
    convert CircleIntegrable.sum S hterm using 1
    ext z
    simp
  have hm : Measurable (fun θ : ℝ =>
      ‖∑ i ∈ S, w i / (circleMap 0 r θ - a i) ^ q‖ ^ α) := by fun_prop
  change IntervalIntegrable _ _ _ _
  apply (hsum : IntervalIntegrable _ _ _ _).mono_fun' hm.aestronglyMeasurable
  filter_upwards [] with θ
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using
    norm_finsetSum_rpow_le S (fun i => w i / (circleMap 0 r θ - a i) ^ q) hα hα1

/-- Uniform circle moments of arbitrary finite pole sums, for LaTeX `lem:NH`. -/
theorem circle_weighted_poles_fractional_moment_bound {ι : Type*} :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset ι) (a w : ι → ℂ) (r α : ℝ) (q : ℕ),
      0 < r → 0 < α → α ≤ 1 → (q : ℝ) * α = 1 / 2 →
      Real.circleAverage (fun z : ℂ => ‖∑ i ∈ S, w i / (z - a i) ^ q‖ ^ α) 0 r ≤
        K * r ^ (-(1 / 2 : ℝ)) * ∑ i ∈ S, ‖w i‖ ^ α := by
  obtain ⟨K, hK, hkernel⟩ := circle_singular_half_power_bound
  refine ⟨K, hK, fun S a w r α q hr hα hα1 hpow => ?_⟩
  have hterm (i : ι) (_hi : i ∈ S) :=
    circleIntegrable_pole_fractional_moment (w i) (a i) hr hpow
  have hsum : CircleIntegrable (fun z : ℂ => ∑ i ∈ S, ‖w i / (z - a i) ^ q‖ ^ α) 0 r := by
    convert CircleIntegrable.sum S hterm using 1
    ext z
    simp
  calc
    _ ≤ Real.circleAverage (fun z : ℂ => ∑ i ∈ S, ‖w i / (z - a i) ^ q‖ ^ α) 0 r :=
      Real.circleAverage_mono
        (circleIntegrable_weighted_poles_fractional_moment S a w hr hα hα1 hpow) hsum
        (fun z _ => norm_finsetSum_rpow_le S (fun i => w i / (z - a i) ^ q) hα hα1)
    _ = ∑ i ∈ S, Real.circleAverage (fun z : ℂ => ‖w i / (z - a i) ^ q‖ ^ α) 0 r :=
      Real.circleAverage_fun_sum hterm
    _ ≤ ∑ i ∈ S, ‖w i‖ ^ α * (K * r ^ (-(1 / 2 : ℝ))) := by
      apply Finset.sum_le_sum
      intro i _
      simp_rw [norm_div_pow_rpow, neg_mul, hpow]
      have he : Real.circleAverage (fun z : ℂ =>
          ‖w i‖ ^ α * ‖z - a i‖ ^ (-(1 / 2 : ℝ))) 0 r =
          ‖w i‖ ^ α * Real.circleAverage (fun z : ℂ => ‖z - a i‖ ^ (-(1 / 2 : ℝ))) 0 r := by
        simpa only [smul_eq_mul] using
          (Real.circleAverage_fun_smul (a := ‖w i‖ ^ α)
            (f := fun z : ℂ => ‖z - a i‖ ^ (-(1 / 2 : ℝ))) (c := 0) (R := r))
      rw [he]
      exact mul_le_mul_of_nonneg_left (hkernel r hr (a i)) (Real.rpow_nonneg (norm_nonneg _) _)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

theorem meromorphic_weighted_poles {ι : Type*} (S : Finset ι) (a w : ι → ℂ) (q : ℕ) :
    Meromorphic (fun z : ℂ => ∑ i ∈ S, w i / (z - a i) ^ q) := by
  have he : (fun z : ℂ => ∑ i ∈ S, w i / (z - a i) ^ q) =
      ∑ i ∈ S, (fun z : ℂ => w i / (z - a i) ^ q) := by ext z; simp
  rw [he]
  apply Meromorphic.sum
  intro i _ z
  have hn : AnalyticAt ℂ (fun _ : ℂ => w i) z := by fun_prop
  have hd : AnalyticAt ℂ (fun y : ℂ => (y - a i) ^ q) z := by fun_prop
  exact hn.meromorphicAt.div hd.meromorphicAt

/-- The finite-sum cost enters only inside a logarithm. -/
theorem circle_weighted_poles_proximity_bound {ι : Type*} :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset ι) (a w : ι → ℂ) (r α : ℝ) (q : ℕ),
      0 < r → 0 < α → α ≤ 1 → (q : ℝ) * α = 1 / 2 →
      ValueDistribution.proximity (fun z : ℂ => ∑ i ∈ S, w i / (z - a i) ^ q) ⊤ r ≤
        α⁻¹ * (Real.log (1 + K * r ^ (-(1 / 2 : ℝ)) * ∑ i ∈ S, ‖w i‖ ^ α) + 1) := by
  obtain ⟨K, hK, hbound⟩ := circle_weighted_poles_fractional_moment_bound (ι := ι)
  refine ⟨K, hK, fun S a w r α q hr hα hα1 hpow => ?_⟩
  apply circle_proximity_le_of_fractional_moment hα (by positivity)
  · exact (meromorphic_weighted_poles S a w q).meromorphicOn.circleIntegrable_posLog_norm
  · exact circleIntegrable_weighted_poles_fractional_moment S a w hr hα hα1 hpow
  · exact hbound S a w r α q hr hα hα1 hpow

end ModifiedCartan
#print axioms ModifiedCartan.circle_weighted_poles_fractional_moment_bound
#print axioms ModifiedCartan.circle_weighted_poles_proximity_bound

