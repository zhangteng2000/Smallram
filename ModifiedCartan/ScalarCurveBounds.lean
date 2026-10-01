import ModifiedCartan.EuclideanJensen

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem scalar_circle_log_le_curve_mean {n : ℕ} (f : Curve n)
    {H : ℂ → ℂ} (hH : Differentiable ℂ H) (hHnonzero : ∃ z, H z ≠ 0)
    {C r : ℝ} (hC : 0 < C) (hbound : ∀ z, ‖H z‖ ≤ C * euclideanNorm (f.vector z))
    (hr : 0 < r) :
    Real.circleAverage (fun z => Real.log ‖H z‖) 0 r ≤
      Real.log C + Real.circleAverage (fun z => Real.log (euclideanNorm (f.vector z))) 0 r := by
  classical
  let U := fun z => C * euclideanNorm (f.vector z)
  have hUc : Continuous U := continuous_const.mul
    (euclideanNorm_continuous.comp (continuous_pi (fun j => (f.holomorphic j).continuous)))
  have hUp : ∀ z, 0 < U z := fun z => mul_pos hC (euclideanNorm_pos (f.vector_ne_zero z))
  have hA := Complex.analyticOnNhd_univ_iff_differentiable.mpr hH
  obtain ⟨b, hb⟩ := hHnonzero
  have hn : ∀ᶠ z in codiscrete ℂ, H z ≠ 0 := hA.preimage_zero_mem_codiscrete hb
  have hns : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |r|), H z ≠ 0 :=
    hn.filter_mono (Filter.codiscreteWithin_mono (Set.subset_univ _))
  let v := fun z => if H z = 0 then Real.log (U z) else Real.log ‖H z‖
  have heq : v =ᶠ[codiscreteWithin (sphere (0 : ℂ) |r|)] (fun z => Real.log ‖H z‖) := by
    filter_upwards [hns] with z hz
    simp only [v, hz, if_false]
  have hint : CircleIntegrable (fun z => Real.log ‖H z‖) 0 r :=
    (hA.meromorphicOn.mono_set (Set.subset_univ _)).circleIntegrable_log_norm
  have hvint : CircleIntegrable v 0 r := CircleIntegrable.congr_codiscreteWithin heq.symm hint
  have hUint : CircleIntegrable (fun z => Real.log (U z)) 0 r :=
    (hUc.log (fun z => (hUp z).ne')).continuousOn.circleIntegrable'
  have hmean := Real.circleAverage_mono hvint hUint (by
    intro z _
    by_cases hz : H z = 0
    · simp only [v, hz, if_true, le_refl]
    · simpa only [v, hz, if_false] using Real.log_le_log (norm_pos_iff.mpr hz) (hbound z))
  rw [Real.circleAverage_congr_codiscreteWithin heq hr.ne'] at hmean
  have hlog : (fun z => Real.log (U z)) =
      (fun z => Real.log C + Real.log (euclideanNorm (f.vector z))) := by
    funext z
    exact Real.log_mul hC.ne' (euclideanNorm_pos (f.vector_ne_zero z)).ne'
  rw [hlog, Real.circleAverage_fun_add (circleIntegrable_const _ _ _)
    (curve_log_euclideanNorm_continuous f).continuousOn.circleIntegrable',
    Real.circleAverage_const] at hmean
  exact hmean

theorem hasPolynomialRepresentation_of_proportional_coordinates {n : ℕ} (f : Curve n)
    (hprop : ∀ z j k, f.coord j 0 * f.coord k z = f.coord k 0 * f.coord j z) :
    f.HasPolynomialRepresentation := by
  obtain ⟨j, hj⟩ := f.reduced 0
  have hjnz : ∀ z, f.coord j z ≠ 0 := by
    intro z hz
    obtain ⟨k, hk⟩ := f.reduced z
    have he := hprop z j k
    rw [hz, mul_zero] at he
    exact hk ((mul_eq_zero.mp he).resolve_left hj)
  refine ⟨fun k => Polynomial.C (f.coord k 0), fun z => f.coord j z / f.coord j 0,
    fun z => div_ne_zero (hjnz z) hj, (f.holomorphic j).div_const _, ?_⟩
  intro k z
  simp only [Polynomial.eval_C]
  field_simp
  simpa only [mul_comm] using hprop z j k

theorem exists_scalar_zero_of_transcendental {n : ℕ} (f : Curve n)
    (htrans : f.Transcendental) :
    ∃ (H : ℂ → ℂ) (C : ℝ), Differentiable ℂ H ∧ (∃ z, H z ≠ 0) ∧
      H 0 = 0 ∧ 0 < C ∧ ∀ z, ‖H z‖ ≤ C * euclideanNorm (f.vector z) := by
  have hnon : ∃ z j k, f.coord j 0 * f.coord k z ≠ f.coord k 0 * f.coord j z := by
    by_contra he
    push Not at he
    exact htrans (hasPolynomialRepresentation_of_proportional_coordinates f he)
  obtain ⟨b, j, k, hb⟩ := hnon
  let H := fun z => f.coord j 0 * f.coord k z - f.coord k 0 * f.coord j z
  let C := ‖f.coord j 0‖ + ‖f.coord k 0‖ + 1
  refine ⟨H, C, ((f.holomorphic k).const_mul _).sub ((f.holomorphic j).const_mul _),
    ⟨b, sub_ne_zero.mpr hb⟩, ?_, by dsimp [C]; positivity, ?_⟩
  · dsimp only [H]
    ring
  · intro z
    have hjz : ‖f.coord j z‖ ≤ euclideanNorm (f.vector z) :=
      (norm_le_pi_norm (f.vector z) j).trans (norm_le_euclideanNorm _)
    have hkz : ‖f.coord k z‖ ≤ euclideanNorm (f.vector z) :=
      (norm_le_pi_norm (f.vector z) k).trans (norm_le_euclideanNorm _)
    calc
      ‖H z‖ ≤ ‖f.coord j 0 * f.coord k z‖ + ‖f.coord k 0 * f.coord j z‖ := norm_sub_le _ _
      _ = ‖f.coord j 0‖ * ‖f.coord k z‖ + ‖f.coord k 0‖ * ‖f.coord j z‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖f.coord j 0‖ * euclideanNorm (f.vector z) +
          ‖f.coord k 0‖ * euclideanNorm (f.vector z) := add_le_add
        (mul_le_mul_of_nonneg_left hkz (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hjz (norm_nonneg _))
      _ ≤ C * euclideanNorm (f.vector z) := by dsimp only [C]; nlinarith [euclideanNorm_nonneg (f.vector z)]

end
end ModifiedCartan
#print axioms ModifiedCartan.scalar_circle_log_le_curve_mean
#print axioms ModifiedCartan.exists_scalar_zero_of_transcendental
