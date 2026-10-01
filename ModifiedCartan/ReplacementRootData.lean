import ModifiedCartan.SeparatingRadius

open scoped Topology ENNReal BigOperators Classical
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- Root data for `lem:replacement`, with genuine strict separating circles
and sums over the actual polynomial roots, counting multiplicity. -/
theorem replacement_root_data (P R : ℕ → Polynomial ℂ)
    (hP : ∀ ν, (P ν).Monic) {s : ℕ → ℝ} (hs : Tendsto s atTop atTop)
    (hm : Tendsto (fun ν => ((P ν).natDegree : ℝ) / s ν) atTop (𝓝 0))
    {L : ℝ}
    (hR : ∀ᶠ ν in atTop, R ν ≠ 0 ∧ ((R ν).natDegree : ℝ) ≤ L * s ν)
    (herr : ∀ᶠ ν in atTop, ∀ z ∈ closedBall (0 : ℂ) 12,
      ‖(R ν).eval z - (P ν).eval z‖ ≤ 1 / 2) :
    ∃ (a : (ν : ℕ) → Fin (R ν).natDegree → ℂ) (η : ℕ → ℝ),
      (∀ ν, 8 < η ν ∧ η ν < 10 ∧ (∀ i, ‖a ν i‖ ≠ η ν) ∧
        ∀ z, (P ν).eval z = 0 → ‖z‖ ≠ η ν) ∧
      (∀ᶠ ν in atTop, normalize (R ν) = ∏ i, (Polynomial.X - Polynomial.C (a ν i))) ∧
      Tendsto (fun ν => (∑ᶠ z : ℂ, ((MeromorphicOn.divisor (fun w => (R ν).eval w)
        (ball 0 (η ν))) z : ℝ)) / s ν) atTop (𝓝 0) ∧
      Tendsto (fun ν => eLpNorm
        (fun z => reciprocalDistanceSum (Finset.univ.filter (fun i => ‖a ν i‖ < η ν)) (a ν) z / s ν)
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (ball 0 6))) atTop (𝓝 0) ∧
      LocalMeasureConvergence (ball (0 : ℂ) 6)
        (fun ν z => reciprocalDistanceSum (Finset.univ.filter (fun i => ‖a ν i‖ < η ν)) (a ν) z / s ν)
        (fun _ => (0 : ℝ)) ∧
      (∀ᶠ ν in atTop, ∀ z ∈ ball (0 : ℂ) 6,
        reciprocalDistanceSum (Finset.univ.filter (fun i => η ν < ‖a ν i‖)) (a ν) z / s ν ≤ L / 2) := by
  obtain ⟨a, ha⟩ := exists_eventual_normalized_root_lists R (hR.mono (fun _ h => h.1))
  choose η hη using fun ν => exists_separating_radius_root_indices (a ν)
    ((P ν).roots.toFinset.image (fun z => ‖z‖))
  have hin (ν : ℕ) : Finset.univ.filter (fun i => ‖a ν i‖ < η ν) = interiorRootIndices (a ν) :=
    (hη ν).2.2.2.1
  have hout (ν : ℕ) : Finset.univ.filter (fun i => η ν < ‖a ν i‖) = exteriorRootIndices (a ν) :=
    (hη ν).2.2.2.2.1
  have hcount := polynomial_approximation_root_count_tendsto_zero P R hP a ha hs hm herr
  have hain (ν : ℕ) (i : Fin (R ν).natDegree) (hi : i ∈ interiorRootIndices (a ν)) :
      ‖a ν i‖ ≤ 8 := (Finset.mem_filter.mp hi).2
  refine ⟨a, η, ?_, ha, ?_, ?_, ?_, ?_⟩
  · intro ν
    refine ⟨(hη ν).1, (hη ν).2.1, (hη ν).2.2.1, ?_⟩
    intro z hz
    apply (hη ν).2.2.2.2.2 ‖z‖
    exact Finset.mem_image.mpr ⟨z, Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots (hP ν).ne_zero).mpr hz), rfl⟩
  · apply (tendsto_congr' _).mpr hcount
    filter_upwards [ha] with ν haν
    rw [polynomial_root_list_count (R ν) (a ν) haν]
    simp only [mem_ball, dist_zero_right, hin ν, interiorRootIndices]
  · simpa only [hin] using inner_root_sum_eLpNorm_tendsto_zero
      (fun ν => interiorRootIndices (a ν)) a hain hs hcount (by norm_num) (by norm_num)
  · simpa only [hin] using inner_root_sum_localMeasure_zero
      (fun ν => interiorRootIndices (a ν)) a hain hs hcount
  · filter_upwards [hR, hs.eventually_gt_atTop 0] with ν hν hsν z hz
    rw [hout]
    exact exterior_root_sum_scaled_le (a ν) hsν hν.2 hz

end
end ModifiedCartan
#print axioms ModifiedCartan.replacement_root_data
