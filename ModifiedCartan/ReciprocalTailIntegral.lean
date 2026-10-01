import ModifiedCartan.EnvelopeKernel

open scoped Topology BigOperators
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem reciprocal_cutoff_integral {R a : ℝ} (hR : 0 < R) (ha : R ≤ a) :
    IntegrableOn ((Ioi a).indicator (fun t : ℝ => t ^ (-2 : ℝ))) (Ioi R) ∧
      (∫ t in Ioi R, (Ioi a).indicator (fun t : ℝ => t ^ (-2 : ℝ)) t) = a⁻¹ := by
  have ha0 := hR.trans_le ha
  have hset : Ioi a ∩ Ioi R = Ioi a := by rw [Ioi_inter_Ioi, sup_eq_left.mpr ha]
  constructor
  · change Integrable _ (volume.restrict (Ioi R))
    rw [integrable_indicator_iff measurableSet_Ioi]
    change Integrable _ ((volume.restrict (Ioi R)).restrict (Ioi a))
    rw [Measure.restrict_restrict measurableSet_Ioi, hset]
    exact integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha0
  · rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      hset, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha0]
    norm_num
    exact Real.rpow_neg_one a

/-- Finite-sum form of the reciprocal-root tail estimate
`eq:reciprocal-tail`, before passing to the actual infinite divisor. -/
theorem finite_reciprocal_tail_bound {ι : Type*} (S : Finset ι) (a : ι → ℝ)
    {R C σ : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hσ : σ < 1)
    (ha : ∀ i ∈ S, R ≤ a i)
    (hc : ∀ t, R ≤ t → ((S.filter (fun i => a i ≤ t)).card : ℝ) ≤ C * t ^ σ) :
    ∑ i ∈ S, (a i)⁻¹ ≤ (C / (1 - σ)) * R ^ (σ - 1) := by
  classical
  let F : ℝ → ℝ := fun t => ∑ i ∈ S, (Ioi (a i)).indicator (fun u : ℝ => u ^ (-2 : ℝ)) t
  have hi (i : ι) (hi : i ∈ S) := reciprocal_cutoff_integral hR (ha i hi)
  have hF : IntegrableOn F (Ioi R) := by
    apply integrable_finsetSum
    intro i hi'
    exact (hi i hi').1
  have hFeq : (∫ t in Ioi R, F t) = ∑ i ∈ S, (a i)⁻¹ := by
    rw [integral_finsetSum S (fun i hi' => (hi i hi').1)]
    exact Finset.sum_congr rfl (fun i hi' => (hi i hi').2)
  have hmajorant : IntegrableOn (fun t : ℝ => C * t ^ (σ - 2)) (Ioi R) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : σ - 2 < -1) hR).const_mul C
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi R), F t ≤ C * t ^ (σ - 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 := hR.trans ht
    have hp : 0 ≤ t ^ (-2 : ℝ) := Real.rpow_nonneg ht0.le _
    calc
      F t ≤ ∑ i ∈ S, if a i ≤ t then t ^ (-2 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hit : a i < t
        · simp only [indicator_of_mem (show t ∈ Ioi (a i) from hit), ite_eq_left hit.le, le_refl]
        · rw [indicator_of_notMem (show t ∉ Ioi (a i) from hit)]
          split_ifs <;> positivity
      _ = ((S.filter (fun i => a i ≤ t)).card : ℝ) * t ^ (-2 : ℝ) := by
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (C * t ^ σ) * t ^ (-2 : ℝ) := mul_le_mul_of_nonneg_right (hc t ht.le) hp
      _ = C * t ^ (σ - 2) := by
        rw [show σ - 2 = σ + (-2) by ring, Real.rpow_add ht0]
        ring
  have hineq := integral_mono_ae hF hmajorant hbound
  rw [hFeq, integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : σ - 2 < -1) hR] at hineq
  exact hineq.trans_eq (by
    rw [show σ - 2 + 1 = σ - 1 by ring]
    calc
      C * (-R ^ (σ - 1) / (σ - 1)) = C * (R ^ (σ - 1) / (1 - σ)) := by
        rw [show 1 - σ = -(σ - 1) by ring, div_neg, neg_div]
      _ = _ := by ring)

end ModifiedCartan
#print axioms ModifiedCartan.finite_reciprocal_tail_bound
