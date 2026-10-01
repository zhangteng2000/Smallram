import ModifiedCartan.NegativeLogKernel
import ModifiedCartan.MonicPolynomialParameters

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan
noncomputable section

theorem integrable_negativeLogNorm_root_product {ι : Type*}
    (S : Finset ι) (a : ι → ℂ) :
    Integrable (fun z : ℂ => negativeLogNorm (∏ i ∈ S, (z - a i))) := by
  have hsum := integrable_finsetSum S (fun i _ => integrable_negativeLogNorm_sub (a i))
  apply hsum.mono'
  · apply measurable_negativeLogNorm.comp _ |>.aestronglyMeasurable
    fun_prop
  · filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (negativeLogNorm_nonneg _)]
    exact negativeLogNorm_prod_le S (fun i => z - a i)

theorem integral_negativeLogNorm_root_product_le {ι : Type*}
    (S : Finset ι) (a : ι → ℂ) :
    (∫ z : ℂ, negativeLogNorm (∏ i ∈ S, (z - a i))) ≤
      Real.pi * S.card / 2 := by
  calc
    _ ≤ ∫ z : ℂ, ∑ i ∈ S, negativeLogNorm (z - a i) :=
      integral_mono (integrable_negativeLogNorm_root_product S a)
        (integrable_finsetSum S (fun i _ => integrable_negativeLogNorm_sub (a i)))
        (fun z => negativeLogNorm_prod_le S (fun i => z - a i))
    _ = ∑ i ∈ S, ∫ z : ℂ, negativeLogNorm (z - a i) :=
      integral_finsetSum S (fun i _ => integrable_negativeLogNorm_sub (a i))
    _ = _ := by simp only [integral_negativeLogNorm_sub, Finset.sum_const,
      nsmul_eq_mul]; ring

theorem monic_polynomial_eval_root_product (P : Polynomial ℂ) (hP : P.Monic) :
    ∃ a : Fin P.natDegree → ℂ, ∀ z, P.eval z = ∏ i, (z - a i) := by
  obtain ⟨a, ha⟩ := complex_monic_eq_prod_linear P hP rfl
  refine ⟨fun i => -a i, ?_⟩
  intro z
  calc
    _ = Polynomial.eval z (∏ i, (Polynomial.X + Polynomial.C (a i))) :=
      congrArg (Polynomial.eval z) ha
    _ = _ := by rw [Polynomial.eval_prod]; simp

theorem integrable_negativeLogNorm_monic (P : Polynomial ℂ) (hP : P.Monic) :
    Integrable (fun z : ℂ => negativeLogNorm (P.eval z)) := by
  obtain ⟨a, ha⟩ := monic_polynomial_eval_root_product P hP
  simp_rw [ha]
  exact integrable_negativeLogNorm_root_product Finset.univ a

theorem integral_negativeLogNorm_monic_le (P : Polynomial ℂ) (hP : P.Monic) :
    (∫ z : ℂ, negativeLogNorm (P.eval z)) ≤ Real.pi * P.natDegree / 2 := by
  obtain ⟨a, ha⟩ := monic_polynomial_eval_root_product P hP
  simp_rw [ha]
  simpa only [Finset.card_univ, Fintype.card_fin] using
    integral_negativeLogNorm_root_product_le Finset.univ a

namespace Paper

/-- LaTeX `eq:polynomial-negative-area`. The estimate holds on every set,
in particular the manuscript's disk of radius twelve. -/
theorem eq_polynomial_negative_area (P : Polynomial ℂ) (hP : P.Monic)
    (K : Set ℂ) :
    (∫ z in K, negativeLogNorm (P.eval z)) ≤ Real.pi * P.natDegree / 2 :=
  (setIntegral_le_integral (integrable_negativeLogNorm_monic P hP)
    (Eventually.of_forall (fun z => negativeLogNorm_nonneg (P.eval z)))).trans
    (integral_negativeLogNorm_monic_le P hP)

end Paper

theorem monic_polynomial_small_value_area_le (P : Polynomial ℂ) (hP : P.Monic)
    {t : ℝ} (ht : 0 < t) (K : Set ℂ) :
    volume {z : ℂ | z ∈ K ∧ ‖P.eval z‖ < Real.exp (-t)} ≤
      ENNReal.ofReal (Real.pi * P.natDegree / (2 * t)) := by
  have hroot : ∀ᵐ z : ℂ, P.eval z ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not, Polynomial.IsRoot] using
      (Polynomial.finite_setOfPred_isRoot hP.ne_zero).measure_zero (volume : Measure ℂ)
  have hi := (integrable_negativeLogNorm_monic P hP).div_const t
  calc
    volume {z : ℂ | z ∈ K ∧ ‖P.eval z‖ < Real.exp (-t)} ≤
        volume {z : ℂ | 1 ≤ negativeLogNorm (P.eval z) / t} := by
      apply measure_mono_ae
      filter_upwards [hroot] with z hz
      intro hsmall
      apply (le_div_iff₀ ht).mpr
      have hlog := (Real.log_lt_iff_lt_exp (norm_pos_iff.mpr hz)).mpr hsmall.2
      have hmax : -Real.log ‖P.eval z‖ ≤ negativeLogNorm (P.eval z) := le_max_right _ _
      linarith
    _ ≤ ENNReal.ofReal (∫ z : ℂ, negativeLogNorm (P.eval z) / t) :=
      hi.measure_le_integral
        (Eventually.of_forall (fun z => div_nonneg (negativeLogNorm_nonneg _) ht.le))
        (fun _ hz => hz)
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [integral_div]
      calc
        _ ≤ (Real.pi * P.natDegree / 2) / t :=
          div_le_div_of_nonneg_right (integral_negativeLogNorm_monic_le P hP) ht.le
        _ = _ := by ring

theorem monic_polynomial_small_value_area_tendsto_zero
    (P : ℕ → Polynomial ℂ) (hP : ∀ ν, (P ν).Monic)
    {s : ℕ → ℝ} (hs : Tendsto s atTop atTop)
    (hm : Tendsto (fun ν => ((P ν).natDegree : ℝ) / s ν) atTop (𝓝 0))
    (K : Set ℂ) :
    Tendsto (fun ν => volume {z : ℂ | z ∈ K ∧ ‖(P ν).eval z‖ < Real.exp (-s ν)})
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun ν => ENNReal.ofReal
      (Real.pi * (P ν).natDegree / (2 * s ν))) atTop (𝓝 0) := by
    have hmul : Tendsto (fun ν => (Real.pi / 2) *
        (((P ν).natDegree : ℝ) / s ν)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hm.const_mul (Real.pi / 2)
    have h := ENNReal.tendsto_ofReal hmul
    simp only [ENNReal.ofReal_zero] at h
    convert! h using 1
    funext ν
    congr 1
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [hs.eventually_gt_atTop 0] with ν hν
  exact monic_polynomial_small_value_area_le (P ν) (hP ν) hν K

end
end ModifiedCartan
