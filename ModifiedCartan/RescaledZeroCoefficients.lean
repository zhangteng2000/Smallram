import ModifiedCartan.EventualCoefficientComparison
import ModifiedCartan.RescaledRepresentation

open scoped Topology BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem eventually_wronskian_ae_ne_zero_of_monic {n : ℕ} {U : Set ℂ}
    (hU : MeasurableSet U) {g : ℕ → Index n → ℂ → ℂ} {P : ℕ → Polynomial ℂ}
    (hd : ∀ᶠ ν in atTop, (P ν).Monic ∧
      ∀ z ∈ U, FewInflection.wronskian n (g ν) z = (P ν).eval z) :
    ∀ᶠ ν in atTop, ∀ᵐ z ∂volume.restrict U, FewInflection.wronskian n (g ν) z ≠ 0 := by
  filter_upwards [hd] with ν hν
  filter_upwards [ae_restrict_of_ae (monic_polynomial_eval_ne_zero_ae (P ν) hν.1),
    ae_restrict_mem hU] with z hz hzU
  rwa [hν.2 z hzU]

/-- The exact coefficient transfer in Step 2 of `prop:indices`, from the
original canonical peak coefficients to the fundamental operator of the
actual M9 representation. The last canonical coefficient is proved zero. -/
theorem rescaled_fundamental_coefficients_zero {n : ℕ} (f : Curve n)
    {t s : ℕ → ℝ} {H : ℕ → ℂ → ℂ} {P : ℕ → Polynomial ℂ} {C : ℝ}
    (ht : Tendsto t atTop atTop) (hs : Tendsto s atTop atTop)
    (hm : Tendsto (fun ν => ((P ν).natDegree : ℝ) / s ν) atTop (𝓝 0))
    (hd : ∀ᶠ ν in atTop, AnalyticOnNhd ℂ (H ν) (ball 0 64) ∧ (P ν).Monic ∧
      (∀ z ∈ ball (0 : ℂ) 32,
        FewInflection.wronskian n (rescaledRepresentation f (t ν) (H ν)) z = (P ν).eval z) ∧
      ∀ z ∈ ball (0 : ℂ) 32,
        euclideanNorm (fun j => rescaledRepresentation f (t ν) (H ν) j z) ≤ Real.exp (C * s ν))
    (hscaled : ∀ i : Fin n, LocalMeasureConvergence (ball (0 : ℂ) 4)
      (fun ν z => ((t ν / s ν : ℝ) : ℂ) ^ (n + 1 - i.val) *
        canonicalCoefficient n f.coord i.castSucc ((t ν : ℂ) * z)) (fun _ => 0)) :
    ∀ i : Index n, LocalMeasureConvergence (ball (0 : ℂ) 4)
      (fun ν z => FewInflection.fundamentalCoefficients n
        (rescaledRepresentation f (t ν) (H ν)) z i / (s ν : ℂ) ^ (n + 1 - i.val)) (fun _ => 0) := by
  have hall (i : Index n) : LocalMeasureConvergence (ball (0 : ℂ) 4)
      (fun ν z => ((t ν / s ν : ℝ) : ℂ) ^ (n + 1 - i.val) *
        canonicalCoefficient n f.coord i ((t ν : ℂ) * z)) (fun _ => 0) := by
    by_cases hi : i.val < n
    · let k : Fin n := ⟨i.val, hi⟩
      have he : k.castSucc = i := Fin.ext rfl
      simpa only [he] using hscaled k
    · have he : i = Fin.last n := Fin.ext (by change i.val = n; omega)
      subst i
      have hz (z : ℂ) : canonicalCoefficient n f.coord (Fin.last n) z = 0 :=
        canonicalCoefficient_last_eq_zero (fun j =>
          Complex.analyticOnNhd_univ_iff_differentiable.mpr (f.holomorphic j) z (mem_univ z))
      simpa only [hz, mul_zero] using
        (uniformlyOn_localMeasureConvergence
          (tendsto_const_nhds.tendstoUniformlyOn_const (ball (0 : ℂ) 4))
          (Subset.refl (ball (0 : ℂ) 4)) :
          LocalMeasureConvergence (ball (0 : ℂ) 4) (fun (_ : ℕ) (_ : ℂ) => (0 : ℂ)) (fun _ => 0))
  have hcan (i : Index n) : LocalMeasureConvergence (ball (0 : ℂ) 4)
      (fun ν z => canonicalCoefficient n (rescaledRepresentation f (t ν) (H ν)) i z /
        (s ν : ℂ) ^ (n + 1 - i.val)) (fun _ => 0) := by
    intro K hK hKU
    apply (hall i K hK hKU).congr' _ EventuallyEq.rfl
    filter_upwards [hd, ht.eventually_gt_atTop 0] with ν hν htν
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    rw [Paper.eq_canonical_coefficient_identification f htν
      (hν.1 z ((ball_subset_ball (by norm_num : (4 : ℝ) ≤ 64)) (hKU hz))) i]
    simp only [Complex.ofReal_div, div_pow]
    ring
  have hcomp := Paper.eq_gaugecomparison_eventual C
    (fun ν => rescaledRepresentation f (t ν) (H ν)) s P hs hm (by
      filter_upwards [hd] with ν hν
      refine ⟨fun j z hz => rescaledRepresentation_analyticAt f (t ν)
        (hν.1 z ((ball_subset_ball (by norm_num : (32 : ℝ) ≤ 64)) hz)) j,
        hν.2.1, hν.2.2.1, hν.2.2.2⟩)
  intro i
  have hsum := (hcan i).add (hcomp i).neg_zero
  convert! hsum using 1
  · funext ν z
    ring
  · funext z
    simp only [add_zero]

end ModifiedCartan
#print axioms ModifiedCartan.rescaled_fundamental_coefficients_zero
