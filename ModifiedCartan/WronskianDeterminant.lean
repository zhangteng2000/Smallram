import ModifiedCartan.ExtendedLogConvergence

open scoped Topology ENNReal
open Filter MeasureTheory Set

set_option autoImplicit false

namespace ModifiedCartan

noncomputable def normalizedWronskian (n : ℕ) (s : ℝ)
    (f : FewInflection.Index n → ℂ → ℂ) (z : ℂ) : ℂ :=
  Matrix.det (Matrix.of (fun i j : FewInflection.Index n =>
    iteratedDeriv (i : ℕ) (f j) z / ((s : ℂ) ^ (i : ℕ) * f j z)))

theorem normalizedWronskian_eq_div (n : ℕ) (s : ℝ)
    (f : FewInflection.Index n → ℂ → ℂ) (z : ℂ) :
    normalizedWronskian n s f z = FewInflection.wronskian n f z /
      ((s : ℂ) ^ (∑ i : FewInflection.Index n, (i : ℕ)) * ∏ j, f j z) := by
  classical
  unfold normalizedWronskian
  have heq : Matrix.of (fun i j : FewInflection.Index n =>
      iteratedDeriv (i : ℕ) (f j) z / ((s : ℂ) ^ (i : ℕ) * f j z)) =
      Matrix.of (fun i j : FewInflection.Index n => ((s : ℂ) ^ (i : ℕ))⁻¹ *
        ((f j z)⁻¹ * iteratedDeriv (i : ℕ) (f j) z)) := by
    funext i j
    simp only [Matrix.of_apply, div_eq_mul_inv, mul_inv_rev]
    ring
  have hcol := Matrix.det_mul_column (fun i : FewInflection.Index n => ((s : ℂ) ^ (i : ℕ))⁻¹)
    (Matrix.of (fun i j : FewInflection.Index n => (f j z)⁻¹ * iteratedDeriv (i : ℕ) (f j) z))
  have hrow := Matrix.det_mul_row (fun j : FewInflection.Index n => (f j z)⁻¹)
    (Matrix.of (fun i j : FewInflection.Index n => iteratedDeriv (i : ℕ) (f j) z))
  simp only [Matrix.of_apply] at hcol hrow
  rw [heq, hcol, hrow]
  simp only [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum]
  change ((s : ℂ) ^ (∑ i : FewInflection.Index n, (i : ℕ)))⁻¹ *
    ((∏ j, f j z)⁻¹ * FewInflection.wronskian n f z) = _
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem tendstoInMeasure_matrix_det {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    [DecidableEq ι] {μ : Measure A} [IsFiniteMeasure μ]
    {f : ι → ι → ℕ → A → ℂ} {g : ι → ι → A → ℂ}
    (hf : ∀ i j n, AEStronglyMeasurable (f i j n) μ)
    (h : ∀ i j, TendstoInMeasure μ (f i j) atTop (g i j)) :
    TendstoInMeasure μ (fun n x => Matrix.det (Matrix.of (fun i j => f i j n x)))
      atTop (fun x => Matrix.det (Matrix.of (fun i j => g i j x))) := by
  classical
  simp only [Matrix.det_apply', Matrix.of_apply]
  apply tendstoInMeasure_finsetSum
  · intro σ _ n
    exact (Finset.univ.aestronglyMeasurable_fun_prod (fun i _ => hf (σ i) i n)).const_mul _
  · intro σ _
    exact tendstoInMeasure_continuous_map
      (fun n => Finset.univ.aestronglyMeasurable_fun_prod (fun i _ => hf (σ i) i n))
      (tendstoInMeasure_finsetProd Finset.univ (fun i _ n => hf (σ i) i n)
        (fun i _ => h (σ i) i))
      (Φ := fun x : ℂ => ((Equiv.Perm.sign σ : ℤ) : ℂ) * x) (by fun_prop)

theorem normalized_derivative_aestronglyMeasurable {U K : Set ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hK : IsCompact K) (hKU : K ⊆ U) (j : ℕ) (s : ℝ) :
    AEStronglyMeasurable (fun z => iteratedDeriv j f z / ((s : ℂ) ^ j * f z))
      (volume.restrict K) := by
  have hm := ((analyticOnNhd_iteratedDeriv hf j).continuousOn.mono hKU).aestronglyMeasurable (μ := volume)
    hK.measurableSet
  have hm' := (hf.continuousOn.mono hKU).aestronglyMeasurable (μ := volume) hK.measurableSet
  exact (hm.aemeasurable.div (hm'.const_mul ((s : ℂ) ^ j)).aemeasurable).aestronglyMeasurable

theorem normalizedWronskian_aestronglyMeasurable {n : ℕ} {U K : Set ℂ}
    {f : FewInflection.Index n → ℂ → ℂ} (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hK : IsCompact K) (hKU : K ⊆ U) (s : ℝ) :
    AEStronglyMeasurable (normalizedWronskian n s f) (volume.restrict K) := by
  classical
  unfold normalizedWronskian
  simp only [Matrix.det_apply', Matrix.of_apply]
  exact Finset.univ.aestronglyMeasurable_fun_sum (fun σ _ =>
    (Finset.univ.aestronglyMeasurable_fun_prod (fun i _ =>
      normalized_derivative_aestronglyMeasurable (hf i) hK hKU (σ i : ℕ) s)).const_mul _)

theorem normalizedWronskian_localMeasure {n : ℕ} {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    {f : ℕ → FewInflection.Index n → ℂ → ℂ} {s : ℕ → ℝ}
    {v : FewInflection.Index n → ℂ → ℝ} {g : FewInflection.Index n → ℂ → ℂ}
    (hv : ∀ j, LocalLpConvergence 1 U (fun ν z => (s ν)⁻¹ * Real.log ‖f ν j z‖) (v j))
    (hf : ∀ ν j, AnalyticOnNhd ℂ (f ν j) U)
    (hnz : ∀ ν j, ∃ z ∈ U, f ν j z ≠ 0)
    (hs : Tendsto s atTop atTop) (hg : ∀ j, HasWeakComplexGradient U (v j) (g j)) :
    LocalMeasureConvergence U (fun ν => normalizedWronskian n (s ν) (f ν))
      (fun z => Matrix.det (Matrix.of (fun i j : FewInflection.Index n => g j z ^ (i : ℕ)))) := by
  intro K hK hKU
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  exact tendstoInMeasure_matrix_det
    (fun i j ν => normalized_derivative_aestronglyMeasurable (hf ν j) hK hKU (i : ℕ) (s ν))
    (fun i j => (hv j).iteratedDeriv_div_localMeasure hU hUc (fun ν => hf ν j)
      (fun ν => hnz ν j) hs (hg j) (i : ℕ) K hK hKU)


end ModifiedCartan

