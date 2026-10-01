import ModifiedCartan.MeasureDilation
import Mathlib.Topology.UniformSpace.HeineCantor

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- A dilation by at least one does not enlarge pulled-back area. -/
theorem complex_dilation_map_restrict_le {c : ℝ} (hc : 1 ≤ c)
    {K J : Set ℂ} (hJ : MeasurableSet J)
    (hmap : MapsTo (fun z : ℂ => (c : ℂ) * z) K J) :
    (volume.restrict K).map (fun z : ℂ => (c : ℂ) * z) ≤ volume.restrict J := by
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hm : Measurable (fun z : ℂ => (c : ℂ) * z) := measurable_const.mul measurable_id
  have hfull : (volume : Measure ℂ).map (fun z => (c : ℂ) * z) ≤ volume := by
    have he := Measure.map_addHaar_smul (volume : Measure ℂ) hcpos.ne'
    simp only [Complex.real_smul] at he
    rw [he]
    have hcoef : ENNReal.ofReal (abs (c ^ Module.finrank ℝ ℂ)⁻¹) ≤ 1 := by
      have hinv : (c ^ Module.finrank ℝ ℂ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hc)
      simpa only [ENNReal.ofReal_one, abs_of_nonneg (inv_nonneg.mpr
        (pow_nonneg hcpos.le _))] using ENNReal.ofReal_le_ofReal hinv
    calc
      _ ≤ (1 : ℝ≥0∞) • (volume : Measure ℂ) := by
        intro S
        simp only [Measure.smul_apply, smul_eq_mul]
        gcongr
      _ = _ := one_smul _ _
  calc
    _ ≤ (volume.restrict ((fun z : ℂ => (c : ℂ) * z) ⁻¹' J)).map
        (fun z : ℂ => (c : ℂ) * z) :=
      Measure.map_mono (Measure.restrict_mono_set _ hmap) hm
    _ = ((volume : Measure ℂ).map (fun z : ℂ => (c : ℂ) * z)).restrict J :=
      (Measure.restrict_map hm hJ).symm
    _ ≤ _ := Measure.restrict_mono (Subset.rfl) hfull

theorem complex_real_dilation_mem_closedBall_two {c : ℝ} (hc : c ∈ Icc (1 : ℝ) 2)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    (c : ℂ) * z ∈ closedBall (0 : ℂ) 2 := by
  simp only [mem_closedBall, dist_zero_right] at hz ⊢
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith [hc.1] : 0 ≤ c)]
  calc
    c * ‖z‖ ≤ c * 1 := mul_le_mul_of_nonneg_left hz (by linarith [hc.1])
    _ ≤ 2 := by simpa using hc.2

/-- Variable dilations in [1,2] preserve vanishing local errors in measure. -/
theorem LocalMeasureConvergence.variable_dilate_zero
    {E : Type*} [SeminormedAddCommGroup E] {F : ℕ → ℂ → E}
    (h : LocalMeasureConvergence (ball (0 : ℂ) 4) F (fun _ => 0))
    {c : ℕ → ℝ} (hc : ∀ ν, c ν ∈ Icc (1 : ℝ) 2) :
    LocalMeasureConvergence (ball (0 : ℂ) 1)
      (fun ν z => F ν ((c ν : ℂ) * z)) (fun _ => 0) := by
  intro K hK hKU
  have hJ : closedBall (0 : ℂ) 2 ⊆ ball (0 : ℂ) 4 := closedBall_subset_ball (by norm_num)
  have hh := h (closedBall (0 : ℂ) 2) (isCompact_closedBall _ _) hJ
  rw [tendstoInMeasure_iff_norm] at hh ⊢
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hh ε hε)
    (fun _ => bot_le)
  intro ν
  have hm := complex_dilation_map_restrict_le (hc ν).1 measurableSet_closedBall
    (fun z hz => complex_real_dilation_mem_closedBall_two (hc ν)
      (ball_subset_closedBall (hKU hz)))
  have hνpos : 0 < c ν := by linarith [(hc ν).1]
  let e : ℂ ≃ᵐ ℂ := (Homeomorph.smul (isUnit_iff_ne_zero.mpr hνpos.ne').unit).toMeasurableEquiv
  have he : (e : ℂ → ℂ) = fun z => (c ν : ℂ) * z := by
    funext z
    simp [e, Complex.real_smul]
  have heq := e.map_apply (μ := volume.restrict K) {z | ε ≤ ‖F ν z - 0‖}
  rw [he] at heq
  change (volume.restrict K) ((fun z : ℂ => (c ν : ℂ) * z) ⁻¹' {z | ε ≤ ‖F ν z - 0‖}) ≤ _
  rw [← heq]
  exact hm {z | ε ≤ ‖F ν z - 0‖}

/-- Continuous profiles vary uniformly under convergent bounded dilations. -/
theorem continuousOn_variable_dilate_uniform {u : ℂ → ℝ}
    (hu : ContinuousOn u (ball (0 : ℂ) 4))
    {c : ℕ → ℝ} {c₀ : ℝ} (hc : ∀ ν, c ν ∈ Icc (1 : ℝ) 2)
    (hc₀ : c₀ ∈ Icc (1 : ℝ) 2) (hclim : Tendsto c atTop (𝓝 c₀)) :
    TendstoUniformlyOn (fun ν z => u ((c ν : ℂ) * z))
      (fun z => u ((c₀ : ℂ) * z)) atTop (closedBall (0 : ℂ) 1) := by
  let Φ : ℝ → ℂ → ℝ := fun a z => u ((a : ℂ) * z)
  have hΦ : ContinuousOn (Function.uncurry Φ)
      (Icc (1 : ℝ) 2 ×ˢ closedBall (0 : ℂ) 1) := by
    apply hu.comp ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd).continuousOn
    intro x hx
    exact closedBall_subset_ball (by norm_num : (2 : ℝ) < 4)
      (complex_real_dilation_mem_closedBall_two hx.1 hx.2)
  have huni := UniformContinuousOn.tendstoUniformlyOn (F := Φ)
    ((isCompact_Icc.prod (isCompact_closedBall (0 : ℂ) 1)).uniformContinuousOn_of_continuous hΦ) hc₀
  have hcw : Tendsto c atTop (𝓝[Icc (1 : ℝ) 2] c₀) :=
    by
      simpa only [nhdsWithin, inf_idem] using hclim.inf
        (show Tendsto c atTop (𝓟 (Icc (1 : ℝ) 2)) from
          tendsto_principal.mpr (Eventually.of_forall hc))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  exact hcw.eventually (Metric.tendstoUniformlyOn_iff.mp huni ε hε)

/-- Continuity of the limiting profile plus the area estimate handles genuinely
varying radii, without assuming pointwise convergence of the source sequence. -/
theorem LocalMeasureConvergence.variable_dilate {F : ℕ → ℂ → ℝ} {u : ℂ → ℝ}
    (h : LocalMeasureConvergence (ball (0 : ℂ) 4) F u)
    (hu : ContinuousOn u (ball (0 : ℂ) 4))
    {c : ℕ → ℝ} {c₀ : ℝ} (hc : ∀ ν, c ν ∈ Icc (1 : ℝ) 2)
    (hc₀ : c₀ ∈ Icc (1 : ℝ) 2) (hclim : Tendsto c atTop (𝓝 c₀)) :
    LocalMeasureConvergence (ball (0 : ℂ) 1)
      (fun ν z => F ν ((c ν : ℂ) * z)) (fun z => u ((c₀ : ℂ) * z)) := by
  have he : LocalMeasureConvergence (ball (0 : ℂ) 4) (fun ν z => F ν z - u z) (fun _ => 0) := by
    intro K hK hKU
    simpa only [tendstoInMeasure_iff_norm, sub_zero] using h K hK hKU
  have hz := he.variable_dilate_zero hc
  have hucomp := uniformlyOn_localMeasureConvergence
    (continuousOn_variable_dilate_uniform hu hc hc₀ hclim) ball_subset_closedBall
  simpa only [sub_add_cancel, zero_add] using hz.add hucomp

end ModifiedCartan
#print axioms ModifiedCartan.complex_dilation_map_restrict_le
#print axioms ModifiedCartan.LocalMeasureConvergence.variable_dilate_zero
#print axioms ModifiedCartan.continuousOn_variable_dilate_uniform
#print axioms ModifiedCartan.LocalMeasureConvergence.variable_dilate



