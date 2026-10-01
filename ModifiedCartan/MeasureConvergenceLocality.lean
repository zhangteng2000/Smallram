import ModifiedCartan.MeasureConvergenceAlgebra
import ModifiedCartan.HarmonicComplexDerivatives

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

/-! Locality, subsequence criteria, and vanishing rescaled continuous remainders in measure, supporting `eq:higher-logderiv-measure`. -/

theorem tendstoInMeasure_of_finite_cover {E ι : Type*} [PseudoEMetricSpace E] [Fintype ι]
    {K : Set ℂ} {V : ι → Set ℂ} (hcover : K ⊆ ⋃ i, V i)
    {f : ℕ → ℂ → E} {g : ℂ → E}
    (h : ∀ i, TendstoInMeasure (volume.restrict (V i)) f atTop g) :
    TendstoInMeasure (volume.restrict K) f atTop g := by
  intro ε hε
  have hlim := tendsto_finsetSum Finset.univ (fun i _ => h i ε hε)
  simp only [Finset.sum_const_zero] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
  intro n
  have hm : volume.restrict K ≤ Measure.sum (fun i => volume.restrict (V i)) :=
    (Measure.restrict_mono_set _ hcover).trans Measure.restrict_iUnion_le
  simpa only [Measure.sum_fintype, Measure.finsetSum_apply] using hm {x | ε ≤ edist (f n x) (g x)}

theorem localMeasureConvergence_of_locally {E : Type*} [PseudoEMetricSpace E]
    {U : Set ℂ} {f : ℕ → ℂ → E} {g : ℂ → E}
    (hlocal : ∀ x ∈ U, ∃ V, IsOpen V ∧ x ∈ V ∧ LocalMeasureConvergence V f g) :
    LocalMeasureConvergence U f g := by
  intro K hK hKU
  have hsmall (x : K) : ∃ r > 0,
      TendstoInMeasure (volume.restrict (closedBall (x : ℂ) r)) f atTop g := by
    obtain ⟨V, hV, hxV, hlim⟩ := hlocal x (hKU x.2)
    obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hV x hxV
    exact ⟨ε / 2, half_pos hε, hlim _ (isCompact_closedBall _ _)
      ((closedBall_subset_ball (half_lt_self hε)).trans hεV)⟩
  choose r hr hlim using hsmall
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover (fun x : K => ball (x : ℂ) (r x))
    (fun _ => isOpen_ball) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr _)⟩)
  have hcover : K ⊆ ⋃ i : S, closedBall ((i : K) : ℂ) (r i) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hS hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, ball_subset_closedBall hxi⟩
  exact tendstoInMeasure_of_finite_cover hcover (fun i : S => hlim i)

theorem localMeasureConvergence_of_subseq {E : Type*} [PseudoEMetricSpace E]
    {U : Set ℂ} {f : ℕ → ℂ → E} {g : ℂ → E}
    (h : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∃ ms : ℕ → ℕ,
      LocalMeasureConvergence U (fun n => f (ns (ms n))) g) :
    LocalMeasureConvergence U f g := by
  intro K hK hKU ε hε
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, hms⟩ := h ns hns
  exact ⟨ms, hms K hK hKU ε hε⟩

theorem tendstoInMeasure_of_uniform_on_compact {E : Type*} [NormedAddCommGroup E]
    {K : Set ℂ} (hK : IsCompact K) {f : ℕ → ℂ → E} {g : ℂ → E}
    (hf : ∀ n, ContinuousOn (f n) K) (h : TendstoUniformlyOn f g atTop K) :
    TendstoInMeasure (volume.restrict K) f atTop g := by
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  apply tendstoInMeasure_of_tendsto_ae (fun n => (hf n).aestronglyMeasurable hK.measurableSet)
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  exact h.tendsto_at hz

theorem uniform_diverging_scale_tendstoInMeasure {K : Set ℂ} (hK : IsCompact K)
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ} (hf : ∀ n, ContinuousOn (f n) K)
    (h : TendstoUniformlyOn f g atTop K) {s : ℕ → ℝ} (hs : Tendsto s atTop atTop)
    {j : ℕ} (hj : 0 < j) :
    TendstoInMeasure (volume.restrict K) (fun n z => f n z / (s n : ℂ) ^ j) atTop (fun _ => 0) := by
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  have hscalar : Tendsto (fun n => ((s n : ℂ)⁻¹) ^ j) atTop (𝓝 0) := by
    have hi : Tendsto (fun n => (s n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hs
    simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_zero, zero_pow hj.ne'] using
      ((Complex.continuous_ofReal.tendsto 0).comp hi).pow j
  have hscalarM : TendstoInMeasure (volume.restrict K)
      (fun n (_ : ℂ) => ((s n : ℂ)⁻¹) ^ j) atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (Eventually.of_forall (fun _ => hscalar))
  have hprod := tendstoInMeasure_continuous_map₂
    (fun n => (hf n).aestronglyMeasurable hK.measurableSet)
    (fun _ => aestronglyMeasurable_const) (tendstoInMeasure_of_uniform_on_compact hK hf h)
    hscalarM (Φ := fun x : ℂ × ℂ => x.1 * x.2) (by fun_prop)
  simpa only [mul_zero, div_eq_mul_inv, inv_pow] using hprod


end ModifiedCartan

