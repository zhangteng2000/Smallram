import ModifiedCartan.MeasureConvergenceAlgebra
import Mathlib.Topology.UniformSpace.UniformConvergence

open scoped Topology ENNReal
open Filter MeasureTheory Set
set_option autoImplicit false
namespace ModifiedCartan

theorem tendstoInMeasure_add {α E : Type*} [MeasurableSpace α]
    [SeminormedAddCommGroup E] {μ : Measure α}
    {f g : ℕ → α → E} {u v : α → E}
    (hf : TendstoInMeasure μ f atTop u) (hg : TendstoInMeasure μ g atTop v) :
    TendstoInMeasure μ (fun ν x => f ν x + g ν x) atTop (fun x => u x + v x) := by
  rw [tendstoInMeasure_iff_norm] at hf hg ⊢
  intro ε hε
  have he : 0 < ε / 2 := by linarith
  have hlim := (hf (ε / 2) he).add (hg (ε / 2) he)
  simp only [add_zero] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
  intro ν
  apply (measure_mono (t := {x | ε / 2 ≤ ‖f ν x - u x‖} ∪
    {x | ε / 2 ≤ ‖g ν x - v x‖}) ?_).trans (measure_union_le _ _)
  intro x hx
  by_contra h
  simp only [mem_union, mem_setOf_eq, not_or, not_le] at h
  have htriangle : ‖f ν x + g ν x - (u x + v x)‖ ≤
      ‖f ν x - u x‖ + ‖g ν x - v x‖ := by
    convert! norm_add_le (f ν x - u x) (g ν x - v x) using 1 <;> abel
  change ε ≤ ‖f ν x + g ν x - (u x + v x)‖ at hx
  linarith

theorem LocalMeasureConvergence.add {E : Type*} [SeminormedAddCommGroup E]
    {U : Set ℂ} {f g : ℕ → ℂ → E} {u v : ℂ → E}
    (hf : LocalMeasureConvergence U f u) (hg : LocalMeasureConvergence U g v) :
    LocalMeasureConvergence U (fun ν z => f ν z + g ν z) (fun z => u z + v z) := by
  intro K hK hKU
  exact tendstoInMeasure_add (hf K hK hKU) (hg K hK hKU)

theorem LocalMeasureConvergence.mono {E : Type*} [PseudoEMetricSpace E]
    {U V : Set ℂ} {f : ℕ → ℂ → E} {u : ℂ → E}
    (h : LocalMeasureConvergence U f u) (hVU : V ⊆ U) :
    LocalMeasureConvergence V f u := fun K hK hKV => h K hK (hKV.trans hVU)

theorem LocalMeasureConvergence.comp {E : Type*} [PseudoEMetricSpace E]
    {U : Set ℂ} {f : ℕ → ℂ → E} {u : ℂ → E} {ns : ℕ → ℕ}
    (h : LocalMeasureConvergence U f u) (hns : Tendsto ns atTop atTop) :
    LocalMeasureConvergence U (fun ν => f (ns ν)) u := by
  intro K hK hKU
  exact (h K hK hKU).comp hns

theorem LocalMeasureConvergence.congr_ae {E : Type*} [PseudoEMetricSpace E]
    {U : Set ℂ} {f g : ℕ → ℂ → E} {u : ℂ → E}
    (h : LocalMeasureConvergence U f u) (he : ∀ᶠ ν in atTop, f ν =ᵐ[volume] g ν) :
    LocalMeasureConvergence U g u := by
  intro K hK hKU
  apply (h K hK hKU).congr' _ EventuallyEq.rfl
  filter_upwards [he] with ν hν
  exact hν.filter_mono (ae_mono Measure.restrict_le_self)

theorem tendstoInMeasure_zero_of_norm_le_norm {α E F : Type*} [MeasurableSpace α]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] {μ : Measure α}
    {f : ℕ → α → E} {g : ℕ → α → F}
    (hg : TendstoInMeasure μ g atTop (fun _ => 0))
    (hbound : ∀ᶠ ν in atTop, ∀ᵐ x ∂μ, ‖f ν x‖ ≤ ‖g ν x‖) :
    TendstoInMeasure μ f atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm] at hg ⊢
  intro ε hε
  have hlim := hg ε hε
  simp only [sub_zero] at hlim ⊢
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [hbound] with ν hν
  apply measure_mono_ae
  filter_upwards [hν] with x hx
  exact fun he => he.trans hx

theorem uniformlyOn_localMeasureConvergence {E : Type*} [SeminormedAddCommGroup E]
    {S U : Set ℂ} {f : ℕ → ℂ → E} {g : ℂ → E}
    (h : TendstoUniformlyOn f g atTop S) (hUS : U ⊆ S) :
    LocalMeasureConvergence U f g := by
  intro K hK hKU
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have he : ∀ᶠ ν in atTop,
      (volume.restrict K) {z | ε ≤ ‖f ν z - g z‖} = 0 := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp h ε hε] with ν hν
    apply measure_mono_null_ae (t := ∅) _ (measure_empty)
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    intro hbad
    have hn := hν z (hUS (hKU hz))
    rw [dist_comm, dist_eq_norm] at hn
    exact (not_le.mpr hn hbad).elim
  exact (tendsto_congr' he).mpr tendsto_const_nhds

theorem LocalMeasureConvergence.neg_zero {E : Type*} [SeminormedAddCommGroup E]
    {U : Set ℂ} {f : ℕ → ℂ → E}
    (h : LocalMeasureConvergence U f (fun _ => 0)) :
    LocalMeasureConvergence U (fun ν z => -f ν z) (fun _ => 0) := by
  intro K hK hKU
  apply tendstoInMeasure_zero_of_norm_le_norm (h K hK hKU)
  exact Eventually.of_forall (fun _ => Eventually.of_forall (fun _ => (norm_neg _).le))

theorem LocalMeasureConvergence.div_pow_scale_zero {U : Set ℂ} {f : ℕ → ℂ → ℂ}
    {s : ℕ → ℝ} (h : LocalMeasureConvergence U f (fun _ => 0))
    (hs : Tendsto s atTop atTop) (q : ℕ) :
    LocalMeasureConvergence U (fun ν z => f ν z / (s ν : ℂ) ^ q) (fun _ => 0) := by
  intro K hK hKU
  apply tendstoInMeasure_zero_of_norm_le_norm (h K hK hKU)
  filter_upwards [hs.eventually_ge_atTop 1] with ν hsν
  apply Eventually.of_forall
  intro z
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ s ν)]
  exact div_le_self (norm_nonneg _) (one_le_pow₀ hsν)

end ModifiedCartan
#print axioms ModifiedCartan.tendstoInMeasure_add
#print axioms ModifiedCartan.uniformlyOn_localMeasureConvergence
