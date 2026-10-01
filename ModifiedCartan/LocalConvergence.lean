import ModifiedCartan.NormComparison
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set

open scoped Topology ENNReal
open Filter MeasureTheory Set

namespace ModifiedCartan

/-- Literal local Lp convergence on a complex domain, including local membership.
This definition supplies the meaning of local convergence in `lem:logderivlimit`;
it is not a substitute for that lemma's analytic conclusion. -/
structure LocalLpConvergence {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) (U : Set ℂ) (f : ℕ → ℂ → E) (u : ℂ → E) : Prop where
  source_mem : ∀ K, IsCompact K → K ⊆ U → ∀ ν, MemLp (f ν) p (volume.restrict K)
  limit_mem : ∀ K, IsCompact K → K ⊆ U → MemLp u p (volume.restrict K)
  tendsto : ∀ K, IsCompact K → K ⊆ U →
    Tendsto (fun ν => eLpNorm (f ν - u) p (volume.restrict K)) atTop (𝓝 0)

def LocalMeasureConvergence {E : Type*} [PseudoEMetricSpace E]
    (U : Set ℂ) (f : ℕ → ℂ → E) (u : ℂ → E) : Prop :=
  ∀ K, IsCompact K → K ⊆ U → TendstoInMeasure (volume.restrict K) f atTop u

theorem LocalLpConvergence.inMeasure {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} {U : Set ℂ} {f : ℕ → ℂ → E} {u : ℂ → E}
    (h : LocalLpConvergence p U f u) (hp : p ≠ 0) : LocalMeasureConvergence U f u := by
  intro K hK hKU
  exact tendstoInMeasure_of_tendsto_eLpNorm hp
    (fun ν => (h.source_mem K hK hKU ν).aestronglyMeasurable)
    (h.limit_mem K hK hKU).aestronglyMeasurable (h.tendsto K hK hKU)

theorem LocalLpConvergence.restrict {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} {U V : Set ℂ} {f : ℕ → ℂ → E} {u : ℂ → E}
    (h : LocalLpConvergence p U f u) (hVU : V ⊆ U) : LocalLpConvergence p V f u where
  source_mem K hK hKV := h.source_mem K hK (hKV.trans hVU)
  limit_mem K hK hKV := h.limit_mem K hK (hKV.trans hVU)
  tendsto K hK hKV := h.tendsto K hK (hKV.trans hVU)

theorem LocalLpConvergence.test_integral {U K : Set ℂ}
    {f : ℕ → ℂ → ℝ} {u φ : ℂ → ℝ} {C : ℝ}
    (h : LocalLpConvergence 1 U f u) (hK : IsCompact K) (hKU : K ⊆ U)
    (hφ : AEStronglyMeasurable φ (volume.restrict K))
    (hbound : ∀ᵐ z ∂volume.restrict K, ‖φ z‖ ≤ C) :
    Tendsto (fun ν => ∫ z in K, φ z * f ν z) atTop (𝓝 (∫ z in K, φ z * u z)) := by
  have hf : ∀ ν, Integrable (f ν) (volume.restrict K) :=
    fun ν => memLp_one_iff_integrable.mp (h.source_mem K hK hKU ν)
  have hu := memLp_one_iff_integrable.mp (h.limit_mem K hK hKU)
  apply tendsto_integral_of_L1' (fun z => φ z * u z)
    (hφ.mul hu.aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun ν => (hf ν).bdd_mul hφ hbound))
  have hlim : Tendsto
      (fun ν => ENNReal.ofReal C * eLpNorm (f ν - u) 1 (volume.restrict K)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul (h.tendsto K hK hKU)
      (Or.inr ENNReal.ofReal_ne_top : (0 : ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal C ≠ ⊤)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
  intro ν
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
  filter_upwards [hbound] with z hz
  simp only [Pi.sub_apply, ← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)

theorem LocalLpConvergence.compactlySupported_test_integral {U : Set ℂ}
    {f : ℕ → ℂ → ℝ} {u φ : ℂ → ℝ} (h : LocalLpConvergence 1 U f u)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    Tendsto (fun ν => ∫ z, φ z * f ν z) atTop (𝓝 (∫ z, φ z * u z)) := by
  obtain ⟨C, hC⟩ := hφc.exists_bound_of_continuous hφ
  have hlim := h.test_integral hφc hφU hφ.aestronglyMeasurable
    (Filter.Eventually.of_forall hC)
  have heq (v : ℂ → ℝ) : (∫ z in tsupport φ, φ z * v z) = ∫ z, φ z * v z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hzero : φ z = 0 := by
      by_contra hh
      exact hz (subset_closure hh)
    rw [hzero, zero_mul]
  simpa only [heq] using hlim

theorem LocalMeasureConvergence.exists_seq_tendsto_ae_on_compact
    {E : Type*} [PseudoEMetricSpace E] {U K : Set ℂ}
    {f : ℕ → ℂ → E} {u : ℂ → E}
    (h : LocalMeasureConvergence U f u) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ z ∂volume.restrict K, Tendsto (fun ν => f (ns ν) z) atTop (𝓝 (u z)) :=
  (h K hK hKU).exists_seq_tendsto_ae

end ModifiedCartan

