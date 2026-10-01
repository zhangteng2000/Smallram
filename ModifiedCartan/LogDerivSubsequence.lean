import ModifiedCartan.AnalyticWeakGradient
import ModifiedCartan.GradientConvergence
import ModifiedCartan.LogLimitRepresentation

open scoped Topology ENNReal ContDiff
open Filter MeasureTheory Set Metric InnerProductSpace

set_option autoImplicit false

namespace ModifiedCartan

/-! First logarithmic derivative convergence along an actual zero-measure
subsequence, Step 1 of `lem:logderivlimit`. Both source and limit gradients
are identified by the proved weak identities and uniqueness, not assumed. -/

theorem LocalLpConvergence.logDeriv_subseq_on_ball
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {u : ℂ → ℝ} {g : ℂ → ℂ} {c : ℂ} {r R : ℝ}
    (hu : LocalLpConvergence 1 (ball c R) (fun n z => (s n)⁻¹ * Real.log ‖f n z‖) u)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) (closedBall c R))
    (hnonzero : ∀ n, ∃ b ∈ ball c R, f n b ≠ 0) (hs : ∀ n, 0 ≤ s n)
    (hr : 0 < r) (hrR : r < R) (hg : HasWeakComplexGradient (ball c r) u g) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ p : ℝ, 1 ≤ p → p < 2 →
      LocalLpConvergence (ENNReal.ofReal p) (ball c r)
        (fun n z => (s (ns n))⁻¹ • logDeriv (f (ns n)) z) g := by
  let ρ := (r + R) / 2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hrρ : r < ρ := by dsimp [ρ]; linarith
  have hρR : ρ < R := by dsimp [ρ]; linarith
  obtain ⟨χ, hχ, hχc, hχU, hχbound, hχone⟩ := exists_smooth_disk_cutoff c hρ hρR
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  obtain ⟨ν₀, ns, Hn, H, hns, hweak, hsupp, hHn, heq, hSmooth, hH, hAE, _, hD, _⟩ :=
    hu.log_limit_representation_on_ball hf hnonzero hs hrρ hρR.le hχ2 hχc hχU
      (fun z => (hχbound z).1) (fun z hz => hχone z (ball_subset_closedBall hz))
  let ν (n : ℕ) := localizedZeroMeasure (hf (ns n)) (s (ns n)) χ hχ2.continuous hχc
  have hHr (n : ℕ) : HarmonicOnNhd (Hn n) (ball c r) :=
    (hHn n).mono (ball_subset_ball hrρ.le)
  have hsource (n : ℕ) : HasWeakComplexGradient (ball c r)
      (fun z => (s (ns n))⁻¹ * Real.log ‖f (ns n) z‖)
      (fun z => (s (ns n))⁻¹ • logDeriv (f (ns n)) z) := by
    obtain ⟨b, hb, hb0⟩ := hnonzero (ns n)
    exact ((logNorm_hasWeakComplexGradient_on_ball (hf (ns n)) hb hb0).restrict
      (ball_subset_ball hrR.le)).const_mul _
  have hdec (n : ℕ) : HasWeakComplexGradient (ball c r)
      (fun z => (s (ns n))⁻¹ * Real.log ‖f (ns n) z‖)
      (cauchyTransform (ν n) + classicalComplexGradient (Hn n)) := by
    have hv := logPotential_hasWeakComplexGradient (ν n : Measure ℂ) hχc
      (localizedZeroMeasure_ae_mem (hf (ns n)) (s (ns n)) hχ2.continuous hχc) (ball c r)
    have hh := contDiffOn_hasWeakComplexGradient isOpen_ball ((hHr n).contDiffOn.of_le (by norm_num))
    exact (hv.add hh).congr_function_ae isOpen_ball ((heq n).symm.filter_mono
      (ae_mono (Measure.restrict_mono_set _ (ball_subset_ball hrρ.le))))
  have hdec₀ : HasWeakComplexGradient (ball c r) u
      (cauchyTransform ν₀ + classicalComplexGradient H) := by
    have hv := logPotential_hasWeakComplexGradient (ν₀ : Measure ℂ) hχc hsupp (ball c r)
    have hh := contDiff_hasWeakComplexGradient
      (hSmooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) (ball c r)
    exact (hv.add hh).congr_function_ae isOpen_ball hAE.symm
  refine ⟨ns, hns, ?_⟩
  intro p hp1 hp2
  have hv : LocalLpConvergence (ENNReal.ofReal p) (ball c r)
      (fun n => cauchyTransform (ν n)) (cauchyTransform ν₀) :=
    cauchyTransform_localLpConvergence hweak hp1 hp2 _
  have hh := harmonicGradient_localLpConvergence isOpen_ball hHr hH hD (ENNReal.ofReal p)
  exact (hv.add (ENNReal.one_le_ofReal.mpr hp1) hh).congr_ae
    (fun n => ((hsource n).unique isOpen_ball (hdec n)).symm) (hdec₀.unique isOpen_ball hg)



end ModifiedCartan


