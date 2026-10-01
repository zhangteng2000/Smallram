import ModifiedCartan.MeasureSubsequence
import ModifiedCartan.LocalizedRepresentation
import ModifiedCartan.HarmonicInterior

open scoped Topology ENNReal ContDiff
open Filter MeasureTheory Set Metric InnerProductSpace

set_option autoImplicit false

namespace ModifiedCartan

/-! Local logarithmic-potential representation of normalized analytic log-modulus
limits, supporting `lem:logderivlimit`. Actual zero-counting measures give a weak
subsequence; their potentials converge in local L1, so the harmonic remainders
do too. The proved harmonic interior theorem constructs the limit representative.
The existential disk version chooses the cutoff and its support internally. -/

theorem LocalLpConvergence.log_limit_representation_on_ball
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {u : ℂ → ℝ} {c : ℂ} {r ρ R : ℝ}
    (hu : LocalLpConvergence 1 (ball c R) (fun n z => (s n)⁻¹ * Real.log ‖f n z‖) u)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) (closedBall c R))
    (hnonzero : ∀ n, ∃ b ∈ ball c R, f n b ≠ 0) (hs : ∀ n, 0 ≤ s n)
    (hrρ : r < ρ) (hρR : ρ ≤ R)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ ball c R) (hχ0 : ∀ a, 0 ≤ χ a)
    (hχρ : ∀ a ∈ ball c ρ, χ a = 1) :
    ∃ (ν₀ : FiniteMeasure ℂ) (ns : ℕ → ℕ) (Hn : ℕ → ℂ → ℝ) (H : ℂ → ℝ),
      StrictMono ns ∧
      Tendsto (fun n => localizedZeroMeasure (hf (ns n)) (s (ns n)) χ hχ.continuous hχc)
        atTop (𝓝 ν₀) ∧
      (∀ᵐ a ∂(ν₀ : Measure ℂ), a ∈ tsupport χ) ∧
      (∀ n, HarmonicOnNhd (Hn n) (ball c ρ)) ∧
      (∀ n, (fun z => (s (ns n))⁻¹ * Real.log ‖f (ns n) z‖) =ᵐ[volume.restrict (ball c ρ)]
        (fun z => logPotential (localizedZeroMeasure (hf (ns n)) (s (ns n)) χ hχ.continuous hχc) z + Hn n z)) ∧
      ContDiff ℝ ∞ H ∧ HarmonicOnNhd H (ball c r) ∧
      u =ᵐ[volume.restrict (ball c r)] (fun z => logPotential ν₀ z + H z) ∧
      TendstoUniformlyOn Hn H atTop (ball c r) ∧
      TendstoUniformlyOn (fun n => fderiv ℝ (Hn n)) (fderiv ℝ H) atTop (ball c r) ∧
      TendstoUniformlyOn (fun n => fderiv ℝ (fderiv ℝ (Hn n)))
        (fderiv ℝ (fderiv ℝ H)) atTop (ball c r) := by
  classical
  obtain ⟨ν₀, ns, hns, hweak, hsupp, hv, _⟩ :=
    hu.localizedZeroMeasure_potentials_subseq (Subset.refl _) hf hnonzero hs hχ hχc hχU hχ0
  have hex (n : ℕ) : ∃ H : ℂ → ℝ, HarmonicOnNhd H (ball c ρ) ∧
      (fun z => (s (ns n))⁻¹ * Real.log ‖f (ns n) z‖) =ᵐ[volume.restrict (ball c ρ)]
        (fun z => logPotential (localizedZeroMeasure (hf (ns n)) (s (ns n)) χ hχ.continuous hχc) z + H z) := by
    obtain ⟨b, hb, hb0⟩ := hnonzero (ns n)
    exact logNorm_eq_localized_potential_add_harmonic (hf (ns n)) hb hb0 (hs (ns n))
      hχ.continuous hχc hχ0 (ball_subset_ball hρR) hχρ
  choose Hn hHn heq using hex
  have hsub := ((hu.comp_strictMono hns).sub le_rfl hv).restrict (ball_subset_ball hρR)
  have hrem : LocalLpConvergence 1 (ball c ρ) Hn (u - logPotential ν₀) := by
    apply hsub.congr_ae _ (EventuallyEq.rfl)
    intro n
    filter_upwards [heq n] with z hz
    change (s (ns n))⁻¹ * Real.log ‖f (ns n) z‖ -
      logPotential (localizedZeroMeasure (hf (ns n)) (s (ns n)) χ hχ.continuous hχc) z = Hn n z
    rw [hz]
    ring
  obtain ⟨H, hSmooth, hHarm, hAE, hUnif, hUnif₁, hUnif₂⟩ :=
    hrem.harmonic_representative_on_ball hrρ hHn
  refine ⟨ν₀, ns, Hn, H, hns, hweak, hsupp, hHn, heq, hSmooth, hHarm, ?_, hUnif, hUnif₁, hUnif₂⟩
  filter_upwards [hAE] with z hz
  change u z - logPotential ν₀ z = H z at hz
  linarith


theorem LocalLpConvergence.exists_log_potential_harmonic_on_ball
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {u : ℂ → ℝ} {c : ℂ} {r R : ℝ}
    (hu : LocalLpConvergence 1 (ball c R) (fun n z => (s n)⁻¹ * Real.log ‖f n z‖) u)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) (closedBall c R))
    (hnonzero : ∀ n, ∃ b ∈ ball c R, f n b ≠ 0) (hs : ∀ n, 0 ≤ s n)
    (hr : 0 < r) (hrR : r < R) :
    ∃ (ν : FiniteMeasure ℂ) (S : Set ℂ) (H : ℂ → ℝ), IsCompact S ∧ S ⊆ ball c R ∧
      (∀ᵐ a ∂(ν : Measure ℂ), a ∈ S) ∧ ContDiff ℝ ∞ H ∧ HarmonicOnNhd H (ball c r) ∧
      u =ᵐ[volume.restrict (ball c r)] (fun z => logPotential ν z + H z) := by
  let ρ := (r + R) / 2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hrρ : r < ρ := by dsimp [ρ]; linarith
  have hρR : ρ < R := by dsimp [ρ]; linarith
  obtain ⟨χ, hχ, hχc, hχU, hχbound, hχone⟩ := exists_smooth_disk_cutoff c hρ hρR
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  obtain ⟨ν, _, _, H, _, _, hsupp, _, _, hSmooth, hHarm, hAE, _, _, _⟩ :=
    hu.log_limit_representation_on_ball hf hnonzero hs hrρ hρR.le hχ2 hχc hχU
      (fun z => (hχbound z).1) (fun z hz => hχone z (ball_subset_closedBall hz))
  exact ⟨ν, tsupport χ, H, hχc, hχU, hsupp, hSmooth, hHarm, hAE⟩


end ModifiedCartan
