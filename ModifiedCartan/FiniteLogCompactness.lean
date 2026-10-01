import ModifiedCartan.NormalizedLogCompactness
import ModifiedCartan.FiniteSubsequenceExtraction

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem exists_common_normalized_log_subsequence {N : ℕ}
    {f : ℕ → Fin N → ℂ → ℂ} {s : ℕ → ℝ} {C : ℝ}
    (hf : ∀ ν j, AnalyticOnNhd ℂ (f ν j) (ball 0 4))
    (hf0 : ∀ ν j, f ν j 0 ≠ 0) (hs : ∀ ν, 0 < s ν)
    (hbound : ∀ ν j z, z ∈ ball (0 : ℂ) 4 → ‖f ν j z‖ ≤ Real.exp (C * s ν))
    (hcenter : ∀ j, Tendsto (fun ν => Real.log ‖f ν j 0‖ / s ν) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ u : Fin N → ℂ → ℝ,
      ∀ j, LocalLpConvergence 1 (ball (0 : ℂ) 4)
        (fun ν z => (s (ns ν))⁻¹ * Real.log ‖f (ns ν) j z‖) (u j) := by
  let P : Fin N → (ℕ → ℕ) → Prop := fun j ρ => ∃ u : ℂ → ℝ,
    LocalLpConvergence 1 (ball (0 : ℂ) 4)
      (fun ν z => (s (ρ ν))⁻¹ * Real.log ‖f (ρ ν) j z‖) u
  obtain ⟨ns, hns, hP⟩ := finite_subsequence_extraction N P (by
    intro j ρ hρ
    obtain ⟨σ, hσ, u, hu⟩ := exists_normalized_log_subsequence
      (fun ν => hf (ρ ν) j) (fun ν => hf0 (ρ ν) j) (fun ν => hs (ρ ν))
      (fun ν => hbound (ρ ν) j) ((hcenter j).comp hρ.tendsto_atTop)
    exact ⟨σ, hσ, u, hu⟩) (by
    intro j ρ σ hP hσ
    obtain ⟨u, hu⟩ := hP
    exact ⟨u, hu.comp_tendsto hσ.tendsto_atTop⟩)
  choose u hu using hP
  exact ⟨ns, hns, u, hu⟩

/-- Finite-prefix removal and simultaneous logarithm compactness under
exactly the eventual bounds furnished by `prop:representation`. -/
theorem exists_common_normalized_log_subsequence_eventual {N : ℕ}
    {f : ℕ → Fin N → ℂ → ℂ} {s : ℕ → ℝ} {C : ℝ}
    (hs : Tendsto s atTop atTop)
    (hdata : ∀ᶠ ν in atTop, ∀ j, AnalyticOnNhd ℂ (f ν j) (ball 0 4) ∧
      f ν j 0 ≠ 0 ∧ ∀ z ∈ ball (0 : ℂ) 4, ‖f ν j z‖ ≤ Real.exp (C * s ν))
    (hcenter : ∀ j, Tendsto (fun ν => Real.log ‖f ν j 0‖ / s ν) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      (∀ ν, 0 < s (ns ν) ∧ ∀ j, AnalyticOnNhd ℂ (f (ns ν) j) (ball 0 4) ∧
        f (ns ν) j 0 ≠ 0 ∧ ∀ z ∈ ball (0 : ℂ) 4, ‖f (ns ν) j z‖ ≤ Real.exp (C * s (ns ν))) ∧
      ∃ u : Fin N → ℂ → ℝ, ∀ j, LocalLpConvergence 1 (ball (0 : ℂ) 4)
        (fun ν z => (s (ns ν))⁻¹ * Real.log ‖f (ns ν) j z‖) (u j) := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp ((hs.eventually_gt_atTop 0).and hdata)
  let ρ : ℕ → ℕ := fun ν => ν + M
  have hρ : StrictMono ρ := fun _ _ h => Nat.add_lt_add_right h M
  have hd (ν : ℕ) := hM (ρ ν) (by dsimp only [ρ]; omega)
  obtain ⟨σ, hσ, u, hu⟩ := exists_common_normalized_log_subsequence
    (fun ν j => (hd ν).2 j |>.1) (fun ν j => ((hd ν).2 j).2.1)
    (fun ν => (hd ν).1) (fun ν j => ((hd ν).2 j).2.2)
    (fun j => (hcenter j).comp hρ.tendsto_atTop)
  exact ⟨ρ ∘ σ, hρ.comp hσ, fun ν => hd (σ ν), u, hu⟩

end
end ModifiedCartan
#print axioms ModifiedCartan.exists_common_normalized_log_subsequence_eventual
