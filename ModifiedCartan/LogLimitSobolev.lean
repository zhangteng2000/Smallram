import ModifiedCartan.LogLimitRepresentation
import ModifiedCartan.WeakGradientCalculus

open scoped Topology ENNReal ContDiff
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

/-! Local Sobolev regularity in `lem:logderivlimit`, derived from the constructed
logarithmic-potential plus harmonic limit representation on disks. -/

theorem LocalLpConvergence.log_limit_memW1pLoc_on_ball
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {u : ℂ → ℝ} {c : ℂ} {r R p : ℝ}
    (hu : LocalLpConvergence 1 (ball c R) (fun n z => (s n)⁻¹ * Real.log ‖f n z‖) u)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) (closedBall c R))
    (hnonzero : ∀ n, ∃ b ∈ ball c R, f n b ≠ 0) (hs : ∀ n, 0 ≤ s n)
    (hr : 0 < r) (hrR : r < R) (hp1 : 1 ≤ p) (hp2 : p < 2) :
    MemW1pLoc (ENNReal.ofReal p) (ball c r) u := by
  obtain ⟨ν, S, H, hS, _, hsupp, hH, _, hAE⟩ :=
    hu.exists_log_potential_harmonic_on_ball hf hnonzero hs hr hrR
  have hV := logPotential_memW1pLoc (ν : Measure ℂ) hp1 hp2 hS hsupp (ball c r)
  have hH₁ : ContDiff ℝ 1 H := hH.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)
  exact (hV.add (contDiff_memW1pLoc hH₁ _ _)).congr_ae isOpen_ball hAE.symm



end ModifiedCartan


