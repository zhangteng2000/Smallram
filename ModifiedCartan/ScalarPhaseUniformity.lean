import ModifiedCartan.ScalarPhaseSlowChange

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- The proved sequential slow change is uniform over all multipliers in [1,2]. -/
theorem scalarPhaseCoefficient_slow_change_uniform
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal)) {m : ℕ} (hm : ρ = (m : ℝ) / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ c ∈ Icc (1 : ℝ) 2,
      ‖scalarPhaseCoefficient f m (c * t) - scalarPhaseCoefficient f m t‖ < ε := by
  classical
  rw [eventually_atTop]
  by_contra h
  push_neg at h
  choose r hr c hc hbad using (fun ν : ℕ => h (ν : ℝ))
  have ht : Tendsto r atTop atTop := tendsto_atTop_mono hr tendsto_natCast_atTop_atTop
  have hh := scalarPhaseCoefficient_slow_change f hlin htrans hsmall hρ hl hu hm ht hc
  have hn : Tendsto
      (fun ν => ‖scalarPhaseCoefficient f m (c ν * r ν) - scalarPhaseCoefficient f m (r ν)‖)
      atTop (𝓝 0) := by simpa only [norm_zero] using hh.norm
  obtain ⟨ν, hν⟩ := (hn.eventually_lt_const hε).exists
  exact (not_lt_of_ge (hbad ν)) hν

end ModifiedCartan
#print axioms ModifiedCartan.scalarPhaseCoefficient_slow_change_uniform
