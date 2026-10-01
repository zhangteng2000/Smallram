import ModifiedCartan.ScalarValueGluing

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- The quantitative sphere-value gluing theorem applies after any finite
initial segment, retaining an eventual exponential distance bound. -/
theorem scalarSphereImage_limit_of_eventually_exponential_steps
    {x : ℕ → ℂ × ℂ} (hx : ∀ ν, x ν ∈ scalarSphereImage) {s : ℕ → ℝ} {δ : ℝ}
    (hs : ∀ᶠ ν in atTop, Real.log 2 ≤ δ * (s (ν + 1) - s ν))
    (hstep : ∀ᶠ ν in atTop, ‖x ν - x (ν + 1)‖ ≤ Real.exp (-δ * s ν)) :
    ∃ b : WithTop ℂ, Tendsto x atTop (𝓝 (scalarSphereValue b)) ∧
      ∀ᶠ ν in atTop, ‖x ν - scalarSphereValue b‖ ≤ 2 * Real.exp (-δ * s ν) := by
  classical
  have he (ν : ℕ) : ∃ a : WithTop ℂ, scalarSphereValue a = x ν := by
    have hh := hx ν
    rw [scalarSphereImage_eq_range] at hh
    exact hh
  choose a ha using he
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hs.and hstep)
  obtain ⟨b, hb, hbound⟩ := scalarSphereValue_limit_of_exponential_steps
    (fun ν => a (ν + N))
    (s := fun ν => s (ν + N))
    (fun ν => by simpa only [Nat.add_right_comm] using (hN (ν + N) (Nat.le_add_left N ν)).1)
    (fun ν => by simpa only [ha, Nat.add_right_comm] using (hN (ν + N) (Nat.le_add_left N ν)).2)
  refine ⟨b, ?_, ?_⟩
  · apply (tendsto_add_atTop_iff_nat N).mp
    simpa only [ha] using hb
  · apply eventually_atTop.mpr
    refine ⟨N, fun ν hν => ?_⟩
    simpa only [ha, Nat.sub_add_cancel hν] using hbound (ν - N)

end ModifiedCartan
#print axioms ModifiedCartan.scalarSphereImage_limit_of_eventually_exponential_steps