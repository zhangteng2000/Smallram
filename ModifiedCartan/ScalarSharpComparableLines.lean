import ModifiedCartan.ScalarHorizontalRescale

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Sharp fixed-target approach on actual local segments, now in the
coordinates of the original comparable radii. Auxiliary to LaTeX `thm:A` (b). -/
theorem scalar_sharp_target_lines_at_comparable_radii
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) {a : ℕ → ℂ}
    (ha : ∀ ν, ‖a ν‖ = 1)
    (hpeak : ∀ ν, scalarPhaseCoefficient f m ((2 : ℝ) ^ ν) * (a ν) ^ m =
      (((Real.pi / 2) ^ 2 : ℝ) : ℂ))
    (hstep : Tendsto (fun ν => a (ν + 1) - a ν) atTop (𝓝 0))
    (q : ScalarDyadicPeakTargetData f a ρ)
    {n : ℕ → ℕ} (hn : Tendsto n atTop atTop)
    {c : ℕ → ℝ} (hc : ∀ ν, c ν ∈ Icc (1 : ℝ) 2) {c₀ : ℝ}
    (hc₀ : 0 < c₀) (hclim : Tendsto c atTop (𝓝 c₀))
    {a₀ : ℂ} (halim : Tendsto (fun ν => a (n ν)) atTop (𝓝 a₀))
    {κ κ₁ : ℝ} (hκ : 0 < κ) (hκ₁ : κ < κ₁) {z : ℂ}
    (hz : z ∈ scalarLevelChart a₀ ρ ((Real.pi / 2 : ℝ) : ℂ) (κ₁ / 2)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ ε₀ > 0,
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ y : ℕ → ℝ, ∃ C ≥ 0, ∀ᶠ ν in atTop,
        y ν ∈ Icc (z.im - 2 * ε) (z.im + 2 * ε) ∧
        ∀ t ∈ Icc (z.re - ε) (z.re + ε),
          ‖scalarCurveSphere f (((c (ns ν) * (2 : ℝ) ^ n (ns ν) : ℝ) : ℂ) *
            (⟨t, y ν⟩ : ℂ)) - scalarSphereValue q.target‖ ≤
            C * Real.exp (-κ * characteristic f (c (ns ν) * (2 : ℝ) ^ n (ns ν))) := by
  obtain ⟨K, _, ns, hns, ε₀, hε₀, hlines⟩ := scalar_sharp_local_target_lines
    f hlin htrans hsmall hρ hl hu hm ha hpeak hstep q hn hc hc₀ hclim halim hκ hκ₁ hz
  have hL : 0 < (2 : ℝ) ^ K := pow_pos (by norm_num) K
  refine ⟨ns, hns, ε₀ * (2 : ℝ) ^ K / 2, by positivity, ?_⟩
  intro ε hε hεbound
  have hef : 0 < 2 * ε / (2 : ℝ) ^ K := by positivity
  have hef0 : 2 * ε / (2 : ℝ) ^ K ≤ ε₀ := by
    apply (div_le_iff₀ hL).2
    linarith
  obtain ⟨y, C, hC, hy⟩ := hlines (2 * ε / (2 : ℝ) ^ K) hef hef0
  refine ⟨fun ν => y ν / (c (ns ν) / (2 : ℝ) ^ K), C, hC, ?_⟩
  filter_upwards [hy] with ν hν
  apply scalar_horizontal_target_rescale
    (F := fun w => ‖scalarCurveSphere f w - scalarSphereValue q.target‖)
    (b := (2 : ℝ) ^ n (ns ν)) (hc (ns ν)) hL hε.le hν.1
  intro t ht
  have he : (2 : ℝ) ^ K * (2 : ℝ) ^ n (ns ν) = (2 : ℝ) ^ (n (ns ν) + K) := by
    rw [pow_add, mul_comm]
  simpa only [he] using hν.2 t ht

end ModifiedCartan
#print axioms ModifiedCartan.scalar_sharp_target_lines_at_comparable_radii
