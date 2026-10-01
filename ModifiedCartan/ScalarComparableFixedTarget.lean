import ModifiedCartan.ScalarComparableTargetBridge

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Comparable-radius anchors converge to the same fixed dyadic target with
one positive exponential rate on the actual characteristic scale. -/
theorem scalar_comparable_anchor_fixed_target
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) {a : ℕ → ℂ}
    (ha : ∀ ν, ‖a ν‖ = 1)
    (hpeak : ∀ ν, scalarPhaseCoefficient f m ((2 : ℝ) ^ ν) * (a ν) ^ m =
      (((Real.pi / 2) ^ 2 : ℝ) : ℂ))
    {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) {c y : ℕ → ℝ} {b : ℕ → ℂ}
    (hc : ∀ ν, c ν ∈ Icc (1 : ℝ) 2)
    (hbClose : Tendsto (fun ν => b ν - a (n ν)) atTop (𝓝 0))
    (q : ScalarDyadicPeakTargetData f a ρ)
    (hqRad : ∀ z : ℂ, ‖z‖ = 1 → ∀ t ∈ Icc (1 / 2 : ℝ) 1,
      closedBall ((t : ℂ) * z) (4 * q.width) ⊆ scalarFullSector z ρ)
    {δ : ℝ} (hδ : 0 < δ)
    (hH : ∀ᶠ ν in atTop, y ν ∈ Icc ((b ν).im - q.width) ((b ν).im + q.width) ∧
      ∀ t ∈ Icc ((b ν).re - q.width) ((b ν).re + q.width),
        (c ν * (2 : ℝ) ^ n ν) * scalarSphericalSpeed f.coord
          (((c ν * (2 : ℝ) ^ n ν : ℝ) : ℂ) * (⟨t, y ν⟩ : ℂ)) ≤
            Real.exp (-δ * characteristic f (c ν * (2 : ℝ) ^ n ν))) :
    ∃ η > 0, ∀ᶠ ν in atTop,
      ‖scalarCurveSphere f (((c ν * (2 : ℝ) ^ n ν : ℝ) : ℂ) *
          (⟨(b ν).re - q.width, y ν⟩ : ℂ)) - scalarSphereValue q.target‖ ≤
        Real.exp (-η * characteristic f (c ν * (2 : ℝ) ^ n ν)) := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hpow : Tendsto (fun ν : ℕ => (2 : ℝ) ^ ν) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hbase := hpow.comp hn
  have hscale := (characteristic_tendsto_atTop_of_transcendental f htrans).comp hbase
  have hex : ∃ η > 0, ∀ᶠ ν in atTop,
      ‖scalarCurveSphere f (((c ν * (2 : ℝ) ^ n ν : ℝ) : ℂ) *
          (⟨(b ν).re - q.width, y ν⟩ : ℂ)) - scalarSphereValue q.target‖ ≤
        Real.exp (-η * characteristic f ((2 : ℝ) ^ n ν)) := by
    apply exists_exponential_bound_of_subsequences hscale
    intro ns hns
    obtain ⟨c₀, hc₀, ms, hms, hcLim⟩ := (isCompact_Icc : IsCompact (Icc (1 : ℝ) 2)).tendsto_subseq
      (fun ν => hc (ns ν))
    obtain ⟨a₀, ha₀, ks, hks, haLim⟩ := (isCompact_sphere (0 : ℂ) 1).tendsto_subseq
      (fun ν => show a (n (ns (ms ν))) ∈ sphere (0 : ℂ) 1 by
        simpa only [mem_sphere, dist_zero_right] using ha (n (ns (ms ν))))
    let τ : ℕ → ℕ := fun ν => ns (ms (ks ν))
    have hτ : Tendsto τ atTop atTop := (hns.comp hms.tendsto_atTop).comp hks.tendsto_atTop
    have hcLim' : Tendsto (fun ν => c (τ ν)) atTop (𝓝 c₀) := hcLim.comp hks.tendsto_atTop
    have haLim' : Tendsto (fun ν => a (n (τ ν))) atTop (𝓝 a₀) := haLim
    obtain ⟨ls, hls, η, hη, C, hC, hbound⟩ := scalar_comparable_anchor_target_subsequence
      f hlin htrans hsmall hρ hl hu hm ha hpeak (hn.comp hτ)
      (fun ν => hc (τ ν)) hcLim' haLim' (hbClose.comp hτ) q hqRad hδ (hτ.eventually hH)
    refine ⟨ms ∘ ks ∘ ls, (hms.tendsto_atTop.comp hks.tendsto_atTop).comp hls.tendsto_atTop,
      η, hη, C, hC, ?_⟩
    simpa only [Function.comp_def, τ] using hbound
  obtain ⟨η, hη, hbound⟩ := hex
  exact exponential_bound_convert_comparable_characteristic f htrans hlin hsmall hρpos hl hu
    hbase hc hη hbound

end ModifiedCartan
#print axioms ModifiedCartan.scalar_comparable_anchor_fixed_target