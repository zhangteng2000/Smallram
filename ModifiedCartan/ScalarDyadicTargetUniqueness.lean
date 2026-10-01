import ModifiedCartan.ScalarDyadicLineTargets

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Fixed targets do not depend on the width or the selected good horizontal
lines for a given coherently numbered phase peak. -/
theorem scalar_dyadic_peak_target_unique
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) {a : ℕ → ℂ}
    (ha : ∀ ν, ‖a ν‖ = 1)
    (hpeak : ∀ ν, scalarPhaseCoefficient f m ((2 : ℝ) ^ ν) * (a ν) ^ m =
      (((Real.pi / 2) ^ 2 : ℝ) : ℂ))
    (q₁ q₂ : ScalarDyadicPeakTargetData f a ρ) : q₁.target = q₂.target := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hpow : Tendsto (fun ν : ℕ => (2 : ℝ) ^ ν) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨b, hb, ns, hns, hconv⟩ := (isCompact_sphere (0 : ℂ) 1).tendsto_subseq
    (fun ν => show a ν ∈ sphere (0 : ℂ) 1 by simpa only [mem_sphere, dist_zero_right] using ha ν)
  have hbnorm : ‖b‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hb
  have hb0 : b ≠ 0 := norm_ne_zero_iff.mp (by rw [hbnorm]; norm_num)
  obtain ⟨ms, hms, hcross⟩ := scalar_phase_peaks_subsequence_crosses f hlin htrans hsmall hρ hl hu hm
    (hpow.comp hns.tendsto_atTop) (a := fun (_ : Fin 1) ν => a (ns ν)) (a₀ := fun _ => b)
    (fun _ ν => ha (ns ν)) (fun _ => hconv) (fun _ ν => hpeak (ns ν))
  let τ := ns ∘ ms
  have hτ : Tendsto τ atTop atTop := hns.tendsto_atTop.comp hms.tendsto_atTop
  have hrad := hpow.comp hτ
  have hscale := (characteristic_tendsto_atTop_of_transcendental f htrans).comp hrad
  have ha' : Tendsto (fun ν => a (τ ν)) atTop (𝓝 b) := hconv.comp hms.tendsto_atTop
  obtain ⟨δ, hδ, C, hC, hbound⟩ := (hcross 0).two_moving_box_anchors_exponential hrad hscale
    (scalarFullSector_isOpen hb0 hρpos)
    (scalarFullSector_isConnected hb0 (by rw [hbnorm]; norm_num) hρpos).isPreconnected
    ha' ha' q₁.width_pos q₂.width_pos (q₁.sector_disks b hbnorm).1 (q₂.sector_disks b hbnorm).1
    q₁.lineRate_pos q₂.lineRate_pos (hτ.eventually q₁.good) (hτ.eventually q₂.good)
  have hz : Tendsto (fun ν => ‖q₁.anchor (τ ν) - q₂.anchor (τ ν)‖) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun ν => norm_nonneg _)) hbound
    simpa only [mul_zero, Function.comp_def, τ] using (exp_neg_mul_tendsto_zero hscale hδ).const_mul C
  have hl' : Tendsto (fun ν => ‖q₁.anchor (τ ν) - q₂.anchor (τ ν)‖) atTop
      (𝓝 ‖scalarSphereValue q₁.target - scalarSphereValue q₂.target‖) :=
    ((q₁.limit.comp hτ).sub (q₂.limit.comp hτ)).norm
  have he : ‖scalarSphereValue q₁.target - scalarSphereValue q₂.target‖ = 0 :=
    tendsto_nhds_unique hl' hz
  exact scalarSphereValue_injective (sub_eq_zero.mp (norm_eq_zero.mp he))

end ModifiedCartan
#print axioms ModifiedCartan.scalar_dyadic_peak_target_unique