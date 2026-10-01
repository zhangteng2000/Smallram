import ModifiedCartan.ScalarDyadicMeanDefect
import ModifiedCartan.ScalarDyadicDecomposition
import ModifiedCartan.ArbitraryRadiusAccuracy

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- All-radius projective proximity for a normalized curve is the integer
multiplicity of its fixed coherent dyadic targets divided by the order.
Auxiliary to LaTeX `thm:A` (b). -/
theorem scalar_projective_proximity_ratio_dyadic
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) (hf0 : ∀ j, f.coord j 0 ≠ 0)
    {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2)
    (q : (j : Fin m) → ScalarDyadicPeakTargetData f (scalarDyadicSectorCenter f m j) ρ)
    (β : WithTop ℂ) :
    Tendsto (fun r => scalarProjectiveProximity f β r / characteristic f r) atTop
      (𝓝 ((scalarSectorMultiplicity (fun j => (q j).target) β : ℝ) / ρ)) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro r hr
  let R : ℕ → ℝ := fun ν => max 1 (r ν)
  have hR : Tendsto R atTop atTop := tendsto_atTop_mono (fun ν => le_max_right _ _) hr
  let n₁ : ℕ → ℕ := fun ν => scalarDyadicIndex (R ν)
  let c₁ : ℕ → ℝ := fun ν => scalarDyadicMultiplier (R ν)
  have hn₁ : Tendsto n₁ atTop atTop := scalarDyadicIndex_tendsto.comp hR
  have hc₁ : ∀ ν, c₁ ν ∈ Icc (1 : ℝ) 2 := fun ν => scalarDyadicMultiplier_mem (le_max_left _ _)
  obtain ⟨c₀, hc₀, ns, hns, hcLim⟩ := (isCompact_Icc : IsCompact (Icc (1 : ℝ) 2)).tendsto_subseq hc₁
  obtain ⟨a₀, _, ms, hms, haLim⟩ := (isCompact_sphere (0 : ℂ) 1).tendsto_subseq
    (fun ν => show scalarDyadicPeakCenter f m (n₁ (ns ν)) ∈ sphere (0 : ℂ) 1 by
      simpa only [mem_sphere, dist_zero_right] using scalarDyadicPeakCenter_norm f m (n₁ (ns ν)))
  let τ : ℕ → ℕ := ns ∘ ms
  have hτ : StrictMono τ := hns.comp hms
  let n : ℕ → ℕ := n₁ ∘ τ
  let c : ℕ → ℝ := c₁ ∘ τ
  let t : ℕ → ℝ := fun ν => c ν * (2 : ℝ) ^ n ν
  have hn : Tendsto n atTop atTop := hn₁.comp hτ.tendsto_atTop
  have hc : ∀ ν, c ν ∈ Icc (1 : ℝ) 2 := fun ν => hc₁ (τ ν)
  have hclim : Tendsto c atTop (𝓝 c₀) := hcLim.comp hms.tendsto_atTop
  have halim : Tendsto (fun ν => scalarDyadicPeakCenter f m (n ν)) atTop (𝓝 a₀) := haLim
  have htR : ∀ ν, t ν = R (τ ν) := fun ν => scalarDyadicMultiplier_factor (R (τ ν))
  have ht : Tendsto t atTop atTop := by
    have he : t = R ∘ τ := funext htR
    rw [he]
    exact hR.comp hτ.tendsto_atTop
  obtain ⟨d, hA⟩ := exists_arbitrary_radius_limits_normalized_with_accuracy f
    ((Real.pi / 2) * (2 : ℝ) ^ ρ) hlin htrans hsmall hf0
    (lt_of_lt_of_le zero_lt_one hρ) hl hu ht
  obtain ⟨ks, hks, ⟨e⟩⟩ := d.exists_scalar_target_log_limit β
  have heval := e.circle_mean_defect_eq_dyadic_multiplicity f hlin htrans hsmall hρ hl hu
    hm q hn hc (lt_of_lt_of_le zero_lt_one hc₀.1) hclim halim hA
  obtain ⟨ls, hls, hlim⟩ := e.exists_projective_proximity_ratio_limit hlin hρ ht hA
  rw [heval] at hlim
  refine ⟨τ ∘ d.subseq ∘ ks ∘ ls, ?_⟩
  apply hlim.congr'
  have hseq := hτ.tendsto_atTop.comp
    (d.strictMono.tendsto_atTop.comp (hks.tendsto_atTop.comp hls.tendsto_atTop))
  filter_upwards [(hr.comp hseq).eventually_ge_atTop 1] with ν hrν
  change scalarProjectiveProximity f β (t (d.subseq (ks (ls ν)))) /
    characteristic f (t (d.subseq (ks (ls ν)))) = _
  rw [htR]
  dsimp only [R, Function.comp_def] at hrν ⊢
  rw [max_eq_right hrν]

end ModifiedCartan
#print axioms ModifiedCartan.scalar_projective_proximity_ratio_dyadic
