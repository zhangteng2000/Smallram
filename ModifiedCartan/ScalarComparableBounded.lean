import ModifiedCartan.ScalarComparableLimits
import ModifiedCartan.ArbitraryRadiusReindex

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Compactness of the actual radius ratios removes the convergence assumption
on those ratios. Every ratio sequence in [1,2] preserves the same norm profile. -/
theorem ArbitraryRadiusLimitData.scalar_comparable_potential_limit_bounded
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) (hρ : 0 < ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    (hr : Tendsto r atTop atTop) {c : ℕ → ℝ}
    (hc : ∀ ν, c ν ∈ Icc (1 : ℝ) 2) :
    LocalMeasureConvergence (ball (0 : ℂ) 1)
      (fun ν => scalarNormalizedSpherePotential f (c ν * r (d.subseq ν)))
      (fun z => 2 * (d.U z).toReal) := by
  apply localMeasureConvergence_of_subseq
  intro ns hns
  obtain ⟨τ, hτ, hnsτ⟩ := strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨c₀, hc₀, σ, hσ, hconv⟩ := isCompact_Icc.tendsto_subseq (fun ν => hc (ns (τ ν)))
  let e := d.reindex ((ns ∘ τ) ∘ σ) (hnsτ.comp hσ)
  have he := e.scalar_comparable_potential_limit hlin htrans hsmall hρ hl hu hr
    (fun ν => hc (ns (τ (σ ν)))) hc₀ (by simpa only [Function.comp_def] using hconv)
  refine ⟨τ ∘ σ, ?_⟩
  simpa only [e, ArbitraryRadiusLimitData.reindex_subseq, ArbitraryRadiusLimitData.reindex_U,
    Function.comp_def] using he

/-- Exact agreement of all actual comparable-radius norm limits, without
selecting a convergent ratio sequence or adding an angular-phase hypothesis. -/
theorem ArbitraryRadiusLimitData.scalar_comparable_norm_limits_bounded
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) (hρ : 0 < ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    (hr : Tendsto r atTop atTop) {c : ℕ → ℝ}
    (hc : ∀ ν, c ν ∈ Icc (1 : ℝ) 2)
    (e : ArbitraryRadiusLimitData f (fun ν => c ν * r (d.subseq ν)) ρ) :
    EqOn (fun z => (e.U z).toReal) (fun z => (d.U z).toReal) (ball (0 : ℂ) 2) := by
  have ht : Tendsto (fun ν => r (d.subseq ν)) atTop atTop := by
    simpa only [Function.comp_def] using hr.comp d.strictMono.tendsto_atTop
  have hs : Tendsto (fun ν => c ν * r (d.subseq ν)) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ ht
    filter_upwards [ht.eventually_ge_atTop 0] with ν htν
    nlinarith [(hc ν).1]
  have hd := (d.scalar_comparable_potential_limit_bounded hlin htrans hsmall hρ hl hu hr hc).comp
    e.strictMono.tendsto_atTop
  have he := ((e.scalar_spherical_potential_localL1 hlin htrans hsmall hρ hl hu hs).inMeasure
    (by norm_num)).mono (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 4))
  have hae := LocalMeasureConvergence.ae_unique isOpen_ball he hd
  have hunit := Measure.eqOn_open_of_ae_eq hae isOpen_ball
    (continuousOn_const.mul (e.norm_limit_continuous.2.mono (ball_subset_ball (by norm_num))))
    (continuousOn_const.mul (d.norm_limit_continuous.2.mono (ball_subset_ball (by norm_num))))
  apply d.norm_limits_eqOn_of_unit_disk e hρ
  intro z hz
  have hh := hunit hz
  linarith

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_comparable_potential_limit_bounded
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_comparable_norm_limits_bounded
