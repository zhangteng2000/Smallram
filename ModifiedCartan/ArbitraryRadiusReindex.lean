import ModifiedCartan.ArbitraryRadiusData
import ModifiedCartan.ReplacementSubsequence
import ModifiedCartan.MeasureLimitTransfer

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Reindex every good-center assertion while retaining the same full-measure
set and the actual root list with multiplicity. -/
noncomputable def GoodCenterData.reindex {n : ℕ} {s : ℕ → ℝ}
    {p : ℕ → Index n → Polynomial ℂ}
    {a : (ν : ℕ) → Fin (FewInflection.polynomialWronskian (p ν)).natDegree → ℂ}
    (h : GoodCenterData s p a) (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) :
    GoodCenterData (s ∘ ns) (p ∘ ns) (fun ν => a (ns ν)) where
  centers := h.centers
  subset := h.subset
  full_measure := h.full_measure
  wronskian_ne_zero z hz ν := h.wronskian_ne_zero z hz (ns ν)
  log_wronskian z hz := (h.log_wronskian z hz).comp hns
  root_sum_bound z hz := by
    obtain ⟨B, hB, hbound⟩ := h.root_sum_bound z hz
    exact ⟨B, hB, hns.eventually hbound⟩

/-- Every field of the actual arbitrary-radius data survives a subsequence.
In particular the norm and coefficient limits are unchanged. -/
noncomputable def ArbitraryRadiusLimitData.reindex {n : ℕ} {f : Curve n} {r : ℕ → ℝ} {ρ : ℝ}
    (d : ArbitraryRadiusLimitData f r ρ) (ns : ℕ → ℕ) (hns : StrictMono ns) :
    ArbitraryRadiusLimitData f r ρ where
  subseq := d.subseq ∘ ns
  strictMono := d.strictMono.comp hns
  scale_pos ν := d.scale_pos (ns ν)
  scale_tendsto := d.scale_tendsto.comp hns.tendsto_atTop
  C := d.C
  A := d.A
  L := d.L
  C_pos := d.C_pos
  A_pos := d.A_pos
  L_pos := d.L_pos
  gauge := d.gauge ∘ ns
  polynomial := d.polynomial ∘ ns
  roots ν := d.roots (ns ν)
  separatingRadius := d.separatingRadius ∘ ns
  replacement := d.replacement.comp_tendsto hns.tendsto_atTop
  coefficient := d.coefficient
  coefficient_analytic := d.coefficient_analytic
  coefficient_limit i := (d.coefficient_limit i).comp hns.tendsto_atTop
  coefficient_monomial := d.coefficient_monomial
  coefficient_bound := d.coefficient_bound
  u := d.u
  v := d.v
  coordinate_subharmonic := d.coordinate_subharmonic
  coordinate_nontrivial := d.coordinate_nontrivial
  coordinate_representative := d.coordinate_representative
  coordinate_limit j := (d.coordinate_limit j).comp_tendsto hns.tendsto_atTop
  coordinate_sum_nonneg := d.coordinate_sum_nonneg
  U := d.U
  V := d.V
  maximum := d.maximum
  real_maximum := d.real_maximum
  subharmonic := d.subharmonic
  representative := d.representative
  nonneg := d.nonneg
  norm_limit := d.norm_limit.comp_tendsto hns.tendsto_atTop
  polynomial_norm_limit := d.polynomial_norm_limit.comp_tendsto hns.tendsto_atTop
  mean_error := d.mean_error ∘ ns
  mean_error_zero := d.mean_error_zero.comp hns.tendsto_atTop
  radial_mean := hns.tendsto_atTop.eventually d.radial_mean
  origin_zero := d.origin_zero
  origin_bound := d.origin_bound
  good_centers := d.good_centers.reindex ns hns.tendsto_atTop

theorem ArbitraryRadiusLimitData.reindex_subseq {n : ℕ} {f : Curve n} {r : ℕ → ℝ} {ρ : ℝ}
    (d : ArbitraryRadiusLimitData f r ρ) (ns : ℕ → ℕ) (hns : StrictMono ns) :
    (d.reindex ns hns).subseq = d.subseq ∘ ns := rfl

theorem ArbitraryRadiusLimitData.reindex_U {n : ℕ} {f : Curve n} {r : ℕ → ℝ} {ρ : ℝ}
    (d : ArbitraryRadiusLimitData f r ρ) (ns : ℕ → ℕ) (hns : StrictMono ns) :
    (d.reindex ns hns).U = d.U := rfl

theorem ArbitraryRadiusLimitData.reindex_coefficient {n : ℕ} {f : Curve n} {r : ℕ → ℝ} {ρ : ℝ}
    (d : ArbitraryRadiusLimitData f r ρ) (ns : ℕ → ℕ) (hns : StrictMono ns) :
    (d.reindex ns hns).coefficient = d.coefficient := rfl

end ModifiedCartan
#print axioms ModifiedCartan.GoodCenterData.reindex
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.reindex
