import ModifiedCartan.PolynomialReplacement

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Reindexing retains all fields of the actual polynomial replacement,
including its dependent list of roots with multiplicity. -/
theorem PolynomialReplacementData.comp_tendsto {n : ℕ} {f : Curve n} {t s : ℕ → ℝ}
    {C A L : ℝ} {H : ℕ → ℂ → ℂ} {p : ℕ → Index n → Polynomial ℂ}
    {a : (ν : ℕ) → Fin (FewInflection.polynomialWronskian (p ν)).natDegree → ℂ}
    {η : ℕ → ℝ} (h : PolynomialReplacementData f t s C A L H p a η)
    {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop) :
    PolynomialReplacementData f (t ∘ ns) (s ∘ ns) C A L (H ∘ ns) (p ∘ ns)
      (fun ν => a (ns ν)) (η ∘ ns) where
  gauge_analytic := hns.eventually h.gauge_analytic
  gauge_wronskian := hns.eventually h.gauge_wronskian
  gauge_center := h.gauge_center.comp hns
  coordinate_centers j := (h.coordinate_centers j).comp hns
  gauge_norm := hns.eventually h.gauge_norm
  mean_identity := by
    obtain ⟨c, hc, hm⟩ := h.mean_identity
    exact ⟨c ∘ ns, hc.comp hns, hns.eventually hm⟩
  taylor ν j := h.taylor (ns ν) j
  degree := hns.eventually h.degree
  wronskian_degree := hns.eventually h.wronskian_degree
  wronskian_nonzero := hns.eventually h.wronskian_nonzero
  jet_error := hns.eventually h.jet_error
  root_factorization := hns.eventually h.root_factorization
  separating_radii ν := h.separating_radii (ns ν)
  inner_count := h.inner_count.comp hns
  log_wronskian := h.log_wronskian.comp_tendsto hns
  inner_sum_lp := h.inner_sum_lp.comp hns
  inner_sum_measure := h.inner_sum_measure.comp hns
  outer_sum := hns.eventually h.outer_sum
  first_coefficient := h.first_coefficient.comp hns
  scaled_coefficients i := (h.scaled_coefficients i).comp hns

end ModifiedCartan
#print axioms ModifiedCartan.PolynomialReplacementData.comp_tendsto
