import ModifiedCartan.PeakNonvanishing
import ModifiedCartan.PeakLimitScaleModels
import ModifiedCartan.PeakScaleQuantization
import ModifiedCartan.AdmissibleInterval

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Every finite positive point of the strong-index interval is an
admissible order, as proved in Steps 1--3 of LaTeX `prop:indices`. -/
theorem positive_index_order_admissible {n : ℕ} (f : Curve n)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {μ : ℝ} (hμ : 0 < μ)
    (hlower : strongLowerIndex (characteristic f) ≤ (μ : EReal))
    (hupper : (μ : EReal) ≤ strongUpperIndex (characteristic f)) :
    FewInflection.AdmissibleOrder n μ := by
  obtain ⟨r, ε, hrpos, hr, hεpos, _, hε, _, _, hpeak⟩ :=
    characteristic_peaks_with_normalization f htrans hμ hlower hupper
  obtain ⟨K, _, ρ, hρ, a, ha⟩ := peak_coefficient_limit_scale_models f hlin htrans hsmall
    hμ hrpos hr hεpos hε hpeak
  obtain ⟨i, z, hz, haz⟩ := peak_coefficient_limit_nonzero f hlin htrans hsmall hμ
    (fun ν => hrpos (ρ ν)) (hr.comp hρ.tendsto_atTop)
    (fun ν => hεpos (ρ ν)) (hε.comp hρ.tendsto_atTop) (fun ν => hpeak (ρ ν))
    (fun i => (ha i).2.1)
  exact admissibleOrder_of_nonzero_scale_model (K := K) i (ha i).1 ⟨z, hz, haz⟩ (ha i).2.2

namespace Paper

/-- LaTeX `prop:indices`, including `eq:indices-collapse`. The exact joint
Drasin--Shea indices, lower order and order have one finite real value,
which is zero or belongs to the manuscript's admissible set. All analytic
hypotheses are exactly those of the submitted proposition. -/
theorem prop_indices {n : ℕ} (f : Curve n)
    (htrans : f.Transcendental) (hlin : f.linearlyNonDegenerate)
    (hfinite : FiniteLowerOrder f) (hsmall : SmallRamification f) :
    ∃ ρ : ℝ, strongLowerIndex (characteristic f) = (ρ : EReal) ∧
      lowerOrder f = (ρ : EReal) ∧ order f = (ρ : EReal) ∧
      strongUpperIndex (characteristic f) = (ρ : EReal) ∧
      (ρ = 0 ∨ FewInflection.AdmissibleOrder n ρ) := by
  obtain ⟨hnonneg, hlo, hmid, hup⟩ := eq_index_order_bounds_of_transcendental f htrans
  have hcollapse : strongLowerIndex (characteristic f) = strongUpperIndex (characteristic f) :=
    admissible_interval_eq hnonneg (hlo.trans (hmid.trans hup))
      (fun μ hμ hl hu => positive_index_order_admissible f hlin htrans hsmall hμ hl hu)
  have htop : strongLowerIndex (characteristic f) ≠ ⊤ := ne_of_lt (hlo.trans_lt hfinite)
  have hbot : strongLowerIndex (characteristic f) ≠ ⊥ :=
    ne_of_gt ((by simp : (⊥ : EReal) < 0).trans_le hnonneg)
  let ρ := (strongLowerIndex (characteristic f)).toReal
  have hreal : (ρ : EReal) = strongLowerIndex (characteristic f) := EReal.coe_toReal htop hbot
  have hloeq : lowerOrder f = strongLowerIndex (characteristic f) :=
    le_antisymm (hmid.trans (hup.trans hcollapse.symm.le)) hlo
  have hord : order f = strongLowerIndex (characteristic f) :=
    le_antisymm (hup.trans hcollapse.symm.le) (hlo.trans hmid)
  refine ⟨ρ, hreal.symm, hloeq.trans hreal.symm, hord.trans hreal.symm,
    hcollapse.symm.trans hreal.symm, ?_⟩
  by_cases hzero : ρ = 0
  · exact Or.inl hzero
  · have hpos : 0 < ρ := lt_of_le_of_ne (EReal.toReal_nonneg hnonneg) (Ne.symm hzero)
    exact Or.inr (positive_index_order_admissible f hlin htrans hsmall hpos
      hreal.symm.le (hreal.trans hcollapse).le)

end Paper
end ModifiedCartan
#print axioms ModifiedCartan.positive_index_order_admissible
#print axioms ModifiedCartan.Paper.prop_indices
