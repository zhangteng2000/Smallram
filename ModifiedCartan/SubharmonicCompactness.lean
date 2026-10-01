import ModifiedCartan.SubharmonicL1Alternative
import ModifiedCartan.SubharmonicLocalCompactness
import ModifiedCartan.SubharmonicLimitRepresentative
import ModifiedCartan.SubharmonicUpperBounds

open scoped Topology ENNReal NNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan.Paper

/-- LaTeX label `lem:subharmonic-compactness`: the subsequence dichotomy.
The upper-bound conclusion is `lem_subharmonic_compactness_upper_bound`.
The cited compactness theorem is proved here by lower anchors, disk averaging,
Arzela-Ascoli, countable L1 extraction, and construction of the subharmonic representative. -/
theorem lem_subharmonic_compactness {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) (hne : U.Nonempty) {u : ℕ → ℂ → EReal}
    (hu : ∀ n, IsSubharmonicOn U (u n))
    (hbdd : ∀ K, IsCompact K → K ⊆ U → ∃ M : ℝ,
      ∀ n z, z ∈ K → u n z ≤ (M : EReal)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      (LocalUniformlyToBot U (fun n => u (ns n)) ∨
        ∃ v : ℂ → EReal, IsSubharmonicOn U v ∧ (∃ z ∈ U, v z ≠ ⊥) ∧
          ∃ f : ℂ → ℝ, v =ᵐ[volume.restrict U] (fun z => (f z : EReal)) ∧
            LocalERealLpConvergence 1 U (fun n => u (ns n)) f) := by
  rcases subharmonic_collapse_or_l1_bounded_subsequence hU hUc hu hbdd with hcollapse | hbounded
  · exact ⟨id, strictMono_id, Or.inl hcollapse⟩
  obtain ⟨ns, hns, _, hfinite, hB⟩ := hbounded
  obtain ⟨ms, hms, f, hconv⟩ := subharmonic_localL1_subsequence hU (fun n => hu (ns n)) hfinite
    (fun K hK hKU => by
      obtain ⟨B, _, hB'⟩ := hB K hK hKU
      exact ⟨B, hB'⟩)
  obtain ⟨v, hv, hnz, hrep⟩ := exists_nontrivial_subharmonic_representative_of_localL1_limit
    hU hne (fun n => hu (ns (ms n))) (fun n => hfinite (ms n)) hconv
  exact ⟨ns ∘ ms, hns.comp hms, Or.inr ⟨v, hv, hnz, f, hrep,
    ⟨fun n => hfinite (ms n), hconv⟩⟩⟩


end ModifiedCartan.Paper
