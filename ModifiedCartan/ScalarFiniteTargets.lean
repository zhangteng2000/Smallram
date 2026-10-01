import ModifiedCartan.ScalarChartTarget
import ModifiedCartan.FiniteSubsequenceExtraction

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- All members of a finite family of actual cross domains have selected-line
targets on one common subsequence. The targets need not be distinct. -/
theorem scalar_finite_common_line_targets
    {f : Curve 1} {r s : ℕ → ℝ} {N : ℕ} (Ω : Fin N → Set ℂ)
    (hcross : ∀ j, HasSmallRectangleCrosses f r s (Ω j))
    (hr : Tendsto r atTop atTop) (hs : Tendsto s atTop atTop)
    (hopen : ∀ j, IsOpen (Ω j)) (hconn : ∀ j, IsConnected (Ω j)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ β : Fin N → WithTop ℂ,
      ∃ q : (j : Fin N) → ScalarHorizontalSelection f (r ∘ ns) (s ∘ ns) (Ω j),
        ∀ j, HasSmallRectangleCrosses f (r ∘ ns) (s ∘ ns) (Ω j) ∧
          ∀ R : {R : ComplexRect // R.closed ⊆ Ω j},
            Tendsto ((q j).anchor R) atTop (𝓝 (scalarSphereValue (β j))) ∧
            ∀ ε > 0, ∀ᶠ ν in atTop, ∀ t ∈ Icc R.val.left R.val.right,
              ‖scalarCurveSphere f ((r (ns ν) : ℂ) * (⟨t, (q j).height R ν⟩ : ℂ)) -
                scalarSphereValue (β j)‖ < ε := by
  classical
  let q₀ : (j : Fin N) → ScalarHorizontalSelection f r s (Ω j) :=
    fun j => Classical.choice (hcross j).exists_horizontal_selection
  let P : Fin N → (ℕ → ℕ) → Prop := fun j τ =>
    ∃ β : WithTop ℂ, ∀ R : {R : ComplexRect // R.closed ⊆ Ω j},
      Tendsto (fun ν => (q₀ j).anchor R (τ ν)) atTop (𝓝 (scalarSphereValue β))
  obtain ⟨ns, hns, hP⟩ := finite_subsequence_extraction N P (by
    intro j τ hτ
    obtain ⟨β, σ, hσ, ht⟩ := ((q₀ j).reindex τ hτ.tendsto_atTop).exists_common_subsequence_target
      ((hcross j).comp hτ.tendsto_atTop) (hr.comp hτ.tendsto_atTop) (hs.comp hτ.tendsto_atTop)
      (hopen j) (hconn j)
    exact ⟨σ, hσ, β, ht⟩) (by
    intro j τ σ hP hσ
    obtain ⟨β, ht⟩ := hP
    exact ⟨β, fun R => (ht R).comp hσ.tendsto_atTop⟩)
  choose β hβ using hP
  refine ⟨ns, hns, β, (fun j => (q₀ j).reindex ns hns.tendsto_atTop), ?_⟩
  intro j
  refine ⟨(hcross j).comp hns.tendsto_atTop, ?_⟩
  intro R
  exact ⟨hβ j R, ((q₀ j).reindex ns hns.tendsto_atTop).horizontal_line_limit
    (hr.comp hns.tendsto_atTop) (hs.comp hns.tendsto_atTop) R (hβ j R)⟩

end ModifiedCartan
#print axioms ModifiedCartan.scalar_finite_common_line_targets
