import ModifiedCartan.LocalCompactness

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- Eventual hypotheses suffice for simultaneous compactness of the actual
canonical coefficients. This is the finite-prefix transfer used by
`prop:representation`; the bound still precedes all sequence data. -/
theorem canonical_coefficient_relative_compactness_eventual (n : ℕ) (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (g : ℕ → Index n → ℂ → ℂ) (s : ℕ → ℝ) (P : ℕ → Polynomial ℂ),
        Tendsto s atTop atTop →
        Tendsto (fun ν => ((P ν).natDegree : ℝ) / s ν) atTop (𝓝 0) →
        (∀ᶠ ν in atTop,
          (∀ j, AnalyticOnNhd ℂ (g ν j) (ball 0 32)) ∧ (P ν).Monic ∧
          (∀ z ∈ ball (0 : ℂ) 32, FewInflection.wronskian n (g ν) z = (P ν).eval z) ∧
          (∀ z ∈ ball (0 : ℂ) 32, euclideanNorm (fun j => g ν j z) ≤ Real.exp (C * s ν))) →
        ∀ ρ : ℕ → ℕ, StrictMono ρ →
          ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ b : Index n → ℂ → ℂ,
            ∀ i, AnalyticOnNhd ℂ (b i) (ball 0 4) ∧
              LocalMeasureConvergence (ball (0 : ℂ) 4)
                (fun ν z => canonicalCoefficient n (g (ρ (σ ν))) i z /
                  (s (ρ (σ ν)) : ℂ) ^ (n + 1 - i.val)) (b i) ∧
              ∀ z ∈ ball (0 : ℂ) 1, ‖b i z‖ ≤ K := by
  obtain ⟨K, hK, hmain⟩ := Paper.prop_localcompact n C
  refine ⟨K, hK, ?_⟩
  intro g s P hs hm hd ρ hρ
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hρ.tendsto_atTop.eventually hd)
  have hshift : StrictMono (fun ν : ℕ => ν + N) := fun i j hij => Nat.add_lt_add_right hij N
  have hindices : Tendsto (fun ν => ρ (ν + N)) atTop atTop :=
    hρ.tendsto_atTop.comp hshift.tendsto_atTop
  let g' := fun ν => g (ρ (ν + N))
  let s' := fun ν => s (ρ (ν + N))
  let P' := fun ν => P (ρ (ν + N))
  have hD (ν : ℕ) := hN (ν + N) (by omega : N ≤ ν + N)
  obtain ⟨hc, _, he⟩ := hmain g' s' P' (fun ν => (hD ν).1) (hs.comp hindices)
    (fun ν => (hD ν).2.1) (fun ν => (hD ν).2.2.1) (fun ν => (hD ν).2.2.2)
    (hm.comp hindices)
  obtain ⟨σ, hσ, b, hb⟩ := hc id strictMono_id
  refine ⟨fun ν => σ ν + N, fun i j hij => Nat.add_lt_add_right (hσ hij) N, b, ?_⟩
  intro i
  refine ⟨(hb i).1, ?_, (hb i).2.2⟩
  have hlim := ((he i).comp hσ.tendsto_atTop).add (hb i).2.1
  convert! hlim using 1
  · funext ν z
    simp only [g', s', id_eq]
    ring
  · funext z
    exact (zero_add (b i z)).symm

end
end ModifiedCartan
#print axioms ModifiedCartan.canonical_coefficient_relative_compactness_eventual
