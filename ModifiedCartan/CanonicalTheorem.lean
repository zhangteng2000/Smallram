import ModifiedCartan.CanonicalDilation

open scoped BigOperators Topology
open Filter Set

namespace ModifiedCartan

/-- LaTeX label: `lem:canonical-gauge`.
The coefficient indexed by `i` multiplies `D^i`, so `Q_q` has `i=n+1-q`.
The last entry is included explicitly and proved to vanish. The formula is
defined on the original domain, and identified with every permissible branch.
All basis, scalar, and dilation transformations are included in the conclusion. -/
theorem Paper.lem_canonical_gauge {n : ℕ} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (_hΩc : IsConnected Ω) {g : Index n → ℂ → ℂ}
    (hg : ∀ j, DifferentiableOn ℂ (g j) Ω)
    (_hW : ∃ z ∈ Ω, FewInflection.wronskian n g z ≠ 0) :
    (∀ i, MeromorphicOn (canonicalCoefficient n g i) Ω) ∧
    (∀ i, AnalyticOnNhd ℂ (canonicalCoefficient n g i)
      {z | z ∈ Ω ∧ FewInflection.wronskian n g z ≠ 0}) ∧
    (∀ z ∈ Ω, canonicalCoefficient n g (Fin.last n) z = 0) ∧
    (∀ U : Set ℂ, IsSimplyConnected U → IsOpen U → U ⊆ Ω →
      (∀ z ∈ U, FewInflection.wronskian n g z ≠ 0) →
      ∃ η : ℂ → ℂ, AnalyticOnNhd ℂ η U ∧ (∀ z, η z ≠ 0) ∧
        (∀ z ∈ U, η z ^ (n + 1) * FewInflection.wronskian n g z = 1) ∧
        (∀ z ∈ U, FewInflection.wronskian n (fun j w => η w * g j w) z = 1) ∧
        (∀ i z, z ∈ U → canonicalCoefficient n g i z =
          FewInflection.fundamentalCoefficients n (fun j w => η w * g j w) z i) ∧
        ∀ j z, z ∈ U → iteratedDeriv (n + 1) (fun w => η w * g j w) z +
          ∑ i, canonicalCoefficient n g i z *
            iteratedDeriv (i : ℕ) (fun w => η w * g j w) z = 0) ∧
    (∀ U : Set ℂ, IsOpen U → U ⊆ Ω → ∀ η : ℂ → ℂ,
      AnalyticOnNhd ℂ η U → (∀ z ∈ U, η z ≠ 0) →
      (∀ z ∈ U, η z ^ (n + 1) * FewInflection.wronskian n g z = 1) →
      ∀ i z, z ∈ U → canonicalCoefficient n g i z =
        FewInflection.fundamentalCoefficients n (fun j w => η w * g j w) z i) ∧
    (∀ A : Matrix (Index n) (Index n) ℂ, A.det ≠ 0 → ∀ i z, z ∈ Ω →
      canonicalCoefficient n (fun j w => ∑ k, g k w * A k j) i z =
        canonicalCoefficient n g i z) ∧
    (∀ s : ℂ → ℂ, AnalyticOnNhd ℂ s Ω → (∀ z ∈ Ω, s z ≠ 0) →
      ∀ i z, z ∈ Ω → canonicalCoefficient n (fun j w => s w * g j w) i z =
        canonicalCoefficient n g i z) ∧
    (∀ t : ℝ, 0 < t → ∀ i z, (t : ℂ) * z ∈ Ω →
      canonicalCoefficient n (fun j w => g j ((t : ℂ) * w)) i z =
        (t : ℂ) ^ (n + 1 - (i : ℕ)) * canonicalCoefficient n g i ((t : ℂ) * z)) := by
  have hga : ∀ j, AnalyticOnNhd ℂ (g j) Ω := fun j => (hg j).analyticOnNhd hΩ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i z hz
    exact meromorphicAt_canonicalCoefficient (fun j => hga j z hz) i
  · intro i z hz
    exact analyticAt_canonicalCoefficient (fun j => hga j z hz.1) hz.2 i
  · intro z hz
    exact canonicalCoefficient_last_eq_zero (fun j => hga j z hz)
  · intro U hUc hU hsub hW
    have hgu : ∀ j, AnalyticOnNhd ℂ (g j) U := fun j z hz => hga j z (hsub hz)
    obtain ⟨η, hη, hη0, hroot, hnorm, _⟩ := FewInflection.exists_canonical_gauge hUc hU hgu hW
    have hcoeff : ∀ i z, z ∈ U → canonicalCoefficient n g i z =
        FewInflection.fundamentalCoefficients n (fun j w => η w * g j w) z i :=
      fun i z hz => canonicalCoefficient_eq_normalized hU hgu hη
        (fun w _ => hη0 w) hroot i hz
    refine ⟨η, hη, hη0, hroot, hnorm, hcoeff, ?_⟩
    intro j z hz
    simp_rw [hcoeff _ z hz]
    exact FewInflection.fundamentalCoefficients_spec (by rw [hnorm z hz]; exact one_ne_zero) j
  · intro U hU hsub η hη hη0 hroot i z hz
    exact canonicalCoefficient_eq_normalized hU (fun j w hw => hga j w (hsub hw))
      hη hη0 hroot i hz
  · intro A hA i z hz
    exact canonicalCoefficient_matrix (fun j => hga j z hz) A hA i
  · intro s hs hs0 i z hz
    exact canonicalCoefficient_scalar_mul (fun j => hga j z hz) (hs z hz) (hs0 z hz) i
  · intro t ht i z hz
    exact Paper.eq_scalecoeff (fun j => hga j ((t : ℂ) * z) hz) ht i

end ModifiedCartan

