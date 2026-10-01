import ModifiedCartan.LinearODESpan
import ModifiedCartan.RayMatrixContinuity

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- Comparison with the actual asymptotic family is a consequence of uniqueness,
not an extra representation premise. -/
theorem rayCompanion_family_spans_solution {q : ℕ} {ρ β T : ℝ}
    (hρ : ρ ≠ 0) (hT : 0 < T) (δ η : ℂ) (X : Fin q → ℝ → Fin q → ℂ)
    (hX : ∀ j t, T ≤ t → HasDerivAt (X j)
      ((rayCompanionCoefficient q ρ β δ η t).mulVec (X j t)) t)
    (hli : LinearIndependent ℂ (fun j => X j T)) {Y : ℝ → Fin q → ℂ}
    (hY : ∀ t, T ≤ t → HasDerivAt Y
      ((rayCompanionCoefficient q ρ β δ η t).mulVec (Y t)) t) :
    ∃ c : Fin q → ℂ, ∀ t, T ≤ t → Y t = ∑ j, c j • X j t := by
  exact linearODE_family_spans_solution (rayCompanionCLM_continuousOn hρ β δ η hT)
    X hX hli hY

/-- The actual scaled derivatives of every entire solution are in the span of
one genuine asymptotic fundamental family. -/
theorem scalar_ray_fundamental_expansion {q k : ℕ} (hq : 1 ≤ q) {ρ β : ℝ}
    (hρ : 0 < ρ) (hρβ : ρ = 1 + β) (hβ : β * (q : ℝ) = k) {δ η : ℂ}
    (hδ : δ ≠ 0) (hη : η ≠ 0) (hphase : δ ^ q = η ^ k) :
    ∃ T : ℝ, 1 ≤ T ∧ ∃ X : Fin q → ℝ → Fin q → ℂ,
      (∀ j t, T ≤ t → HasDerivAt (X j)
        ((rayCompanionCoefficient q ρ β δ η t).mulVec (X j t)) t) ∧
      (∀ t, T ≤ t → LinearIndependent ℂ (fun j => X j t)) ∧
      (∀ j, Tendsto (fun t : ℝ => t ^ (-rayDiagonalPower q ρ β) •
        (Complex.exp (-raySpectralValues q δ η j * (t : ℂ)) • X j t))
        atTop (𝓝 (fun i : Fin q => sharpnessRoot q j ^ i.val))) ∧
      (∀ y : ℂ → ℂ, Differentiable ℂ y →
        (∀ z, iteratedDeriv q y z = z ^ k * y z) →
        ∃ c : Fin q → ℂ, ∀ t, T ≤ t →
          rayDerivativeJet q ρ β δ η y t = ∑ j, c j • X j t) := by
  obtain ⟨T, hT, X, hd, hli, hl⟩ :=
    rayCompanion_tail_fundamental_system_exists hq ρ β hδ hη
  refine ⟨T, hT, X, hd, hli, hl, ?_⟩
  intro y hy heq
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  exact rayCompanion_family_spans_solution hρ.ne' hTpos δ η X hd (hli T le_rfl)
    (fun t ht => rayDerivativeJet_companion_hasDerivAt hρ (lt_of_lt_of_le hTpos ht)
      hρβ hβ hδ hphase hy heq)

end ModifiedCartan
#print axioms ModifiedCartan.scalar_ray_fundamental_expansion
