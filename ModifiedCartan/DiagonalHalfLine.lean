import ModifiedCartan.DiagonalTailIndependent

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Tail construction from continuity only on the manuscript's half-line. -/
theorem diagonal_halfLine_tail_exists (lam : ι → ℂ)
    {A : ℝ → (ι → ℂ) →L[ℂ] (ι → ℂ)} (t0 : ℝ)
    (hA : ContinuousOn A (Ici t0)) (hAi : IntegrableOn A (Ici t0)) :
    ∃ T : ℝ, t0 ≤ T ∧ ∃ X : ι → ℝ → ι → ℂ,
      (∀ j t, T ≤ t → HasDerivWithinAt (X j)
        (fun i => lam i * X j t i + A t (X j t) i) (Ici T) t) ∧
      (∀ t, T ≤ t → LinearIndependent ℂ (fun j => X j t)) ∧
      (∀ j, Tendsto (fun t : ℝ => Complex.exp (-lam j * (t : ℂ)) • X j t)
        atTop (𝓝 (Pi.single j (1 : ℂ)))) := by
  let C : ℝ → (ι → ℂ) →L[ℂ] (ι → ℂ) := fun t => A (max t0 t)
  have hC : Continuous C := hA.comp_continuous (continuous_const.max continuous_id)
    (fun t => le_max_left t0 t)
  have hCi : IntegrableOn C (Ici t0) := hAi.congr_fun (by
    intro t ht
    dsimp [C]
    rw [max_eq_right (show t0 ≤ t from ht)]) measurableSet_Ici
  obtain ⟨T, hT, X, hd, hli, hl⟩ := diagonal_tail_fundamental_system_exists lam hC t0 hCi
  refine ⟨T, hT, X, ?_, hli, hl⟩
  intro j t ht
  simpa only [C, max_eq_right (hT.trans ht)] using hd j t ht

end ModifiedCartan
#print axioms ModifiedCartan.diagonal_halfLine_tail_exists
