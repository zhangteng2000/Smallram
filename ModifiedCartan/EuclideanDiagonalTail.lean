import ModifiedCartan.DiagonalHalfLine
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Analysis.Calculus.FDeriv.Linear

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The actual tail fundamental system in the manuscript's Euclidean norm.
Changing between finite-dimensional norms is a proved continuous linear
conjugacy; its integrability is derived, not assumed. -/
theorem euclidean_diagonal_tail_fundamental_system_exists {q : ℕ}
    (lam : Fin q → ℂ) (E : ℝ → Matrix (Fin q) (Fin q) ℂ) (t0 : ℝ)
    (hE : ContinuousOn (fun t => Matrix.toEuclideanCLM (n := Fin q) (𝕜 := ℂ) (E t)) (Ici t0))
    (hEi : IntegrableOn (fun t => Matrix.toEuclideanCLM (n := Fin q) (𝕜 := ℂ) (E t)) (Ici t0)) :
    ∃ T : ℝ, t0 ≤ T ∧ ∃ X : Fin q → ℝ → EuclideanSpace ℂ (Fin q),
      (∀ j t, T ≤ t → HasDerivWithinAt (X j)
        (Matrix.toEuclideanCLM (n := Fin q) (𝕜 := ℂ) (Matrix.diagonal lam + E t) (X j t)) (Ici T) t) ∧
      (∀ t, T ≤ t → LinearIndependent ℂ (fun j => X j t)) ∧
      (∀ j, Tendsto (fun t : ℝ => Complex.exp (-lam j * (t : ℂ)) • X j t)
        atTop (𝓝 (WithLp.toLp 2 (Pi.single j (1 : ℂ))))) := by
  let e : EuclideanSpace ℂ (Fin q) ≃L[ℂ] (Fin q → ℂ) :=
    PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin q => ℂ)
  let A : ℝ → (Fin q → ℂ) →L[ℂ] (Fin q → ℂ) :=
    fun t => (e.arrowCongr e) (Matrix.toEuclideanCLM (n := Fin q) (𝕜 := ℂ) (E t))
  have hA : ContinuousOn A (Ici t0) := (e.arrowCongr e).continuous.comp_continuousOn hE
  have hAi : IntegrableOn A (Ici t0) :=
    (e.arrowCongr e).toContinuousLinearMap.integrable_comp hEi
  obtain ⟨T, hT, X, hd, hli, hl⟩ := diagonal_halfLine_tail_exists lam t0 hA hAi
  let Y : Fin q → ℝ → EuclideanSpace ℂ (Fin q) := fun j t => e.symm (X j t)
  refine ⟨T, hT, Y, ?_, ?_, ?_⟩
  · intro j t ht
    have hder := (e.symm.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t (hd j t ht)
    have he : e.symm (fun i => lam i * X j t i + A t (X j t) i) =
        Matrix.toEuclideanCLM (n := Fin q) (𝕜 := ℂ) (Matrix.diagonal lam + E t) (e.symm (X j t)) := by
      apply e.injective
      rw [ContinuousLinearEquiv.apply_symm_apply]
      change (fun i => lam i * X j t i + A t (X j t) i) =
        (Matrix.diagonal lam + E t).mulVec (X j t)
      funext i
      simp only [Matrix.add_mulVec, Pi.add_apply, Matrix.mulVec_diagonal]
      rfl
    change HasDerivWithinAt (fun s => e.symm (X j s))
      (e.symm (fun i => lam i * X j t i + A t (X j t) i)) (Ici T) t at hder
    rw [he] at hder
    exact hder
  · intro t ht
    simpa only [Function.comp_apply, ContinuousLinearEquiv.coe_coe] using!
      (hli t ht).map' e.symm.toLinearMap (LinearMap.ker_eq_bot_of_injective e.symm.injective)
  · intro j
    change Tendsto (fun t : ℝ => Complex.exp (-lam j * (t : ℂ)) • e.symm (X j t))
      atTop (𝓝 (e.symm (Pi.single j (1 : ℂ))))
    simpa only [Function.comp_apply, map_smul] using!
      (e.symm.continuous.tendsto (Pi.single j (1 : ℂ))).comp (hl j)

end ModifiedCartan
#print axioms ModifiedCartan.euclidean_diagonal_tail_fundamental_system_exists

