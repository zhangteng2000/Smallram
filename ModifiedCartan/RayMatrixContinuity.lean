import ModifiedCartan.RayCompanionAsymptotics
import ModifiedCartan.LinearODEIndependent
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

noncomputable def matrixPiCLMEquiv (q : ℕ) :
    Matrix (Fin q) (Fin q) ℂ ≃L[ℂ] ((Fin q → ℂ) →L[ℂ] (Fin q → ℂ)) :=
  (Matrix.toLin'.trans LinearMap.toContinuousLinearMap).toContinuousLinearEquiv

@[simp] theorem matrixPiCLMEquiv_apply {q : ℕ} (M : Matrix (Fin q) (Fin q) ℂ)
    (v : Fin q → ℂ) : matrixPiCLMEquiv q M v = M.mulVec v := rfl

theorem rayCompanionCoefficient_continuousOn {q : ℕ} {ρ : ℝ} (hρ : ρ ≠ 0)
    (β : ℝ) (δ η : ℂ) {T : ℝ} (hT : 0 < T) :
    ContinuousOn (rayCompanionCoefficient q ρ β δ η) (Ici T) := by
  unfold rayCompanionCoefficient
  apply continuousOn_const.add
  have hc : ContinuousOn (fun t : ℝ => -((β / (ρ * t) : ℝ) : ℂ)) (Ici T) := by
    apply ContinuousOn.neg
    apply Complex.continuous_ofReal.comp_continuousOn
    exact continuousOn_const.div (continuousOn_const.mul continuousOn_id)
      (fun t ht => mul_ne_zero hρ (ne_of_gt (lt_of_lt_of_le hT ht)))
  exact hc.smul (continuousOn_const (c := Matrix.diagonal (fun i : Fin q => (i.val : ℂ))))

theorem rayCompanionCLM_continuousOn {q : ℕ} {ρ : ℝ} (hρ : ρ ≠ 0)
    (β : ℝ) (δ η : ℂ) {T : ℝ} (hT : 0 < T) :
    ContinuousOn (fun t => matrixPiCLMEquiv q (rayCompanionCoefficient q ρ β δ η t))
      (Ici T) :=
  (matrixPiCLMEquiv q).continuous.comp_continuousOn
    (rayCompanionCoefficient_continuousOn hρ β δ η hT)

end ModifiedCartan
#print axioms ModifiedCartan.rayCompanionCLM_continuousOn

