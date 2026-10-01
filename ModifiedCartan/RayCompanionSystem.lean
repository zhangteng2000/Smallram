import ModifiedCartan.RayScaleAlgebra
import ModifiedCartan.SharpnessCompanion

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem cyclicCompanion_mulVec {q : ℕ} (v : Fin q → ℂ) (i : Fin q) :
    (cyclicCompanion q).mulVec v i = v (cyclicSuccessor i) := by
  simp [Matrix.mulVec, dotProduct, cyclicCompanion]

theorem rayDerivativeCoordinate_cyclic {q k : ℕ} {ρ β t : ℝ} (hρ : 0 < ρ) (ht : 0 < t)
    (hβ : β * (q : ℝ) = k) {δ η : ℂ} (hδ : δ ≠ 0) (hphase : δ ^ q = η ^ k)
    {y : ℂ → ℂ} (heq : ∀ z, iteratedDeriv q y z = z ^ k * y z) (i : Fin q) :
    rayDerivativeCoordinate ρ β δ η y (i.val + 1) t =
      rayDerivativeJet q ρ β δ η y t (cyclicSuccessor i) := by
  by_cases hi : i.val + 1 < q
  · simp only [rayDerivativeJet, cyclicSuccessor, Nat.mod_eq_of_lt hi]
  · have he : i.val + 1 = q := by have := i.isLt; omega
    simp only [rayDerivativeJet, cyclicSuccessor, he, Nat.mod_self]
    exact rayDerivativeCoordinate_top hρ ht hβ hδ hphase heq

theorem rayDerivativeJet_hasDerivAt {q k : ℕ} {ρ β t : ℝ} (hρ : 0 < ρ) (ht : 0 < t)
    (hρβ : ρ = 1 + β) (hβ : β * (q : ℝ) = k) {δ η : ℂ}
    (hδ : δ ≠ 0) (hphase : δ ^ q = η ^ k) {y : ℂ → ℂ}
    (hy : Differentiable ℂ y) (heq : ∀ z, iteratedDeriv q y z = z ^ k * y z) :
    HasDerivAt (rayDerivativeJet q ρ β δ η y)
      (fun i => (η * δ) * rayDerivativeJet q ρ β δ η y t (cyclicSuccessor i) -
        (i.val : ℂ) * ((β / (ρ * t) : ℝ) : ℂ) * rayDerivativeJet q ρ β δ η y t i) t := by
  apply hasDerivAt_pi.mpr
  intro i
  have hi := rayDerivativeCoordinate_hasDerivAt hρ ht β hδ η hy i.val
  rw [rayDerivativeCoordinate_next_term hρ ht hρβ hδ,
    rayDerivativeCoordinate_cyclic hρ ht hβ hδ hphase heq] at hi
  exact hi

noncomputable def rayCompanionCoefficient (q : ℕ) (ρ β : ℝ) (δ η : ℂ) (t : ℝ) :
    Matrix (Fin q) (Fin q) ℂ :=
  (η * δ) • cyclicCompanion q +
    (-((β / (ρ * t) : ℝ) : ℂ)) • Matrix.diagonal (fun i : Fin q => (i.val : ℂ))

/-- LaTeX `eq:sharpness-scaled-system`, parametrized by real ray time:
the literal scaled derivatives satisfy the actual cyclic companion system. -/
theorem rayDerivativeJet_companion_hasDerivAt {q k : ℕ} {ρ β t : ℝ}
    (hρ : 0 < ρ) (ht : 0 < t) (hρβ : ρ = 1 + β) (hβ : β * (q : ℝ) = k)
    {δ η : ℂ} (hδ : δ ≠ 0) (hphase : δ ^ q = η ^ k) {y : ℂ → ℂ}
    (hy : Differentiable ℂ y) (heq : ∀ z, iteratedDeriv q y z = z ^ k * y z) :
    HasDerivAt (rayDerivativeJet q ρ β δ η y)
      ((rayCompanionCoefficient q ρ β δ η t).mulVec (rayDerivativeJet q ρ β δ η y t)) t := by
  apply (rayDerivativeJet_hasDerivAt hρ ht hρβ hβ hδ hphase hy heq).congr_deriv
  funext i
  simp only [rayCompanionCoefficient, Matrix.add_mulVec, Matrix.smul_mulVec,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_diagonal, cyclicCompanion_mulVec]
  ring

end ModifiedCartan
#print axioms ModifiedCartan.rayDerivativeJet_companion_hasDerivAt
