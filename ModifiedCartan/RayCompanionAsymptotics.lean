import ModifiedCartan.RayFourierSystem
import ModifiedCartan.FirstOrderPiTail

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem sharpnessFourier_mulVec_injective {q : ℕ} (hq : 1 ≤ q) :
    Function.Injective (sharpnessFourier q).mulVec := by
  intro v w hvw
  have he := congrArg (sharpnessFourierInverse q).mulVec hvw
  simpa only [Matrix.mulVec_mulVec, sharpnessFourierInverse_mul hq, Matrix.one_mulVec] using he

theorem matrix_mulVec_continuous {q : ℕ} (M : Matrix (Fin q) (Fin q) ℂ) :
    Continuous M.mulVec := by
  apply continuous_pi
  intro i
  change Continuous (fun v : Fin q → ℂ => ∑ j, M i j * v j)
  fun_prop

/-- The actual fundamental system of the scaled cyclic ray equation, including
its scalar first-coordinate asymptotics. This expands the undoing of the Fourier
transformation in Step 2 of `prop:sharpness-orders`. -/
theorem rayCompanion_tail_fundamental_system_exists {q : ℕ} (hq : 1 ≤ q)
    (ρ β : ℝ) {δ η : ℂ} (hδ : δ ≠ 0) (hη : η ≠ 0) :
    ∃ T : ℝ, 1 ≤ T ∧ ∃ Y : Fin q → ℝ → Fin q → ℂ,
      (∀ j t, T ≤ t → HasDerivAt (Y j)
        ((rayCompanionCoefficient q ρ β δ η t).mulVec (Y j t)) t) ∧
      (∀ t, T ≤ t → LinearIndependent ℂ (fun j => Y j t)) ∧
      (∀ j, Tendsto (fun t : ℝ => t ^ (-rayDiagonalPower q ρ β) •
        (Complex.exp (-raySpectralValues q δ η j * (t : ℂ)) • Y j t))
        atTop (𝓝 (fun i : Fin q => sharpnessRoot q j ^ i.val))) := by
  let lam := raySpectralValues q δ η
  let B := rayDiagonalPerturbation q ρ β
  let b := rayDiagonalPower q ρ β
  let V := sharpnessFourier q
  let U := sharpnessFourierInverse q
  obtain ⟨T, hT, Z, hd, hli, hl⟩ := firstOrder_diagonal_pi_tail_exists lam
    (raySpectralValues_injective hq hδ hη) B b (rayDiagonalPerturbation_diagonal hq ρ β)
  let Y : Fin q → ℝ → Fin q → ℂ := fun j t => V.mulVec (Z j t)
  have hVU : V * U = 1 := sharpnessFourier_mul_inverse hq
  have hcoef (t : ℝ) : V * (Matrix.diagonal lam + ((t⁻¹ : ℝ) : ℂ) • B) =
      rayCompanionCoefficient q ρ β δ η t * V := by
    rw [← rayFourier_coefficient hq]
    change V * (U * rayCompanionCoefficient q ρ β δ η t * V) = _
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hVU, Matrix.one_mul]
  refine ⟨T + 1, by linarith, Y, ?_, ?_, ?_⟩
  · intro j t ht
    have hTt : T < t := by linarith
    have hdz := (hd j t hTt.le).hasDerivAt (Ici_mem_nhds hTt)
    have hdy := matrix_mulVec_hasDerivAt V hdz
    apply hdy.congr_deriv
    rw [Matrix.mulVec_mulVec, hcoef, ← Matrix.mulVec_mulVec]
  · intro t ht
    have hTt : T ≤ t := by linarith
    exact (hli t hTt).map' (Matrix.toLin' V)
      (LinearMap.ker_eq_bot_of_injective (sharpnessFourier_mulVec_injective hq))
  · intro j
    have hc := matrix_mulVec_continuous V
    have he := (hc.tendsto (Pi.single j (1 : ℂ))).comp (hl j)
    have hval : V.mulVec (Pi.single j (1 : ℂ)) = fun i : Fin q => sharpnessRoot q j ^ i.val := by
      rw [Matrix.mulVec_single_one]
      rfl
    have hfun (t : ℝ) : V.mulVec (t ^ (-b) • (Complex.exp (-lam j * (t : ℂ)) • Z j t)) =
        t ^ (-b) • (Complex.exp (-lam j * (t : ℂ)) • Y j t) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
    change Tendsto (fun t : ℝ => V.mulVec (t ^ (-b) • (Complex.exp (-lam j * (t : ℂ)) • Z j t)))
      atTop (𝓝 (V.mulVec (Pi.single j (1 : ℂ)))) at he
    simpa only [hval, hfun] using! he

end ModifiedCartan
#print axioms ModifiedCartan.rayCompanion_tail_fundamental_system_exists

