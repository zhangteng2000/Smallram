import ModifiedCartan.RayCompanionSystem
import ModifiedCartan.FirstOrderDiagonalTail

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

noncomputable def raySpectralValues (q : ℕ) (δ η : ℂ) (j : Fin q) : ℂ :=
  (η * δ) * sharpnessRoot q j

noncomputable def rayDiagonalPerturbation (q : ℕ) (ρ β : ℝ) : Matrix (Fin q) (Fin q) ℂ :=
  (-((β / ρ : ℝ) : ℂ)) • (sharpnessFourierInverse q *
    Matrix.diagonal (fun i : Fin q => (i.val : ℂ)) * sharpnessFourier q)

noncomputable def rayDiagonalPower (q : ℕ) (ρ β : ℝ) : ℝ := -β * ((q : ℝ) - 1) / (2 * ρ)

theorem raySpectralValues_injective {q : ℕ} (hq : 1 ≤ q) {δ η : ℂ}
    (hδ : δ ≠ 0) (hη : η ≠ 0) : Function.Injective (raySpectralValues q δ η) := by
  intro i j hij
  exact sharpnessRoot_injective hq (mul_left_cancel₀ (mul_ne_zero hη hδ) hij)

theorem rayDiagonalPerturbation_diagonal {q : ℕ} (hq : 1 ≤ q) (ρ β : ℝ) (j : Fin q) :
    rayDiagonalPerturbation q ρ β j j = (rayDiagonalPower q ρ β : ℂ) := by
  rw [rayDiagonalPerturbation, Matrix.smul_apply, smul_eq_mul, sharpnessFourier_degree_diagonal hq]
  unfold rayDiagonalPower
  push_cast
  ring

theorem rayFourier_coefficient {q : ℕ} (hq : 1 ≤ q) (ρ β : ℝ) (δ η : ℂ) (t : ℝ) :
    sharpnessFourierInverse q * rayCompanionCoefficient q ρ β δ η t * sharpnessFourier q =
      Matrix.diagonal (raySpectralValues q δ η) +
        ((t⁻¹ : ℝ) : ℂ) • rayDiagonalPerturbation q ρ β := by
  simp only [rayCompanionCoefficient, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, sharpnessFourier_diagonalizes_companion hq]
  have hc : -((β / (ρ * t) : ℝ) : ℂ) =
      ((t⁻¹ : ℝ) : ℂ) * (-((β / ρ : ℝ) : ℂ)) := by
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_inv,
      div_eq_mul_inv, mul_inv_rev]
    ring
  have hlead : (η * δ) • Matrix.diagonal (sharpnessRoot q) =
      Matrix.diagonal (raySpectralValues q δ η) := by
    rw [← Matrix.diagonal_smul]
    congr 1
  rw [hlead, hc, mul_smul] <;> rfl

theorem matrix_mulVec_hasDerivAt {q : ℕ} (U : Matrix (Fin q) (Fin q) ℂ)
    {Y : ℝ → Fin q → ℂ} {Y' : Fin q → ℂ} {t : ℝ} (hY : HasDerivAt Y Y' t) :
    HasDerivAt (fun u => U.mulVec (Y u)) (U.mulVec Y') t := by
  apply hasDerivAt_pi.mpr
  intro i
  simpa only [Matrix.mulVec, dotProduct] using!
    (HasDerivAt.fun_sum (u := Finset.univ)
      (fun j _ => (hasDerivAt_pi.mp hY j).const_mul (U i j)))

theorem matrix_conjugate_hasDerivAt {q : ℕ} (U V A : Matrix (Fin q) (Fin q) ℂ)
    (hVU : V * U = 1) {Y : ℝ → Fin q → ℂ} {t : ℝ}
    (hY : HasDerivAt Y (A.mulVec (Y t)) t) :
    HasDerivAt (fun u => U.mulVec (Y u)) ((U * A * V).mulVec (U.mulVec (Y t))) t := by
  apply (matrix_mulVec_hasDerivAt U hY).congr_deriv
  symm
  calc
    _ = ((U * A * V) * U).mulVec (Y t) := Matrix.mulVec_mulVec _ _ _
    _ = (U * A).mulVec (Y t) := by rw [Matrix.mul_assoc, hVU, Matrix.mul_one]
    _ = _ := (Matrix.mulVec_mulVec _ _ _).symm

noncomputable def rayFourierJet (q : ℕ) (ρ β : ℝ) (δ η : ℂ) (y : ℂ → ℂ) (t : ℝ) : Fin q → ℂ :=
  (sharpnessFourierInverse q).mulVec (rayDerivativeJet q ρ β δ η y t)

/-- LaTeX `eq:sharpness-scaled-system` after literal Fourier conjugation. -/
theorem rayFourierJet_hasDerivAt {q k : ℕ} (hq : 1 ≤ q) {ρ β t : ℝ}
    (hρ : 0 < ρ) (ht : 0 < t) (hρβ : ρ = 1 + β) (hβ : β * (q : ℝ) = k)
    {δ η : ℂ} (hδ : δ ≠ 0) (hphase : δ ^ q = η ^ k) {y : ℂ → ℂ}
    (hy : Differentiable ℂ y) (heq : ∀ z, iteratedDeriv q y z = z ^ k * y z) :
    HasDerivAt (rayFourierJet q ρ β δ η y)
      ((Matrix.diagonal (raySpectralValues q δ η) +
        ((t⁻¹ : ℝ) : ℂ) • rayDiagonalPerturbation q ρ β).mulVec (rayFourierJet q ρ β δ η y t)) t := by
  have hd := matrix_conjugate_hasDerivAt (sharpnessFourierInverse q) (sharpnessFourier q)
    (rayCompanionCoefficient q ρ β δ η t) (sharpnessFourier_mul_inverse hq)
    (rayDerivativeJet_companion_hasDerivAt hρ ht hρβ hβ hδ hphase hy heq)
  rw [rayFourier_coefficient hq] at hd
  exact hd

end ModifiedCartan
#print axioms ModifiedCartan.rayDiagonalPerturbation_diagonal
#print axioms ModifiedCartan.rayFourierJet_hasDerivAt



