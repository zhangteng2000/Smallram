import ModifiedCartan.SharpnessFourier

open scoped BigOperators
set_option autoImplicit false
namespace ModifiedCartan

def cyclicSuccessor {q : ℕ} (i : Fin q) : Fin q :=
  ⟨(i.val + 1) % q, Nat.mod_lt _ (by have := i.isLt; omega)⟩

def cyclicCompanion (q : ℕ) : Matrix (Fin q) (Fin q) ℂ :=
  fun i j => if j = cyclicSuccessor i then 1 else 0

theorem cyclicCompanion_mul {q : ℕ} (M : Matrix (Fin q) (Fin q) ℂ) (i j : Fin q) :
    (cyclicCompanion q * M) i j = M (cyclicSuccessor i) j := by
  simp [Matrix.mul_apply, cyclicCompanion]

theorem root_cyclic_power {q : ℕ} (hq : 1 ≤ q) (i j : Fin q) :
    sharpnessRoot q j ^ (cyclicSuccessor i).val =
      sharpnessRoot q j ^ i.val * sharpnessRoot q j := by
  by_cases hi : i.val + 1 < q
  · simp only [cyclicSuccessor, Nat.mod_eq_of_lt hi]
    exact pow_succ _ _
  · have he : i.val + 1 = q := by have := i.isLt; omega
    change sharpnessRoot q j ^ ((i.val + 1) % q) = _
    rw [he, Nat.mod_self, pow_zero, ← pow_succ, he, sharpnessRoot_pow hq]

theorem cyclicCompanion_fourier_eigenvectors {q : ℕ} (hq : 1 ≤ q) :
    cyclicCompanion q * sharpnessFourier q =
      sharpnessFourier q * Matrix.diagonal (sharpnessRoot q) := by
  ext i j
  rw [cyclicCompanion_mul, Matrix.mul_diagonal]
  exact root_cyclic_power hq i j

theorem sharpnessFourier_diagonalizes_companion {q : ℕ} (hq : 1 ≤ q) :
    sharpnessFourierInverse q * cyclicCompanion q * sharpnessFourier q =
      Matrix.diagonal (sharpnessRoot q) := by
  rw [Matrix.mul_assoc, cyclicCompanion_fourier_eigenvectors hq, ← Matrix.mul_assoc,
    sharpnessFourierInverse_mul hq, Matrix.one_mul]

theorem sharpnessFourier_conjugate_diagonal {q : ℕ} (d : Fin q → ℂ) (j : Fin q) :
    (sharpnessFourierInverse q * Matrix.diagonal d * sharpnessFourier q) j j =
      (q : ℂ)⁻¹ * ∑ i, d i := by
  rw [Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_diagonal]
  unfold sharpnessFourierInverse sharpnessFourier
  calc
    _ = (q : ℂ)⁻¹ * d i * ((sharpnessRoot q j ^ i.val)⁻¹ * sharpnessRoot q j ^ i.val) := by ring
    _ = _ := by rw [inv_mul_cancel₀ (pow_ne_zero _ (sharpnessRoot_ne_zero j)), mul_one]

theorem sum_fin_val_complex (q : ℕ) :
    (∑ i : Fin q, (i.val : ℂ)) = (q : ℂ) * ((q : ℂ) - 1) / 2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.cast_add, Nat.cast_one]
    ring

/-- Fourier conjugation replaces the degree diagonal by its actual arithmetic
mean, as required in `eq:sharpness-scaled-system`. -/
theorem sharpnessFourier_degree_diagonal {q : ℕ} (hq : 1 ≤ q) (j : Fin q) :
    (sharpnessFourierInverse q * Matrix.diagonal (fun i : Fin q => (i.val : ℂ)) *
      sharpnessFourier q) j j = ((q : ℂ) - 1) / 2 := by
  rw [sharpnessFourier_conjugate_diagonal, sum_fin_val_complex]
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

end ModifiedCartan
#print axioms ModifiedCartan.sharpnessFourier_diagonalizes_companion
#print axioms ModifiedCartan.sharpnessFourier_degree_diagonal
