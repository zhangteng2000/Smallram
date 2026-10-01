import ModifiedCartan.LocalJetDeterminantBounds

open scoped BigOperators
set_option autoImplicit false
namespace ModifiedCartan

theorem norm_matrix_det_le_of_row_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (M : ι → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hA : ∀ i j, ‖A i j‖ ≤ M i) :
    ‖A.det‖ ≤ ((Fintype.card ι).factorial : ℝ) * ∏ i, M i := by
  rw [← Matrix.det_transpose A, Matrix.det_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, ‖Equiv.Perm.sign σ • ∏ i, A.transpose (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm ι, ∏ i, M i := by
      apply Finset.sum_le_sum
      intro σ _
      rw [norm_units_zsmul]
      calc
        _ ≤ ∏ i, ‖A i (σ i)‖ := Finset.norm_prod_le _ _
        _ ≤ ∏ i, M i := by
          apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          intro i _
          exact hA i (σ i)
    _ = _ := by simp [Fintype.card_perm]

theorem norm_matrix_det_le_zero_row {n : ℕ} (A : Matrix (Index n) (Index n) ℂ)
    {B : ℝ} (hB : 0 ≤ B) (hA : ∀ i j, i ≠ 0 → ‖A i j‖ ≤ B) :
    ‖A.det‖ ≤ ((n + 1).factorial : ℝ) * ‖A 0‖ * B ^ n := by
  classical
  let M : Index n → ℝ := fun i => if i = 0 then ‖A 0‖ else B
  have hM (i : Index n) : 0 ≤ M i := by dsimp [M]; split_ifs <;> positivity
  have hb := norm_matrix_det_le_of_row_bounds A M hM (by
    intro i j
    dsimp [M]
    split_ifs with hi
    · subst i; exact norm_le_pi_norm (A 0) j
    · exact hA i j hi)
  have hp : (∏ i, M i) = ‖A 0‖ * B ^ n := by
    rw [Fin.prod_univ_succ]
    simp [M]
  simpa only [Index, FewInflection.Index, Fintype.card_fin, hp, mul_assoc] using hb

end ModifiedCartan
#print axioms ModifiedCartan.norm_matrix_det_le_zero_row
