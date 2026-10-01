import ModifiedCartan.NormComparison
import Mathlib.Analysis.Matrix.PosDef

open scoped BigOperators Matrix
open Matrix
set_option autoImplicit false
namespace ModifiedCartan

theorem euclideanNorm_sq {n : ℕ} (v : Index n → ℂ) :
    euclideanNorm v ^ 2 = ∑ j, ‖v j‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem star_dotProduct_self_eq_euclideanNorm_sq {n : ℕ} (v : Index n → ℂ) :
    star v ⬝ᵥ v = ((euclideanNorm v ^ 2 : ℝ) : ℂ) := by
  rw [euclideanNorm_sq]
  change (∑ j, star (v j) * v j) = _
  simp_rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

/-- The row-vector convention used by the manuscript: multiplication
on the right by a constant unitary matrix preserves the exact norm. -/
theorem euclideanNorm_vecMul_unitary {n : ℕ}
    (V : Matrix.unitaryGroup (Index n) ℂ) (x : Index n → ℂ) :
    euclideanNorm (x ᵥ* (V : Matrix (Index n) (Index n) ℂ)) = euclideanNorm x := by
  have hV : (V : Matrix (Index n) (Index n) ℂ) *
      (V : Matrix (Index n) (Index n) ℂ)ᴴ = 1 := V.property.2
  have hh : (x ᵥ* (V : Matrix (Index n) (Index n) ℂ)) ⬝ᵥ
      star (x ᵥ* (V : Matrix (Index n) (Index n) ℂ)) = x ⬝ᵥ star x := by
    rw [Matrix.star_vecMul, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      hV, Matrix.vecMul_one]
  rw [dotProduct_comm _ (star _), dotProduct_comm x (star x),
    star_dotProduct_self_eq_euclideanNorm_sq, star_dotProduct_self_eq_euclideanNorm_sq] at hh
  have hr := Complex.ofReal_injective hh
  have hn1 := euclideanNorm_nonneg (x ᵥ* (V : Matrix (Index n) (Index n) ℂ))
  have hn2 := euclideanNorm_nonneg x
  nlinarith

/-- Spectral decomposition of the actual Gram matrix supplies one
constant unitary basis change with orthogonal initial-jet columns. -/
theorem exists_unitary_gram_diagonal {n : ℕ} (J : Matrix (Index n) (Index n) ℂ) :
    ∃ V : Matrix.unitaryGroup (Index n) ℂ, ∃ d : Index n → ℝ,
      (∀ i, 0 ≤ d i) ∧
      (J * (V : Matrix (Index n) (Index n) ℂ))ᴴ *
        (J * (V : Matrix (Index n) (Index n) ℂ)) = Matrix.diagonal (fun i => (d i : ℂ)) := by
  let hG := Matrix.isHermitian_conjTranspose_mul_self J
  refine ⟨hG.eigenvectorUnitary, hG.eigenvalues,
    Matrix.eigenvalues_conjTranspose_mul_self_nonneg J, ?_⟩
  simpa only [Unitary.conjStarAlgAut_star_apply, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using hG.conjStarAlgAut_star_eigenvectorUnitary

theorem norm_det_unitary {n : ℕ} (V : Matrix.unitaryGroup (Index n) ℂ) :
    ‖(V : Matrix (Index n) (Index n) ℂ).det‖ = 1 := by
  have hh := congrArg norm (Matrix.det_of_mem_unitary V.property).1
  simp only [norm_mul, norm_star, norm_one] at hh
  have hn := norm_nonneg (V : Matrix (Index n) (Index n) ℂ).det
  nlinarith

theorem gram_diagonal_column_norms {n : ℕ} {K : Matrix (Index n) (Index n) ℂ}
    {d : Index n → ℝ} (hd : Kᴴ * K = Matrix.diagonal (fun i => (d i : ℂ))) (i : Index n) :
    euclideanNorm (fun k => K k i) ^ 2 = d i := by
  have he := congrFun (congrFun hd i) i
  simp only [Matrix.diagonal_apply_eq] at he
  change star (fun k => K k i) ⬝ᵥ (fun k => K k i) = (d i : ℂ) at he
  rw [star_dotProduct_self_eq_euclideanNorm_sq] at he
  exact Complex.ofReal_injective he

theorem prod_column_norms_of_diagonal_gram {n : ℕ} {K : Matrix (Index n) (Index n) ℂ}
    {d : Index n → ℝ} (hd : Kᴴ * K = Matrix.diagonal (fun i => (d i : ℂ))) :
    (∏ i, euclideanNorm (fun k => K k i)) = ‖K.det‖ := by
  have he := congrArg Matrix.det hd
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_diagonal,
    Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq] at he
  have he' : ((‖K.det‖ ^ 2 : ℝ) : ℂ) = (((∏ i, d i : ℝ)) : ℂ) := by
    simpa only [Complex.ofReal_prod] using he
  have hs : ‖K.det‖ ^ 2 = (∏ i, euclideanNorm (fun k => K k i)) ^ 2 := by
    have hh := Complex.ofReal_injective he'
    rw [← Finset.prod_pow] at ⊢
    simpa only [gram_diagonal_column_norms hd] using hh
  have hp : 0 ≤ ∏ i, euclideanNorm (fun k => K k i) :=
    Finset.prod_nonneg (fun i _ => euclideanNorm_nonneg _)
  have hn := norm_nonneg K.det
  nlinarith

/-- The exact finite-dimensional singular-value facts used in Step 1
of `lem:basis-at-point`, with actual unitary matrices and column lengths. -/
theorem exists_unitary_positive_column_norms {n : ℕ}
    (J : Matrix (Index n) (Index n) ℂ) (hJ : J.det ≠ 0) :
    ∃ V : Matrix.unitaryGroup (Index n) ℂ, ∃ σ : Index n → ℝ,
      (∀ j, 0 < σ j) ∧
      (∀ j, σ j = euclideanNorm (fun k => (J * (V : Matrix (Index n) (Index n) ℂ)) k j)) ∧
      (∀ i j, i ≠ j →
        star (fun k => (J * (V : Matrix (Index n) (Index n) ℂ)) k i) ⬝ᵥ
          (fun k => (J * (V : Matrix (Index n) (Index n) ℂ)) k j) = 0) ∧
      (∏ j, σ j) = ‖J.det‖ := by
  obtain ⟨V, d, _, hd⟩ := exists_unitary_gram_diagonal J
  let K := J * (V : Matrix (Index n) (Index n) ℂ)
  let σ : Index n → ℝ := fun j => euclideanNorm (fun k => K k j)
  have hprod : (∏ j, σ j) = ‖J.det‖ := by
    rw [prod_column_norms_of_diagonal_gram hd, Matrix.det_mul, norm_mul,
      norm_det_unitary, mul_one]
  refine ⟨V, σ, ?_, fun _ => rfl, ?_, hprod⟩
  · intro j
    have hp : (∏ j, σ j) ≠ 0 := by rw [hprod]; exact norm_ne_zero_iff.mpr hJ
    have hn : σ j ≠ 0 := (Finset.prod_ne_zero_iff.mp hp) j (Finset.mem_univ j)
    exact lt_of_le_of_ne (euclideanNorm_nonneg _) hn.symm
  · intro i j hij
    have he := congrFun (congrFun hd i) j
    change star (fun k => (J * (V : Matrix (Index n) (Index n) ℂ)) k i) ⬝ᵥ
      (fun k => (J * (V : Matrix (Index n) (Index n) ℂ)) k j) =
        Matrix.diagonal (fun k => (d k : ℂ)) i j at he
    simpa only [Matrix.diagonal_apply_ne _ hij] using he

end ModifiedCartan
#print axioms ModifiedCartan.euclideanNorm_vecMul_unitary
#print axioms ModifiedCartan.exists_unitary_gram_diagonal
#print axioms ModifiedCartan.exists_unitary_positive_column_norms
