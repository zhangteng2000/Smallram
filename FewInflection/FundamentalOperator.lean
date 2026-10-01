import FewInflection.WronskianRegularity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open scoped BigOperators Topology

namespace FewInflection

noncomputable section

/- A matrix form of Cramer's rule that is convenient for the fundamental
   differential relation.  This is a purely algebraic consequence of the
   nonsingular inverse API: no coefficient function is postulated. -/
lemma vecMul_solution_cramer
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ} {x b : ι → ℂ}
    (hM : IsUnit M.det) (hsol : Matrix.vecMul x M = b) :
    M.det • x = Matrix.cramer M.transpose b := by
  have hcancel : Matrix.vecMul b M⁻¹ = x := by
    rw [← hsol]
    rw [Matrix.vecMul_vecMul]
    rw [Matrix.mul_nonsing_inv M hM]
    exact Matrix.vecMul_one x
  have hcr := Matrix.det_smul_inv_vecMul_eq_cramer_transpose M b hM
  rw [hcancel] at hcr
  exact hcr

/-! ### The pointwise fundamental differential relation

This is the first, purely algebraic part of the fundamental-operator
construction.  At a point where the Wronskian is nonzero, the jet matrix is
invertible, so the `(n+1)`-st derivatives of all components have one and only
one linear relation with the derivatives of orders `0, ..., n`.

The analytic continuation of the coefficients and their pole estimates are
separate statements; this lemma deliberately exposes the exact local input
needed for those later arguments.
-/

theorem fundamental_coefficients_exists_unique
    {n : ℕ} {g : Index n → ℂ → ℂ} {z : ℂ}
    (hW : wronskian n g z ≠ 0) :
    ∃! b : Index n → ℂ, ∀ j : Index n,
      iteratedDeriv (n + 1) (g j) z +
        ∑ i : Index n, b i * iteratedDeriv (i : ℕ) (g j) z = 0 := by
  classical
  let M : Matrix (Index n) (Index n) ℂ :=
    fun i j => iteratedDeriv (i : ℕ) (g j) z
  have hdet : M.det ≠ 0 := by
    simpa [M, wronskian] using hW
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have hunitM : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 hunit
  have hsurj : Function.Surjective
      (fun b : Index n → ℂ => Matrix.vecMul b M) :=
    Matrix.vecMul_surjective_iff_isUnit.mpr hunitM
  let rhs : Index n → ℂ :=
    fun j => -iteratedDeriv (n + 1) (g j) z
  obtain ⟨b, hb⟩ := hsurj rhs
  refine ⟨b, ?_, ?_⟩
  · intro j
    have hj := congrFun hb j
    change Matrix.vecMul b M j = rhs j at hj
    rw [Matrix.vecMul_eq_sum, Finset.sum_apply] at hj
    simp [M, smul_eq_mul] at hj
    change iteratedDeriv (n + 1) (g j) z +
      ∑ i : Index n, b i * iteratedDeriv (i : ℕ) (g j) z = 0
    rw [hj]
    ring
  · intro c hc
    have hcinj : Function.Injective
        (fun b : Index n → ℂ => Matrix.vecMul b M) :=
      Matrix.vecMul_injective_iff_isUnit.mpr hunitM
    have hcvec : Matrix.vecMul c M = rhs := by
      funext j
      rw [Matrix.vecMul_eq_sum, Finset.sum_apply]
      simp [M, smul_eq_mul]
      dsimp [rhs]
      linear_combination hc j
    exact hcinj (hcvec.trans hb.symm)

/- The coefficient vector can be chosen canonically from the proved local
   existence theorem.  At a Wronskian zero we use the harmless zero value; all
   equations below are stated only on the nonzero-Wronskian locus. -/
noncomputable def fundamentalCoefficients
    (n : ℕ) (g : Index n → ℂ → ℂ) (z : ℂ) : Index n → ℂ :=
  if hW : wronskian n g z ≠ 0 then
    Classical.choose (fundamental_coefficients_exists_unique hW)
  else 0

theorem fundamentalCoefficients_spec
    {n : ℕ} {g : Index n → ℂ → ℂ} {z : ℂ}
    (hW : wronskian n g z ≠ 0) :
    ∀ j : Index n,
      iteratedDeriv (n + 1) (g j) z +
        ∑ i : Index n, fundamentalCoefficients n g z i *
          iteratedDeriv (i : ℕ) (g j) z = 0 := by
  classical
  rw [fundamentalCoefficients, dite_eq_left hW]
  exact (fundamental_coefficients_exists_unique hW).choose_spec.1

theorem fundamentalCoefficients_unique
    {n : ℕ} {g : Index n → ℂ → ℂ} {z : ℂ}
    (hW : wronskian n g z ≠ 0) {b : Index n → ℂ}
    (hb : ∀ j : Index n,
      iteratedDeriv (n + 1) (g j) z +
        ∑ i : Index n, b i * iteratedDeriv (i : ℕ) (g j) z = 0) :
    b = fundamentalCoefficients n g z := by
  exact (fundamental_coefficients_exists_unique hW).unique
    hb (fundamentalCoefficients_spec hW)

theorem fundamentalCoefficients_cramer
    {n : ℕ} {g : Index n → ℂ → ℂ} {z : ℂ}
    (hW : wronskian n g z ≠ 0) :
    let M : Matrix (Index n) (Index n) ℂ :=
      fun i j => iteratedDeriv (i : ℕ) (g j) z
    let rhs : Index n → ℂ :=
      fun j => -iteratedDeriv (n + 1) (g j) z
    M.det • fundamentalCoefficients n g z = Matrix.cramer M.transpose rhs := by
  classical
  dsimp
  let M : Matrix (Index n) (Index n) ℂ :=
    fun i j => iteratedDeriv (i : ℕ) (g j) z
  let rhs : Index n → ℂ :=
    fun j => -iteratedDeriv (n + 1) (g j) z
  have hdet : M.det ≠ 0 := by
    simpa [M, wronskian] using hW
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have hsol : Matrix.vecMul (fundamentalCoefficients n g z) M = rhs := by
    funext j
    have hj := fundamentalCoefficients_spec hW j
    change Matrix.vecMul (fundamentalCoefficients n g z) M j = rhs j
    rw [Matrix.vecMul_eq_sum]
    simp [M, rhs, smul_eq_mul]
    linear_combination hj
  exact vecMul_solution_cramer hunit hsol

end

end FewInflection
