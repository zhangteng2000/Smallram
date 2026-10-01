import FewInflection.PolynomialJets
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Initial-value bases from a nonzero Wronskian

At a point where the jet matrix is invertible, its inverse gives a basis
whose first `n+1` derivatives are prescribed.  This is the elementary
linear-algebra input behind the initial-value estimate in the paper.  The
construction below keeps the orientation of the jet matrix explicit, so no
analytic or growth statement is hidden in the definition.
-/

open scoped BigOperators

namespace FewInflection

noncomputable section

def jetMatrix {n : ℕ} (g : Index n → ℂ → ℂ) (a : ℂ) :
    Matrix (Index n) (Index n) ℂ :=
  fun i j => iteratedDeriv (i : ℕ) (g j) a

def initialBasisCoeff {n : ℕ} (g : Index n → ℂ → ℂ) (a : ℂ)
    (j : Index n) : Index n → ℂ :=
  fun k => (jetMatrix g a)⁻¹ k j

def initialBasis {n : ℕ} (g : Index n → ℂ → ℂ) (a : ℂ)
    (j : Index n) : ℂ → ℂ :=
  fun z => ∑ k : Index n, initialBasisCoeff g a j k * g k z

theorem jetMatrix_det_eq_wronskian
    {n : ℕ} (g : Index n → ℂ → ℂ) (a : ℂ) :
    (jetMatrix g a).det = wronskian n g a := by
  rfl

theorem initialBasis_derivative
    {n : ℕ} {g : Index n → ℂ → ℂ} {a : ℂ}
    (hW : wronskian n g a ≠ 0)
    (hcont : ∀ i j : Index n,
      ContDiffAt ℂ (i : ℕ) (g j) a) :
    ∀ i j : Index n,
      iteratedDeriv (i : ℕ) (initialBasis g a j) a =
        if i = j then 1 else 0 := by
  classical
  intro i j
  let M : Matrix (Index n) (Index n) ℂ := jetMatrix g a
  have hdet : M.det ≠ 0 := by
    rw [show M.det = wronskian n g a by rfl]
    exact hW
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have hmul : M * M⁻¹ = (1 : Matrix (Index n) (Index n) ℂ) :=
    Matrix.mul_nonsing_inv M hunit
  have hsum : ∑ k : Index n, M i k * M⁻¹ k j =
      if i = j then 1 else 0 := by
    have hentry := congrArg (fun N : Matrix (Index n) (Index n) ℂ => N i j) hmul
    simpa [Matrix.mul_apply, Matrix.one_apply] using hentry
  change iteratedDeriv (i : ℕ)
    (fun z => ∑ k : Index n, initialBasisCoeff g a j k * g k z) a = _
  rw [iteratedDeriv_fun_sum]
  · simp_rw [iteratedDeriv_const_mul_field]
    change (∑ k : Index n,
      (M⁻¹ k j) * iteratedDeriv (i : ℕ) (g k) a) =
      if i = j then 1 else 0
    rw [show (∑ k : Index n,
        (M⁻¹ k j) * iteratedDeriv (i : ℕ) (g k) a) =
        ∑ k : Index n, M i k * M⁻¹ k j by
      apply Finset.sum_congr rfl
      intro k hk
      rw [show M i k = iteratedDeriv (i : ℕ) (g k) a by rfl]
      exact mul_comm _ _]
    exact hsum
  · intro k hk
    simpa [initialBasisCoeff] using
      ((contDiffAt_const :
          ContDiffAt ℂ (i : ℕ) (fun _ : ℂ => M⁻¹ k j) a).mul (hcont i k))

theorem initialBasis_jetMatrix_mul
    {n : ℕ} {g : Index n → ℂ → ℂ} {a : ℂ}
    (hW : wronskian n g a ≠ 0)
    (hcont : ∀ i j : Index n,
      ContDiffAt ℂ (i : ℕ) (g j) a) :
    ∀ i j : Index n,
      iteratedDeriv (i : ℕ) (initialBasis g a j) a =
        (1 : Matrix (Index n) (Index n) ℂ) i j := by
  intro i j
  rw [Matrix.one_apply]
  exact initialBasis_derivative hW hcont i j

theorem initialBasis_reconstruct_combination
    {n : ℕ} {g : Index n → ℂ → ℂ} {a : ℂ}
    (hW : wronskian n g a ≠ 0)
    (c : Index n → ℂ) (z : ℂ) :
    ∑ k : Index n, c k * g k z =
      ∑ i : Index n,
        (∑ k : Index n, c k * iteratedDeriv (i : ℕ) (g k) a) *
          initialBasis g a i z := by
  classical
  let M : Matrix (Index n) (Index n) ℂ := jetMatrix g a
  have hdet : M.det ≠ 0 := by
    rw [show M.det = wronskian n g a by rfl]
    exact hW
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have hinv : M⁻¹ * M = (1 : Matrix (Index n) (Index n) ℂ) :=
    Matrix.nonsing_inv_mul M hunit
  have hcoeff (l : Index n) :
      ∑ i : Index n,
          (∑ k : Index n, c k * M i k) * M⁻¹ l i = c l := by
    have hentry := congrArg (fun N : Matrix (Index n) (Index n) ℂ =>
      (N.mulVec c) l) hinv
    rw [← Matrix.mulVec_mulVec] at hentry
    have hentry' :
        (∑ i : Index n, M⁻¹ l i * (∑ k : Index n, M i k * c k)) = c l := by
      simpa [Matrix.mulVec, Matrix.mul_apply, Matrix.one_apply, dotProduct] using hentry
    calc
      ∑ i : Index n,
          (∑ k : Index n, c k * M i k) * M⁻¹ l i =
          ∑ i : Index n,
            M⁻¹ l i * (∑ k : Index n, M i k * c k) := by
              apply Finset.sum_congr rfl
              intro i hi
              calc
                (∑ k : Index n, c k * M i k) * M⁻¹ l i =
                    (∑ k : Index n, M i k * c k) * M⁻¹ l i := by
                      congr 1
                      apply Finset.sum_congr rfl
                      intro k hk
                      ring
                _ = M⁻¹ l i * (∑ k : Index n, M i k * c k) := by ring
      _ = c l := hentry'
  change ∑ k : Index n, c k * g k z =
    ∑ i : Index n,
      (∑ k : Index n, c k * M i k) *
        (∑ l : Index n, M⁻¹ l i * g l z)
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  rw [hcoeff l]

theorem curve_initialBasis_derivative
    {n : ℕ} (f : Curve n) {a : ℂ}
    (hW : wronskian n f.coord a ≠ 0) :
    ∀ i j : Index n,
      iteratedDeriv (i : ℕ) (initialBasis f.coord a j) a =
        if i = j then 1 else 0 := by
  apply initialBasis_derivative hW
  intro i j
  exact (f.holomorphic j).contDiff.contDiffAt

end

end FewInflection
