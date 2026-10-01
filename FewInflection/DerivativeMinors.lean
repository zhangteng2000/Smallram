import FewInflection.Results

/-!
# Derivative minors

The polynomial-space part of the paper uses determinants of arbitrary finite
lists of derivative orders.  This file proves the change-of-basis identities
for those determinants directly from the iterated-derivative rules.  The
Wronskian is the special case in which the order list is `i ↦ i`.
-/

open scoped BigOperators

namespace FewInflection

noncomputable section

def derivativeMinor {n : ℕ} (orders : Index n → ℕ)
    (f : Index n → ℂ → ℂ) (z : ℂ) : ℂ :=
  Matrix.det (fun (i j : Index n) =>
    iteratedDeriv (orders i) (f j) z)

theorem derivativeMinor_constGauge
    {n : ℕ} (orders : Index n → ℕ) (f : Index n → ℂ → ℂ)
    (c z : ℂ)
    (hf : ∀ i j : Index n, ContDiffAt ℂ (orders i) (f j) z) :
    derivativeMinor orders (fun j x => c * f j x) z =
      c ^ (n + 1) * derivativeMinor orders f z := by
  let M : Matrix (Index n) (Index n) ℂ :=
    fun (i : Index n) (j : Index n) =>
      iteratedDeriv (orders i) (f j) z
  have hM :
      (fun (i : Index n) (j : Index n) =>
        iteratedDeriv (orders i) (fun x => c * f j x) z) = c • M := by
    funext i j
    rw [iteratedDeriv_const_mul c (hf i j)]
    rfl
  calc
    derivativeMinor orders (fun j x => c * f j x) z = (c • M).det := by
      simp only [derivativeMinor, hM]
    _ = c ^ Fintype.card (Index n) * M.det := Matrix.det_smul M c
    _ = c ^ (n + 1) * derivativeMinor orders f z := by
      rw [Fintype.card_fin]
      rfl

theorem derivativeMinor_matrixGauge
    {n : ℕ} (orders : Index n → ℕ) (f : Index n → ℂ → ℂ)
    (A : Matrix (Index n) (Index n) ℂ) (z : ℂ)
    (hf : ∀ i j : Index n, ContDiffAt ℂ (orders i) (f j) z) :
    derivativeMinor orders
        (fun j x => ∑ k : Index n, f k x * A k j) z =
      derivativeMinor orders f z * A.det := by
  let M : Matrix (Index n) (Index n) ℂ :=
    fun (i : Index n) (j : Index n) =>
      iteratedDeriv (orders i) (f j) z
  have hM :
      (fun (i : Index n) (j : Index n) =>
        iteratedDeriv (orders i)
          (fun x => ∑ k : Index n, f k x * A k j) z) = M * A := by
    funext i j
    change iteratedDeriv (orders i)
        (fun x => ∑ k : Index n, f k x * A k j) z =
      ∑ k : Index n, iteratedDeriv (orders i) (f k) z * A k j
    rw [iteratedDeriv_fun_sum]
    · simp only [iteratedDeriv_mul_const_field]
    · intro k hk
      simpa [smul_eq_mul] using (hf i k).smul_const (A k j)
  calc
    derivativeMinor orders
        (fun j x => ∑ k : Index n, f k x * A k j) z = (M * A).det := by
      simp only [derivativeMinor, hM]
    _ = M.det * A.det := Matrix.det_mul M A
    _ = derivativeMinor orders f z * A.det := by rfl

theorem derivativeMinor_matrixGauge_ne_zero
    {n : ℕ} (orders : Index n → ℕ) (f : Index n → ℂ → ℂ)
    (A : Matrix (Index n) (Index n) ℂ) (z : ℂ)
    (hf : ∀ i j : Index n, ContDiffAt ℂ (orders i) (f j) z)
    (hminor : derivativeMinor orders f z ≠ 0)
    (hA : IsUnit A.det) :
    derivativeMinor orders
        (fun j x => ∑ k : Index n, f k x * A k j) z ≠ 0 := by
  rw [derivativeMinor_matrixGauge orders f A z hf]
  exact mul_ne_zero hminor hA.ne_zero

theorem derivativeMinor_wronskian_special_case
    {n : ℕ} (f : Index n → ℂ → ℂ) (z : ℂ) :
    derivativeMinor (fun i : Index n => (i : ℕ)) f z =
      wronskian n f z := by
  rfl

theorem derivativeMinor_translate
    {n : ℕ} (orders : Index n → ℕ) (f : Index n → ℂ → ℂ)
    (a z : ℂ) :
    derivativeMinor orders (fun j x => f j (x + a)) z =
      derivativeMinor orders f (z + a) := by
  unfold derivativeMinor
  congr 1
  funext i j
  rw [iteratedDeriv_comp_add_const]

theorem derivativeMinor_dilate
    {n : ℕ} (orders : Index n → ℕ) (f : Index n → ℂ → ℂ)
    (t z : ℂ)
    (hf : ∀ j : Index n, ContDiff ℂ (⊤ : WithTop ℕ∞) (f j)) :
    derivativeMinor orders (fun j x => f j (t * x)) z =
      (∏ i : Index n, t ^ (orders i)) *
        derivativeMinor orders f (t * z) := by
  let M : Matrix (Index n) (Index n) ℂ :=
    fun (i : Index n) (j : Index n) =>
      iteratedDeriv (orders i) (f j) (t * z)
  let D : Matrix (Index n) (Index n) ℂ :=
    Matrix.diagonal (fun i => t ^ (orders i))
  have hM :
      (fun (i : Index n) (j : Index n) =>
        iteratedDeriv (orders i) (fun x => f j (t * x)) z) = D * M := by
    funext i j
    have hcomp := congrFun
      (iteratedDeriv_comp_const_mul (n := orders i)
        ((hf j).of_le (by simp)) t) z
    have hDM : (D * M) i j = t ^ (orders i) * M i j := by
      rw [Matrix.mul_apply]
      simp [D, M, Matrix.diagonal_apply, dotProduct]
    rw [hDM]
    exact hcomp
  calc
    derivativeMinor orders (fun j x => f j (t * x)) z = (D * M).det := by
      simp only [derivativeMinor, hM]
    _ = D.det * M.det := Matrix.det_mul D M
    _ = (∏ i : Index n, t ^ (orders i)) *
          derivativeMinor orders f (t * z) := by
      rw [Matrix.det_diagonal]
      rfl

theorem derivativeMinor_affineDilate
    {n : ℕ} (orders : Index n → ℕ) (f : Index n → ℂ → ℂ)
    (a t z : ℂ)
    (hf : ∀ j : Index n, ContDiff ℂ (⊤ : WithTop ℕ∞) (f j)) :
    derivativeMinor orders (fun j x => f j (a + t * x)) z =
      (∏ i : Index n, t ^ (orders i)) *
        derivativeMinor orders f (a + t * z) := by
  have hshift : ∀ j : Index n,
      ContDiff ℂ (⊤ : WithTop ℕ∞) (fun x : ℂ => f j (x + a)) := by
    intro j
    exact (hf j).comp (contDiff_id.add contDiff_const)
  have h := derivativeMinor_dilate orders (fun j x => f j (x + a)) t z hshift
  rw [derivativeMinor_translate] at h
  simpa only [add_comm] using h

end

end FewInflection
