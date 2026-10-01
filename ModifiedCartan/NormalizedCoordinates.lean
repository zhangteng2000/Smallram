import ModifiedCartan.ShiftedCombinations
import ModifiedCartan.SystemMaximum
import ModifiedCartan.EntireTaylorJets
import FewInflection.InitialBasis

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- The actual vector g(b+z) J_b inverse from
LaTeX `lem:small-order-coordinates`, with J_b the derivative matrix. -/
noncomputable def normalizedCoordinates {n : ℕ} (g : Index n → ℂ → ℂ)
    (b : ℂ) (j : Index n) (z : ℂ) : ℂ := FewInflection.initialBasis g b j (b + z)

theorem normalizedCoordinates_eq_vecMul {n : ℕ} (g : Index n → ℂ → ℂ)
    (b z : ℂ) :
    (fun j => normalizedCoordinates g b j z) =
      Matrix.vecMul (fun k => g k (b + z)) (FewInflection.jetMatrix g b)⁻¹ := by
  classical
  funext j
  simp only [normalizedCoordinates, FewInflection.initialBasis, FewInflection.initialBasisCoeff,
    Matrix.vecMul, dotProduct, mul_comm]

theorem normalizedCoordinates_differentiable {n : ℕ} {g : Index n → ℂ → ℂ}
    (hg : ∀ j, Differentiable ℂ (g j)) (b : ℂ) (j : Index n) :
    Differentiable ℂ (normalizedCoordinates g b j) :=
  shiftedCombination_differentiable hg (FewInflection.initialBasisCoeff g b j) b

theorem normalizedCoordinates_initialJets {n : ℕ} {g : Index n → ℂ → ℂ}
    (hg : ∀ j, Differentiable ℂ (g j)) {b : ℂ}
    (hW : FewInflection.wronskian n g b ≠ 0) (i j : Index n) :
    iteratedDeriv i.val (normalizedCoordinates g b j) 0 = if i = j then 1 else 0 := by
  change iteratedDeriv i.val (fun z => FewInflection.initialBasis g b j (b + z)) 0 = _
  rw [iteratedDeriv_comp_const_add]
  simpa only [add_zero] using
    FewInflection.initialBasis_derivative hW (fun i k => (hg k).contDiff.contDiffAt) i j

theorem normalizedCoordinates_entireOrder_le {n : ℕ} {g : Index n → ℂ → ℂ}
    (hg : ∀ j, Differentiable ℂ (g j)) (b : ℂ) {ρ : EReal}
    (hρ : 0 ≤ ρ) (ho : ∀ j, entireOrder (g j) ≤ ρ) (j : Index n) :
    entireOrder (normalizedCoordinates g b j) ≤ ρ :=
  shiftedCombination_entireOrder_le hg (FewInflection.initialBasisCoeff g b j) b hρ ho

theorem normalizedCoordinates_reconstruct {n : ℕ} {g : Index n → ℂ → ℂ}
    {b : ℂ} (hW : FewInflection.wronskian n g b ≠ 0) (j : Index n) (z : ℂ) :
    g j z = ∑ i, iteratedDeriv i.val (g j) b * normalizedCoordinates g b i (z - b) := by
  classical
  have hh := FewInflection.initialBasis_reconstruct_combination hW
    (fun k => if k = j then 1 else 0) z
  simpa [normalizedCoordinates, add_sub_cancel_left, ite_mul] using hh

set_option backward.isDefEq.respectTransparency false in
theorem normalizedCoordinates_wronskian {n : ℕ} {g : Index n → ℂ → ℂ}
    (hg : ∀ j, Differentiable ℂ (g j)) (b z : ℂ) :
    FewInflection.wronskian n (normalizedCoordinates g b) z =
      FewInflection.wronskian n g (b + z) * (FewInflection.jetMatrix g b)⁻¹.det := by
  have he : normalizedCoordinates g b = fun j z =>
      ∑ k, g k (b + z) * (FewInflection.jetMatrix g b)⁻¹ k j := by
    funext j z
    simp only [normalizedCoordinates, FewInflection.initialBasis, FewInflection.initialBasisCoeff, mul_comm]
  have hshift (j : Index n) : Differentiable ℂ (fun w => g j (b + w)) :=
    (hg j).comp (by fun_prop)
  rw [he, FewInflection.wronskian_matrix_gauge (fun j w => g j (b + w))
    (FewInflection.jetMatrix g b)⁻¹ z (fun i j => (hshift j).contDiff.contDiffAt)]
  congr 1
  unfold FewInflection.wronskian
  congr 1
  funext i j
  rw [iteratedDeriv_comp_const_add]

theorem normalizedCoordinates_wronskian_zero {n : ℕ} {g : Index n → ℂ → ℂ}
    (hg : ∀ j, Differentiable ℂ (g j)) {b : ℂ}
    (hW : FewInflection.wronskian n g b ≠ 0) :
    FewInflection.wronskian n (normalizedCoordinates g b) 0 = 1 :=
  wronskian_zero_of_initial_jets (normalizedCoordinates_initialJets hg hW)

theorem normalizedCoordinates_inverse_det_ne_zero {n : ℕ} {g : Index n → ℂ → ℂ}
    (hg : ∀ j, Differentiable ℂ (g j)) {b : ℂ}
    (hW : FewInflection.wronskian n g b ≠ 0) :
    (FewInflection.jetMatrix g b)⁻¹.det ≠ 0 := by
  have hh := normalizedCoordinates_wronskian hg b 0
  rw [normalizedCoordinates_wronskian_zero hg hW, add_zero] at hh
  exact (mul_ne_zero_iff.mp (hh ▸ one_ne_zero)).2

end ModifiedCartan
#print axioms ModifiedCartan.normalizedCoordinates_initialJets
#print axioms ModifiedCartan.normalizedCoordinates_entireOrder_le
#print axioms ModifiedCartan.normalizedCoordinates_reconstruct
#print axioms ModifiedCartan.normalizedCoordinates_wronskian
