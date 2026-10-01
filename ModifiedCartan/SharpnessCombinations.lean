import ModifiedCartan.SharpnessWronskian
import ModifiedCartan.EntirePrimitives
import FewInflection.InitialBasis

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

noncomputable def sharpnessCombination {n : ℕ} (g : Index n → ℂ → ℂ)
    (c : Index n → ℂ) (z : ℂ) : ℂ := ∑ j, c j * g j z

theorem IsSharpnessSystem.combination_differentiable {n k q : ℕ} {g : Index n → ℂ → ℂ}
    (h : IsSharpnessSystem n k q g) (c : Index n → ℂ) :
    Differentiable ℂ (sharpnessCombination g c) := by
  unfold sharpnessCombination
  exact Differentiable.fun_sum (fun j _ => (h.1 j).const_mul (c j))

theorem IsSharpnessSystem.combination_derivative {n k q : ℕ} {g : Index n → ℂ → ℂ}
    (h : IsSharpnessSystem n k q g) (c : Index n → ℂ) (i : ℕ) (z : ℂ) :
    iteratedDeriv i (sharpnessCombination g c) z = ∑ j, c j * iteratedDeriv i (g j) z := by
  unfold sharpnessCombination
  rw [iteratedDeriv_fun_sum]
  · simp only [iteratedDeriv_const_mul_field]
  · intro j _
    exact (contDiffAt_const : ContDiffAt ℂ i (fun _ : ℂ => c j) z).mul
      (h.1 j).contDiff.contDiffAt

theorem IsSharpnessSystem.combination_equation {n k q : ℕ} {g : Index n → ℂ → ℂ}
    (h : IsSharpnessSystem n k q g) (c : Index n → ℂ) (z : ℂ) :
    iteratedDeriv (n + 1) (sharpnessCombination g c) z =
      z ^ k * iteratedDeriv (n + 1 - q) (sharpnessCombination g c) z := by
  rw [h.combination_derivative, h.combination_derivative, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [h.2.2 j z]
  ring

/-- Since the actual Wronskian is 1, every jet at every finite point can be
realized by an actual constant linear combination of the prescribed solutions. -/
theorem IsSharpnessSystem.combination_with_jet_exists {n k q : ℕ}
    {g : Index n → ℂ → ℂ} (h : IsSharpnessSystem n k q g)
    (hq : 2 ≤ q) (hqn : q ≤ n + 1) (z : ℂ) (v : Index n → ℂ) :
    ∃ c : Index n → ℂ, ∀ i : Index n,
      iteratedDeriv i.val (sharpnessCombination g c) z = v i := by
  classical
  let M := FewInflection.jetMatrix g z
  have hdet : IsUnit M.det := by
    change IsUnit (FewInflection.wronskian n g z)
    rw [h.wronskian_one hq hqn]
    exact isUnit_one
  let c := M⁻¹.mulVec v
  have he : M.mulVec c = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hdet, Matrix.one_mulVec]
  refine ⟨c, ?_⟩
  intro i
  rw [h.combination_derivative]
  have hi := congrFun he i
  simpa only [M, FewInflection.jetMatrix, Matrix.mulVec, dotProduct, mul_comm] using hi

theorem scalar_equation_of_iterated_primitive {n k q : ℕ} (hqn : q ≤ n + 1)
    {w : ℂ → ℂ}
    (heq : ∀ z, iteratedDeriv (n + 1) w z = z ^ k * iteratedDeriv (n + 1 - q) w z) :
    ∀ z, iteratedDeriv q (iteratedDeriv (n + 1 - q) w) z =
      z ^ k * iteratedDeriv (n + 1 - q) w z := by
  intro z
  rw [← iteratedDeriv_add_orders, show q + (n + 1 - q) = n + 1 by omega]
  exact heq z

theorem entire_iteratedDeriv {w : ℂ → ℂ} (hw : Differentiable ℂ w) (m : ℕ) :
    Differentiable ℂ (iteratedDeriv m w) := by
  intro z
  exact (FewInflection.analyticAt_iteratedDeriv
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr hw) z (mem_univ z)) m).differentiableAt

/-- Prescribe the complete jet of the mth derivative inside the original
entire solution space, using the actual nonzero Wronskian. -/
theorem IsSharpnessSystem.combination_with_derivative_jet_exists {n k q : ℕ}
    {g : Index n → ℂ → ℂ} (h : IsSharpnessSystem n k q g)
    (hq : 2 ≤ q) (hqn : q ≤ n + 1) (z a : ℂ) (x : Fin q → ℂ) :
    ∃ c : Index n → ℂ, ∀ i : Fin q,
      iteratedDeriv i.val (iteratedDeriv (n + 1 - q) (sharpnessCombination g c)) z =
        a ^ i.val * x i := by
  classical
  let m := n + 1 - q
  have hm : m + q = n + 1 := Nat.sub_add_cancel hqn
  let v : Index n → ℂ := fun l => if hl : l.val < m then 0 else
    a ^ (l.val - m) * x ⟨l.val - m, by have := l.isLt; omega⟩
  obtain ⟨c, hc⟩ := h.combination_with_jet_exists hq hqn z v
  refine ⟨c, ?_⟩
  intro i
  let l : Index n := ⟨i.val + m, by have := i.isLt; omega⟩
  have hi := hc l
  have hnot : ¬ l.val < m := by dsimp [l]; omega
  have hsub : l.val - m = i.val := by dsimp [l]; omega
  have hv : v l = a ^ i.val * x i := by
    simp only [v, dite_eq_right hnot, hsub]
  rw [hv] at hi
  rw [← iteratedDeriv_add_orders]
  exact hi
end ModifiedCartan
#print axioms ModifiedCartan.IsSharpnessSystem.combination_with_jet_exists
#print axioms ModifiedCartan.scalar_equation_of_iterated_primitive


