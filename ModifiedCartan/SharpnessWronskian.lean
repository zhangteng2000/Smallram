import ModifiedCartan.Targets
import FewInflection.FundamentalAnalytic
import Mathlib.Analysis.Calculus.MeanValue

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem IsSharpnessSystem.analyticAt {n k q : ℕ} {g : Index n → ℂ → ℂ}
    (h : IsSharpnessSystem n k q g) (j : Index n) (z : ℂ) : AnalyticAt ℂ (g j) z :=
  (Complex.analyticOnNhd_univ_iff_differentiable.mpr (h.1 j)) z (mem_univ z)

/-- LaTeX `prop:sharpness-orders`: the missing top coefficient makes the
Wronskian derivative zero, by an actual repeated-row determinant calculation. -/
theorem IsSharpnessSystem.deriv_wronskian_eq_zero {n k q : ℕ} {g : Index n → ℂ → ℂ}
    (h : IsSharpnessSystem n k q g) (hq : 2 ≤ q) (hqn : q ≤ n + 1) (z : ℂ) :
    deriv (fun w => FewInflection.wronskian n g w) z = 0 := by
  classical
  let m : Index n := ⟨n + 1 - q, by omega⟩
  let last : Index n := ⟨n, Nat.lt_succ_self n⟩
  let M : Matrix (Index n) (Index n) ℂ := fun i j => iteratedDeriv i.val (g j) z
  have hm : m ≠ last := by
    intro he
    have hv := congrArg Fin.val he
    dsimp [m, last] at hv
    omega
  rw [FewInflection.deriv_wronskian_update_last (fun j => h.analyticAt j z)]
  have hrow : (fun j => iteratedDeriv (n + 1) (g j) z) = z ^ k • M m := by
    funext j
    simpa only [Pi.smul_apply, smul_eq_mul, M, m] using h.2.2 j z
  rw [hrow]
  change (M.updateRow last (z ^ k • M m)).det = 0
  rw [Matrix.det_updateRow_smul, Matrix.det_updateRow_eq_zero hm, mul_zero]

/-- LaTeX `prop:sharpness-orders`: Abel's identity with the prescribed initial jets. -/
theorem IsSharpnessSystem.wronskian_one {n k q : ℕ} {g : Index n → ℂ → ℂ}
    (h : IsSharpnessSystem n k q g) (hq : 2 ≤ q) (hqn : q ≤ n + 1) (z : ℂ) :
    FewInflection.wronskian n g z = 1 := by
  have hd : Differentiable ℂ (fun w => FewInflection.wronskian n g w) :=
    fun w => (FewInflection.analyticAt_wronskian (fun j => h.analyticAt j w)).differentiableAt
  rw [is_const_of_deriv_eq_zero hd (h.deriv_wronskian_eq_zero hq hqn) z 0]
  unfold FewInflection.wronskian
  have he : (fun i j : Index n => iteratedDeriv i.val (g j) 0) =
      (1 : Matrix (Index n) (Index n) ℂ) := by
    funext i j
    simpa only [Matrix.one_apply] using h.2.1 i j
  rw [he, Matrix.det_one]

theorem IsSharpnessSystem.reduced {n k q : ℕ} {g : Index n → ℂ → ℂ}
    (h : IsSharpnessSystem n k q g) (hq : 2 ≤ q) (hqn : q ≤ n + 1) :
    ∀ z, ∃ j, g j z ≠ 0 := by
  intro z
  by_contra hn
  push Not at hn
  have hz : FewInflection.wronskian n g z = 0 :=
    Matrix.det_eq_zero_of_row_eq_zero (0 : Index n) (by
      intro j
      simpa only [Fin.val_zero, iteratedDeriv_zero] using hn j)
  rw [h.wronskian_one hq hqn] at hz
  exact one_ne_zero hz

/-- The actual reduced curve with the prescribed solution coordinates. -/
def IsSharpnessSystem.curve {n k q : ℕ} {g : Index n → ℂ → ℂ}
    (h : IsSharpnessSystem n k q g) (hq : 2 ≤ q) (hqn : q ≤ n + 1) : Curve n where
  coord := g
  holomorphic := h.1
  reduced := h.reduced hq hqn

theorem IsSharpnessSystem.curve_linearlyNonDegenerate {n k q : ℕ} {g : Index n → ℂ → ℂ}
    (h : IsSharpnessSystem n k q g) (hq : 2 ≤ q) (hqn : q ≤ n + 1) :
    (h.curve hq hqn).linearlyNonDegenerate := by
  exact FewInflection.linearlyIndependent_of_wronskian_ne_zero g 0
    (fun i j => (h.analyticAt j 0).contDiffAt)
    (by rw [h.wronskian_one hq hqn]; exact one_ne_zero)

theorem IsSharpnessSystem.curve_smallRamification {n k q : ℕ} {g : Index n → ℂ → ℂ}
    (h : IsSharpnessSystem n k q g) (hq : 2 ≤ q) (hqn : q ≤ n + 1) :
    SmallRamification (h.curve hq hqn) := by
  unfold SmallRamification
  change FewInflection.ramification (h.curve hq hqn) =o[atTop] characteristic (h.curve hq hqn)
  rw [FewInflection.ramification_eq_zero_of_wronskian_const (h.curve hq hqn) 1
    (h.wronskian_one hq hqn)]
  exact Asymptotics.isLittleO_zero _ _

end ModifiedCartan
#print axioms ModifiedCartan.IsSharpnessSystem.wronskian_one
#print axioms ModifiedCartan.IsSharpnessSystem.curve_linearlyNonDegenerate
#print axioms ModifiedCartan.IsSharpnessSystem.curve_smallRamification

