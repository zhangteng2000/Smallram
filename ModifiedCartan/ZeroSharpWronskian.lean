import ModifiedCartan.ZeroSharpRealRoots
import ModifiedCartan.CountingDilation

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem zeroSharpCoordinates_entire (n : ℕ) (j : Index n) :
    Differentiable ℂ (zeroSharpCoordinates n j) := by
  unfold zeroSharpCoordinates
  split_ifs
  · fun_prop
  · exact zeroSharpFunction_differentiable

noncomputable def zeroSharpCurve (n : ℕ) (hn : 1 ≤ n) : Curve n where
  coord := zeroSharpCoordinates n
  holomorphic := zeroSharpCoordinates_entire n
  reduced := fun z => ⟨0, by simp [zeroSharpCoordinates, show 0 < n by omega]⟩

theorem zeroSharpCoordinates_last (n : ℕ) :
    zeroSharpCoordinates n (Fin.last n) = zeroSharpFunction := by
  ext z
  simp [zeroSharpCoordinates]

/-- Literal Wronskian identity in LaTeX `prop:sharpness-zero`. -/
theorem zeroSharpCoordinates_wronskian (n : ℕ) (z : ℂ) :
    FewInflection.wronskian n (zeroSharpCoordinates n) z =
      (∏ j : Fin n, (j.val.factorial : ℂ)) * iteratedDeriv n zeroSharpFunction z := by
  let M : Matrix (Index n) (Index n) ℂ :=
    fun i j => iteratedDeriv i.val (zeroSharpCoordinates n j) z
  have hu : M.IsUpperTriangular := by
    intro i j hij
    have hjn : j.val < n := by have := i.isLt; change j.val < i.val at hij; omega
    change iteratedDeriv i.val (zeroSharpCoordinates n j) z = 0
    have he : zeroSharpCoordinates n j = fun w : ℂ => w ^ j.val := by
      ext w
      simp [zeroSharpCoordinates, hjn]
    rw [he, iteratedDeriv_pow]
    simp [Nat.descFactorial_eq_zero_iff_lt.mpr (show j.val < i.val from hij)]
  change M.det = _
  rw [Matrix.det_of_isUpperTriangular hu, Fin.prod_univ_castSucc]
  have hd (j : Fin n) : M j.castSucc j.castSucc = (j.val.factorial : ℂ) := by
    have he : zeroSharpCoordinates n j.castSucc = fun w : ℂ => w ^ j.val := by
      ext w
      simp [zeroSharpCoordinates, j.isLt]
    dsimp only [M]
    rw [he, iteratedDeriv_pow]
    simp [Nat.descFactorial_self]
  simp only [hd, M, Fin.val_last, zeroSharpCoordinates_last]

theorem zeroSharpCurve_linearlyNonDegenerate (n : ℕ) (hn : 1 ≤ n) :
    (zeroSharpCurve n hn).linearlyNonDegenerate := by
  obtain ⟨z, hz⟩ := zeroSharpFunction_iteratedDeriv_nonzero n
  apply FewInflection.linearlyIndependent_of_wronskian_ne_zero (zeroSharpCoordinates n) z
    (fun i j => (zeroSharpCoordinates_entire n j).contDiff.contDiffAt)
  rw [zeroSharpCoordinates_wronskian]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun j _ => by
    exact_mod_cast Nat.factorial_ne_zero j.val)) hz

theorem zeroSharpCurve_ramification (n : ℕ) (hn : 1 ≤ n) (r : ℝ) :
    ramification (zeroSharpCurve n hn) r =
      ValueDistribution.logCounting (iteratedDeriv n zeroSharpFunction) (0 : WithTop ℂ) r := by
  have he : FewInflection.wronskian n (zeroSharpCurve n hn).coord =
      fun z => (∏ j : Fin n, (j.val.factorial : ℂ)) * iteratedDeriv n zeroSharpFunction z :=
    funext (zeroSharpCoordinates_wronskian n)
  change ValueDistribution.logCounting _ (0 : WithTop ℂ) r = _
  rw [he]
  exact logCounting_const_mul (zeroSharpFunction_iteratedDeriv_entire n)
    (zeroSharpFunction_iteratedDeriv_nonzero n)
    (Finset.prod_ne_zero_iff.mpr (fun j _ => by exact_mod_cast Nat.factorial_ne_zero j.val)) r

end ModifiedCartan
#print axioms ModifiedCartan.zeroSharpCoordinates_wronskian
#print axioms ModifiedCartan.zeroSharpCurve_linearlyNonDegenerate
#print axioms ModifiedCartan.zeroSharpCurve_ramification
