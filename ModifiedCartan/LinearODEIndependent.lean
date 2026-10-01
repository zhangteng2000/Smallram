import ModifiedCartan.LinearODECompact
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

open scoped Topology BigOperators
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  [IsScalarTower ℝ ℂ V] [CompleteSpace V] {ι : Type*} [Fintype ι]

/-- Independence of a finite solution family is preserved in both time
 directions, by the proved uniqueness theorem applied to each linear relation. -/
theorem linearODE_family_independent_of_one_time {B : ℝ → V →L[ℂ] V} {a b : ℝ}
    (hB : ContinuousOn B (Ici a)) (hb : a ≤ b) (X : ι → ℝ → V)
    (hd : ∀ j t, a ≤ t → HasDerivAt (X j) (B t (X j t)) t)
    (hli : LinearIndependent ℂ (fun j => X j b)) :
    ∀ t, a ≤ t → LinearIndependent ℂ (fun j => X j t) := by
  classical
  let BR : ℝ → V →L[ℝ] V := fun t => (B t).restrictScalars ℝ
  have hBR : ContinuousOn BR (Ici a) :=
    (ContinuousLinearMap.continuous_restrictScalars ℝ).comp_continuousOn hB
  intro t hat
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  let Z : ℝ → V := fun s => ∑ j, c j • X j s
  have hZ (s : ℝ) (hs : a ≤ s) : HasDerivAt Z (BR s (Z s)) s := by
    change HasDerivAt (fun x => ∑ j, c j • X j x) (B s (∑ j, c j • X j s)) s
    simpa only [map_sum, map_smul, Pi.smul_apply] using!
      (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => (hd j s hs).const_smul (c j)))
  have hzero (s : ℝ) : HasDerivAt (fun _ : ℝ => (0 : V)) (BR s 0) s := by
    simpa only [map_zero] using hasDerivAt_const s (0 : V)
  have hbzero : Z b = 0 := by
    by_cases htb : t ≤ b
    · have heq : EqOn Z (fun _ => (0 : V)) (Icc t b) := by
        apply continuousOn_linearODE_unique_right
          (hBR.mono (fun s hs => hat.trans hs.1))
          (fun s hs => (hZ s (hat.trans hs.1)).continuousAt.continuousWithinAt)
          continuousOn_const
          (fun s hs => hZ s (hat.trans hs.1)) (fun s _ => hzero s) hc
      exact heq ⟨htb, le_rfl⟩
    · have hbt : b ≤ t := (lt_of_not_ge htb).le
      have heq : EqOn Z (fun _ => (0 : V)) (Icc b t) := by
        apply continuousOn_linearODE_unique_left
          (hBR.mono (fun s hs => hb.trans hs.1))
          (fun s hs => (hZ s (hb.trans hs.1)).continuousAt.continuousWithinAt)
          continuousOn_const
          (fun s hs => hZ s (hb.trans hs.1.le)) (fun s _ => hzero s) hc
      exact heq ⟨le_rfl, hbt⟩
  exact (Fintype.linearIndependent_iff.mp hli) c hbzero i

end ModifiedCartan
#print axioms ModifiedCartan.linearODE_family_independent_of_one_time
