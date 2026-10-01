import ModifiedCartan.LinearODEIndependent
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem linearODE_unique_halfLine {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] {B : ℝ → V →L[ℝ] V} {T : ℝ}
    (hB : ContinuousOn B (Ici T)) {Y Z : ℝ → V}
    (hY : ∀ t, T ≤ t → HasDerivAt Y (B t (Y t)) t)
    (hZ : ∀ t, T ≤ t → HasDerivAt Z (B t (Z t)) t)
    (he : Y T = Z T) : ∀ t, T ≤ t → Y t = Z t := by
  intro t ht
  have hh : EqOn Y Z (Icc T t) := continuousOn_linearODE_unique_right
    (hB.mono (fun u hu => hu.1))
    (fun u hu => (hY u hu.1).continuousAt.continuousWithinAt)
    (fun u hu => (hZ u hu.1).continuousAt.continuousWithinAt)
    (fun u hu => hY u hu.1) (fun u hu => hZ u hu.1) he
  exact hh ⟨ht, le_rfl⟩

/-- Every actual solution has constant coefficients in an actual fundamental
family; the equality is proved by initial-value uniqueness. -/
theorem linearODE_family_spans_solution {q : ℕ}
    {B : ℝ → (Fin q → ℂ) →L[ℂ] (Fin q → ℂ)} {T : ℝ}
    (hB : ContinuousOn B (Ici T)) (X : Fin q → ℝ → Fin q → ℂ)
    (hX : ∀ j t, T ≤ t → HasDerivAt (X j) (B t (X j t)) t)
    (hli : LinearIndependent ℂ (fun j => X j T)) {Y : ℝ → Fin q → ℂ}
    (hY : ∀ t, T ≤ t → HasDerivAt Y (B t (Y t)) t) :
    ∃ c : Fin q → ℂ, ∀ t, T ≤ t → Y t = ∑ j, c j • X j t := by
  classical
  let basis := basisOfPiSpaceOfLinearIndependent hli
  let c : Fin q → ℂ := fun j => basis.repr (Y T) j
  have hb (j : Fin q) : basis j = X j T :=
    congrFun (coe_basisOfPiSpaceOfLinearIndependent hli) j
  have hinit : Y T = ∑ j, c j • X j T := by
    simpa only [c, hb] using (basis.sum_repr (Y T)).symm
  let Z : ℝ → Fin q → ℂ := fun t => ∑ j, c j • X j t
  have hZ (t : ℝ) (ht : T ≤ t) : HasDerivAt Z (B t (Z t)) t := by
    simpa only [Z, map_sum, map_smul] using!
      (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => (hX j t ht).const_smul (c j)))
  let BR : ℝ → (Fin q → ℂ) →L[ℝ] (Fin q → ℂ) := fun t => (B t).restrictScalars ℝ
  have hBR : ContinuousOn BR (Ici T) :=
    (ContinuousLinearMap.continuous_restrictScalars ℝ).comp_continuousOn hB
  exact ⟨c, linearODE_unique_halfLine hBR hY hZ hinit⟩

end ModifiedCartan
#print axioms ModifiedCartan.linearODE_family_spans_solution
