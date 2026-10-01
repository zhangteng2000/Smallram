import ModifiedCartan.GaudinDegenerationIdentity
import ModifiedCartan.JucysMurphyElements
import ModifiedCartan.MatrixCyclicOpen

open scoped BigOperators Classical MonoidAlgebra Topology

namespace ModifiedCartan
noncomputable section

variable {N : ℕ}

def gaudinDegenerationElement (z : Fin N → ℂ) (i : Fin N) (t : ℂ) : ℂ[Equiv.Perm (Fin N)] :=
  ∑ j : Fin N, gaudinDegenerationCoefficient z i j t • transpositionElement i j

theorem gaudinDegenerationElement_zero (z : Fin N → ℂ) (i : Fin N) :
    gaudinDegenerationElement z i 0 = jucysMurphyElement i := by
  rw [gaudinDegenerationElement, jucysMurphyElement_eq_sum_ite]
  apply Finset.sum_congr rfl
  intro j _
  rw [gaudinDegenerationCoefficient_zero]
  split_ifs <;> simp

theorem gaudinDegenerationElement_eq (z : Fin N → ℂ) (i : Fin N) (t : ℂ) (ht : t ≠ 0) :
    gaudinDegenerationElement z i t =
      (t ^ (i.val + 1))⁻¹ • kpGaudin (gaudinDeformedParameters z t) i := by
  rw [gaudinDegenerationElement, kpGaudin, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [gaudinDegenerationCoefficient_eq z i j t ht, mul_smul]

theorem gaudinDegenerationElement_matrix_continuousAt_zero
    {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ V) (ρ : Representation ℂ (Equiv.Perm (Fin N)) V)
    (z : Fin N → ℂ) (i : Fin N) :
    ContinuousAt (fun t => LinearMap.toMatrixAlgEquiv b
      (ρ.asAlgebraHom (gaudinDegenerationElement z i t))) 0 := by
  simp only [gaudinDegenerationElement, map_sum, map_smul]
  exact tendsto_finsetSum _ (fun j _ =>
    (gaudinDegenerationCoefficient_continuousAt_zero z i j).smul continuousAt_const)

def gaudinDegenerationCombination (z w : Fin N → ℂ) (t : ℂ) : ℂ[Equiv.Perm (Fin N)] :=
  ∑ i : Fin N, w i • gaudinDegenerationElement z i t

theorem gaudinDegenerationCombination_zero (z w : Fin N → ℂ) :
    gaudinDegenerationCombination z w 0 = ∑ i : Fin N, w i • jucysMurphyElement i := by
  simp only [gaudinDegenerationCombination, gaudinDegenerationElement_zero]

theorem gaudinDegenerationCombination_matrix_continuousAt_zero
    {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ V) (ρ : Representation ℂ (Equiv.Perm (Fin N)) V)
    (z w : Fin N → ℂ) :
    ContinuousAt (fun t => LinearMap.toMatrixAlgEquiv b
      (ρ.asAlgebraHom (gaudinDegenerationCombination z w t))) 0 := by
  simp only [gaudinDegenerationCombination, map_sum, map_smul]
  exact tendsto_finsetSum _ (fun i _ =>
    (show ContinuousAt (fun _ : ℂ => w i) 0 from continuousAt_const).smul
    (gaudinDegenerationElement_matrix_continuousAt_zero b ρ z i))

end
end ModifiedCartan


