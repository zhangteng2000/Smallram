import ModifiedCartan.KPGeneratedCommutative

open scoped Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

def kpSpechtAlgebra {A : Type*} [Fintype A] [DecidableEq A]
    (τ : YoungDiagram) (h : Fintype.card A = partitionSize τ) (z : A → ℂ) :
    Subalgebra ℂ (Module.End ℂ (YoungSpechtModule τ)) :=
  (kpGeneratedAlgebra z).map (spechtRepresentationOn τ h).asAlgebraHom

theorem kpSpechtAlgebra_elements_commute {N : ℕ} (τ : YoungDiagram)
    (h : Fintype.card (Fin N) = partitionSize τ) (z : Fin N → ℂ)
    (x : Module.End ℂ (YoungSpechtModule τ)) (hx : x ∈ kpSpechtAlgebra τ h z)
    (y : Module.End ℂ (YoungSpechtModule τ)) (hy : y ∈ kpSpechtAlgebra τ h z) :
    Commute x y := by
  obtain ⟨a, ha, rfl⟩ := Subalgebra.mem_map.mp hx
  obtain ⟨b, hb, rfl⟩ := Subalgebra.mem_map.mp hy
  have he := congrArg Subtype.val (kpGeneratedAlgebra_elements_commute z ⟨a, ha⟩ ⟨b, hb⟩)
  have hc : Commute a b := he
  exact hc.map (spechtRepresentationOn τ h).asAlgebraHom

end
end ModifiedCartan


