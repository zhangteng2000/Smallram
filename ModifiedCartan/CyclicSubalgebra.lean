import ModifiedCartan.CyclicCentralizer

open scoped Classical

namespace ModifiedCartan
noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem commutative_subalgebra_eq_centralizer_of_cyclic
    (S : Subalgebra ℂ (Module.End ℂ V))
    (hS : ∀ x ∈ S, ∀ y ∈ S, Commute x y)
    (T : Module.End ℂ V) (hT : T ∈ S) (v : V) (hv : HasPolynomialCyclicVector T v) :
    S = Subalgebra.centralizer ℂ {T} := by
  apply le_antisymm
  · intro x hx
    apply (Subalgebra.mem_centralizer_iff ℂ).mpr
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact (hS T hT x hx).eq
  · intro x hx
    have hc : Commute x T :=
      ((Subalgebra.mem_centralizer_iff ℂ).mp hx T (Set.mem_singleton T)).symm
    obtain ⟨p, rfl⟩ := commuting_eq_aeval_of_cyclic T v hv x hc
    have hle : Algebra.adjoin ℂ {T} ≤ S := by
      apply Algebra.adjoin_le
      rintro _ rfl
      exact hT
    exact hle (Polynomial.aeval_mem_adjoin_singleton ℂ T)

def subalgebraEvaluation (S : Subalgebra ℂ (Module.End ℂ V)) (v : V) : S →ₗ[ℂ] V where
  toFun T := T.val v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem subalgebraEvaluation_bijective_of_cyclic (S : Subalgebra ℂ (Module.End ℂ V))
    (hS : ∀ x ∈ S, ∀ y ∈ S, Commute x y)
    (T : Module.End ℂ V) (hT : T ∈ S) (v : V) (hv : HasPolynomialCyclicVector T v) :
    Function.Bijective (subalgebraEvaluation S v) := by
  constructor
  · intro x y he
    apply Subtype.ext
    exact cyclic_commuting_ext T v hv x.val y.val (hS x.val x.property T hT)
      (hS y.val y.property T hT) he
  · intro w
    obtain ⟨p, hp⟩ := hv w
    have hle : Algebra.adjoin ℂ {T} ≤ S := by
      apply Algebra.adjoin_le
      rintro _ rfl
      exact hT
    exact ⟨⟨Polynomial.aeval T p, hle (Polynomial.aeval_mem_adjoin_singleton ℂ T)⟩, hp⟩

theorem finrank_commutative_subalgebra_of_cyclic (S : Subalgebra ℂ (Module.End ℂ V))
    (hS : ∀ x ∈ S, ∀ y ∈ S, Commute x y)
    (T : Module.End ℂ V) (hT : T ∈ S) (v : V) (hv : HasPolynomialCyclicVector T v) :
    Module.finrank ℂ S = Module.finrank ℂ V :=
  (LinearEquiv.ofBijective (subalgebraEvaluation S v)
    (subalgebraEvaluation_bijective_of_cyclic S hS T hT v hv)).finrank_eq

end
end ModifiedCartan


