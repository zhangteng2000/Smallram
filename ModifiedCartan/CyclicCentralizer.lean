import ModifiedCartan.ClassWeightedOperator
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

open scoped Classical

namespace ModifiedCartan
noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def HasPolynomialCyclicVector (T : Module.End ℂ V) (v : V) : Prop :=
  ∀ w : V, ∃ p : Polynomial ℂ, (Polynomial.aeval T p) v = w

theorem commute_aeval_of_commute (T A : Module.End ℂ V) (h : Commute A T) (p : Polynomial ℂ) :
    Commute A (Polynomial.aeval T p) := by
  have hle : Algebra.adjoin ℂ {T} ≤ Subalgebra.centralizer ℂ {A} := by
    apply Algebra.adjoin_le
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    apply (Subalgebra.mem_centralizer_iff ℂ).mpr
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact h
  exact ((Subalgebra.mem_centralizer_iff ℂ).mp
    (hle (Polynomial.aeval_mem_adjoin_singleton ℂ T))) A (Set.mem_singleton A)

theorem cyclic_commuting_ext (T : Module.End ℂ V) (v : V) (hv : HasPolynomialCyclicVector T v)
    (A B : Module.End ℂ V) (hA : Commute A T) (hB : Commute B T) (hab : A v = B v) : A = B := by
  apply LinearMap.ext
  intro w
  obtain ⟨p, rfl⟩ := hv w
  have ha := congrArg (fun L : Module.End ℂ V => L v) (commute_aeval_of_commute T A hA p).eq
  have hb := congrArg (fun L : Module.End ℂ V => L v) (commute_aeval_of_commute T B hB p).eq
  change A ((Polynomial.aeval T p) v) = (Polynomial.aeval T p) (A v) at ha
  change B ((Polynomial.aeval T p) v) = (Polynomial.aeval T p) (B v) at hb
  exact ha.trans ((congrArg (Polynomial.aeval T p) hab).trans hb.symm)

theorem commuting_eq_aeval_of_cyclic (T : Module.End ℂ V) (v : V)
    (hv : HasPolynomialCyclicVector T v) (A : Module.End ℂ V) (hA : Commute A T) :
    ∃ p : Polynomial ℂ, A = Polynomial.aeval T p := by
  obtain ⟨p, hp⟩ := hv (A v)
  refine ⟨p, cyclic_commuting_ext T v hv A _ hA ?_ hp.symm⟩
  exact (commute_aeval_of_commute T T (Commute.refl T) p).symm

theorem centralizer_commutative_of_cyclic (T : Module.End ℂ V) (v : V)
    (hv : HasPolynomialCyclicVector T v) (A B : Module.End ℂ V)
    (hA : Commute A T) (hB : Commute B T) : Commute A B := by
  obtain ⟨p, rfl⟩ := commuting_eq_aeval_of_cyclic T v hv A hA
  exact (commute_aeval_of_commute T B hB p).symm

def polynomialOrbitMap (T : Module.End ℂ V) (v : V) : Polynomial ℂ →ₗ[ℂ] V where
  toFun p := (Polynomial.aeval T p) v
  map_add' p q := by rw [map_add, LinearMap.add_apply]
  map_smul' c p := by rw [map_smul, LinearMap.smul_apply]; rfl

theorem hasPolynomialCyclicVector_of_power_span (T : Module.End ℂ V) (v : V)
    (h : Submodule.span ℂ (Set.range (fun n : ℕ => (T ^ n) v)) = ⊤) :
    HasPolynomialCyclicVector T v := by
  have hle : Submodule.span ℂ (Set.range (fun n : ℕ => (T ^ n) v)) ≤
      LinearMap.range (polynomialOrbitMap T v) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact ⟨Polynomial.X ^ n, by simp [polynomialOrbitMap]⟩
  intro w
  exact hle (by rw [h]; trivial)

end
end ModifiedCartan


