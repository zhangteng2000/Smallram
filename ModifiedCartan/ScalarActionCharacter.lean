import ModifiedCartan.ScalarActionAdjoin

open scoped Classical

namespace ModifiedCartan
noncomputable section

variable {R V : Type*} [Semiring R] [Algebra ℂ R] [AddCommGroup V] [Module ℂ V]

def scalarActionValue (ρ : R →ₐ[ℂ] Module.End ℂ V) (v : V)
    (h : ∀ x : R, ∃ c : ℂ, ρ x v = c • v) (x : R) : ℂ := Classical.choose (h x)

theorem scalarActionValue_spec (ρ : R →ₐ[ℂ] Module.End ℂ V) (v : V)
    (h : ∀ x : R, ∃ c : ℂ, ρ x v = c • v) (x : R) :
    ρ x v = scalarActionValue ρ v h x • v := Classical.choose_spec (h x)

theorem scalarActionValue_eq (ρ : R →ₐ[ℂ] Module.End ℂ V) (v : V) (hv : v ≠ 0)
    (h : ∀ x : R, ∃ c : ℂ, ρ x v = c • v) (x : R) (c : ℂ) (hc : ρ x v = c • v) :
    scalarActionValue ρ v h x = c :=
  smul_left_injective ℂ hv ((scalarActionValue_spec ρ v h x).symm.trans hc)

/-- The eigenvalue on a fixed nonzero common eigenvector is an algebra character. -/
def scalarActionCharacter (ρ : R →ₐ[ℂ] Module.End ℂ V) (v : V) (hv : v ≠ 0)
    (h : ∀ x : R, ∃ c : ℂ, ρ x v = c • v) : R →ₐ[ℂ] ℂ where
  toFun := scalarActionValue ρ v h
  map_zero' := by
    apply scalarActionValue_eq ρ v hv h
    simp only [map_zero, LinearMap.zero_apply, zero_smul]
  map_one' := by
    apply scalarActionValue_eq ρ v hv h
    simp only [map_one, Module.End.one_apply, one_smul]
  map_add' x y := by
    apply scalarActionValue_eq ρ v hv h
    rw [map_add, LinearMap.add_apply, scalarActionValue_spec ρ v h x,
      scalarActionValue_spec ρ v h y, add_smul]
  map_mul' x y := by
    apply scalarActionValue_eq ρ v hv h
    rw [map_mul, Module.End.mul_apply, scalarActionValue_spec ρ v h y,
      map_smul, scalarActionValue_spec ρ v h x, smul_smul, mul_comm]
  commutes' c := by
    change scalarActionValue ρ v h (algebraMap ℂ R c) = c
    apply scalarActionValue_eq ρ v hv h
    rw [AlgHom.commutes, Module.algebraMap_end_apply]

theorem scalarActionCharacter_apply (ρ : R →ₐ[ℂ] Module.End ℂ V) (v : V) (hv : v ≠ 0)
    (h : ∀ x : R, ∃ c : ℂ, ρ x v = c • v) (x : R) :
    ρ x v = scalarActionCharacter ρ v hv h x • v := scalarActionValue_spec ρ v h x

end
end ModifiedCartan


