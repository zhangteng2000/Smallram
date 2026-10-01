import ModifiedCartan.CyclicCentralizer

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem scalar_action_of_mem_adjoin {R V : Type*} [Semiring R] [Algebra ℂ R]
    [AddCommGroup V] [Module ℂ V] (ρ : R →ₐ[ℂ] Module.End ℂ V)
    (S : Submodule ℂ V) (s : Set R)
    (hs : ∀ g ∈ s, ∃ c : ℂ, ∀ v ∈ S, ρ g v = c • v)
    (x : R) (hx : x ∈ Algebra.adjoin ℂ s) :
    ∃ c : ℂ, ∀ v ∈ S, ρ x v = c • v := by
  induction hx using Algebra.adjoin_induction with
  | mem g hg => exact hs g hg
  | algebraMap c =>
    refine ⟨c, ?_⟩
    intro v _
    rw [AlgHom.commutes, Module.algebraMap_end_apply]
  | add x y hx hy ihx ihy =>
    obtain ⟨c, hc⟩ := ihx
    obtain ⟨d, hd⟩ := ihy
    refine ⟨c + d, ?_⟩
    intro v hv
    rw [map_add, LinearMap.add_apply, hc v hv, hd v hv, add_smul]
  | mul x y hx hy ihx ihy =>
    obtain ⟨c, hc⟩ := ihx
    obtain ⟨d, hd⟩ := ihy
    refine ⟨c * d, ?_⟩
    intro v hv
    rw [map_mul, Module.End.mul_apply, hd v hv, map_smul, hc v hv, smul_smul, mul_comm]

end
end ModifiedCartan


