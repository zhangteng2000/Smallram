import ModifiedCartan.CyclicCentralizer
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

open scoped Classical

namespace ModifiedCartan
noncomputable section

universe u v

/-- Every commuting family of endomorphisms of a nonzero finite dimensional
complex vector space has an actual common eigenvector. The index set may be infinite. -/
theorem exists_commonEigenvector_of_finrank {ι : Type v} (n : ℕ) :
    ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V],
      Module.finrank ℂ V = n → ∀ (T : ι → Module.End ℂ V),
        (∀ i j, Commute (T i) (T j)) →
          ∃ (χ : ι → ℂ) (v : V), v ≠ 0 ∧ ∀ i, T i v = χ i • v := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ _ _ hd T hT
    by_cases hall : ∀ i, ∃ c : ℂ, T i = c • 1
    · choose χ hχ using hall
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      refine ⟨χ, v, hv, ?_⟩
      intro i
      rw [hχ i, LinearMap.smul_apply, Module.End.one_apply]
    · push_neg at hall
      obtain ⟨i, hi⟩ := hall
      obtain ⟨c, hc⟩ := (T i).exists_eigenvalue
      let E := (T i).eigenspace c
      have hE : E ≠ ⊥ := hc
      letI : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hE
      have hproper : E ≠ ⊤ := by
        intro he
        apply hi c
        apply LinearMap.ext
        intro v
        change T i v = c • v
        apply Module.End.mem_eigenspace_iff.mp
        change v ∈ E
        rw [he]
        trivial
      have hdim : Module.finrank ℂ E < n := (Submodule.finrank_lt hproper).trans_eq hd
      have hinv (j : ι) (v : V) (hv : v ∈ E) : T j v ∈ E := by
        apply Module.End.mem_eigenspace_iff.mpr
        have hv' : T i v = c • v := Module.End.mem_eigenspace_iff.mp hv
        have hh := congrArg (fun S : Module.End ℂ V => S v) (hT i j).eq
        change T i (T j v) = T j (T i v) at hh
        rw [hh, hv', map_smul]
      let S : ι → Module.End ℂ E := fun j => (T j).restrict (hinv j)
      have hS (j k : ι) : Commute (S j) (S k) := by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        exact congrArg (fun L : Module.End ℂ V => L v.val) (hT j k).eq
      obtain ⟨χ, v, hv, he⟩ := ih (Module.finrank ℂ E) hdim E rfl S hS
      refine ⟨χ, v.val, ?_, ?_⟩
      · intro hz
        exact hv (Subtype.ext hz)
      · intro j
        exact congrArg (fun w : E => w.val) (he j)

theorem exists_commonEigenvector {ι V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] (T : ι → Module.End ℂ V)
    (hT : ∀ i j, Commute (T i) (T j)) :
    ∃ (χ : ι → ℂ) (v : V), v ≠ 0 ∧ ∀ i, T i v = χ i • v :=
  exists_commonEigenvector_of_finrank (Module.finrank ℂ V) V rfl T hT

end
end ModifiedCartan


