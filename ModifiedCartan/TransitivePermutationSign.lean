import ModifiedCartan.CycleColorings

open scoped Classical

namespace ModifiedCartan
noncomputable section

/-- Sign of one complete cycle, including the singleton cycle. -/
theorem transitivePermutation_sign {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (σ : Equiv.Perm A) (htrans : ∀ a b : A, σ.SameCycle a b) :
    Equiv.Perm.sign σ = (-1) ^ (Fintype.card A + 1) := by
  rcases subsingleton_or_nontrivial A with hs | hn
  · letI : Subsingleton A := hs
    letI : Unique A := { default := Classical.choice ‹Nonempty A›, uniq := fun _ => Subsingleton.elim _ _ }
    have he : σ = 1 := Subsingleton.elim _ _
    rw [he, Equiv.Perm.sign_one, Fintype.card_unique]
    simp
  · letI : Nontrivial A := hn
    have hc : σ.IsCycleOn Set.univ := by
      refine ⟨⟨fun _ _ => Set.mem_univ _, σ.injective.injOn, ?_⟩, ?_⟩
      · intro a ha
        exact ⟨σ⁻¹ a, Set.mem_univ _, σ.apply_symm_apply a⟩
      · intro a ha b hb
        exact htrans a b
    have hm : ∀ a, σ a ≠ a := fun a => hc.apply_ne Set.nontrivial_univ (Set.mem_univ a)
    let a : A := Classical.choice ‹Nonempty A›
    have hcycle : σ.IsCycle := ⟨a, hm a, fun b _ => htrans a b⟩
    have hsupport : σ.support = Finset.univ := by
      ext b
      simp [Equiv.Perm.mem_support, hm b]
    rw [hcycle.sign, hsupport, Finset.card_univ, pow_succ]
    simp

end
end ModifiedCartan

