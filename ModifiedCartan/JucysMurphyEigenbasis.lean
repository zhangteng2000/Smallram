import ModifiedCartan.JucysMurphyBasisZero

open scoped Classical

namespace ModifiedCartan
noncomputable section

universe u

theorem exists_simpleJucysMurphyBasis_of_card (n : ℕ) :
    ∀ (A : Type u) [Fintype A] [LinearOrder A], Fintype.card A = n →
      ∀ (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ), Nonempty (SimpleJucysMurphyBasis μ h) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A _ _ hA μ h
    by_cases hn : n = 0
    · exact ⟨simpleJucysMurphyBasisZero μ h (hA.trans hn)⟩
    · have hne : Nonempty A := Fintype.card_pos_iff.mp (by rw [hA]; omega)
      have hu : (Finset.univ : Finset A).Nonempty := ⟨Classical.choice hne, Finset.mem_univ _⟩
      let a : A := (Finset.univ : Finset A).max' hu
      have ha (i : A) : i ≤ a := Finset.le_max' Finset.univ i (Finset.mem_univ i)
      have hK : Fintype.card (↥(Finset.univ.erase a)) < n := by
        rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, hA]
        omega
      have hD (b : YoungCorner μ) : Nonempty (SimpleJucysMurphyBasis (removePartitionBox μ b)
          (card_erase_eq_partition_remove μ h a b)) :=
        ih (Fintype.card (↥(Finset.univ.erase a))) hK (↥(Finset.univ.erase a)) rfl
          (removePartitionBox μ b) (card_erase_eq_partition_remove μ h a b)
      exact ⟨simpleJucysMurphyBasisStep μ h a ha (fun b => Classical.choice (hD b))⟩

theorem exists_simpleJucysMurphyBasis {A : Type*} [Fintype A] [LinearOrder A]
    (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ) : Nonempty (SimpleJucysMurphyBasis μ h) :=
  exists_simpleJucysMurphyBasis_of_card (Fintype.card A) A rfl μ h

def simpleJucysMurphyBasis {A : Type*} [Fintype A] [LinearOrder A]
    (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ) : SimpleJucysMurphyBasis μ h :=
  Classical.choice (exists_simpleJucysMurphyBasis μ h)

end
end ModifiedCartan


