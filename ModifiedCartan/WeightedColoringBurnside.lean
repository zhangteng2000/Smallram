import ModifiedCartan.ColoringOrbits
import ModifiedCartan.FixedColoringTransport

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

attribute [local instance] coloringPermutationAction

/-- Each coloring orbit contributes once to the normalized fixed-coloring sum. -/
theorem sum_fixed_coloring_multiset_weights {A B V : Type*} [Fintype A] [Fintype B]
    [AddCommMonoid V] (w : Sym B (Fintype.card A) → V) :
    (∑ σ : Equiv.Perm A, ∑ f : {f : A → B // ∀ a, f (σ a) = f a},
      w (coloringMultiset f.val)) =
        Fintype.card (Equiv.Perm A) • ∑ s : Sym B (Fintype.card A), w s := by
  calc
    _ = ∑ σ : Equiv.Perm A, ∑ f : MulAction.fixedBy (A → B) σ,
        w (coloringMultiset f.val) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      exact Equiv.sum_comp (Equiv.subtypeEquivRight (fun f => (coloring_fixedBy_iff σ f).symm))
        (fun f => w (coloringMultiset f.val))
    _ = Fintype.card (Equiv.Perm A) •
        ∑ q : ColoringOrbit A B, w (coloringOrbitEquivMultiset q) := by
      have h := sum_fixedBy_orbit_weights (G := Equiv.Perm A) (X := A → B)
        (w ∘ coloringOrbitEquivMultiset)
      simpa only [Function.comp_apply, coloringOrbitEquivMultiset_mk] using h
    _ = _ := by rw [Equiv.sum_comp coloringOrbitEquivMultiset w]

theorem coloringMultiset_product {A B R : Type*} [Fintype A] [CommMonoid R]
    (f : A → B) (x : B → R) :
    ((coloringMultiset f).val.map x).prod = ∏ a : A, x (f a) := by
  rw [coloringMultiset, Multiset.map_map, Finset.prod_map_val]
  rfl

/-- The cycle-index sum equals the multiset generating polynomial, by actual
finite Burnside counting. Auxiliary to the finite Frobenius/Schur bridge. -/
theorem sum_permutationFixedColoringSum {A B R : Type*} [Fintype A] [Fintype B]
    [CommSemiring R] (x : B → R) :
    (∑ σ : Equiv.Perm A, permutationFixedColoringSum σ x) =
      Fintype.card (Equiv.Perm A) •
        ∑ s : Sym B (Fintype.card A), (s.val.map x).prod := by
  simpa only [permutationFixedColoringSum, coloringMultiset_product] using
    sum_fixed_coloring_multiset_weights (A := A) (fun s => (s.val.map x).prod)

end
end ModifiedCartan


