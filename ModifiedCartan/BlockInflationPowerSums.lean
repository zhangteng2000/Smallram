import ModifiedCartan.BlockInflationColorings
import ModifiedCartan.CycleWeightedPowers

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem blockInflation_fixed_coloring_sum {A B R : Type*} [Fintype A] [Fintype B]
    [CommSemiring R] (κ : A → ℕ) (σ : Equiv.Perm A) (x : B → R) :
    (∑ f : (Σ a, Fin (κ a + 1)) → B,
      if ∀ p, f (blockInflation κ σ p) = f p then ∏ p, x (f p) else 0) =
    ∑ g : A → B, if ∀ a, g (σ a) = g a then ∏ a, x (g a) ^ (κ a + 1) else 0 := by
  calc
    _ = ∑ f : {f : (Σ a, Fin (κ a + 1)) → B // ∀ p, f (blockInflation κ σ p) = f p},
        ∏ p, x (f.val p) :=
      sum_dite_eq_sum_subtype (fun f : (Σ a, Fin (κ a + 1)) → B =>
        ∀ p, f (blockInflation κ σ p) = f p) (fun f _ => ∏ p, x (f p))
    _ = ∑ g : {g : A → B // ∀ a, g (σ a) = g a},
        ∏ p : (Σ a, Fin (κ a + 1)), x (g.val p.1) :=
      (Equiv.sum_comp (blockInflationColoringEquiv κ σ) (fun f => ∏ p, x (f.val p))).symm
    _ = ∑ g : {g : A → B // ∀ a, g (σ a) = g a}, ∏ a, x (g.val a) ^ (κ a + 1) := by
      apply Finset.sum_congr rfl
      intro g hg
      exact blockConstant_coloring_product κ x g.val
    _ = _ := (sum_dite_eq_sum_subtype (fun g : A → B => ∀ a, g (σ a) = g a)
      (fun g _ => ∏ a, x (g a) ^ (κ a + 1))).symm

theorem blockInflation_cycle_power_sums {A B R : Type*} [Fintype A] [Fintype B]
    [CommSemiring R] (κ : A → ℕ) (σ : Equiv.Perm A) (x : B → R) :
    (∏ c : PermutationCycles (blockInflation κ σ),
      ∑ b : B, x b ^ permutationCycleWeight (blockInflation κ σ) (fun _ => 1) c) =
    ∏ c : PermutationCycles σ, ∑ b : B, x b ^ permutationCycleWeight σ (fun a => κ a + 1) c := by
  rw [← fixed_coloring_sum_eq_cycle_powers (blockInflation κ σ) (fun _ => 1) x,
    ← fixed_coloring_sum_eq_cycle_powers σ (fun a => κ a + 1) x]
  simpa only [pow_one] using blockInflation_fixed_coloring_sum κ σ x

end
end ModifiedCartan

