import ModifiedCartan.CycleWeightedPowers
import Mathlib.Logic.Equiv.Prod

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def permutationFixedColoringSum {A B R : Type*} [Fintype A] [Fintype B] [CommSemiring R]
    (σ : Equiv.Perm A) (x : B → R) : R :=
  ∑ f : {f : A → B // ∀ a, f (σ a) = f a}, ∏ a : A, x (f.val a)

theorem permutationFixedColoringSum_cycles {A B R : Type*} [Fintype A] [Fintype B]
    [CommSemiring R] (σ : Equiv.Perm A) (x : B → R) :
    permutationFixedColoringSum σ x =
      ∏ c : PermutationCycles σ, ∑ b : B, x b ^ permutationCycleWeight σ (fun _ => 1) c := by
  unfold permutationFixedColoringSum
  calc
    _ = ∑ f : A → B, if ∀ a, f (σ a) = f a then ∏ a, x (f a) else 0 :=
      (sum_dite_eq_sum_subtype (fun f : A → B => ∀ a, f (σ a) = f a)
        (fun f _ => ∏ a, x (f a))).symm
    _ = _ := by simpa only [pow_one] using fixed_coloring_sum_eq_cycle_powers σ (fun _ => 1) x

def fixedColoringConjugationEquiv {A C B : Type*} (e : A ≃ C) (σ : Equiv.Perm A) :
    {f : A → B // ∀ a, f (σ a) = f a} ≃
      {g : C → B // ∀ c, g (e.permCongr σ c) = g c} where
  toFun f := ⟨fun c => f.val (e.symm c), by
    intro c
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    exact f.property (e.symm c)⟩
  invFun g := ⟨fun a => g.val (e a), by
    intro a
    have h := g.property (e a)
    simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using h⟩
  left_inv f := by apply Subtype.ext; funext a; exact congrArg f.val (e.symm_apply_apply a)
  right_inv g := by apply Subtype.ext; funext c; exact congrArg g.val (e.apply_symm_apply c)

theorem permutationFixedColoringSum_conjugate {A C B R : Type*} [Fintype A] [Fintype C]
    [Fintype B] [CommSemiring R] (e : A ≃ C) (σ : Equiv.Perm A) (x : B → R) :
    permutationFixedColoringSum (e.permCongr σ) x = permutationFixedColoringSum σ x := by
  unfold permutationFixedColoringSum
  rw [← Equiv.sum_comp (fixedColoringConjugationEquiv e σ) (fun g => ∏ c, x (g.val c))]
  apply Finset.sum_congr rfl
  intro f hf
  exact Equiv.prod_comp e.symm (fun a => x (f.val a))

end
end ModifiedCartan

