import ModifiedCartan.FixedColoringTransport
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def transitiveSigmaColoringEquiv {I C : Type*} [Fintype I] (B : I → Type*)
    [∀ i, Fintype (B i)] [∀ i, Nonempty (B i)] (σ : ∀ i, Equiv.Perm (B i))
    (htrans : ∀ i (a b : B i), (σ i).SameCycle a b) :
    (I → C) ≃ {f : (Σ i, B i) → C // ∀ p, f (Equiv.Perm.sigmaCongrRight σ p) = f p} where
  toFun g := ⟨fun p => g p.1, fun _ => rfl⟩
  invFun f i := f.val ⟨i, Classical.choice (inferInstance : Nonempty (B i))⟩
  left_inv g := rfl
  right_inv f := by
    apply Subtype.ext
    funext p
    exact coloring_sameCycle_eq (σ p.1) (fun b => f.val ⟨p.1, b⟩)
      (fun b => f.property ⟨p.1, b⟩) (htrans p.1 _ p.2)

theorem permutationFixedColoringSum_sigma_transitive {I C R : Type*} [Fintype I]
    [Fintype C] [CommSemiring R] (B : I → Type*) [∀ i, Fintype (B i)]
    [∀ i, Nonempty (B i)] (σ : ∀ i, Equiv.Perm (B i))
    (htrans : ∀ i (a b : B i), (σ i).SameCycle a b) (x : C → R) :
    permutationFixedColoringSum (Equiv.Perm.sigmaCongrRight σ) x =
      ∏ i : I, ∑ c : C, x c ^ Fintype.card (B i) := by
  letI : DecidableEq (Σ i, B i) := Classical.decEq _
  unfold permutationFixedColoringSum
  rw [← Equiv.sum_comp (transitiveSigmaColoringEquiv B σ htrans) (fun f => ∏ p, x (f.val p))]
  calc
    _ = ∑ g : I → C, ∏ i : I, x (g i) ^ Fintype.card (B i) := by
      apply Finset.sum_congr rfl
      intro g hg
      change (∏ p : (Σ i, B i), x (g p.1)) = _
      rw [Fintype.prod_sigma]
      simp only [Finset.prod_const, Finset.card_univ]
    _ = _ := (Fintype.prod_sum (fun i c => x c ^ Fintype.card (B i))).symm

end
end ModifiedCartan

