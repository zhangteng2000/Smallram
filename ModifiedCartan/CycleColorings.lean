import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.Fintype.Quotient

open scoped Classical

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- All cycles, including singleton cycles, of the actual permutation. -/
def PermutationCycles (σ : Equiv.Perm A) := Quotient (Equiv.Perm.SameCycle.setoid σ)

instance (σ : Equiv.Perm A) : Fintype (PermutationCycles σ) :=
  inferInstanceAs (Fintype (Quotient (Equiv.Perm.SameCycle.setoid σ)))

def permutationCycleClass (σ : Equiv.Perm A) (a : A) : PermutationCycles σ :=
  Quotient.mk _ a

theorem permutationCycleClass_apply (σ : Equiv.Perm A) (a : A) :
    permutationCycleClass σ (σ a) = permutationCycleClass σ a :=
  Quotient.sound (Equiv.Perm.SameCycle.apply_left (Equiv.Perm.SameCycle.refl σ a))

theorem coloring_pow_eq {B : Type*} (σ : Equiv.Perm A) (f : A → B)
    (hf : ∀ a, f (σ a) = f a) (n : ℕ) (a : A) : f ((σ ^ n) a) = f a := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, hf, ih]

theorem coloring_sameCycle_eq {B : Type*} (σ : Equiv.Perm A) (f : A → B)
    (hf : ∀ a, f (σ a) = f a) {a b : A} (hab : σ.SameCycle a b) : f a = f b := by
  obtain ⟨n, hn⟩ := hab.exists_nat_pow_eq
  rw [← hn]
  exact (coloring_pow_eq σ f hf n a).symm

/-- A fixed coloring is exactly an independent choice of color for each cycle. -/
def cycleColoringEquiv (σ : Equiv.Perm A) (B : Type*) :
    (PermutationCycles σ → B) ≃ {f : A → B // ∀ a, f (σ a) = f a} where
  toFun F := ⟨fun a => F (permutationCycleClass σ a),
    fun a => congrArg F (permutationCycleClass_apply σ a)⟩
  invFun f := Quotient.lift f.val (fun _ _ hab => coloring_sameCycle_eq σ f.val f.property hab)
  left_inv F := by
    funext c
    exact Quotient.inductionOn c (fun a => rfl)
  right_inv f := by
    apply Subtype.ext
    funext a
    rfl

end
end ModifiedCartan


