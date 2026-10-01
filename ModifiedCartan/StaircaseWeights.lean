import ModifiedCartan.FinitePartitionDegrees
import ModifiedCartan.StrictPermutationWeight

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- Exponent vectors for the finite alternants in paper `lem:KP-correspondence`. -/
def finiteExponent {m : ℕ} (e : Fin m → ℕ) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm e

@[simp] theorem finiteExponent_apply {m : ℕ} (e : Fin m → ℕ) (i : Fin m) :
    finiteExponent e i = e i := rfl

def finiteStaircaseDegree (m : ℕ) : Fin m →₀ ℕ :=
  finiteExponent (fun i => i.rev.val)

def finitePermutedStaircaseDegree {m : ℕ} (σ : Equiv.Perm (Fin m)) : Fin m →₀ ℕ :=
  finiteExponent (fun i => (σ i).rev.val)

@[simp] theorem finitePermutedStaircaseDegree_one (m : ℕ) :
    finitePermutedStaircaseDegree (1 : Equiv.Perm (Fin m)) = finiteStaircaseDegree m := rfl

theorem finiteColorWeight_add {m : ℕ} (d e : Fin m →₀ ℕ) :
    finiteColorWeight (d + e) = finiteColorWeight d + finiteColorWeight e := by
  simp [finiteColorWeight, mul_add, Finset.sum_add_distrib]

theorem finiteColorWeight_sub_add {m : ℕ} (d e : Fin m →₀ ℕ) (h : e ≤ d) :
    finiteColorWeight (d - e) + finiteColorWeight e = finiteColorWeight d := by
  rw [← finiteColorWeight_add, tsub_add_cancel_of_le h]

theorem staircase_weight_complement {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    finiteColorWeight (finitePermutedStaircaseDegree σ) +
      (∑ i : Fin m, i.val * (σ i).val) = ∑ i : Fin m, i.val * (m - 1) := by
  simp only [finiteColorWeight, finitePermutedStaircaseDegree, finiteExponent_apply,
    ← Finset.sum_add_distrib, ← mul_add]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hi := (σ i).isLt
  simp only [Fin.val_rev]
  omega

theorem finiteStaircaseDegree_weight_le {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    finiteColorWeight (finiteStaircaseDegree m) ≤
      finiteColorWeight (finitePermutedStaircaseDegree σ) := by
  have h1 := staircase_weight_complement (1 : Equiv.Perm (Fin m))
  have hσ := staircase_weight_complement σ
  have hr := fin_strictMono_weighted_sum_perm_le (fun i : Fin m => i.val)
    (fun _ _ h => h) σ
  simp only [Equiv.Perm.one_apply, finitePermutedStaircaseDegree_one] at h1
  simp only [mul_comm] at hr
  omega

theorem finiteStaircaseDegree_weight_lt {m : ℕ} (σ : Equiv.Perm (Fin m)) (hne : σ ≠ 1) :
    finiteColorWeight (finiteStaircaseDegree m) <
      finiteColorWeight (finitePermutedStaircaseDegree σ) := by
  have h1 := staircase_weight_complement (1 : Equiv.Perm (Fin m))
  have hσ := staircase_weight_complement σ
  have hr := fin_strictMono_weighted_sum_perm_lt (fun i : Fin m => i.val)
    (fun _ _ h => h) σ hne
  simp only [Equiv.Perm.one_apply, finitePermutedStaircaseDegree_one] at h1
  simp only [mul_comm] at hr
  omega

theorem staircase_sub_weight_le {m : ℕ} (d : Fin m →₀ ℕ)
    (σ : Equiv.Perm (Fin m))
    (h : finitePermutedStaircaseDegree σ ≤ d + finiteStaircaseDegree m) :
    finiteColorWeight (d + finiteStaircaseDegree m - finitePermutedStaircaseDegree σ) ≤
      finiteColorWeight d := by
  have hs := finiteColorWeight_sub_add _ _ h
  rw [finiteColorWeight_add] at hs
  have hw := finiteStaircaseDegree_weight_le σ
  omega

theorem staircase_sub_weight_lt {m : ℕ} (d : Fin m →₀ ℕ)
    (σ : Equiv.Perm (Fin m)) (hne : σ ≠ 1)
    (h : finitePermutedStaircaseDegree σ ≤ d + finiteStaircaseDegree m) :
    finiteColorWeight (d + finiteStaircaseDegree m - finitePermutedStaircaseDegree σ) <
      finiteColorWeight d := by
  have hs := finiteColorWeight_sub_add _ _ h
  rw [finiteColorWeight_add] at hs
  have hw := finiteStaircaseDegree_weight_lt σ hne
  omega

end
end ModifiedCartan

#print axioms ModifiedCartan.finiteStaircaseDegree_weight_lt
