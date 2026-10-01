import ModifiedCartan.AmbientFactorizationParameters
import ModifiedCartan.SupportedDataColoringTransport
import ModifiedCartan.SupportedPowerSumQuadratic

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem supportedPowerSumLaurentWeight_extend {A B : Type*} [Fintype A] [Fintype B]
    (U : Finset A) (p q : SupportedPermutationData U) :
    supportedPowerSumLaurentWeight B
      (extendSupportedPermutationData U p, extendSupportedPermutationData U q) =
      supportedPowerSumLaurentWeight B (p, q) := by
  simp only [supportedPowerSumLaurentWeight, extendSupportedPermutationData_sign,
    extendSupportedPermutationData_card, extendSupportedPermutationData_fixedColoringSum]
  have hs :
      @Equiv.Perm.sign U (@Subtype.instDecidableEq A (fun a => a ∈ U) (Classical.decEq A)) _ p.2.val =
      @Equiv.Perm.sign U (Classical.decEq U) _ p.2.val :=
    congrArg (fun d : DecidableEq U => @Equiv.Perm.sign U d _ p.2.val) (Subsingleton.elim _ _)
  rw [hs]
  rfl

def ambientFactorizationLaurentSeries {A : Type*} [Fintype A] (B : Type*) [Fintype B]
    (θ : Equiv.Perm A) (U Z : Finset A) : LaurentPolynomial (MvPolynomial B ℂ) :=
  ∑ p : AmbientFactorizationParameters θ U Z, supportedPowerSumLaurentWeight B p.val

theorem ambientFactorizationLaurentSeries_restrict {A B : Type*} [Fintype A] [Fintype B]
    (θ : Equiv.Perm A) (U Z : Finset A) (hθ : θ ∈ supportedPermutationSubgroup U) (hZ : Z ⊆ U) :
    ambientFactorizationLaurentSeries B θ U Z =
      zFactorizationLaurentSeries B (supportedPermutationRestriction U θ hθ)
        (Z.subtype (fun a => a ∈ U)) := by
  rw [ambientFactorizationLaurentSeries,
    ← Equiv.sum_comp (ambientFactorizationRestrictionEquiv θ U Z hθ hZ)
      (fun p => supportedPowerSumLaurentWeight B p.val), zFactorizationLaurentSeries]
  apply Finset.sum_congr (by ext; simp)
  intro p hp
  change supportedPowerSumLaurentWeight B
      (extendSupportedPermutationData U p.val.1, extendSupportedPermutationData U p.val.2) = _
  rw [supportedPowerSumLaurentWeight_extend]
  rfl

theorem ambientFactorizationLaurentSeries_zero_of_not_supported {A B : Type*}
    [Fintype A] [Fintype B] (θ : Equiv.Perm A) (U Z : Finset A)
    (hθ : θ ∉ supportedPermutationSubgroup U) :
    ambientFactorizationLaurentSeries B θ U Z = 0 := by
  letI : IsEmpty (AmbientFactorizationParameters θ U Z) :=
    ⟨fun p => hθ (ambientFactorization_product_supported p)⟩
  simp [ambientFactorizationLaurentSeries]

theorem ambientFactorizationLaurentSeries_zero_of_not_subset {A B : Type*}
    [Fintype A] [Fintype B] (θ : Equiv.Perm A) (U Z : Finset A) (hZ : ¬ Z ⊆ U) :
    ambientFactorizationLaurentSeries B θ U Z = 0 := by
  letI : IsEmpty (AmbientFactorizationParameters θ U Z) :=
    ⟨fun p => hZ (ambientFactorization_overlap_subset p)⟩
  simp [ambientFactorizationLaurentSeries]

end
end ModifiedCartan

