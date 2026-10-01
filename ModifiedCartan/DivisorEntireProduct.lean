import ModifiedCartan.CorrectedDivisorFactor
import ModifiedCartan.DivisorCopies
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

open scoped Topology BigOperators
open Filter Set Metric Function
set_option autoImplicit false
namespace ModifiedCartan

noncomputable def divisorCopiesEncoding (D : locallyFinsupp ℂ ℤ) : Encodable (divisorCopies D) := by
  letI := divisorCopies_countable D
  exact Encodable.ofCountable _

noncomputable def divisorCopyIndex (D : locallyFinsupp ℂ ℤ) : divisorCopies D → ℕ :=
  @Encodable.encode _ (divisorCopiesEncoding D)

theorem divisorCopyIndex_injective (D : locallyFinsupp ℂ ℤ) :
    Function.Injective (divisorCopyIndex D) :=
  @Encodable.encode_injective _ (divisorCopiesEncoding D)

theorem divisorCopy_geometric_summable (D : locallyFinsupp ℂ ℤ) :
    Summable (fun a : divisorCopies D => (1 / 2 : ℝ) ^ divisorCopyIndex D a) :=
  (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).comp_injective (divisorCopyIndex_injective D)

theorem divisor_factors_eventually_bound (D : locallyFinsupp ℂ ℤ)
    (S : Set (divisorCopies D)) {R : ℝ} (hR : 0 ≤ R) :
    ∀ᶠ a : S in cofinite, ∀ z : ℂ, ‖z‖ ≤ R →
      ‖correctedDivisorFactor (divisorCopyIndex D a.val) a.val.1 z - 1‖ ≤
        (1 / 2 : ℝ) ^ divisorCopyIndex D a.val := by
  have ht : Tendsto (Subtype.val : S → divisorCopies D) cofinite cofinite :=
    Subtype.val_injective.tendsto_cofinite
  filter_upwards [ht.eventually (divisorCopies_eventually_norm_gt D (2 * R + 1))] with a ha z hz
  apply correctedDivisorFactor_half_disk_bound
  · apply norm_pos_iff.mp
    linarith
  · linarith

theorem divisor_factor_deviation_summable (D : locallyFinsupp ℂ ℤ)
    (S : Set (divisorCopies D)) (z : ℂ) :
    Summable (fun a : S =>
      ‖correctedDivisorFactor (divisorCopyIndex D a.val) a.val.1 z - 1‖) := by
  apply ((divisorCopy_geometric_summable D).subtype S).of_norm_bounded_eventually
  filter_upwards [divisor_factors_eventually_bound D S (norm_nonneg z)] with a ha
  simpa only [norm_norm, Function.comp_apply] using! ha z le_rfl

/-- The product uses actual divisor copies and chosen entire corrections.
All convergence is proved from local finiteness, not from a growth premise. -/
noncomputable def divisorEntireSubproduct (D : locallyFinsupp ℂ ℤ)
    (S : Set (divisorCopies D)) (z : ℂ) : ℂ :=
  ∏' a : S, correctedDivisorFactor (divisorCopyIndex D a.val) a.val.1 z

noncomputable def divisorEntireProduct (D : locallyFinsupp ℂ ℤ) (z : ℂ) : ℂ :=
  ∏' a : divisorCopies D, correctedDivisorFactor (divisorCopyIndex D a) a.1 z

theorem divisorEntireSubproduct_multipliable (D : locallyFinsupp ℂ ℤ)
    (S : Set (divisorCopies D)) (z : ℂ) :
    Multipliable (fun a : S => correctedDivisorFactor (divisorCopyIndex D a.val) a.val.1 z) := by
  simpa only [add_sub_cancel] using
    multipliable_one_add_of_summable (divisor_factor_deviation_summable D S z)

theorem divisorEntireSubproduct_hasProdUniformlyOn (D : locallyFinsupp ℂ ℤ)
    (S : Set (divisorCopies D)) {K : Set ℂ} (hK : IsCompact K) :
    HasProdUniformlyOn
      (fun a : S => correctedDivisorFactor (divisorCopyIndex D a.val) a.val.1)
      (divisorEntireSubproduct D S) K := by
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  have hb : ∀ᶠ a : S in cofinite, ∀ z ∈ K,
      ‖correctedDivisorFactor (divisorCopyIndex D a.val) a.val.1 z - 1‖ ≤
        (1 / 2 : ℝ) ^ divisorCopyIndex D a.val := by
    filter_upwards [divisor_factors_eventually_bound D S hR.le] with a ha z hz
    apply ha
    simpa only [mem_closedBall, dist_zero_right] using hKR hz
  simpa only [add_sub_cancel, divisorEntireSubproduct] using!
    ((divisorCopy_geometric_summable D).subtype S).hasProdUniformlyOn_one_add hK hb
      (fun a => ((correctedDivisorFactor_differentiable _ _).continuous.sub continuous_const).continuousOn)

theorem divisorEntireSubproduct_differentiable (D : locallyFinsupp ℂ ℤ)
    (S : Set (divisorCopies D)) : Differentiable ℂ (divisorEntireSubproduct D S) := by
  have hlocal : HasProdLocallyUniformlyOn
      (fun a : S => correctedDivisorFactor (divisorCopyIndex D a.val) a.val.1)
      (divisorEntireSubproduct D S) univ :=
    hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
      (fun _ _ hK => divisorEntireSubproduct_hasProdUniformlyOn D S hK)
  have ht : TendstoLocallyUniformlyOn
      (fun T : Finset S => fun z => ∏ a ∈ T,
        correctedDivisorFactor (divisorCopyIndex D a.val) a.val.1 z)
      (divisorEntireSubproduct D S) atTop univ := hlocal
  apply differentiableOn_univ.mp
  apply ht.differentiableOn _ isOpen_univ
  exact Eventually.of_forall (fun T => DifferentiableOn.fun_finsetProd
    (fun a _ => (correctedDivisorFactor_differentiable _ _).differentiableOn))

theorem divisorEntireSubproduct_univ (D : locallyFinsupp ℂ ℤ) :
    divisorEntireSubproduct D univ = divisorEntireProduct D := by
  funext z
  exact tprod_univ (fun a : divisorCopies D => correctedDivisorFactor (divisorCopyIndex D a) a.1 z)

theorem divisorEntireProduct_differentiable (D : locallyFinsupp ℂ ℤ) :
    Differentiable ℂ (divisorEntireProduct D) := by
  rw [← divisorEntireSubproduct_univ]
  exact divisorEntireSubproduct_differentiable D univ

theorem divisorEntireSubproduct_mul_compl (D : locallyFinsupp ℂ ℤ)
    (S : Set (divisorCopies D)) (z : ℂ) :
    divisorEntireSubproduct D S z * divisorEntireSubproduct D Sᶜ z =
      divisorEntireProduct D z :=
  Multipliable.tprod_mul_tprod_compl
    (f := fun a : divisorCopies D => correctedDivisorFactor (divisorCopyIndex D a) a.1 z) (s := S)
    (divisorEntireSubproduct_multipliable D S z)
    (divisorEntireSubproduct_multipliable D Sᶜ z)

theorem divisorEntireSubproduct_ne_zero (D : locallyFinsupp ℂ ℤ)
    (S : Set (divisorCopies D)) {z : ℂ} (hz : ∀ a ∈ S, z ≠ a.1) :
    divisorEntireSubproduct D S z ≠ 0 := by
  have hf (a : S) : 1 + (correctedDivisorFactor (divisorCopyIndex D a.val) a.val.1 z - 1) ≠ 0 := by
    rw [add_sub_cancel]
    exact mt (correctedDivisorFactor_eq_zero_iff _ _ _).mp (hz a.val a.property)
  simpa only [add_sub_cancel, divisorEntireSubproduct] using!
    tprod_one_add_ne_zero_of_summable hf (divisor_factor_deviation_summable D S z)

end ModifiedCartan
#print axioms ModifiedCartan.divisorEntireProduct_differentiable
#print axioms ModifiedCartan.divisorEntireSubproduct_ne_zero

