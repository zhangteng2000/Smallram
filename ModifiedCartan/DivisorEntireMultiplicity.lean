import ModifiedCartan.DivisorEntireProduct

open scoped Topology BigOperators
open Filter Set Function MeromorphicOn
set_option autoImplicit false
namespace ModifiedCartan

/-- Analytic multiplicity of a finite product, used to isolate each actual
root fiber in the scalar `thm:A` representation construction. -/
theorem analyticOrderAt_finset_product {ι : Type*} (S : Finset ι)
    (F : ι → ℂ → ℂ) (z : ℂ) (hF : ∀ i ∈ S, AnalyticAt ℂ (F i) z) :
    analyticOrderAt (fun w => ∏ i ∈ S, F i w) z =
      ∑ i ∈ S, analyticOrderAt (F i) z := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [analyticOrderAt_eq_zero]
  | @insert i S hi ih =>
      have hiA := hF i (Finset.mem_insert_self i S)
      have hSA : ∀ j ∈ S, AnalyticAt ℂ (F j) z :=
        fun j hj => hF j (Finset.mem_insert_of_mem hj)
      have he : (fun w => ∏ j ∈ insert i S, F j w) =
          F i * (fun w => ∏ j ∈ S, F j w) := by
        ext w
        exact Finset.prod_insert hi
      rw [he, analyticOrderAt_mul hiA (S.analyticAt_fun_prod hSA), ih hSA,
        Finset.sum_insert hi]

theorem divisorEntireSubproduct_fiber (D : locallyFinsupp ℂ ℤ) (z w : ℂ) :
    divisorEntireSubproduct D {a | a.1 = z} w =
      ∏ i : Fin (D z).toNat,
        correctedDivisorFactor (divisorCopyIndex D ⟨z, i⟩) z w := by
  unfold divisorEntireSubproduct
  calc
    (∏' a : {a : divisorCopies D // a.1 = z},
        correctedDivisorFactor (divisorCopyIndex D a.val) a.val.1 w) =
      ∏' i : Fin (D z).toNat,
        correctedDivisorFactor (divisorCopyIndex D ⟨z, i⟩) z w := by
      simpa only [divisorCopiesFiberEquiv, Equiv.coe_fn_symm_mk] using
        ((divisorCopiesFiberEquiv D z).symm.tprod_eq
          (fun a : {a : divisorCopies D // a.1 = z} =>
            correctedDivisorFactor (divisorCopyIndex D a.val) a.val.1 w)).symm
    _ = _ := tprod_fintype _

theorem divisorEntireSubproduct_fiber_order (D : locallyFinsupp ℂ ℤ) (z : ℂ) :
    analyticOrderAt (divisorEntireSubproduct D {a | a.1 = z}) z = ((D z).toNat : ℕ∞) := by
  rw [funext (divisorEntireSubproduct_fiber D z), analyticOrderAt_finset_product
    Finset.univ _ z (fun i _ => (correctedDivisorFactor_differentiable _ _).analyticAt z)]
  simp only [correctedDivisorFactor_analyticOrderAt, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_one]

/-- The product has exactly the prescribed multiplicity at every point,
including the origin. No unspecified nonvanishing factor is assumed. -/
theorem divisorEntireProduct_analyticOrderAt (D : locallyFinsupp ℂ ℤ) (z : ℂ) :
    analyticOrderAt (divisorEntireProduct D) z = ((D z).toNat : ℕ∞) := by
  have he : divisorEntireProduct D =
      divisorEntireSubproduct D {a | a.1 = z} *
      divisorEntireSubproduct D {a | a.1 = z}ᶜ := by
    ext w
    exact (divisorEntireSubproduct_mul_compl D {a | a.1 = z} w).symm
  have hA := (divisorEntireSubproduct_differentiable D {a | a.1 = z}).analyticAt z
  have hB := (divisorEntireSubproduct_differentiable D {a | a.1 = z}ᶜ).analyticAt z
  have hn : divisorEntireSubproduct D {a | a.1 = z}ᶜ z ≠ 0 :=
    divisorEntireSubproduct_ne_zero D _ (fun a ha he => ha he.symm)
  rw [he, analyticOrderAt_mul hA hB, divisorEntireSubproduct_fiber_order,
    hB.analyticOrderAt_eq_zero.mpr hn, add_zero]

theorem divisorEntireProduct_divisor (D : locallyFinsupp ℂ ℤ) (hD : 0 ≤ D) :
    divisor (divisorEntireProduct D) univ = D := by
  ext z
  rw [entire_divisor_eq_analyticMultiplicity (divisorEntireProduct_differentiable D),
    divisorEntireProduct_analyticOrderAt, ENat.toNat_natCast, Int.toNat_of_nonneg (hD z)]

/-- A proved Weierstrass product for any nonnegative locally finite divisor.
This is the exact general representation dependency needed by scalar `thm:A`. -/
theorem exists_entire_with_nonnegative_divisor (D : locallyFinsupp ℂ ℤ) (hD : 0 ≤ D) :
    ∃ q : ℂ → ℂ, Differentiable ℂ q ∧ divisor q univ = D ∧
      ∀ z : ℂ, meromorphicOrderAt q z ≠ ⊤ := by
  refine ⟨divisorEntireProduct D, divisorEntireProduct_differentiable D,
    divisorEntireProduct_divisor D hD, fun z => ?_⟩
  rw [(divisorEntireProduct_differentiable D).analyticAt z |>.meromorphicOrderAt_eq,
    divisorEntireProduct_analyticOrderAt]
  simp

end ModifiedCartan
#print axioms ModifiedCartan.divisorEntireProduct_analyticOrderAt
#print axioms ModifiedCartan.exists_entire_with_nonnegative_divisor
