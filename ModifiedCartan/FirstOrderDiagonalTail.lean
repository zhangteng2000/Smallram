import ModifiedCartan.FirstOrderGaugeAsymptotics

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The diagonal system with its actual B/t term has a fundamental system
with the exact polynomial and exponential normalization. All spectral values
are distinct; coincident real parts require no extra assumption. -/
theorem firstOrder_diagonal_tail_fundamental_system_exists {q : ℕ}
    (lam : Fin q → ℂ) (hlam : Function.Injective lam)
    (B : Matrix (Fin q) (Fin q) ℂ) (b : ℝ) (hB : ∀ i, B i i = (b : ℂ)) :
    ∃ T : ℝ, 1 ≤ T ∧ ∃ Z : Fin q → ℝ → EuclideanSpace ℂ (Fin q),
      (∀ j t, T ≤ t → HasDerivWithinAt (Z j)
        (Matrix.toEuclideanCLM (n := Fin q) (𝕜 := ℂ)
          (Matrix.diagonal lam + ((t⁻¹ : ℝ) : ℂ) • B) (Z j t)) (Ici T) t) ∧
      (∀ t, T ≤ t → LinearIndependent ℂ (fun j => Z j t)) ∧
      (∀ j, Tendsto (fun t : ℝ => t ^ (-b) •
        (Complex.exp (-lam j * (t : ℂ)) • Z j t))
        atTop (𝓝 (WithLp.toLp 2 (Pi.single j (1 : ℂ))))) := by
  let F := Matrix.toEuclideanCLM (n := Fin q) (𝕜 := ℂ)
  let L := F (Matrix.diagonal lam)
  let H := F B
  let C := F (firstOrderEliminator lam B)
  have hs (a : ℝ) (M : EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) :
      (a : ℂ) • M = a • M := IsScalarTower.algebraMap_smul ℂ a M
  have hc : L * C - C * L + H = b • (1 : EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) := by
    have hh := congrArg (fun M => F M) (firstOrderEliminator_commutator lam hlam B (b : ℂ) hB)
    simpa only [map_add, map_sub, map_mul, map_smul, map_one, hs, L, H, C] using! hh
  let D := (H - b • (1 : EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q))) * C + C
  obtain ⟨T, hT, hu, hEc, hEi, _⟩ := firstOrderError_tail_exists C D
  let E : ℝ → Matrix (Fin q) (Fin q) ℂ := fun t => F.symm (firstOrderError C D t)
  have hE (t : ℝ) : F (E t) = firstOrderError C D t := F.apply_symm_apply _
  have hEc' : ContinuousOn (fun t => F (E t)) (Ici T) := by simpa only [hE] using hEc
  have hEi' : IntegrableOn (fun t => F (E t)) (Ici T) := by simpa only [hE] using hEi
  obtain ⟨S, hS, X, hXd, hXli, hXl⟩ :=
    euclidean_diagonal_tail_fundamental_system_exists lam E T hEc' hEi'
  let Z : Fin q → ℝ → EuclideanSpace ℂ (Fin q) := fun j => powerLinearGauge C b (X j)
  have hcoef (t : ℝ) : F (Matrix.diagonal lam + ((t⁻¹ : ℝ) : ℂ) • B) = L + t⁻¹ • H := by
    rw [map_add, map_smul, hs]
  refine ⟨S, hT.trans hS, Z, ?_, ?_, ?_⟩
  · intro j t ht
    have hdt : HasDerivWithinAt (X j) ((L + firstOrderError C D t) (X j t)) (Ici S) t := by
      have hh := hXd j t ht
      change HasDerivWithinAt (X j) (F (Matrix.diagonal lam + E t) (X j t)) (Ici S) t at hh
      simpa only [map_add, hE, L] using! hh
    have ht0 : 0 < t := zero_lt_one.trans_le (hT.trans (hS.trans ht))
    change HasDerivWithinAt (Z j) (F (Matrix.diagonal lam + ((t⁻¹ : ℝ) : ℂ) • B) (Z j t)) (Ici S) t
    rw [hcoef]
    exact powerLinearGauge_hasDerivWithinAt L H C b hc ht0 (hu t (hS.trans ht)) hdt
  · intro t ht
    exact powerLinearGauge_linearIndependent C b X
      (zero_lt_one.trans_le (hT.trans (hS.trans ht))) (hu t (hS.trans ht)) (hXli t ht)
  · intro j
    exact powerLinearGauge_normalized_tendsto C b (hXl j)

end ModifiedCartan
#print axioms ModifiedCartan.firstOrder_diagonal_tail_fundamental_system_exists

