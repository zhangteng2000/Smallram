import ModifiedCartan.FirstOrderDiagonalTail

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- The proved diagonal B/t fundamental system in finite-product coordinates,
for comparison with actual scaled derivative jets. -/
theorem firstOrder_diagonal_pi_tail_exists {q : ℕ}
    (lam : Fin q → ℂ) (hlam : Function.Injective lam)
    (B : Matrix (Fin q) (Fin q) ℂ) (b : ℝ) (hB : ∀ i, B i i = (b : ℂ)) :
    ∃ T : ℝ, 1 ≤ T ∧ ∃ Z : Fin q → ℝ → Fin q → ℂ,
      (∀ j t, T ≤ t → HasDerivWithinAt (Z j)
        ((Matrix.diagonal lam + ((t⁻¹ : ℝ) : ℂ) • B).mulVec (Z j t)) (Ici T) t) ∧
      (∀ t, T ≤ t → LinearIndependent ℂ (fun j => Z j t)) ∧
      (∀ j, Tendsto (fun t : ℝ => t ^ (-b) •
        (Complex.exp (-lam j * (t : ℂ)) • Z j t)) atTop (𝓝 (Pi.single j (1 : ℂ)))) := by
  obtain ⟨T, hT, X, hd, hli, hl⟩ :=
    firstOrder_diagonal_tail_fundamental_system_exists lam hlam B b hB
  let e : EuclideanSpace ℂ (Fin q) ≃L[ℂ] (Fin q → ℂ) :=
    PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin q => ℂ)
  let Z : Fin q → ℝ → Fin q → ℂ := fun j t => e (X j t)
  refine ⟨T, hT, Z, ?_, ?_, ?_⟩
  · intro j t ht
    have he := (e.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t (hd j t ht)
    have he' : HasDerivWithinAt (fun u => e (X j u))
        (e (Matrix.toEuclideanCLM (n := Fin q) (𝕜 := ℂ)
          (Matrix.diagonal lam + ((t⁻¹ : ℝ) : ℂ) • B) (X j t))) (Ici T) t := by
      simpa only [Function.comp_apply] using! he
    exact he'
  · intro t ht
    exact (hli t ht).map' e.toLinearMap (LinearMap.ker_eq_bot_of_injective e.injective)
  · intro j
    have he := (e.continuous.tendsto (WithLp.toLp 2 (Pi.single j (1 : ℂ)))).comp (hl j)
    have hs (a : ℝ) (v : EuclideanSpace ℂ (Fin q)) : e (a • v) = a • e v :=
      e.toContinuousLinearMap.map_smul_of_tower a v
    simpa only [Function.comp_apply, hs, map_smul] using! he

end ModifiedCartan
#print axioms ModifiedCartan.firstOrder_diagonal_pi_tail_exists
