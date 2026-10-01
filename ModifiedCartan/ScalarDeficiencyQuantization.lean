import ModifiedCartan.ScalarProximityMultiplicities
import ModifiedCartan.ScalarProximityLimits
import ModifiedCartan.ScalarDeficiencyBasics

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- The literal deficiencies of the original scalar meromorphic function are
integer multiples of the reciprocal order, with the exact total integer count.
All projective limits and their transfer to the scalar characteristic are proved.
Auxiliary to LaTeX `thm:A` (b). -/
theorem scalarDeficiency_quantization_of_lift {f : ℂ → ℂ} (hf : Meromorphic f)
    (F : Curve 1) (hFt : F.Transcendental) (hFl : F.linearlyNonDegenerate)
    (he : f =ᶠ[codiscreteWithin (univ : Set ℂ)] (fun z => F.coord 1 z / F.coord 0 z))
    (hD : MeromorphicOn.divisor (F.coord 0) univ = (MeromorphicOn.divisor f univ)⁻)
    (hsmall : SmallRamification F) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic F) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic F) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) :
    ∃ p : WithTop ℂ → ℕ, HasSum (fun a => (p a : ℝ)) (2 * ρ) ∧
      ∀ a : WithTop ℂ, scalarDeficiency f a = (((p a : ℝ) / ρ : ℝ) : EReal) := by
  obtain ⟨p, hp, hlim⟩ := scalar_exists_projective_proximity_multiplicities F hFl hFt hsmall hρ hl hu hm
  refine ⟨p, hp, fun a => ?_⟩
  apply scalarDeficiency_eq_of_proximity_ratio_tendsto
  apply Filter.tendsto_of_subseq_tendsto
  intro r hr
  refine ⟨id, ?_⟩
  exact scalar_proximity_ratio_tendsto_of_lift hf F hFt hFl he hD a hr ((hlim a).comp hr)

end ModifiedCartan
#print axioms ModifiedCartan.scalarDeficiency_quantization_of_lift
