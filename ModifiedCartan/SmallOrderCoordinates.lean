import ModifiedCartan.NormalizedCharacteristic
import ModifiedCartan.TranslatedCounting
import ModifiedCartan.ExponentialGauge

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan.Paper

/-- LaTeX `lem:small-order-coordinates`, including the actual inverse-jet
coordinates, `eq:small-order-T`, and `eq:translated-count`. The same entire
gauge works for all growth exponents, and every regular base point is allowed. -/
theorem lem_small_order_coordinates {n : ℕ} (f : Curve n)
    (hlin : f.linearlyNonDegenerate) (horder : order f < 1) (h0 : f.coord 0 0 ≠ 0) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      (∀ z, f.coord 0 z = genusZeroProduct (f.coord 0) z * Complex.exp (G z)) ∧
      (∀ j : Index n, entireOrder (gaugedCoordinates f G j) ≤ order f) ∧
      (∃ b : ℂ, FewInflection.wronskian n (gaugedCoordinates f G) b ≠ 0) ∧
      ∀ b : ℂ, FewInflection.wronskian n (gaugedCoordinates f G) b ≠ 0 →
        (∀ i j : Index n, iteratedDeriv i.val
          (normalizedCoordinates (gaugedCoordinates f G) b j) 0 = if i = j then 1 else 0) ∧
        (∀ j : Index n, entireOrder (normalizedCoordinates (gaugedCoordinates f G) b j)
          ≤ order f) ∧
        (∃ C : ℝ, ∀ s : ℝ, 1 ≤ s → characteristic f s ≤
          systemLogMaximum (normalizedCoordinates (gaugedCoordinates f G) b) (s + ‖b‖) + C) ∧
        (∃ Cb : ℝ, ∀ t : ℝ, 1 ≤ t →
          systemCounting (normalizedCoordinates (gaugedCoordinates f G) b) t ≤
            ramification f (t + ‖b‖) + Cb) := by
  obtain ⟨G, hG, he, ho⟩ := exists_small_order_entire_gauge f horder h0
  refine ⟨G, hG, he, ho, exponentialGauge_exists_regular_point f hlin G hG, ?_⟩
  intro b hW
  have hg : ∀ j, Differentiable ℂ (gaugedCoordinates f G j) :=
    (exponentialGauge f G hG).holomorphic
  refine ⟨normalizedCoordinates_initialJets hg hW,
    normalizedCoordinates_entireOrder_le hg b (order_nonneg f) ho, ?_, ?_⟩
  · obtain ⟨C, hc⟩ := normalizedCoordinates_characteristic_bound (exponentialGauge f G hG) hW
    refine ⟨C, fun s hs => ?_⟩
    have hh := hc s hs
    rw [exponentialGauge_characteristic f G hG (zero_lt_one.trans_le hs)] at hh
    exact hh
  · obtain ⟨C, hc⟩ := normalizedCoordinates_counting_bound hg (fun j => (ho j).trans_lt horder) hW
    refine ⟨C, fun t ht => ?_⟩
    have hh := hc t ht
    have hr : ValueDistribution.logCounting (FewInflection.wronskian n (gaugedCoordinates f G))
        (0 : WithTop ℂ) (t + ‖b‖) = ramification f (t + ‖b‖) :=
      congrFun (exponentialGauge_ramification f G hG) (t + ‖b‖)
    rw [hr] at hh
    exact hh

end ModifiedCartan.Paper
#print axioms ModifiedCartan.Paper.lem_small_order_coordinates
