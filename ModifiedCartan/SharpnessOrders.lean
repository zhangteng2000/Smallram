import ModifiedCartan.RationalCharacteristicGrowth
import ModifiedCartan.SharpnessCharacteristicLimit
import ModifiedCartan.SharpnessSystemExistence

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem IsSharpnessSystem.curve_transcendental {n k q : ℕ} {g : Index n → ℂ → ℂ}
    (h : IsSharpnessSystem n k q g) (hq : 2 ≤ q) (hqn : q ≤ n + 1) :
    (h.curve hq hqn).Transcendental :=
  transcendental_of_positive_characteristic_power_limit (h.curve hq hqn)
    (sharpness_rho_pos q k) (sharpness_asymptotic_constant_pos hq k)
    (h.characteristic_power_limit hq hqn)

namespace Paper

/-- LaTeX `prop:sharpness-orders`: the prescribed normalized entire system is
reduced, transcendental and nondegenerate, has W=1, and has the exact positive
characteristic asymptotic. -/
theorem prop_sharpness_orders (n k q : ℕ) (g : Index n → ℂ → ℂ) :
    SharpnessOrdersTarget n k q g := by
  intro _hn hq hqn h
  exact ⟨h.curve hq hqn, rfl, h.curve_transcendental hq hqn,
    h.curve_linearlyNonDegenerate hq hqn, h.wronskian_one hq hqn,
    h.characteristic_power_limit hq hqn⟩

/-- The entire prescribed system exists and satisfies the exact sharpness
conclusion for every admissible pair (q,k). -/
theorem prop_sharpness_orders_realized (n k q : ℕ) (hn : 1 ≤ n)
    (hq : 2 ≤ q) (hqn : q ≤ n + 1) :
    ∃ g : Index n → ℂ → ℂ, IsSharpnessSystem n k q g ∧
      ∃ f : Curve n, f.coord = g ∧ f.Transcendental ∧ f.linearlyNonDegenerate ∧
        (∀ z, FewInflection.wronskian n g z = 1) ∧
        Tendsto (fun r : ℝ => characteristic f r / r ^ (1 + (k : ℝ) / q)) atTop
          (𝓝 ((q : ℝ) * Real.sin (Real.pi / q) / (Real.pi * (1 + (k : ℝ) / q)))) := by
  obtain ⟨g, hg⟩ := sharpnessSystem_exists n k q hn hq hqn
  exact ⟨g, hg, prop_sharpness_orders n k q g hn hq hqn hg⟩

end Paper
end ModifiedCartan
#print axioms ModifiedCartan.Paper.prop_sharpness_orders
#print axioms ModifiedCartan.Paper.prop_sharpness_orders_realized
