import FewInflection.Dilation
import FewInflection.GrowthBasics

open scoped Topology
open Filter

namespace FewInflection

noncomputable section

/-! A positive change of the radial variable preserves the compact-uniform
form of regular variation.  The proof keeps the compact multiplier fixed and
applies the defining estimate at the rescaled base point `t * r`. -/
theorem regularlyVarying_comp_const_mul
    {T : ℝ → ℝ} {ρ t : ℝ} (ht : 0 < t)
    (hT : RegularlyVarying T ρ) :
    RegularlyVarying (fun r => T (t * r)) ρ := by
  intro K hK hKpos ε hε
  rcases hT K hK hKpos ε hε with ⟨R, hR, hbound⟩
  refine ⟨R / t, div_pos hR ht, ?_⟩
  intro r hr c hc
  have htr : R < t * r := by
    simpa [mul_comm] using (div_lt_iff₀ ht).mp hr
  have hbound' := hbound (t * r) htr c hc
  simpa [mul_assoc, mul_left_comm, mul_comm] using hbound'

/-! The same change of scale preserves the slowly varying condition used in
the formal statement. -/
theorem slowlyVarying_comp_const_mul
    {ℓ : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (hℓ : SlowlyVarying ℓ) :
    SlowlyVarying (fun r => ℓ (t * r)) := by
  rcases hℓ with ⟨hpos, hcont, hε⟩
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    exact hpos (t * r) (mul_pos ht hr)
  · exact hcont.comp (continuous_const.mul continuous_id).continuousOn
      (fun r hr => mul_pos ht hr)
  · intro ε hεpos
    rcases hε ε hεpos with ⟨R, hR, hbound⟩
    refine ⟨R / t, div_pos hR ht, ?_⟩
    intro r hr c hc
    have htr : R < t * r := by
      simpa [mul_comm] using (div_lt_iff₀ ht).mp hr
    have hbound' := hbound (t * r) htr c hc
    simpa [mul_assoc, mul_left_comm, mul_comm] using hbound'

/-! Positive real dilation transports regular variation of a curve's
characteristic without changing its index. -/
theorem Curve.regularlyVarying_characteristic_dilate_of_pos
    {n : ℕ} (f : Curve n) {t ρ : ℝ} (ht : 0 < t)
    (hT : RegularlyVarying (characteristic f) ρ) :
    RegularlyVarying (characteristic (f.dilate (t : ℂ))) ρ := by
  have hcomp := regularlyVarying_comp_const_mul ht hT
  have heq : characteristic (f.dilate (t : ℂ)) =
      (fun r => characteristic f (t * r)) := by
    funext r
    exact Curve.characteristic_dilate_of_pos f ht
  rw [heq]
  exact hcomp

end

end FewInflection
