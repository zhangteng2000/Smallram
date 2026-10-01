import ModifiedCartan.WeakGradientAffine
import ModifiedCartan.PhaseConePropagation

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem convex_translated_strictPhaseCone (A : Finset ℂ) (a c : ℂ) :
    Convex ℝ ((fun x => x - c) ⁻¹' strictPhaseCone A a) := by
  simpa only [sub_eq_add_neg] using (convex_strictPhaseCone A a).translate_preimage_left (-c)

theorem HasWeakComplexGradient.affine_on_strict_cone
    {A : Finset ℂ} {a c : ℂ} {s : ℝ} (hs : 0 < s)
    {u : ℂ → ℝ} {g : ℂ → ℂ} (hc : Continuous u)
    (hw : HasWeakComplexGradient (ball c s ∩ (fun x => x - c) ⁻¹' strictPhaseCone A a) u g)
    (hg : g =ᵐ[volume.restrict (ball c s ∩ (fun x => x - c) ⁻¹' strictPhaseCone A a)] (fun _ => a))
    {x : ℂ} (hx : x ∈ ball c s) (hcone : x - c ∈ strictPhaseCone A a) :
    u x = u c + (a * (x - c)).re := by
  let V := ball c s ∩ (fun x => x - c) ⁻¹' strictPhaseCone A a
  have hV : IsOpen V := isOpen_ball.inter
    ((isOpen_strictPhaseCone A a).preimage (continuous_id.sub continuous_const))
  have hVc : Convex ℝ V := (convex_ball c s).inter (convex_translated_strictPhaseCone A a c)
  let z : ℕ → ℂ := fun n => c + (shrinkingWeakBump n).rOut • (x - c)
  have hz (n : ℕ) : z n ∈ V := by
    have ht : 0 < (shrinkingWeakBump n).rOut := inv_pos.mpr (by positivity)
    have ht1 : (shrinkingWeakBump n).rOut ≤ 1 := inv_le_one_of_one_le₀ (by norm_num)
    refine ⟨(convex_ball c s).add_smul_mem (mem_ball_self hs)
      (by simpa only [add_sub_cancel] using hx) ⟨ht.le, ht1⟩, ?_⟩
    simpa only [z, mem_preimage, add_sub_cancel_left] using strictPhaseCone_smul hcone ht
  have hzt : Tendsto z atTop (𝓝 c) := by
    simpa only [zero_smul, add_zero] using
      tendsto_const_nhds.add (shrinkingWeakBump_tendsto.smul_const (x - c))
  have he : IsClosed {y : ℂ | u y - u x = (a * (y - x)).re} :=
    isClosed_eq (hc.sub continuous_const)
      (Complex.continuous_re.comp (continuous_const.mul (continuous_id.sub continuous_const)))
  have hcx : u c - u x = (a * (c - x)).re := he.mem_of_tendsto hzt
    (Eventually.of_forall (fun n => hw.affine_difference_of_ae_const hV hVc.isPreconnected hc hg ⟨hx, hcone⟩ (hz n)))
  have heq : (a * (c - x)).re = -(a * (x - c)).re := by
    rw [← Complex.neg_re, ← mul_neg, neg_sub]
  rw [heq] at hcx
  linarith

theorem IsSubharmonicOn.affine_on_essential_strict_cone
    {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : IsSubharmonicOn U (fun z => (u z : EReal)))
    (hc : Continuous u) (hw : HasWeakComplexGradient U u g)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂volume.restrict U, ‖g z‖ ≤ C)
    {A : Finset ℂ} (hA : ∀ᵐ z ∂volume.restrict U, g z ∈ A)
    (a : ℂ) {c : ℂ} {s r R : ℝ} (hs : 0 < s) (hsr : s < r) (hrR : r < R)
    (hball : closedBall c R ⊆ U) (hess : IsEssentialPhaseAt g a c)
    {x : ℂ} (hx : x ∈ ball c s) (hcone : x - c ∈ strictPhaseCone A a) :
    u x = u c + (a * (x - c)).re := by
  have hVU : ball c s ∩ (fun x => x - c) ⁻¹' strictPhaseCone A a ⊆ U :=
    inter_subset_left.trans ((ball_subset_closedBall.trans
      (closedBall_subset_closedBall (hsr.trans hrR).le)).trans hball)
  exact (hw.restrict hVU).affine_on_strict_cone hs hc
    (hu.phase_eq_ae_on_strict_cone hU hc hw hC hbound hA a hs hsr hrR hball hess) hx hcone

end ModifiedCartan
#print axioms ModifiedCartan.IsSubharmonicOn.affine_on_essential_strict_cone

