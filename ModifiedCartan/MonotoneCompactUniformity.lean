import ModifiedCartan.AnnularRatioLimit

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- Compact uniformity for monotone functions with a continuous pointwise limit. -/
theorem eventually_uniform_of_monotone_pointwise
    {F : ℝ → ℝ → ℝ} {g : ℝ → ℝ}
    (hmono : ∀ᶠ r in atTop, MonotoneOn (F r) (Ioi 0))
    (hg : ContinuousOn g (Ioi 0))
    (hlim : ∀ c : ℝ, 0 < c → Tendsto (fun r => F r c) atTop (𝓝 (g c)))
    {K : Set ℝ} (hK : IsCompact K) (hKpos : K ⊆ Ioi 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r in atTop, ∀ c ∈ K, |F r c - g c| < ε := by
  classical
  have hloc (x : K) : ∃ a b : ℝ, 0 < a ∧ a < x.val ∧ x.val < b ∧
      ∀ y ∈ Icc a b, g x.val - ε / 4 < g y ∧ g y < g x.val + ε / 4 := by
    have hgc : ContinuousAt g x.val := hg.continuousAt (Ioi_mem_nhds (hKpos x.property))
    have hn : ∀ᶠ y in 𝓝 x.val, 0 < y ∧
        g x.val - ε / 4 < g y ∧ g y < g x.val + ε / 4 :=
      (show ∀ᶠ y in 𝓝 x.val, 0 < y from Ioi_mem_nhds (hKpos x.property)).and
        (hgc (Ioo_mem_nhds (by linarith) (by linarith)))
    obtain ⟨a₀, b₀, hx₀, hab₀⟩ := hn.exists_Ioo_subset
    let a := (a₀ + x.val) / 2
    let b := (x.val + b₀) / 2
    have ha₀ : a₀ < a := by dsimp [a]; linarith [hx₀.1]
    have hax : a < x.val := by dsimp [a]; linarith [hx₀.1]
    have hxb : x.val < b := by dsimp [b]; linarith [hx₀.2]
    have hb₀ : b < b₀ := by dsimp [b]; linarith [hx₀.2]
    have hnear : ∀ y ∈ Icc a b, 0 < y ∧
        g x.val - ε / 4 < g y ∧ g y < g x.val + ε / 4 := by
      intro y hy
      exact hab₀ ⟨ha₀.trans_le hy.1, hy.2.trans_lt hb₀⟩
    exact ⟨a, b, (hnear a ⟨le_rfl, hax.le.trans hxb.le⟩).1, hax, hxb,
      fun y hy => (hnear y hy).2⟩
  choose a b ha hax hxb hnear using hloc
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover (fun x : K => Ioo (a x) (b x))
    (fun _ => isOpen_Ioo)
    (fun c hc => mem_iUnion.mpr ⟨⟨c, hc⟩, hax ⟨c, hc⟩, hxb ⟨c, hc⟩⟩)
  have hend : ∀ᶠ r in atTop, ∀ x ∈ S,
      g (a x) - ε / 4 < F r (a x) ∧ F r (b x) < g (b x) + ε / 4 := by
    apply (Finset.eventually_all S).mpr
    intro x hx
    exact ((tendsto_order.mp (hlim (a x) (ha x))).1 _ (by linarith)).and
      ((tendsto_order.mp (hlim (b x) ((hKpos x.property).trans (hxb x)))).2 _ (by linarith))
  filter_upwards [hmono, hend] with r hm he
  intro c hc
  obtain ⟨x, hxS, hcx⟩ := mem_iUnion₂.mp (hS hc)
  have hlow := hm (ha x) (hKpos hc) hcx.1.le
  have hupp := hm (hKpos hc) ((hKpos x.property).trans (hxb x)) hcx.2.le
  have hea := (he x hxS).1
  have heb := (he x hxS).2
  have hga := hnear x (a x) ⟨le_rfl, (hax x).le.trans (hxb x).le⟩
  have hgb := hnear x (b x) ⟨(hax x).le.trans (hxb x).le, le_rfl⟩
  have hgc := hnear x c ⟨hcx.1.le, hcx.2.le⟩
  exact abs_lt.mpr ⟨by linarith [hga.1, hgc.2], by linarith [hgb.2, hgc.1]⟩

end ModifiedCartan
#print axioms ModifiedCartan.eventually_uniform_of_monotone_pointwise
