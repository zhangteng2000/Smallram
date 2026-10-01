import ModifiedCartan.FiniteCauchyDerivatives
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open scoped Topology ContDiff
open Filter Set

set_option autoImplicit false

namespace ModifiedCartan

/-! The exact higher derivative partition expansion in Step 3 of
`lem:logderivlimit`. A local logarithm and the proved Faà di Bruno formula
replace the informal differential-polynomial induction. -/

noncomputable def logDerivativePartitionPolynomial (k : ℕ) (X : ℕ → ℂ) : ℂ :=
  ∑ c : OrderedFinpartition k, ∏ i, X (c.partSize i - 1)

theorem iteratedDeriv_div_eq_partition_of_slitPlane {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hslit : f z ∈ Complex.slitPlane) (k : ℕ) :
    iteratedDeriv k f z / f z =
      logDerivativePartitionPolynomial k (fun j => iteratedDeriv j (logDeriv f) z) := by
  have hf0 := Complex.slitPlane_ne_zero hslit
  let L (w : ℂ) := Complex.log (f w)
  have hL : AnalyticAt ℂ L z := hf.clog hslit
  have hnear : ∀ᶠ w in 𝓝 z, f w ∈ Complex.slitPlane :=
    hf.continuousAt.eventually (Complex.isOpen_slitPlane.mem_nhds hslit)
  have hlogD : deriv L =ᶠ[𝓝 z] logDeriv f := by
    filter_upwards [hf.eventually_analyticAt, hnear] with w hw hws
    simpa only [logDeriv_apply, L] using (hw.differentiableAt.hasDerivAt.clog hws).deriv
  have hexp : f =ᶠ[𝓝 z] Complex.exp ∘ L := by
    filter_upwards [hnear] with w hw
    exact (Complex.exp_log (Complex.slitPlane_ne_zero hw)).symm
  have hpart (c : OrderedFinpartition k) (i : Fin c.length) :
      iteratedDeriv (c.partSize i) L z = iteratedDeriv (c.partSize i - 1) (logDeriv f) z := by
    calc
      _ = iteratedDeriv ((c.partSize i - 1) + 1) L z := by rw [Nat.sub_add_cancel (c.partSize_pos i)]
      _ = iteratedDeriv (c.partSize i - 1) (deriv L) z := by rw [iteratedDeriv_succ']
      _ = _ := (hlogD.iteratedDeriv _).eq_of_nhds
  have hFaa := iteratedDeriv_comp_eq_sum_orderedFinpartition (n := k) (i := k)
    Complex.contDiff_exp.contDiffAt hL.contDiffAt le_rfl
  have he (m : ℕ) : iteratedDeriv m Complex.exp = Complex.exp := by
    rw [iteratedDeriv_eq_iterate, Complex.iter_deriv_exp]
  have hmain : iteratedDeriv k f z = f z *
      logDerivativePartitionPolynomial k (fun j => iteratedDeriv j (logDeriv f) z) := by
    rw [(hexp.iteratedDeriv k).eq_of_nhds, hFaa]
    simp only [he, L, Complex.exp_log hf0, logDerivativePartitionPolynomial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    exact hpart c i
  apply (div_eq_iff hf0).mpr
  rw [hmain]
  ring

theorem iteratedDeriv_div_eq_partition {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hf0 : f z ≠ 0) (k : ℕ) :
    iteratedDeriv k f z / f z =
      logDerivativePartitionPolynomial k (fun j => iteratedDeriv j (logDeriv f) z) := by
  let a : ℂ := (f z)⁻¹
  have ha : a ≠ 0 := inv_ne_zero hf0
  have hscaled : AnalyticAt ℂ (fun w => a * f w) z := analyticAt_const.mul hf
  have hslit : a * f z ∈ Complex.slitPlane := by
    simpa only [a, inv_mul_cancel₀ hf0] using Complex.one_mem_slitPlane
  have h := iteratedDeriv_div_eq_partition_of_slitPlane hscaled hslit k
  have hlog : logDeriv (fun w => a * f w) = logDeriv f :=
    funext (fun w => logDeriv_const_mul w a ha)
  rw [hlog, iteratedDeriv_const_mul_field, mul_div_mul_left _ _ ha] at h
  exact h

theorem partitionPolynomial_constant_jet (k : ℕ) (b : ℂ) :
    logDerivativePartitionPolynomial k (fun j => if j = 0 then b else 0) = b ^ k := by
  have hf : AnalyticAt ℂ (fun z : ℂ => Complex.exp (b * z)) 0 := by fun_prop
  have hlog : logDeriv (fun z : ℂ => Complex.exp (b * z)) = fun _ => b := by
    funext z
    rw [logDeriv_apply]
    have hd : HasDerivAt (fun w : ℂ => Complex.exp (b * w)) (Complex.exp (b * z) * b) z := by
      simpa only [id_eq, mul_one] using! ((hasDerivAt_id z).const_mul b).cexp
    rw [hd.deriv]
    field_simp [Complex.exp_ne_zero]
  have h := iteratedDeriv_div_eq_partition hf (by simp) k
  rw [hlog] at h
  simpa only [iteratedDeriv_cexp_const_mul, mul_zero, Complex.exp_zero, mul_one, div_one,
    iteratedDeriv_const] using h.symm

theorem partition_product_powers (k : ℕ) (c : OrderedFinpartition k) (s : ℂ) :
    (∏ i, s ^ c.partSize i) = s ^ k := by
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    c.prod_sigma_eq_prod (fun _ => s)

theorem partitionPolynomial_div_pow (k : ℕ) (X : ℕ → ℂ) (s : ℂ) :
    logDerivativePartitionPolynomial k X / s ^ k =
      logDerivativePartitionPolynomial k (fun j => X j / s ^ (j + 1)) := by
  classical
  unfold logDerivativePartitionPolynomial
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.prod_div_distrib]
  congr 1
  have hp (i : Fin c.length) : c.partSize i - 1 + 1 = c.partSize i :=
    Nat.sub_add_cancel (c.partSize_pos i)
  simp_rw [hp]
  exact (partition_product_powers k c s).symm

theorem normalized_iteratedDeriv_eq_partition {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hf0 : f z ≠ 0) (k : ℕ) (s : ℂ) :
    iteratedDeriv k f z / (s ^ k * f z) =
      logDerivativePartitionPolynomial k (fun j => iteratedDeriv j (logDeriv f) z / s ^ (j + 1)) := by
  rw [← partitionPolynomial_div_pow, ← iteratedDeriv_div_eq_partition hf hf0 k]
  simp only [div_div, mul_comm]


end ModifiedCartan

