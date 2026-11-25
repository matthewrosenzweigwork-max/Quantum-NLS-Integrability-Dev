import QuantumNLS.ResetMoserBounds
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# `thm:reset-moser` (LOCAL-017), stage 2a: the radial primitive `β`, `dβ = Ω − ω`, and `‖β_z‖ ≤ M‖z‖³`

Source: `symplectic_correction.tex`, "The periods of a radial primitive": "The radial homotopy formula gives a primitive
`α_z(h) = ∫₀¹ t Ω_{tz}(z,h) dt`, `dα = Ω`. This formula follows by differentiating pullback under `z ↦ tz` and using `dΩ = 0`
... For the constant form its primitive is `α⁰_z(h) = Im⟨z,h⟩`. Put `β = α − α⁰`. Then `dβ = Ω − ω`, `‖β_z‖ ≤ C‖z‖³`"
(eq:reset-beta-bounds, first estimate; the derivative bounds follow in the next stages from `Lval`).

* `Dl S z = Ω_z − ω` (`Δ`), `betaR S z = ∫₀¹ t Δ_{tz}(z, ·) dt` (this is `β`, and `α = β + ω(z,·)/2 = β + α⁰`);
* `Loc`: the local-bounds bundle of `Hyp.local_bounds`; `Hyp.exists_loc`;
* `betaR_hasFDerivAt`: `β` is Fréchet differentiable on `B_ρ` with `Dβ_x = ∫₀¹ Lval x t dt`,
  `Lval x t (a, h) = t Δ_{tx}(a,h) + t² DΩ_{tx}(a)(x,h)` (differentiation under the integral sign: dominated version of
  Mathlib's `hasFDerivAt_integral_of_dominated_of_fderiv_le''`, domination from the bounds `‖Δ‖ ≤ M‖z‖²`, `‖DΩ‖ ≤ M‖z‖`);
* `betaR_antisym`: **`dβ = Δ`**: `Dβ_x(a)(h) − Dβ_x(h)(a) = Δ_x(a,h)`, from `dΩ = 0` (`Hyp.Ω_closed`), alternation, and the
  fundamental theorem of calculus for `t ↦ t² Δ_{tx}(a,h)`;
* `norm_betaR_le`: `‖β_z‖ ≤ M‖z‖³`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric MeasureTheory
open scoped Interval

namespace QuantumNLS.ResetMoser

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.RealAnalyticDef

theorem omega_alt (v w : K) : omega v w = - omega w v := by
  unfold omega
  rw [← inner_conj_symm (𝕜 := ℂ) v w, Complex.conj_im]
  ring

theorem omegaF_alt (v w : K) : omegaF v w = - omegaF w v := by
  rw [omegaF_apply, omegaF_apply]; exact omega_alt v w

/-- `Δ = Ω − ω`. -/
def Dl (S : Hyp) (z : K) : Form := S.Ω z - omegaF

theorem Dl_alt (S : Hyp) (z v w : K) : Dl S z v w = - Dl S z w v := by
  simp only [Dl, ContinuousLinearMap.sub_apply]
  rw [S.Ω_alt z v w, omegaF_alt v w]; ring

theorem Dl_hasFDerivAt (S : Hyp) {z : K} (hz : z ∈ ball (0 : K) S.R) :
    HasFDerivAt (Dl S) (fderiv ℝ S.Ω z) z :=
  ((S.Ω_contDiffAt hz).differentiableAt (by norm_num)).hasFDerivAt.sub_const omegaF

theorem Dl_continuousOn (S : Hyp) : ContinuousOn (Dl S) (ball (0 : K) S.R) :=
  S.Ω_continuousOn.sub continuousOn_const

theorem fderivΩ_continuousOn (S : Hyp) : ContinuousOn (fderiv ℝ S.Ω) (ball (0 : K) S.R) := fun z hz =>
  (((S.Ω_contDiffAt hz).fderiv_right (m := 1) (by norm_num)).continuousAt).continuousWithinAt

/-- `D Ω` is alternating in its last two slots. -/
theorem fderiv_alt (S : Hyp) {z : K} (hz : z ∈ ball (0 : K) S.R) (w u v : K) :
    fderiv ℝ S.Ω z w u v = - fderiv ℝ S.Ω z w v u := by
  have hΩ : HasFDerivAt S.Ω (fderiv ℝ S.Ω z) z :=
    ((S.Ω_contDiffAt hz).differentiableAt (by norm_num)).hasFDerivAt
  let E : K → K → (Form →L[ℝ] ℝ) := fun u v =>
    (ContinuousLinearMap.apply ℝ ℝ v).comp (ContinuousLinearMap.apply ℝ Cov u)
  have h1 : ∀ u v, HasFDerivAt (fun y => S.Ω y u v) ((E u v).comp (fderiv ℝ S.Ω z)) z :=
    fun u v => (E u v).hasFDerivAt.comp z hΩ
  have h2 : HasFDerivAt (fun y => -(S.Ω y v u)) (-((E v u).comp (fderiv ℝ S.Ω z))) z := (h1 v u).neg
  have hfun : (fun y => S.Ω y u v) = fun y => -(S.Ω y v u) := funext fun y => S.Ω_alt y u v
  rw [← hfun] at h2
  have h3 := (h1 u v).unique h2
  have h4 := congrArg (fun L => L w) h3
  simpa [E] using h4

/-- The local-bounds bundle. -/
structure Loc (S : Hyp) (ρ M : ℝ) : Prop where
  ρpos : 0 < ρ
  ρR : ρ ≤ S.R
  M0 : 0 ≤ M
  b2 : ∀ z ∈ ball (0 : K) ρ, ‖S.Ω z - omegaF‖ ≤ M * ‖z‖ ^ 2
  b1 : ∀ z ∈ ball (0 : K) ρ, ‖fderiv ℝ S.Ω z‖ ≤ M * ‖z‖
  b0 : ∀ z ∈ ball (0 : K) ρ, ‖fderiv ℝ (fderiv ℝ S.Ω) z‖ ≤ M

theorem Hyp.exists_loc (S : Hyp) : ∃ ρ M : ℝ, Loc S ρ M := by
  obtain ⟨ρ, M, h1, h2, h3, h4⟩ := S.local_bounds
  exact ⟨ρ, M, ⟨h1, h2, h3, fun z hz => (h4 z hz).1, fun z hz => (h4 z hz).2.1,
    fun z hz => (h4 z hz).2.2⟩⟩

theorem ball_mono_R {S : Hyp} {ρ M : ℝ} (h : Loc S ρ M) : ball (0 : K) ρ ⊆ ball (0 : K) S.R :=
  ball_subset_ball h.ρR

theorem scale_mem' {ρ : ℝ} {x : K} (hx : x ∈ ball (0 : K) ρ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t • x ∈ ball (0 : K) ρ := by
  rw [mem_ball_zero_iff] at hx ⊢
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (norm_nonneg x) ht.2).trans_lt hx

theorem norm_scale_le {x : K} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖t • x‖ ≤ ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact mul_le_of_le_one_left (norm_nonneg x) ht.2

/-- `β_z = ∫₀¹ t Δ_{tz}(z, ·) dt`. -/
def betaR (S : Hyp) (z : K) : Cov := ∫ t in (0 : ℝ)..1, t • (Dl S (t • z) z)

/-- The integrand of `Dβ`: `a ↦ (h ↦ t Δ_{tx}(a,h) + t² DΩ_{tx}(a)(x,h))`. -/
def Lval (S : Hyp) (x : K) (t : ℝ) : K →L[ℝ] Cov :=
  t • Dl S (t • x) + (t ^ 2) • ((ContinuousLinearMap.apply ℝ Cov x).comp (fderiv ℝ S.Ω (t • x)))

theorem Lval_apply (S : Hyp) (x : K) (t : ℝ) (a h : K) :
    Lval S x t a h = t * Dl S (t • x) a h + t ^ 2 * fderiv ℝ S.Ω (t • x) a x h := by
  simp [Lval]

theorem norm_applycomp_le (y : K) (B : K →L[ℝ] Form) :
    ‖(ContinuousLinearMap.apply ℝ Cov y).comp B‖ ≤ ‖B‖ * ‖y‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun a => ?_
  change ‖(B a) y‖ ≤ ‖B‖ * ‖y‖ * ‖a‖
  calc ‖(B a) y‖ ≤ ‖B a‖ * ‖y‖ := (B a).le_opNorm y
    _ ≤ (‖B‖ * ‖a‖) * ‖y‖ := mul_le_mul_of_nonneg_right (B.le_opNorm a) (norm_nonneg _)
    _ = ‖B‖ * ‖y‖ * ‖a‖ := by ring

theorem radial_cont (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {y : K} (hy : y ∈ ball (0 : K) ρ) :
    ContinuousOn (fun t : ℝ => t • (Dl S (t • y) y)) (Icc (0 : ℝ) 1) := by
  have hs : ContinuousOn (fun t : ℝ => t • y) (Icc (0 : ℝ) 1) := (continuous_id.smul continuous_const).continuousOn
  have hd : ContinuousOn (fun t : ℝ => Dl S (t • y)) (Icc (0 : ℝ) 1) :=
    (Dl_continuousOn S).comp hs (fun t ht => ball_mono_R hL (scale_mem' hy ht))
  exact continuousOn_id.smul (hd.clm_apply continuousOn_const)

theorem Lval_cont (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {x : K} (hx : x ∈ ball (0 : K) ρ) :
    ContinuousOn (fun t : ℝ => Lval S x t) (Icc (0 : ℝ) 1) := by
  have hs : ContinuousOn (fun t : ℝ => t • x) (Icc (0 : ℝ) 1) := (continuous_id.smul continuous_const).continuousOn
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, t • x ∈ ball (0 : K) S.R := fun t ht => ball_mono_R hL (scale_mem' hx ht)
  have hd : ContinuousOn (fun t : ℝ => Dl S (t • x)) (Icc (0 : ℝ) 1) := (Dl_continuousOn S).comp hs hmem
  have hf : ContinuousOn (fun t : ℝ => fderiv ℝ S.Ω (t • x)) (Icc (0 : ℝ) 1) :=
    (fderivΩ_continuousOn S).comp hs hmem
  have hc : Continuous (fun B : K →L[ℝ] Form => (ContinuousLinearMap.apply ℝ Cov x).comp B) :=
    ((ContinuousLinearMap.compL ℝ K Form Cov) (ContinuousLinearMap.apply ℝ Cov x)).continuous
  have hf2 : ContinuousOn (fun t : ℝ => (ContinuousLinearMap.apply ℝ Cov x).comp (fderiv ℝ S.Ω (t • x)))
      (Icc (0 : ℝ) 1) := hc.comp_continuousOn hf
  exact (continuousOn_id.smul hd).add ((continuousOn_id.pow 2).smul hf2)

theorem norm_Lval_le (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {x : K} (hx : x ∈ ball (0 : K) ρ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : ‖Lval S x t‖ ≤ 2 * M * ρ ^ 2 := by
  have hxρ : ‖x‖ < ρ := mem_ball_zero_iff.1 hx
  have htx : t • x ∈ ball (0 : K) ρ := scale_mem' hx ht
  have hn : ‖t • x‖ ≤ ‖x‖ := norm_scale_le ht
  have hn0 : 0 ≤ ‖t • x‖ := norm_nonneg _
  have e1 : ‖Dl S (t • x)‖ ≤ M * ρ ^ 2 := by
    refine (hL.b2 _ htx).trans (mul_le_mul_of_nonneg_left ?_ hL.M0)
    nlinarith
  have e2 : ‖fderiv ℝ S.Ω (t • x)‖ ≤ M * ρ := by
    refine (hL.b1 _ htx).trans (mul_le_mul_of_nonneg_left ?_ hL.M0)
    linarith
  have h0 : 0 ≤ t := ht.1
  have h1 : t ≤ 1 := ht.2
  have e3 : ‖(ContinuousLinearMap.apply ℝ Cov x).comp (fderiv ℝ S.Ω (t • x))‖ ≤ M * ρ ^ 2 := by
    refine (norm_applycomp_le x _).trans ?_
    calc ‖fderiv ℝ S.Ω (t • x)‖ * ‖x‖ ≤ (M * ρ) * ρ :=
          mul_le_mul e2 hxρ.le (norm_nonneg _) (by have := hL.M0; have := hL.ρpos; positivity)
      _ = M * ρ ^ 2 := by ring
  have hMρ : 0 ≤ M * ρ ^ 2 := by have := hL.M0; positivity
  unfold Lval
  calc ‖t • Dl S (t • x) + (t ^ 2) • (ContinuousLinearMap.apply ℝ Cov x).comp (fderiv ℝ S.Ω (t • x))‖
      ≤ ‖t • Dl S (t • x)‖ + ‖(t ^ 2) • (ContinuousLinearMap.apply ℝ Cov x).comp (fderiv ℝ S.Ω (t • x))‖ :=
        norm_add_le _ _
    _ ≤ M * ρ ^ 2 + M * ρ ^ 2 := by
        refine add_le_add ?_ ?_
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
          calc t * ‖Dl S (t • x)‖ ≤ 1 * (M * ρ ^ 2) := mul_le_mul h1 e1 (norm_nonneg _) zero_le_one
            _ = M * ρ ^ 2 := one_mul _
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          calc t ^ 2 * ‖(ContinuousLinearMap.apply ℝ Cov x).comp (fderiv ℝ S.Ω (t • x))‖
              ≤ 1 * (M * ρ ^ 2) := mul_le_mul (by nlinarith) e3 (norm_nonneg _) zero_le_one
            _ = M * ρ ^ 2 := one_mul _
    _ = 2 * M * ρ ^ 2 := by ring

theorem hasFDerivAt_integrand (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {y : K} (hy : y ∈ ball (0 : K) ρ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    HasFDerivAt (fun y => t • (Dl S (t • y) y)) (Lval S y t) y := by
  have hty : t • y ∈ ball (0 : K) S.R := ball_mono_R hL (scale_mem' hy ht)
  have hc : HasFDerivAt (fun y => Dl S (t • y)) ((fderiv ℝ S.Ω (t • y)).comp (t • ContinuousLinearMap.id ℝ K)) y :=
    (Dl_hasFDerivAt S hty).comp y ((hasFDerivAt_id y).const_smul t)
  have hcu := hc.clm_apply (hasFDerivAt_id y)
  have h2 := hcu.const_smul t
  refine h2.congr_fderiv ?_
  ext a h
  simp [Lval_apply]
  ring

theorem betaR_hasFDerivAt (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {x₀ : K} (hx₀ : x₀ ∈ ball (0 : K) ρ) :
    HasFDerivAt (betaR S) (∫ t in (0 : ℝ)..1, Lval S x₀ t) x₀ := by
  have hmeas : ∀ y ∈ ball (0 : K) ρ,
      AEStronglyMeasurable (fun t : ℝ => t • (Dl S (t • y) y)) (volume.restrict (Ι (0 : ℝ) 1)) := by
    intro y hy
    rw [uIoc_of_le zero_le_one]
    exact (radial_cont S hL hy).aestronglyMeasurable_of_subset_isCompact isCompact_Icc
      measurableSet_Ioc Ioc_subset_Icc_self
  unfold betaR
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le'' (μ := volume) (s := ball (0 : K) ρ)
    (F := fun y t => t • (Dl S (t • y) y)) (F' := fun y t => Lval S y t) (bound := fun _ => 2 * M * ρ ^ 2)
    (isOpen_ball.mem_nhds hx₀)
  · filter_upwards [isOpen_ball.mem_nhds hx₀] with y hy using hmeas y hy
  · apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one] using radial_cont S hL hx₀
  · rw [uIoc_of_le zero_le_one]
    exact (Lval_cont S hL hx₀).aestronglyMeasurable_of_subset_isCompact isCompact_Icc
      measurableSet_Ioc Ioc_subset_Icc_self
  · rw [uIoc_of_le zero_le_one]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht y hy
    exact norm_Lval_le S hL hy ⟨ht.1.le, ht.2⟩
  · exact intervalIntegrable_const
  · rw [uIoc_of_le zero_le_one]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht y hy
    exact hasFDerivAt_integrand S hL hy ⟨ht.1.le, ht.2⟩

theorem norm_betaR_le (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {z : K} (hz : z ∈ ball (0 : K) ρ) :
    ‖betaR S z‖ ≤ M * ‖z‖ ^ 3 := by
  unfold betaR
  have hz' : ‖z‖ < ρ := mem_ball_zero_iff.1 hz
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun t : ℝ => t • (Dl S (t • z) z)) (C := M * ‖z‖ ^ 3) (fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
      have htz : t • z ∈ ball (0 : K) ρ := scale_mem' hz ht'
      have e1 : ‖Dl S (t • z)‖ ≤ M * ‖z‖ ^ 2 := by
        refine (hL.b2 _ htz).trans (mul_le_mul_of_nonneg_left ?_ hL.M0)
        have := norm_scale_le (x := z) ht'
        nlinarith [norm_nonneg (t • z)]
      calc ‖t • (Dl S (t • z) z)‖ = t * ‖Dl S (t • z) z‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1.le]
        _ ≤ 1 * (‖Dl S (t • z)‖ * ‖z‖) :=
            mul_le_mul ht.2 ((Dl S (t • z)).le_opNorm z) (norm_nonneg _) zero_le_one
        _ ≤ 1 * ((M * ‖z‖ ^ 2) * ‖z‖) := by
            gcongr
        _ = M * ‖z‖ ^ 3 := by ring)
  simpa using h

theorem betaR_antisym (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {x : K} (hx : x ∈ ball (0 : K) ρ) (a h : K) :
    (∫ t in (0 : ℝ)..1, Lval S x t) a h - (∫ t in (0 : ℝ)..1, Lval S x t) h a = Dl S x a h := by
  have hLi : IntervalIntegrable (fun t : ℝ => Lval S x t) volume 0 1 :=
    ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le zero_le_one] using Lval_cont S hL hx)
  let E : K → K → ((K →L[ℝ] Cov) →L[ℝ] ℝ) := fun a h =>
    (ContinuousLinearMap.apply ℝ ℝ h).comp (ContinuousLinearMap.apply ℝ Cov a)
  have hev : ∀ a h, (∫ t in (0 : ℝ)..1, Lval S x t) a h = ∫ t in (0 : ℝ)..1, Lval S x t a h := by
    intro a h
    have := ContinuousLinearMap.intervalIntegral_comp_comm (E a h) hLi
    simpa [E] using this.symm
  have hc : ∀ a h, ContinuousOn (fun t : ℝ => Lval S x t a h) (Icc (0 : ℝ) 1) := fun a h =>
    ((Lval_cont S hL hx).clm_apply continuousOn_const).clm_apply continuousOn_const
  have hii : ∀ a h, IntervalIntegrable (fun t : ℝ => Lval S x t a h) volume 0 1 := fun a h =>
    ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le zero_le_one] using hc a h)
  rw [hev, hev, ← intervalIntegral.integral_sub (hii a h) (hii h a)]
  -- FTC for g(t) = t² Δ_{tx}(a,h)
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => t ^ 2 * Dl S (t • x) a h)
        (Lval S x t a h - Lval S x t h a) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hty : t • x ∈ ball (0 : K) S.R := ball_mono_R hL (scale_mem' hx ht)
    have hline : HasDerivAt (fun t : ℝ => t • x) x t := by
      simpa using (hasDerivAt_id t).smul_const x
    have hD := (Dl_hasFDerivAt S hty).comp_hasDerivAt t hline
    let Eah : Form →L[ℝ] ℝ := (ContinuousLinearMap.apply ℝ ℝ h).comp (ContinuousLinearMap.apply ℝ Cov a)
    have h3 : HasDerivAt (fun t : ℝ => Dl S (t • x) a h) (fderiv ℝ S.Ω (t • x) x a h) t :=
      Eah.hasFDerivAt.comp_hasDerivAt t hD
    have h1' : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h4 : HasDerivAt (fun t : ℝ => t ^ 2 * Dl S (t • x) a h)
        (2 * t * Dl S (t • x) a h + t ^ 2 * fderiv ℝ S.Ω (t • x) x a h) t := h1'.mul h3
    refine h4.congr_deriv ?_
    -- algebra with closedness and alternation
    have hcl := S.Ω_closed (t • x) hty a x h
    have hf1 := fderiv_alt S hty x h a
    have hf2 := fderiv_alt S hty h a x
    have hd1 := Dl_alt S (t • x) a h
    rw [Lval_apply, Lval_apply]
    have hd2 : Dl S (t • x) h a = - Dl S (t • x) a h := by rw [hd1]; ring
    rw [hd2]
    have : fderiv ℝ S.Ω (t • x) h x a = - fderiv ℝ S.Ω (t • x) h a x := by
      rw [hf2]; ring
    rw [this]
    have hf1' : fderiv ℝ S.Ω (t • x) x h a = - fderiv ℝ S.Ω (t • x) x a h := hf1
    rw [hf1'] at hcl
    linear_combination (-(t ^ 2)) * hcl
  have hint : IntervalIntegrable (fun t : ℝ => Lval S x t a h - Lval S x t h a) volume 0 1 :=
    (hii a h).sub (hii h a)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.fderiv_alt
#print axioms QuantumNLS.ResetMoser.Hyp.exists_loc
#print axioms QuantumNLS.ResetMoser.betaR_hasFDerivAt
#print axioms QuantumNLS.ResetMoser.norm_betaR_le
#print axioms QuantumNLS.ResetMoser.betaR_antisym
