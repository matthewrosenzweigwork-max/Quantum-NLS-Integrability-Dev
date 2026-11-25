import QuantumNLS.ResetMoserVar

/-!
# `thm:reset-moser` (LOCAL-017), item 6: `d/dt S_t^* Ω^t = 0`, hence `S^* Ω = ω`

Source: `symplectic_correction.tex`, end of the proof: "Finally, using the closedness of `Ω^t` and `ι_{Y_t}Ω^t = −β⁰`, the full differential-form calculation gives
`d/dt S_t^*Ω^t = S_t^*(Ω − ω + d(ι_{Y_t}Ω^t)) = S_t^*(dβ⁰ − dβ⁰) = 0`.  This identity is evaluated on arbitrary pairs of Hilbert tangent vectors; bounded
differentiability justifies each operation.  Thus `S = S_1` has `S^*Ω = ω`."

Evaluated on `(h, k)`: `g(t) = Ω^t_{S_t z}(DS_t(z)h, DS_t(z)k)`, `Ω^t = ω + t(Ω − ω)` (with the clamped time `sig t`, equal to `t` near `[0,1]`).
* `K1`: the derivative of `ι_{Y_t}Ω^t = −β⁰` in `z` (product rule): `t DΩ_z(a)(Y, v) + Ω^t(DY a, v) = −Dβ⁰_z(a)(v)`;
* `pullback_deriv`: `g'(t) = (sig' − 1)(Ω − ω)(a,b) + t(DΩ(Y)(a,b) + DΩ(a)(b,Y) + DΩ(b)(Y,a)) = 0`, using `dβ⁰ = Ω − ω` (`β0_d`), alternation, and closedness `Ω_closed`;
* `pullback`: `Ω_{S z}(DS z h, DS z k) = ω(h, k)` for `‖z‖ < R0/4`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal NNReal
open Filter Set Metric

namespace QuantumNLS.ResetMoser

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.ResetMoserClamp

/-- `Ω^σ_w = ω + σ(Ω_w − ω)`. -/
def Om (S : Hyp) (σ : ℝ) (w : K) : Form := omegaF + Dt S σ w

theorem Om_apply (S : Hyp) (σ : ℝ) (w u v : K) :
    Om S σ w u v = omegaF u v + σ * (S.Ω w - omegaF) u v := by
  simp [Om, Dt]

theorem Om_alt (S : Hyp) (σ : ℝ) (w u v : K) : Om S σ w u v = - Om S σ w v u := by
  have h := Dl_alt S w u v
  unfold Dl at h
  rw [Om_apply, Om_apply, omegaF_alt u v, h]
  ring

namespace MoserData

variable {S : Hyp} (MD : MoserData S)

theorem Om_iota {σ : ℝ} (hσ : |σ| ≤ 2) {w : K} (hw : w ∈ ball (0 : K) MD.R0) (v : K) :
    Om S σ w (MD.Yf σ w) v = - MD.β0 w v := by
  have := iota_Ycov (MD.norm_Dt_lt hσ hw) (MD.β0 w) v
  rw [Om_apply, omegaF_apply]
  simpa [Dt, Yf] using this

/-- The derivative of `ι_{Y}Ω^σ = −β⁰` in the base point. -/
theorem K1 {σ : ℝ} (hσ : |σ| ≤ 2) {W : K} (hW : W ∈ ball (0 : K) MD.R0) {A : K →L[ℝ] K}
    (hA : HasFDerivAt (MD.Yf σ) A W) (a v : K) :
    σ * fderiv ℝ S.Ω W a (MD.Yf σ W) v + Om S σ W (A a) v = - fderiv ℝ MD.β0 W a v := by
  have hΩd : HasFDerivAt S.Ω (fderiv ℝ S.Ω W) W :=
    ((S.Ω_contDiffAt (MD.ball_sub hW)).differentiableAt (by norm_num)).hasFDerivAt
  have hOm : HasFDerivAt (fun w' => Om S σ w') (σ • fderiv ℝ S.Ω W) W := by
    have : (fun w' => Om S σ w') = fun w' => omegaF + σ • (S.Ω w' - omegaF) := rfl
    rw [this]
    exact ((hΩd.sub_const omegaF).const_smul σ).const_add omegaF
  have h1 := hOm.clm_apply hA
  have h2 := h1.clm_apply (hasFDerivAt_const v W)
  have hβ0d : HasFDerivAt MD.β0 (fderiv ℝ MD.β0 W) W := (MD.β0_an W hW).differentiableAt.hasFDerivAt
  have hβ : HasFDerivAt (fun w' => - (MD.β0 w') v)
      (-((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ MD.β0 W))) W :=
    ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp W hβ0d).neg
  have heq : (fun w' => (Om S σ w' (MD.Yf σ w')) v) =ᶠ[𝓝 W] (fun w' => - (MD.β0 w') v) := by
    filter_upwards [isOpen_ball.mem_nhds hW] with w' hw'
    exact MD.Om_iota hσ hw' v
  have h3 := hβ.congr_of_eventuallyEq heq
  have h4 := congrArg (fun T => T a) (h2.unique h3)
  simp at h4
  linarith [h4]

theorem hasFDerivAt_Yf_Aop {z : K} (hz : ‖z‖ < MD.R0 / 4) (t : ℝ) :
    HasFDerivAt (MD.Yf (sig t)) (Lam (fderiv ℝ MD.Fc (MD.Fl t (z, 0)))) (MD.Sfl t z) := by
  obtain ⟨κ, _, h⟩ := MD.exists_kappa
  have hq : ‖(MD.Sfl t z, t).1‖ < MD.R0 / 4 := by
    simp only; rw [MD.norm_Sfl]; exact hz
  obtain ⟨L, hL, hLf, _⟩ := h (MD.Sfl t z, t) hq
  have h1 : HasFDerivAt (fun w : K => ((w, t) : K × ℝ)) (ContinuousLinearMap.inl ℝ K ℝ) (MD.Sfl t z) :=
    hasFDerivAt_prodMk_left (MD.Sfl t z) t
  have h2 := hL.comp (MD.Sfl t z) h1
  have e : Lam (fderiv ℝ MD.Fc (MD.Fl t (z, 0))) = L.comp (ContinuousLinearMap.inl ℝ K ℝ) := by
    rw [MD.Fl_eq, hLf]
    ext h
    simp [Lam_apply]
  rw [e]
  exact h2

/-- `d/dt` of `g(t) = Ω^{sig t}_{S_t z}(DS_t(z) h, DS_t(z) k)` vanishes near `[0,1]`. -/
theorem pullback_deriv {z : K} (hz : ‖z‖ < MD.R0 / 4) (h k : K) {t : ℝ} (ht : t ∈ Ioo (-1 / 4 : ℝ) (5 / 4)) :
    HasDerivAt (fun s => Om S (sig s) (MD.Sfl s z) (fderiv ℝ (MD.Sfl s) z h) (fderiv ℝ (MD.Sfl s) z k)) 0 t := by
  have hW : MD.Sfl t z ∈ ball (0 : K) MD.R0 := by
    rw [mem_ball_zero_iff, MD.norm_Sfl]; have := MD.R0_pos; linarith
  have hσ : |sig t| ≤ 2 := by have := abs_sig_le t; linarith
  have hΩd : HasFDerivAt S.Ω (fderiv ℝ S.Ω (MD.Sfl t z)) (MD.Sfl t z) :=
    ((S.Ω_contDiffAt (MD.ball_sub hW)).differentiableAt (by norm_num)).hasFDerivAt
  have hw := MD.Sfl_deriv hz.le t
  have hΩw := hΩd.comp_hasDerivAt t hw
  have hsg : HasDerivAt sig (deriv sig t) t := (sig_contDiff_one.differentiable one_ne_zero t).hasDerivAt
  have hOm : HasDerivAt (fun s => Om S (sig s) (MD.Sfl s z))
      (sig t • fderiv ℝ S.Ω (MD.Sfl t z) (MD.Yf (sig t) (MD.Sfl t z)) +
        deriv sig t • (S.Ω (MD.Sfl t z) - omegaF)) t := by
    have : (fun s => Om S (sig s) (MD.Sfl s z)) = fun s => omegaF + (sig s) • (S.Ω (MD.Sfl s z) - omegaF) := rfl
    rw [this]
    exact (hsg.smul (hΩw.sub_const omegaF)).const_add omegaF
  have haA : ∀ v : K, HasDerivAt (fun s => fderiv ℝ (MD.Sfl s) z v)
      (Lam (fderiv ℝ MD.Fc (MD.Fl t (z, 0))) (fderiv ℝ (MD.Sfl t) z v)) t := by
    intro v
    have := (MD.DS_var z t).clm_apply (hasDerivAt_const t v)
    refine this.congr_deriv ?_
    simp
  have hg1 := hOm.clm_apply (haA h)
  have hg2 := hg1.clm_apply (haA k)
  have hA := MD.hasFDerivAt_Yf_Aop hz t
  set W := MD.Sfl t z with hWdef
  set Y := MD.Yf (sig t) W with hYdef
  set A := Lam (fderiv ℝ MD.Fc (MD.Fl t (z, 0))) with hAdef
  set a := fderiv ℝ (MD.Sfl t) z h with hadef
  set b := fderiv ℝ (MD.Sfl t) z k with hbdef
  have hdsig : deriv sig t = 1 := sig_deriv_one ht
  refine hg2.congr_deriv ?_
  have K1a := MD.K1 hσ hW hA a b
  have K1b := MD.K1 hσ hW hA b a
  have halt : Om S (sig t) W (a) (A b) = - Om S (sig t) W (A b) a := Om_alt S _ _ _ _
  have hd1 := MD.hL
  have hdβ := MD.β0_d W hW a b
  have hcl := S.Ω_closed W (MD.ball_sub hW) Y a b
  have halt2 := fderiv_alt S (MD.ball_sub hW) a Y b
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    smul_eq_mul, hdsig]
  rw [halt]
  have hY : (sig t) * (fderiv ℝ S.Ω W Y a b + fderiv ℝ S.Ω W a b Y + fderiv ℝ S.Ω W b Y a) = 0 := by
    rw [hcl]; ring
  have hdβ' : fderiv ℝ MD.β0 W a b - fderiv ℝ MD.β0 W b a = (S.Ω W - omegaF) a b := hdβ
  simp only [ContinuousLinearMap.sub_apply] at hdβ'
  have hY2 : (sig t) * fderiv ℝ S.Ω W a Y b = -((sig t) * fderiv ℝ S.Ω W a b Y) := by rw [halt2]; ring
  linarith [K1a, K1b, hY2, hY, hdβ']

/-- **`S^*Ω = ω`** (`S = S_1`), for `‖z‖ < R0/4` and arbitrary tangent vectors `h, k`. -/
theorem pullback {z : K} (hz : ‖z‖ < MD.R0 / 4) (h k : K) :
    S.Ω (MD.Sfl 1 z) (fderiv ℝ (MD.Sfl 1) z h) (fderiv ℝ (MD.Sfl 1) z k) = omegaF h k := by
  have hc := (isOpen_Ioo (a := (-1 / 4 : ℝ)) (b := 5 / 4)).is_const_of_deriv_eq_zero
    (f := fun s => Om S (sig s) (MD.Sfl s z) (fderiv ℝ (MD.Sfl s) z h) (fderiv ℝ (MD.Sfl s) z k))
    isPreconnected_Ioo
    (fun t ht => (MD.pullback_deriv hz h k ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (MD.pullback_deriv hz h k ht).deriv)
    (x := 1) (y := 0) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
  have e1 : sig 1 = 1 := sig_eq ⟨by norm_num, by norm_num⟩
  have e0 : sig 0 = 0 := sig_eq ⟨by norm_num, by norm_num⟩
  have hS0 : MD.Sfl 0 = id := funext MD.Sfl_zero
  simp only [e1, e0, hS0, fderiv_id] at hc
  rw [Om_apply, Om_apply] at hc
  simp only [id, ContinuousLinearMap.id_apply, zero_mul, add_zero, one_mul] at hc
  simp only [ContinuousLinearMap.sub_apply] at hc
  linarith [hc]

end MoserData

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.MoserData.K1
#print axioms QuantumNLS.ResetMoser.MoserData.pullback_deriv
#print axioms QuantumNLS.ResetMoser.MoserData.pullback
