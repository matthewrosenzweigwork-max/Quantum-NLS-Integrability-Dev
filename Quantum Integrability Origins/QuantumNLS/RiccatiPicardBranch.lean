import Mathlib
import QuantumNLS.RiccatiSobolevBanach
import QuantumNLS.RiccatiPicardBall
import QuantumNLS.RiccatiPicardAnalytic
import QuantumNLS.Ext025A5Triangular

/-!
# R-3FEAD88B blocker 3, stage E3c: local analytic branch of the small Riccati solution

Applies the GP-03 constituent `QuantumNLS.Ext025A5.analytic_implicit` (analytic implicit function
theorem, stated for complete normed spaces over `𝕜` with an explicit `HasFDerivAt` of the form
`A.coprod B`) to the residual `G(p, r) = r − T(u,v; r)` at a point `(p0, r0)`, where `r0` is the
small fixed point of stage E3a.

Inputs: `residG_analyticAt`, `slice_deriv`, `norm_Nop_le` (stage E3b), `riccatiT_fixed_exists_unique`
(stage E3a). The derivative in `r` is `I + N` with `‖N‖ ≤ 1/4`, invertible by the Neumann series
`Units.oneSub`; the partial derivative in `p` is `A = (∂_G) ∘ inl`.

Main result, `riccati_local_analytic_branch`: for `p0` in the open set `{‖u‖ < β, ‖v‖ < β}` and
`16 |κ| C² β² ≤ η²`, there is `ψ` analytic at `p0` such that, eventually in `p`, `ψ p` is a fixed
point of `T(p, ·)` and the only fixed point of norm at most `4β/η`.

Standard axioms only. No sorry, admit, native_decide, or new axioms.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric

namespace QuantumNLS.RiccatiPicardBranch

open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPicardBall QuantumNLS.RiccatiPicardAnalytic

theorem riccati_local_analytic_branch {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {z : ℂ}
    (hz : 0 < z.im) (κ β : ℝ) (hβ : 0 < β) (hκ : 16 * |κ| * Cmul L a ^ 2 * β ^ 2 ≤ z.im ^ 2)
    (p0 : Ell2 × Ell2) (hp0u : ‖p0.1‖ < β) (hp0v : ‖p0.2‖ < β) :
    ∃ ψ : Ell2 × Ell2 → Ell2, AnalyticAt ℂ ψ p0 ∧
      ∀ᶠ p in 𝓝 p0, riccatiT hL ha hz κ p.1 p.2 (ψ p) = ψ p ∧
        ∀ r' : Ell2, ‖r'‖ ≤ 4 * β / z.im → riccatiT hL ha hz κ p.1 p.2 r' = r' → r' = ψ p := by
  obtain ⟨r0, hr0n, hfix0, -⟩ :=
    riccatiT_fixed_exists_unique hL ha hz κ β hβ hκ p0.1 p0.2 hp0u.le hp0v.le
  -- the residual vanishes at the base point
  have hG0 : residG hL ha hz κ ((p0, r0) : Par × Ell2) = 0 := by
    show r0 - riccatiT hL ha hz κ p0.1 p0.2 r0 = 0
    rw [hfix0, sub_self]
  have hG_an : AnalyticAt ℂ (residG hL ha hz κ) ((p0, r0) : Par × Ell2) :=
    residG_analyticAt hL ha hz κ _
  have hG_der := hG_an.differentiableAt.hasFDerivAt
  set Lm := fderiv ℂ (residG hL ha hz κ) ((p0, r0) : Par × Ell2) with hLm
  -- the r-slice derivative of the residual is I + N
  have hinr : HasFDerivAt (fun r : Ell2 => ((p0, r) : Par × Ell2))
      (ContinuousLinearMap.inr ℂ Par Ell2) r0 :=
    (hasFDerivAt_const p0 r0).prodMk (hasFDerivAt_id r0)
  have hslice := HasFDerivAt.comp r0 hG_der hinr
  have hdir := slice_deriv hL ha hz κ p0 r0
  have hEq : Lm.comp (ContinuousLinearMap.inr ℂ Par Ell2)
      = ContinuousLinearMap.id ℂ Ell2 + Nop hL ha hz κ p0.2 r0 :=
    hslice.unique hdir
  -- splitting of the full derivative into A.coprod B
  have hLdecomp : Lm = (Lm.comp (ContinuousLinearMap.inl ℂ Par Ell2)).coprod
      (ContinuousLinearMap.id ℂ Ell2 + Nop hL ha hz κ p0.2 r0) := by
    refine ContinuousLinearMap.ext fun x => ?_
    have hsplit : x = ContinuousLinearMap.inl ℂ Par Ell2 x.1
        + ContinuousLinearMap.inr ℂ Par Ell2 x.2 := by
      ext <;> simp
    have hI : Lm (ContinuousLinearMap.inr ℂ Par Ell2 x.2)
        = (ContinuousLinearMap.id ℂ Ell2 + Nop hL ha hz κ p0.2 r0) x.2 := by
      rw [← hEq]
      rfl
    rw [ContinuousLinearMap.coprod_apply]
    calc Lm x = Lm (ContinuousLinearMap.inl ℂ Par Ell2 x.1)
          + Lm (ContinuousLinearMap.inr ℂ Par Ell2 x.2) := by
          rw [← map_add, ← hsplit]
      _ = (Lm.comp (ContinuousLinearMap.inl ℂ Par Ell2)) x.1
          + (ContinuousLinearMap.id ℂ Ell2 + Nop hL ha hz κ p0.2 r0) x.2 := by
          rw [hI]
          rfl
  -- invertibility of the r-derivative I + N (Neumann series)
  have hNu : ‖-(Nop hL ha hz κ p0.2 r0)‖ < 1 :=
    id_add_Nop_isUnit hL ha hz κ β p0.2 r0 hp0v.le hr0n hκ
  let u : (Ell2 →L[ℂ] Ell2)ˣ := Units.oneSub (-(Nop hL ha hz κ p0.2 r0)) hNu
  let Be : Ell2 ≃L[ℂ] Ell2 := ContinuousLinearEquiv.ofUnit u
  have hBe : Be.toContinuousLinearMap = ContinuousLinearMap.id ℂ Ell2 + Nop hL ha hz κ p0.2 r0 := by
    have h1 : Be.toContinuousLinearMap = (u : Ell2 →L[ℂ] Ell2) :=
      ContinuousLinearMap.ext fun x => rfl
    rw [h1, Units.val_oneSub, sub_neg_eq_add, ContinuousLinearMap.one_def]
  have hd : HasFDerivAt (residG hL ha hz κ)
      ((Lm.comp (ContinuousLinearMap.inl ℂ Par Ell2)).coprod Be.toContinuousLinearMap)
      ((p0, r0) : Par × Ell2) := by
    rw [hBe, ← hLdecomp]
    exact hG_der
  -- the analytic implicit function theorem (GP-03 constituent)
  obtain ⟨ψ, hψan, hψ0, -, -, hex⟩ :=
    QuantumNLS.Ext025A5.analytic_implicit (Lm.comp (ContinuousLinearMap.inl ℂ Par Ell2)) Be
      hG_an hd
  have hψ0' : ψ p0 = r0 := hψ0
  have hex' : ∀ᶠ p in 𝓝 p0, residG hL ha hz κ (p, ψ p) = 0 := by
    filter_upwards [hex] with p hp
    rw [hp]
    exact hG0
  -- the parameter neighbourhood {‖u‖ < β, ‖v‖ < β}
  have hU : ∀ᶠ p in 𝓝 p0, ‖p.1‖ < β ∧ ‖p.2‖ < β := by
    have hopen : IsOpen {p : Ell2 × Ell2 | ‖p.1‖ < β ∧ ‖p.2‖ < β} :=
      (isOpen_lt continuous_fst.norm continuous_const).inter
        (isOpen_lt continuous_snd.norm continuous_const)
    exact hopen.mem_nhds ⟨hp0u, hp0v⟩
  have hr0lt : ‖r0‖ < 4 * β / z.im := by
    have hpos : 0 < 2 * β / z.im := div_pos (by linarith) hz
    have key : 4 * β / z.im = 2 * β / z.im + 2 * β / z.im := by ring
    linarith
  have hcont : ∀ᶠ p in 𝓝 p0, ‖ψ p‖ < 4 * β / z.im := by
    have h1 : ContinuousAt (fun p : Ell2 × Ell2 => ‖ψ p‖) p0 := hψan.continuousAt.norm
    have h2 : ContinuousAt (fun _ : Ell2 × Ell2 => 4 * β / z.im) p0 := continuousAt_const
    refine h1.eventually_lt h2 ?_
    show ‖ψ p0‖ < 4 * β / z.im
    rw [hψ0']
    exact hr0lt
  refine ⟨ψ, hψan, ?_⟩
  filter_upwards [hU, hex', hcont] with p hpU hpG hpn
  obtain ⟨hpu, hpv⟩ := hpU
  have hfixψ : riccatiT hL ha hz κ p.1 p.2 (ψ p) = ψ p := by
    have h := hpG
    simp only [residG] at h
    exact (sub_eq_zero.1 h).symm
  refine ⟨hfixψ, fun r' hr' hfr' => ?_⟩
  obtain ⟨rp, -, -, hunp⟩ :=
    riccatiT_fixed_exists_unique hL ha hz κ β hβ hκ p.1 p.2 hpu.le hpv.le
  exact (hunp r' hr' hfr').trans (hunp (ψ p) hpn.le hfixψ).symm

end QuantumNLS.RiccatiPicardBranch

#print axioms QuantumNLS.RiccatiPicardBranch.riccati_local_analytic_branch
