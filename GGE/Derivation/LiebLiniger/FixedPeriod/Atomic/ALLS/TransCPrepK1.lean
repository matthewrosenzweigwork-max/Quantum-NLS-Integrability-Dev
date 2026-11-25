import LiebLiniger.FixedPeriod.Atomic.ALLS.TransCPrepK0
import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB17Analytic
import LiebLiniger.FixedPeriod.Atomic.ALLS.TransCGenK1

/-! # Trunk C PREPARATORY lemmas, package K1 (concrete zero-face division; NOT approved/admitted/rooted)

Author: Claude Opus 5.5 (preparatory author P1, trunk C).  Not self-reviewed, not accepted.
Namespace `NlsGge.ALLS.TransCPrep`; every declaration carries the non-approved prefix `prep_`.
Imports the genuine admitted Track B module `PdeB17Analytic` (`l2Flow_contDiff`), Track A
(`actual_birkhoff_bindings`, via K0) and P2's K0 (`prep_action_invariant`, `prep_continuous_coord`).

Notation: `Φ = physicalBirkhoff`, `Ψ = physicalInverseBirkhoff`, `ℓ² = Lib.L2Z`,
`g_t(x) = Φ_n(l2Flow t (Ψ x))`, `e_n = prep_basis n = lp.single 2 n 1`.

Route (coordinator K1): the time-`t` flow derivative is the evaluation at `t` of the derivative of
the `C¹` map of `l2Flow_contDiff T` (`prep_flowSection_deriv`, K1a; no `C(K)`-valued composition);
chain rule pointwise in `t`; joint continuity of `(t, y) ↦ Dg_t(y)[e_n]`; then the integral quotient
`A_n(t,x) = ∫₀¹ Dg_t(x − x_n e_n + s‖x_n‖ e_n)[e_n] ds` (`prep_zeroFace_integral`, K1b).
ZERO-FACE VANISHING: `g_t(x − x_n e_n) = 0` is obtained from P2's K0 `prep_action_invariant`
(the `n`-th Birkhoff coordinate of `Ψ(x − x_n e_n)` is `0`, hence so is that of the flowed datum).
No phase-equivariance (M1) is used.

Binders and conclusions (one line each):
* `prep_coordCLM n`: the `n`-th coordinate `ℓ² → ℂ` as a continuous ℝ-linear map.
* `prep_basis n`: the unit vector `e_n ∈ ℓ²`.
* `prep_K1_zeroFace_division (n : ℤ) (T : ℝ)`: for every mode `n` and every `T`, there is
  `A : [-T,T] → ℓ² → ℂ` that is (i) jointly continuous on `[-T,T] × ℓ²`; (ii) equal, at every
  `(t, x)`, to `∫₀¹ (fderiv ℝ g_t (x − x_n e_n + (s‖x_n‖) e_n)) e_n ds` (the genuine Fréchet
  derivative of `g_t`); (iii) for every `t ∈ [-T,T]` and every `x` whose `n`-th coordinate is a
  nonnegative real (`x_n = ‖x_n‖`, covering `x_n > 0`), `x_n · A t x = g_t(x)`.
-/

set_option autoImplicit false
noncomputable section

open Filter Topology
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.PDE NlsGge.ThirdConsultation.Common
open NlsGge.SpectralFoundations NlsGge.NLS38
open LiebLiniger.FixedPeriod.ALLS.PdeB NlsGge.ALLS.TransA

namespace NlsGge.ALLS.TransCPrep

/-- The `n`-th coordinate of `ℓ²` as a continuous real-linear map. -/
def prep_coordCLM (n : ℤ) : Lib.L2Z →L[ℝ] ℂ where
  toFun z := (z : ℤ → ℂ) n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := prep_continuous_coord n

/-- The unit vector `e_n`. -/
def prep_basis (n : ℤ) : Lib.L2Z := lp.single (E := fun _ : ℤ => ℂ) 2 n (1 : ℂ)

theorem prep_basis_apply (n k : ℤ) :
    (prep_basis n : ℤ → ℂ) k = if k = n then 1 else 0 := by
  unfold prep_basis
  rw [lp.single_apply]
  by_cases h : k = n
  · subst h; simp
  · simp [h]

/-- **K1** (concrete zero-face division). -/
theorem prep_K1_zeroFace_division (n : ℤ) (T : ℝ) :
    ∃ A : Set.Icc (-T) T → Lib.L2Z → ℂ,
      Continuous (fun q : Set.Icc (-T) T × Lib.L2Z => A q.1 q.2) ∧
      (∀ (t : Set.Icc (-T) T) (x : Lib.L2Z),
        A t x = ∫ s in (0 : ℝ)..1,
          fderiv ℝ (fun y : Lib.L2Z =>
              (physicalBirkhoff (l2Flow (t : ℝ) (physicalInverseBirkhoff y)) : ℤ → ℂ) n)
            (x - ((x : ℤ → ℂ) n) • prep_basis n + (s * ‖(x : ℤ → ℂ) n‖) • prep_basis n)
            (prep_basis n)) ∧
      (∀ (t : Set.Icc (-T) T) (x : Lib.L2Z),
        (x : ℤ → ℂ) n = ((‖(x : ℤ → ℂ) n‖ : ℝ) : ℂ) →
        (x : ℤ → ℂ) n * A t x =
          (physicalBirkhoff (l2Flow (t : ℝ) (physicalInverseBirkhoff x)) : ℤ → ℂ) n) := by
  obtain ⟨hL, hR, hA, hAinv, -⟩ := actual_birkhoff_bindings
  have hΦc : ContDiff ℝ 1 physicalBirkhoff := hA.contDiff
  have hΨc : ContDiff ℝ 1 physicalInverseBirkhoff := hAinv.contDiff
  have hΨ : Continuous physicalInverseBirkhoff := hΨc.continuous
  obtain ⟨F, hF, hFeq⟩ := l2Flow_contDiff T
  obtain ⟨hFd, hFc⟩ := prep_flowSection_deriv T F hF
  set e : Lib.L2Z := prep_basis n with he
  -- the time sections of the flow
  have hflow : ∀ (t : Set.Icc (-T) T) (x : PhysicalL2), HasFDerivAt (fun y => l2Flow (t : ℝ) y)
      ((ContinuousMap.evalCLM ℝ t).comp (fderiv ℝ F x)) x := by
    intro t x
    have h := hFd t x
    have hfun : (fun y => F y t) = fun y => l2Flow (t : ℝ) y := funext fun y => hFeq y t
    rwa [hfun] at h
  set g : Set.Icc (-T) T → Lib.L2Z → ℂ := fun t y =>
    (physicalBirkhoff (l2Flow (t : ℝ) (physicalInverseBirkhoff y)) : ℤ → ℂ) n with hg
  -- the chain rule
  have hgd : ∀ (t : Set.Icc (-T) T) (y : Lib.L2Z), HasFDerivAt (g t)
      ((prep_coordCLM n).comp ((fderiv ℝ physicalBirkhoff (l2Flow (t : ℝ) (physicalInverseBirkhoff y))).comp
        (((ContinuousMap.evalCLM ℝ t).comp (fderiv ℝ F (physicalInverseBirkhoff y))).comp
          (fderiv ℝ physicalInverseBirkhoff y)))) y := by
    intro t y
    have h1 := (hΨc.differentiable one_ne_zero y).hasFDerivAt
    have h2 := hflow t (physicalInverseBirkhoff y)
    have h3 := (hΦc.differentiable one_ne_zero (l2Flow (t : ℝ) (physicalInverseBirkhoff y))).hasFDerivAt
    exact (prep_coordCLM n).hasFDerivAt.comp y (h3.comp y (h2.comp y h1))
  set D : Set.Icc (-T) T → Lib.L2Z → ℂ := fun t y =>
    (fderiv ℝ physicalBirkhoff (l2Flow (t : ℝ) (physicalInverseBirkhoff y))
      ((fderiv ℝ F (physicalInverseBirkhoff y) (fderiv ℝ physicalInverseBirkhoff y e)) t) : ℤ → ℂ) n
    with hD
  have hDeq : ∀ t y, fderiv ℝ (g t) y e = D t y := fun t y => by
    rw [(hgd t y).fderiv]; rfl
  -- joint continuity of the directional derivative
  have hDc : Continuous (fun q : Set.Icc (-T) T × Lib.L2Z => D q.1 q.2) := by
    have hw : Continuous (fun q : Set.Icc (-T) T × Lib.L2Z =>
        l2Flow (q.1 : ℝ) (physicalInverseBirkhoff q.2)) :=
      continuous_l2Flow.comp ((continuous_subtype_val.comp continuous_fst).prodMk
        (hΨ.comp continuous_snd))
    have hv : Continuous (fun q : Set.Icc (-T) T × Lib.L2Z =>
        (fderiv ℝ F (physicalInverseBirkhoff q.2) (fderiv ℝ physicalInverseBirkhoff q.2 e)) q.1) :=
      hFc.comp (continuous_fst.prodMk ((hΨ.comp continuous_snd).prodMk
        (((hΨc.continuous_fderiv one_ne_zero).comp continuous_snd).clm_apply continuous_const)))
    have hd : Continuous (fun q : Set.Icc (-T) T × Lib.L2Z =>
        fderiv ℝ physicalBirkhoff (l2Flow (q.1 : ℝ) (physicalInverseBirkhoff q.2))
          ((fderiv ℝ F (physicalInverseBirkhoff q.2) (fderiv ℝ physicalInverseBirkhoff q.2 e)) q.1)) :=
      ((hΦc.continuous_fderiv one_ne_zero).comp hw).clm_apply hv
    exact (prep_continuous_coord n).comp hd
  -- apply K1b
  obtain ⟨hAc, hAid⟩ := prep_zeroFace_integral (P := Set.Icc (-T) T × Lib.L2Z)
    (fun q y => g q.1 y) (fun q y => D q.1 y) e
    (fun q => q.2 - ((q.2 : ℤ → ℂ) n) • e) (fun q => ‖(q.2 : ℤ → ℂ) n‖)
    (hDc.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
    (continuous_snd.sub (((prep_continuous_coord n).comp continuous_snd).smul continuous_const))
    (continuous_norm.comp ((prep_continuous_coord n).comp continuous_snd))
    (fun q y r => by
      have hl : HasDerivAt (fun r' : ℝ => y + r' • e) ((1 : ℝ) • e) r :=
        ((hasDerivAt_id r).smul_const e).const_add y
      have h := (hgd q.1 (y + r • e)).comp_hasDerivAt r hl
      rw [one_smul] at h
      have h' : HasDerivAt (fun r' : ℝ => g q.1 (y + r' • e)) (fderiv ℝ (g q.1) (y + r • e) e) r := by
        rw [(hgd q.1 (y + r • e)).fderiv]; exact h
      rw [hDeq] at h'
      exact h')
  refine ⟨fun t x => ∫ s in (0 : ℝ)..1, D t (x - ((x : ℤ → ℂ) n) • e + (s * ‖(x : ℤ → ℂ) n‖) • e),
    hAc, fun t x => ?_, fun t x hx => ?_⟩
  · refine intervalIntegral.integral_congr (fun s _ => ?_)
    exact (hDeq t _).symm
  · have hid := hAid (t, x)
    simp only at hid
    -- the zero face
    have hβn : ((x - ((x : ℤ → ℂ) n) • e : Lib.L2Z) : ℤ → ℂ) n = 0 := by
      rw [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, he, prep_basis_apply]
      simp
    have hgβ : g t (x - ((x : ℤ → ℂ) n) • e) = 0 := by
      have h := prep_action_invariant (physicalInverseBirkhoff (x - ((x : ℤ → ℂ) n) • e)) t n
      rw [hR, hβn, norm_zero, norm_eq_zero] at h
      exact h
    have hβx : x - ((x : ℤ → ℂ) n) • e + ‖(x : ℤ → ℂ) n‖ • e = x := by
      ext k
      rw [lp.coeFn_add, lp.coeFn_sub, lp.coeFn_smul, lp.coeFn_smul, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, Pi.smul_apply, he, prep_basis_apply]
      split_ifs with hk
      · subst hk; rw [Complex.real_smul, ← hx]; simp
      · simp
    rw [hgβ, hβx, sub_zero, Complex.real_smul, ← hx] at hid
    exact hid

end NlsGge.ALLS.TransCPrep
