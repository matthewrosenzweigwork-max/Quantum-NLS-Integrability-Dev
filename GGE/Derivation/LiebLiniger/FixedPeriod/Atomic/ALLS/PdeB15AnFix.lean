import Mathlib

/-! # Track B, contracts 18–19 (step 2): analytic dependence of a fixed point on a parameter

Generic real Banach-space lemma (no PDE content): if `G : E × X → X` is real-analytic at `(a₀, x₀)`,
`G (a₀, x₀) = x₀` and the partial derivative `∂ₓG(a₀, x₀)` has operator norm `< 1`, then there is a
function `g`, real-analytic at `a₀`, with `g a₀ = x₀` and `G (a, g a) = g a` for `a` near `a₀`.

Proof: `H (a, x) = (a, x - G (a, x))` is analytic with derivative
`(h, k) ↦ (h, k - DG (h, k))`, inverted explicitly by `(h, m) ↦ (h, (1 - L)⁻¹ (m + DG (h, 0)))`
(`L = ∂ₓG`, Neumann series `Units.oneSub`); Mathlib's analytic inverse function theorem
`OpenPartialHomeomorph.hasFPowerSeriesAt_symm` makes the local inverse analytic and
`g a = (H⁻¹ (a, 0)).2`.
-/

namespace LiebLiniger.FixedPeriod.ALLS.PdeB
open Topology Filter
set_option autoImplicit false
noncomputable section

section AnFix

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

theorem analytic_fixedPoint {G : E × X → X} {a₀ : E} {x₀ : X}
    (hG : AnalyticAt ℝ G (a₀, x₀)) (hfix : G (a₀, x₀) = x₀)
    (hL : ‖(fderiv ℝ G (a₀, x₀)).comp (ContinuousLinearMap.inr ℝ E X)‖ < 1) :
    ∃ g : E → X, AnalyticAt ℝ g a₀ ∧ g a₀ = x₀ ∧ ∀ᶠ a in 𝓝 a₀, G (a, g a) = g a := by
  set DG : E × X →L[ℝ] X := fderiv ℝ G (a₀, x₀) with hDG
  set L : X →L[ℝ] X := DG.comp (ContinuousLinearMap.inr ℝ E X) with hLdef
  have hu : ((Units.oneSub L hL : (X →L[ℝ] X)ˣ) : X →L[ℝ] X) = 1 - L := Units.val_oneSub L hL
  set V : X →L[ℝ] X := ((Units.oneSub L hL)⁻¹ : (X →L[ℝ] X)ˣ).val with hV
  have hinv1 : ∀ k : X, V ((1 - L) k) = k := fun k => by
    rw [← hu]
    exact congrArg (fun T : X →L[ℝ] X => T k) (Units.inv_mul (Units.oneSub L hL))
  have hinv2 : ∀ m : X, (1 - L) (V m) = m := fun m => by
    rw [← hu]
    exact congrArg (fun T : X →L[ℝ] X => T m) (Units.mul_inv (Units.oneSub L hL))
  have hsplit : ∀ (h : E) (k : X), DG (h, k) = DG (h, 0) + L k := fun h k => by
    rw [hLdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, ← map_add,
      Prod.mk_add_mk, add_zero, zero_add]
  have h1L : ∀ k : X, (1 - L) k = k - L k := fun k => rfl
  set H' : E × X →L[ℝ] E × X :=
    (ContinuousLinearMap.fst ℝ E X).prod (ContinuousLinearMap.snd ℝ E X - DG) with hH'
  set J : E × X →L[ℝ] E × X := (ContinuousLinearMap.fst ℝ E X).prod
    (V.comp (ContinuousLinearMap.snd ℝ E X +
      DG.comp ((ContinuousLinearMap.inl ℝ E X).comp (ContinuousLinearMap.fst ℝ E X)))) with hJ
  have hH'app : ∀ (h : E) (k : X), H' (h, k) = (h, k - DG (h, k)) := fun h k => rfl
  have hJapp : ∀ (h : E) (m : X), J (h, m) = (h, V (m + DG (h, 0))) := fun h m => rfl
  have hleft : Function.LeftInverse J H' := by
    rintro ⟨h, k⟩
    rw [hH'app, hJapp, hsplit h k]
    have e : k - (DG (h, 0) + L k) + DG (h, 0) = (1 - L) k := by rw [h1L]; abel
    rw [e, hinv1]
  have hright : Function.RightInverse J H' := by
    rintro ⟨h, m⟩
    rw [hJapp, hH'app, hsplit h (V (m + DG (h, 0)))]
    have e : V (m + DG (h, 0)) - (DG (h, 0) + L (V (m + DG (h, 0)))) =
        (1 - L) (V (m + DG (h, 0))) - DG (h, 0) := by rw [h1L]; abel
    rw [e, hinv2, add_sub_cancel_right]
  set i : (E × X) ≃L[ℝ] (E × X) := ContinuousLinearEquiv.equivOfInverse H' J hleft hright
  set H : E × X → E × X := fun p => (p.1, p.2 - G p) with hH
  have hHs : HasStrictFDerivAt H H' (a₀, x₀) :=
    hasStrictFDerivAt_fst.prodMk (hasStrictFDerivAt_snd.sub hG.hasStrictFDerivAt)
  have hHi : HasStrictFDerivAt H (i : E × X →L[ℝ] E × X) (a₀, x₀) := hHs
  have hHa : AnalyticAt ℝ H (a₀, x₀) := analyticAt_fst.prod (analyticAt_snd.sub hG)
  obtain ⟨p, hp⟩ := hHa
  set Φ := hHi.toOpenPartialHomeomorph H with hΦ
  have hΦc : (Φ : E × X → E × X) = H := hHi.toOpenPartialHomeomorph_coe
  have hsrc : (a₀, x₀) ∈ Φ.source := hHi.mem_toOpenPartialHomeomorph_source
  have hp1 : p 1 = (continuousMultilinearCurryFin1 ℝ (E × X) (E × X)).symm
      (i : E × X →L[ℝ] E × X) := by
    rw [← hHi.hasFDerivAt.fderiv, hp.fderiv_eq, LinearIsometryEquiv.symm_apply_apply]
  have hpΦ : HasFPowerSeriesAt (Φ : E × X → E × X) p (a₀, x₀) := by rw [hΦc]; exact hp
  have hsymm := Φ.hasFPowerSeriesAt_symm hsrc hpΦ hp1
  have hΦp : (Φ : E × X → E × X) (a₀, x₀) = (a₀, 0) := by
    rw [hΦc]; simp only [hH, hfix, sub_self]
  rw [hΦp] at hsymm
  have hA : AnalyticAt ℝ (Φ.symm : E × X → E × X) (a₀, 0) := hsymm.analyticAt
  refine ⟨fun a => (Φ.symm (a, 0)).2, ?_, ?_, ?_⟩
  · have hemb : AnalyticAt ℝ (fun a : E => ((a, (0 : X)) : E × X)) a₀ :=
      analyticAt_id.prod analyticAt_const
    have h2 := AnalyticAt.comp (g := (Φ.symm : E × X → E × X))
      (f := fun a : E => ((a, (0 : X)) : E × X)) (x := a₀) hA hemb
    exact AnalyticAt.comp (g := fun q : E × X => q.2)
      (f := (Φ.symm : E × X → E × X) ∘ (fun a : E => ((a, (0 : X)) : E × X))) (x := a₀)
      analyticAt_snd h2
  · show (Φ.symm (a₀, 0)).2 = x₀
    rw [← hΦp, Φ.left_inv hsrc]
  · have htgt : Φ.target ∈ 𝓝 ((a₀, 0) : E × X) := by
      rw [← hΦp]; exact Φ.open_target.mem_nhds (Φ.map_source hsrc)
    have hpre : (fun a : E => ((a, 0) : E × X)) ⁻¹' Φ.target ∈ 𝓝 a₀ :=
      (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds htgt
    filter_upwards [hpre] with a ha
    have hr := Φ.right_inv ha
    rw [hΦc] at hr
    set q := Φ.symm (a, 0)
    simp only [hH, Prod.mk.injEq] at hr
    have hq : q = (a, q.2) := Prod.ext hr.1 rfl
    rw [← hq]
    exact (sub_eq_zero.1 hr.2).symm

end AnFix

end

end LiebLiniger.FixedPeriod.ALLS.PdeB
