/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams

The continuous-homotopy primitive-pullback argument is adapted from
https://github.com/bjbraams/lean-CA, commit333a684877588d3667c7a0d37e5074aaa2e5b7b7,
ComplexAnalysis/Integral/ContinuousHomotopy.lean. The checked nine-declaration
backport is imported below. This module adds actual finite-piecewise boundary
transport using continuous half-parameter splitting and C1 leaf endpoint formulas.
-/

import NlsGge.Atomic.Support.ContourHomotopy
import NlsGge.Atomic.LIB.LIB042

/-! Continuous homotopy transport for the actual LIB042 finite C1 paths.

The assembled path need not be C1. Integrability is proved from its actual C1
leaves before curve-integral identities. No contour simplicity, Jordan separation,
winding normalization, nested deformation, or Riesz idempotence is asserted here.
-/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval

namespace NlsGge.Atomic.ContourPiecewise
open NlsGge.Atomic.LIB042

/-- The left half of the actual normalized concatenation parameter. -/
def leftHalf (t : I) : I := ⟨(t : ℝ) / 2, by
  constructor <;> nlinarith [t.property.1, t.property.2]⟩

/-- The right half of the actual normalized concatenation parameter. -/
def rightHalf (t : I) : I := ⟨((t : ℝ) + 1) / 2, by
  constructor <;> nlinarith [t.property.1, t.property.2]⟩

lemma continuous_leftHalf : Continuous leftHalf := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.div_const 2

lemma continuous_rightHalf : Continuous rightHalf := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.add continuous_const).div_const 2

@[simp] lemma leftHalf_zero : leftHalf 0 = 0 := by
  apply Subtype.ext
  norm_num [leftHalf]

@[simp] lemma rightHalf_one : rightHalf 1 = 1 := by
  apply Subtype.ext
  norm_num [rightHalf]

lemma leftHalf_one_eq_rightHalf_zero : leftHalf 1 = rightHalf 0 := by
  apply Subtype.ext
  norm_num [leftHalf, rightHalf]

lemma trans_leftHalf {a b c : ℂ} (γ : Path a b) (δ : Path b c) (t : I) :
    (γ.trans δ) (leftHalf t) = γ t := by
  rw [← Path.extend_apply (γ.trans δ) (leftHalf t).property,
    Path.extend_trans_of_le_half γ δ (by dsimp [leftHalf]; nlinarith [t.property.2])]
  have he : 2 * (leftHalf t : ℝ) = (t : ℝ) := by dsimp [leftHalf]; ring
  rw [he, Path.extend_apply γ t.property]

lemma trans_rightHalf {a b c : ℂ} (γ : Path a b) (δ : Path b c) (t : I) :
    (γ.trans δ) (rightHalf t) = δ t := by
  rw [← Path.extend_apply (γ.trans δ) (rightHalf t).property,
    Path.extend_trans_of_half_le γ δ (by dsimp [rightHalf]; nlinarith [t.property.1])]
  have he : 2 * (rightHalf t : ℝ) - 1 = (t : ℝ) := by dsimp [rightHalf]; ring
  rw [he, Path.extend_apply δ t.property]

/-- Genuine integrability for a continuous function along the actual finite C1 leaves. -/
theorem curveIntegrable_of_piecewiseC1
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {U : Set ℂ} {f : ℂ → F} (hf : ContinuousOn f U)
    {a b : ℂ} {γ : Path a b} (hγ : PiecewiseC1 γ) (himage : ∀ t, γ t ∈ U) :
    CurveIntegrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ :=
  hγ.curveIntegrable
    ((ContinuousLinearMap.toSpanSingletonLIE ℂ F).continuous.comp_continuousOn hf) himage

/-- A pulled-back primitive computes the integral along a finite C1 concatenation.
The source parametrization is merely continuous; no C1 claim about the assembled path is used. -/
theorem curveIntegral_eq_sub_of_locally_primitive_of_piecewiseC1
    {X F : Type*} [TopologicalSpace X] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {g : X → ℂ} (hg : Continuous g) {Q : X → F} (hQ : Continuous Q)
    {f : ℂ → F} (hlocal : ∀ x, ∃ P : ℂ → F, HasDerivAt P (f (g x)) (g x) ∧
      ∀ᶠ y in 𝓝 x, Q y = Q x + (P (g y) - P (g x)))
    {U : Set ℂ} (hf : ContinuousOn f U)
    {r : I → X} (hr : Continuous r) {a b : ℂ} {γ : Path a b}
    (hcomp : ∀ t, g (r t) = γ t) (hγ : PiecewiseC1 γ) (himage : ∀ t, γ t ∈ U) :
    CurveIntegrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ ∧
      curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ =
        Q (r 1) - Q (r 0) := by
  induction hγ generalizing r with
  | ofC1 γ hc =>
      have hi := curveIntegrable_of_piecewiseC1 hf (.ofC1 γ hc) himage
      exact ⟨hi, ContourHomotopy.curveIntegral_eq_sub_of_locally_primitive hg hQ hlocal hr
        hcomp (hc.differentiableOn one_ne_zero) hi⟩
  | @trans a b c γ δ hγ hδ ihγ ihδ =>
      have himL : ∀ t, γ t ∈ U := fun t => by
        rw [← trans_leftHalf γ δ t]
        exact himage (leftHalf t)
      have himR : ∀ t, δ t ∈ U := fun t => by
        rw [← trans_rightHalf γ δ t]
        exact himage (rightHalf t)
      have hcompL : ∀ t, g ((r ∘ leftHalf) t) = γ t := fun t =>
        (hcomp (leftHalf t)).trans (trans_leftHalf γ δ t)
      have hcompR : ∀ t, g ((r ∘ rightHalf) t) = δ t := fun t =>
        (hcomp (rightHalf t)).trans (trans_rightHalf γ δ t)
      obtain ⟨hiL, heL⟩ := ihγ (hr.comp continuous_leftHalf) hcompL himL
      obtain ⟨hiR, heR⟩ := ihδ (hr.comp continuous_rightHalf) hcompR himR
      refine ⟨hiL.trans hiR, ?_⟩
      rw [curveIntegral_trans hiL hiR, heL, heR]
      simp only [Function.comp_apply, leftHalf_zero, rightHalf_one,
        leftHalf_one_eq_rightHalf_zero]
      abel

/-- Continuous moving-endpoint homotopies preserve the oriented boundary identity
for actual finite C1 boundary paths. The interior is only continuous. -/
theorem curveIntegral_add_curveIntegral_eq_of_continuous_homotopy
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U : Set ℂ} {f : ℂ → F} {a b c d : ℂ} {γ : Path a b} {δ : Path c d}
    (H : (γ : C(I, ℂ)).Homotopy δ)
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hHU : range H ⊆ U)
    (hγ : PiecewiseC1 γ) (hδ : PiecewiseC1 δ)
    (h₀ : PiecewiseC1 (H.evalAt 0)) (h₁ : PiecewiseC1 (H.evalAt 1)) :
    curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ +
        curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) (H.evalAt 1) =
      curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) δ +
        curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) (H.evalAt 0) := by
  let : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  let : LocallyPathConnectedSpace I := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  obtain ⟨Q, hQ, _, hlocal⟩ := ContourHomotopy.exists_continuous_primitive_pullback
    hf hU H.continuous hHU ((0 : I), (0 : I)) 0
  obtain ⟨_, heγ⟩ := curveIntegral_eq_sub_of_locally_primitive_of_piecewiseC1
    H.continuous hQ hlocal hf.continuousOn
    (r := fun t : I => ((0 : I), t)) (by fun_prop) (fun t => H.apply_zero t) hγ
    (fun t => hHU ⟨(0, t), H.apply_zero t⟩)
  obtain ⟨_, heδ⟩ := curveIntegral_eq_sub_of_locally_primitive_of_piecewiseC1
    H.continuous hQ hlocal hf.continuousOn
    (r := fun t : I => ((1 : I), t)) (by fun_prop) (fun t => H.apply_one t) hδ
    (fun t => hHU ⟨(1, t), H.apply_one t⟩)
  obtain ⟨_, he₀⟩ := curveIntegral_eq_sub_of_locally_primitive_of_piecewiseC1
    H.continuous hQ hlocal hf.continuousOn
    (r := fun t : I => (t, (0 : I))) (by fun_prop) (fun _ => rfl) h₀
    (fun t => hHU ⟨(t, 0), rfl⟩)
  obtain ⟨_, he₁⟩ := curveIntegral_eq_sub_of_locally_primitive_of_piecewiseC1
    H.continuous hQ hlocal hf.continuousOn
    (r := fun t : I => (t, (1 : I))) (by fun_prop) (fun _ => rfl) h₁
    (fun t => hHU ⟨(t, 1), rfl⟩)
  rw [heγ, heδ, he₀, he₁]
  abel

/-- Fixed-endpoint continuous homotopies preserve actual piecewise C1 integrals.
There is no smoothness assumption on the homotopy or its intermediate paths. -/
theorem curveIntegral_eq_of_continuous_homotopy
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U : Set ℂ} {f : ℂ → F} {a b : ℂ} {γ δ : Path a b} (H : γ.Homotopy δ)
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hHU : range H ⊆ U)
    (hγ : PiecewiseC1 γ) (hδ : PiecewiseC1 δ) :
    curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ =
      curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) δ := by
  let : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  let : LocallyPathConnectedSpace I := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  obtain ⟨Q, hQ, _, hlocal⟩ := ContourHomotopy.exists_continuous_primitive_pullback
    hf hU H.continuous hHU ((0 : I), (0 : I)) 0
  have hedge (t : I) (ht : ∀ s, H (s, t) = H (0, t)) : ∀ s, Q (s, t) = Q (0, t) := by
    suffices hc : IsLocallyConstant (fun s : I => Q (s, t)) from
      fun s => hc.apply_eq_of_preconnectedSpace s 0
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro s
    obtain ⟨P, _, he⟩ := hlocal (s, t)
    have hc : ContinuousAt (fun r : I => (r, t)) s := by fun_prop
    filter_upwards [hc.eventually he] with r hr
    simpa only [ht r, ht s, sub_self, add_zero] using hr
  obtain ⟨_, heγ⟩ := curveIntegral_eq_sub_of_locally_primitive_of_piecewiseC1
    H.continuous hQ hlocal hf.continuousOn
    (r := fun t : I => ((0 : I), t)) (by fun_prop) (fun t => H.apply_zero t) hγ
    (fun t => hHU ⟨(0, t), H.apply_zero t⟩)
  obtain ⟨_, heδ⟩ := curveIntegral_eq_sub_of_locally_primitive_of_piecewiseC1
    H.continuous hQ hlocal hf.continuousOn
    (r := fun t : I => ((1 : I), t)) (by fun_prop) (fun t => H.apply_one t) hδ
    (fun t => hHU ⟨(1, t), H.apply_one t⟩)
  rw [hedge 0 (by intro s; simp) 1, hedge 1 (by intro s; simp) 1] at heδ
  exact heγ.trans heδ.symm

open NlsGge.Schur NlsGge.Atomic.Interval
open NlsGge.Atomic.LIB033 NlsGge.Atomic.LIB038 NlsGge.Atomic.LIB041

/-- Openness of the actual bounded-resolvent set, derived from LIB041's proved
local full inverse, without a geometric contour premise. -/
theorem isOpen_zsResolventSet (φ : SourcePairL2) (bc : ZSBoundaryCondition) :
    IsOpen {z : ℂ | HasBoundedResolvent (zsRealization φ bc) z} := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hs : ‖localKernel φ bc z hz (0,z)‖ < 1 := by rw [localKernel_center]; simp
  have ho : IsOpen {w : ℂ | ‖localKernel φ bc z hz (0,w)‖ < 1} :=
    (local_small_open φ bc z hz).preimage (continuous_const.prodMk continuous_id)
  apply Filter.mem_of_superset (ho.mem_nhds hs)
  intro w hw
  change HasBoundedResolvent (zsRealization φ bc) w
  simpa only [commonDomainOperator_zero] using
    local_hasBoundedResolvent φ bc z hz (0,w) hw

/-- The same literal normalized Riesz operators are invariant under an actual
fixed-endpoint continuous homotopy in the actual resolvent set. -/
theorem zsRieszProjection_eq_of_continuous_homotopy
    (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    {a b : ℂ} {γ δ : Path a b} (H : γ.Homotopy δ)
    (hγ : PiecewiseC1 γ) (hδ : PiecewiseC1 δ)
    (hres : ∀ p, HasBoundedResolvent (zsRealization φ bc) (H p)) :
    zsRieszProjection φ bc γ = zsRieszProjection φ bc δ := by
  have he := curveIntegral_eq_of_continuous_homotopy H
    (isOpen_zsResolventSet φ bc)
    (zsResolventFamily_analyticOnNhd φ bc).differentiableOn
    (by rintro _ ⟨p, rfl⟩; exact hres p) hγ hδ
  have hform : (fun z => ContinuousLinearMap.toSpanSingleton ℂ (zsResolventFamily φ bc z)) =
      resolventForm φ bc := by
    funext z
    ext v
    rfl
  rw [hform] at he
  exact congrArg (fun T : ResolventOp => rieszFactor • T) he

end NlsGge.Atomic.ContourPiecewise
