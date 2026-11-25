/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams

Adaptation for NLS-GGE: extracted nine supporting declarations, combined their
namespaces, replaced non-pinned project imports by their actual pinned Mathlib
prerequisites, and used legacy non-module syntax. Mathematical statements and
proofs are retained, with explicit local helper references where namespaces changed.

Upstream: https://github.com/bjbraams/lean-CA
Commit: 333a684877588d3667c7a0d37e5074aaa2e5b7b7
Source paths:
  Topology/LocallyConstantGluing.lean
  ComplexAnalysis/HasPrimitives/Pullback.lean
  ComplexAnalysis/CauchyIntegral.lean (continuous-form integrability wrapper)
  ComplexAnalysis/Integral/ContinuousHomotopy.lean
Sources: https://github.com/bjbraams/lean-CA/tree/333a684877588d3667c7a0d37e5074aaa2e5b7b7
The upstream license and credits are included in licenses/.
-/

import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Analysis.Normed.Operator.Mul

/-! Generic Banach-valued contour integrals under continuous homotopies.

Only boundary paths need differentiability and integrability (or C1 regularity).
The homotopy itself is continuous. This module supplies no piecewise-contour
transport, Jordan separation, winding normalization, nested contour construction,
or Riesz idempotence theorem.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory Bundle
open scoped Topology unitInterval

namespace NlsGge.Atomic.ContourHomotopy

theorem exists_locally_eq_add_of_locally_constant_sub
    {X A ι : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]
    [LocallyPathConnectedSpace X] [AddCommGroup A]
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (p : ι → X → A)
    (hp : ∀ i j x, x ∈ U i ∩ U j →
      ∀ᶠ y in 𝓝 x, p i y - p j y = p i x - p j x)
    (x₀ : X) (a₀ : A) :
    ∃ P : X → A, P x₀ = a₀ ∧ ∀ i x, x ∈ U i →
      ∀ᶠ y in 𝓝 x, P y = P x + (p i y - p i x) := by
  classical
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  let Z : FiberBundleCore ι X A :=
    { baseSet := U
      isOpen_baseSet := hU
      indexAt := fun x => (hcover x).choose
      mem_baseSet_at := fun x => (hcover x).choose_spec
      coordChange := fun i j x v => v + (p i x - p j x)
      coordChange_self := by intros; simp
      continuousOn_coordChange := by
        intro i j q hq
        apply ContinuousAt.continuousWithinAt
        apply (continuousAt_const (y := q.2 + (p i q.1 - p j q.1))).congr
        have he := continuous_fst.continuousAt.eventually (hp i j q.1 hq.1)
        have hv : ∀ᶠ r : X × A in 𝓝 q, r.2 = q.2 :=
          continuous_snd.continuousAt.eventually ((isOpen_discrete {q.2}).mem_nhds rfl)
        filter_upwards [he, hv] with r hr hv
        simp only [hv, hr]
      coordChange_comp := by intros; abel }
  have hcov : IsCoveringMap Z.proj := FiberBundle.isCoveringMap (F := A)
  let e₀ : Z.TotalSpace := ⟨x₀, a₀ - p (Z.indexAt x₀) x₀⟩
  obtain ⟨s, ⟨hs₀, hs⟩, _⟩ := hcov.existsUnique_continuousMap_lifts
    (ContinuousMap.id X) x₀ e₀ rfl
  have hsx (x : X) : (s x).proj = x := congrFun hs x
  let v : X → A := fun x => (s x).2
  let P : X → A := fun x => v x + p (Z.indexAt x) x
  have hlocal (i : ι) (x : X) :
      P x = ((Z.localTriv i) (s x)).2 + p i x := by
    change v x + p (Z.indexAt x) x =
      (v x + (p (Z.indexAt (s x).proj) (s x).proj - p i (s x).proj)) + p i x
    rw [hsx]
    abel
  refine ⟨P, ?_, ?_⟩
  · change v x₀ + p (Z.indexAt x₀) x₀ = a₀
    dsimp only [v]
    rw [hs₀]
    exact sub_add_cancel _ _
  · intro i x hx
    have hmem : s x ∈ (Z.localTriv i).source := by
      apply (Z.localTriv i).mem_source.mpr
      change (s x).proj ∈ U i
      rwa [hsx]
    have hc : ContinuousAt (fun y => ((Z.localTriv i) (s y)).2) x :=
      ((Z.localTriv i).toOpenPartialHomeomorph.continuousAt hmem).snd.comp s.continuous.continuousAt
    have he : ∀ᶠ y in 𝓝 x, ((Z.localTriv i) (s y)).2 = ((Z.localTriv i) (s x)).2 :=
      hc.eventually ((isOpen_discrete {((Z.localTriv i) (s x)).2}).mem_nhds rfl)
    filter_upwards [he] with y hy
    rw [hlocal i y, hlocal i x, hy]
    abel

theorem exists_continuous_primitive_pullback
    {X F : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]
    [LocallyPathConnectedSpace X] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {U : Set ℂ} {f : ℂ → F} (hf : DifferentiableOn ℂ f U)
    (hU : IsOpen U) {g : X → ℂ} (hg : Continuous g) (hgU : range g ⊆ U)
    (x₀ : X) (v₀ : F) :
    ∃ Q : X → F, Continuous Q ∧ Q x₀ = v₀ ∧ ∀ x, ∃ P : ℂ → F,
      HasDerivAt P (f (g x)) (g x) ∧
      ∀ᶠ y in 𝓝 x, Q y = Q x + (P (g y) - P (g x)) := by
  classical
  have hlocal (x : X) : ∃ r > 0, Complex.IsExactOn f (ball (g x) r) := by
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU (g x) (hgU (mem_range_self x))
    exact ⟨r, hr, (hf.mono hsub).isExactOn_ball⟩
  choose r hr P hP using hlocal
  let V : X → Set X := fun x => g ⁻¹' ball (g x) (r x)
  have hV : ∀ x, IsOpen (V x) := fun x => isOpen_ball.preimage hg
  have hcover : ∀ x : X, ∃ i, x ∈ V i := fun x => ⟨x, mem_ball_self (hr x)⟩
  have hdiff : ∀ i j x : X, x ∈ V i ∩ V j →
      ∀ᶠ y in 𝓝 x, P i (g y) - P j (g y) = P i (g x) - P j (g x) := by
    intro i j x hx
    have hd : ∀ z ∈ ball (g i) (r i) ∩ ball (g j) (r j),
        HasDerivAt (fun w => P i w - P j w) 0 z := by
      intro z hz
      change HasDerivAt (P i - P j) 0 z
      simpa only [sub_self] using (hP i z hz.1).sub (hP j z hz.2)
    filter_upwards [((hV i).inter (hV j)).mem_nhds hx] with y hy
    exact (isOpen_ball.inter isOpen_ball).is_const_of_deriv_eq_zero
      ((convex_ball (g i) (r i)).inter (convex_ball (g j) (r j))).isPreconnected
      (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hd z hz).deriv) hy hx
  obtain ⟨Q, hQ₀, hQ⟩ := exists_locally_eq_add_of_locally_constant_sub
    V hV hcover (fun i x => P i (g x)) hdiff x₀ v₀
  refine ⟨Q, ?_, hQ₀, fun x => ⟨P x, hP x (g x) (mem_ball_self (hr x)),
    hQ x x (mem_ball_self (hr x))⟩⟩
  apply continuous_iff_continuousAt.mpr
  intro x
  have hc : ContinuousAt (P x ∘ g) x :=
    (hP x (g x) (mem_ball_self (hr x))).continuousAt.comp hg.continuousAt
  have hc' : ContinuousAt (fun y => Q x + (P x (g y) - P x (g x))) x :=
    continuousAt_const.add (hc.sub continuousAt_const)
  exact hc'.congr_of_eventuallyEq (hQ x x (mem_ball_self (hr x)))


/-- A continuous function locally obtained from primitives computes the integral along
the image of a path. Only the image path needs to be differentiable and integrable. -/
theorem curveIntegral_map_eq_sub_of_locally_primitive
    {X F : Type*} [TopologicalSpace X] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {g : X → ℂ} (hg : Continuous g) {Q : X → F} (hQ : Continuous Q)
    {f : ℂ → F} (hlocal : ∀ x, ∃ P : ℂ → F, HasDerivAt P (f (g x)) (g x) ∧
      ∀ᶠ y in 𝓝 x, Q y = Q x + (P (g y) - P (g x)))
    {x y : X} (η : Path x y) (hη : DifferentiableOn ℝ (η.map hg).extend I)
    (hint : CurveIntegrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z))
      (η.map hg)) :
    curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) (η.map hg) =
      Q y - Q x := by
  have hd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (Q ∘ η.extend)
        (curveIntegralFun (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z))
          (η.map hg) t) t := by
    obtain ⟨P, hP, he⟩ := hlocal (η.extend t)
    have htI : t ∈ I := ⟨ht.1.le, ht.2.le⟩
    rw [curveIntegralFun_def, derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    have hder := (hP.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
      ((hη t htI).differentiableAt (Icc_mem_nhds ht.1 ht.2)).hasDerivAt
    apply ((hder.sub_const (P (g (η.extend t)))).const_add (Q (η.extend t))).congr_of_eventuallyEq
    exact η.continuous_extend.continuousAt.eventually he
  simpa only [curveIntegral_def, Function.comp_apply, η.extend_one, η.extend_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
      (hQ.comp η.continuous_extend).continuousOn hd hint

/-- A parametrization in the source computes a planar curve integral from the increments
of a pulled-back primitive. The parametrization need only be continuous. -/
theorem curveIntegral_eq_sub_of_locally_primitive
    {X F : Type*} [TopologicalSpace X] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {g : X → ℂ} (hg : Continuous g) {Q : X → F} (hQ : Continuous Q)
    {f : ℂ → F} (hlocal : ∀ x, ∃ P : ℂ → F, HasDerivAt P (f (g x)) (g x) ∧
      ∀ᶠ y in 𝓝 x, Q y = Q x + (P (g y) - P (g x)))
    {r : I → X} (hr : Continuous r) {a b : ℂ} {γ : Path a b}
    (hcomp : ∀ t, g (r t) = γ t) (hγ : DifferentiableOn ℝ γ.extend I)
    (hint : CurveIntegrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ) :
    curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ = Q (r 1) - Q (r 0) := by
  let η : Path (r 0) (r 1) := ⟨⟨r, hr⟩, rfl, rfl⟩
  have he : η.map hg = γ.cast ((hcomp 0).trans γ.source) ((hcomp 1).trans γ.target) := by
    ext t
    exact hcomp t
  have h := curveIntegral_map_eq_sub_of_locally_primitive hg hQ hlocal η
    (by simpa only [he, Path.extend_cast] using hγ)
    (by simpa only [he, curveIntegrable_cast_iff] using hint)
  simpa only [he, curveIntegral_cast] using h

/-- A continuous complex Banach-valued function is integrable along a `C¹` path in its domain. -/
theorem curveIntegrable_of_continuousOn
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {U : Set ℂ} {f : ℂ → F} {a b : ℂ} {γ : Path a b}
    (hf : ContinuousOn f U)
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hγU : ∀ t, γ t ∈ U) :
    CurveIntegrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ :=
  ((ContinuousLinearMap.toSpanSingletonLIE ℂ F).continuous.comp_continuousOn
      hf).curveIntegrable_of_contDiffOn
    hγ hγU

/-- Cauchy's theorem for the boundary of a continuous homotopy, with moving endpoints.
The four boundary paths must be differentiable and integrable, but no regularity of
the interior of the homotopy is required beyond continuity. -/
theorem curveIntegral_add_curveIntegral_eq_of_continuous_homotopy
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U : Set ℂ} {f : ℂ → F} {a b c d : ℂ} {γ : Path a b} {δ : Path c d}
    (H : (γ : C(I, ℂ)).Homotopy δ)
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hHU : range H ⊆ U)
    (hγ : DifferentiableOn ℝ γ.extend I) (hδ : DifferentiableOn ℝ δ.extend I)
    (h₀ : DifferentiableOn ℝ (H.evalAt 0).extend I)
    (h₁ : DifferentiableOn ℝ (H.evalAt 1).extend I)
    (hiγ : CurveIntegrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ)
    (hiδ : CurveIntegrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) δ)
    (hi₀ : CurveIntegrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) (H.evalAt 0))
    (hi₁ : CurveIntegrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) (H.evalAt 1)) :
    curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ +
        curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) (H.evalAt 1) =
      curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) δ +
        curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) (H.evalAt 0) := by
  let : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  let : LocallyPathConnectedSpace I := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  obtain ⟨Q, hQ, _, hlocal⟩ := exists_continuous_primitive_pullback hf hU H.continuous
    hHU ((0 : I), (0 : I)) 0
  have heγ := curveIntegral_eq_sub_of_locally_primitive H.continuous hQ hlocal
    (r := fun t : I => ((0 : I), t)) (by fun_prop) (fun t => H.apply_zero t) hγ hiγ
  have heδ := curveIntegral_eq_sub_of_locally_primitive H.continuous hQ hlocal
    (r := fun t : I => ((1 : I), t)) (by fun_prop) (fun t => H.apply_one t) hδ hiδ
  have he₀ := curveIntegral_eq_sub_of_locally_primitive H.continuous hQ hlocal
    (r := fun t : I => (t, (0 : I))) (by fun_prop) (fun _ => rfl) h₀ hi₀
  have he₁ := curveIntegral_eq_sub_of_locally_primitive H.continuous hQ hlocal
    (r := fun t : I => (t, (1 : I))) (by fun_prop) (fun _ => rfl) h₁ hi₁
  rw [heγ, heδ, he₀, he₁]
  abel

/-- The moving-endpoint Cauchy identity for a continuous homotopy with `C¹` boundary paths. -/
theorem curveIntegral_add_curveIntegral_eq_of_continuous_homotopy_of_contDiffOn
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U : Set ℂ} {f : ℂ → F} {a b c d : ℂ} {γ : Path a b} {δ : Path c d}
    (H : (γ : C(I, ℂ)).Homotopy δ)
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hHU : range H ⊆ U)
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hδ : ContDiffOn ℝ 1 δ.extend I)
    (h₀ : ContDiffOn ℝ 1 (H.evalAt 0).extend I)
    (h₁ : ContDiffOn ℝ 1 (H.evalAt 1).extend I) :
    curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ +
        curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) (H.evalAt 1) =
      curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) δ +
        curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) (H.evalAt 0) :=
  curveIntegral_add_curveIntegral_eq_of_continuous_homotopy H hU hf hHU
    (hγ.differentiableOn one_ne_zero) (hδ.differentiableOn one_ne_zero)
    (h₀.differentiableOn one_ne_zero) (h₁.differentiableOn one_ne_zero)
    (curveIntegrable_of_continuousOn hf.continuousOn hγ
      (fun t => hHU ⟨(0, t), H.apply_zero t⟩))
    (curveIntegrable_of_continuousOn hf.continuousOn hδ
      (fun t => hHU ⟨(1, t), H.apply_one t⟩))
    (curveIntegrable_of_continuousOn hf.continuousOn h₀ (fun t => hHU ⟨(t, 0), rfl⟩))
    (curveIntegrable_of_continuousOn hf.continuousOn h₁ (fun t => hHU ⟨(t, 1), rfl⟩))

/-- Holomorphic curve integrals agree under a continuous homotopy fixing endpoints.
Only the two boundary paths must be differentiable and curve integrable. -/
theorem curveIntegral_eq_of_continuous_homotopy
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U : Set ℂ} {f : ℂ → F} {a b : ℂ} {γ δ : Path a b} (H : γ.Homotopy δ)
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hHU : range H ⊆ U)
    (hγ : DifferentiableOn ℝ γ.extend I) (hδ : DifferentiableOn ℝ δ.extend I)
    (hγint : CurveIntegrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ)
    (hδint : CurveIntegrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) δ) :
    curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ =
      curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) δ := by
  let : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  let : LocallyPathConnectedSpace I := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  obtain ⟨Q, hQ, _, hlocal⟩ := exists_continuous_primitive_pullback hf hU H.continuous
    hHU ((0 : I), (0 : I)) 0
  have hedge (t : I) (ht : ∀ s, H (s, t) = H (0, t)) : ∀ s, Q (s, t) = Q (0, t) := by
    suffices hc : IsLocallyConstant (fun s : I => Q (s, t)) from
      fun s => hc.apply_eq_of_preconnectedSpace s 0
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro s
    obtain ⟨P, _, he⟩ := hlocal (s, t)
    have hc : ContinuousAt (fun r : I => (r, t)) s := by fun_prop
    filter_upwards [hc.eventually he] with r hr
    simpa only [ht r, ht s, sub_self, add_zero] using hr
  let η (s : I) : Path (s, (0 : I)) (s, (1 : I)) := (Path.refl s).prod Path.id
  have hmap (s : I) : (η s).map H.continuous =
      (H.eval s).cast (H.source s) (H.target s) := by
    ext t
    rfl
  have hrow (s : I) (hs : DifferentiableOn ℝ (H.eval s).extend I)
      (hint : CurveIntegrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) (H.eval s)) :
      curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) (H.eval s) =
        Q (s, 1) - Q (s, 0) := by
    have h := curveIntegral_map_eq_sub_of_locally_primitive H.continuous hQ hlocal (η s)
      (by simpa only [hmap, Path.extend_cast] using hs)
      (by simpa only [hmap, curveIntegrable_cast_iff] using hint)
    simpa only [hmap, curveIntegral_cast] using h
  have hγeq := hrow 0 (by simpa using hγ) (by simpa using hγint)
  have hδeq := hrow 1 (by simpa using hδ) (by simpa using hδint)
  simp only [Path.Homotopy.eval_zero, Path.Homotopy.eval_one] at hγeq hδeq
  rw [hedge 0 (by intro s; simp) 1, hedge 1 (by intro s; simp) 1] at hδeq
  exact hγeq.trans hδeq.symm

/-- A continuous homotopy in a holomorphy domain preserves integrals along `C¹` boundary paths. -/
theorem curveIntegral_eq_of_continuous_homotopy_of_contDiffOn
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U : Set ℂ} {f : ℂ → F} {a b : ℂ} {γ δ : Path a b} (H : γ.Homotopy δ)
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hHU : range H ⊆ U)
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hδ : ContDiffOn ℝ 1 δ.extend I) :
    curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ =
      curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) δ :=
  curveIntegral_eq_of_continuous_homotopy H hU hf hHU
    (hγ.differentiableOn one_ne_zero) (hδ.differentiableOn one_ne_zero)
    (curveIntegrable_of_continuousOn hf.continuousOn hγ
      (fun t => hHU ⟨(0, t), by simp⟩))
    (curveIntegrable_of_continuousOn hf.continuousOn hδ
      (fun t => hHU ⟨(1, t), by simp⟩))

end NlsGge.Atomic.ContourHomotopy
