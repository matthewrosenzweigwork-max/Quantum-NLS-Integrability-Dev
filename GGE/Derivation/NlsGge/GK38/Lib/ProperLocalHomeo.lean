import Mathlib

/-! # L5: proper local homeomorphisms onto a normed space, and analytic global inverses

Piece L5 of the E01 plan (`campaign/E01_PLAN.md` §6.1), re-proved locally from Mathlib
(user decision E01-D8, no external code).  Based on the scratch proofs of concept recorded in
`campaign/e01/MATHLIB_GAPS.md` §7 (`cover_bijective`, `proper_lh_cover`).

* `cover_bijective`: a covering map from a preconnected space onto a simply connected,
  locally path-connected space is bijective.
* `proper_lh_cover`: a proper local homeomorphism into a `T2`-source space is a covering map.
* `properLocalHomeo_homeomorph`: a proper local homeomorphism from a nonempty, `T2`,
  preconnected space onto a real normed space is a homeomorphism (Hadamard–Caccioppoli).
* `isLocalHomeomorph_of_analytic_fderiv`: a real-analytic map between real Banach spaces with
  everywhere invertible derivative is a local homeomorphism.
* `analytic_inverse_of_global`: if moreover it is bijective, its inverse is real-analytic.
* `properAnalytic_homeomorph`: assembly of the above.

Axioms: only the Mathlib allowlist (`propext`, `Classical.choice`, `Quot.sound`).
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.GK38.Lib

open Topology
open scoped ContDiff

/-- A covering map from a preconnected space onto a simply connected, locally path-connected
space is bijective (lift of the identity is a global section, unique by monodromy). -/
theorem cover_bijective {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}
    (hp : IsCoveringMap p) [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    [PreconnectedSpace E] (e₀ : E) : Function.Bijective p := by
  obtain ⟨s, ⟨hs0, hs⟩, -⟩ :=
    hp.existsUnique_continuousMap_lifts (ContinuousMap.id X) (p e₀) e₀ rfl
  have hsec : ∀ x, p (s x) = x := fun x => congrFun hs x
  have hcomp : (⇑s ∘ p) = id := by
    refine hp.eq_of_comp_eq (g₁ := s ∘ p) (g₂ := id)
      (s.continuous.comp hp.continuous) continuous_id ?_ e₀ ?_
    · ext x; simp [hsec]
    · simp [hs0]
  refine ⟨?_, fun x => ⟨s x, hsec x⟩⟩
  intro a b hab
  have h1 := congrFun hcomp a
  have h2 := congrFun hcomp b
  simp only [Function.comp_apply, id_eq] at h1 h2
  rw [← h1, ← h2, hab]

/-- A proper local homeomorphism with `T2` source is a covering map (closed map with finite
fibres, which are compact and discrete). -/
theorem proper_lh_cover {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space E]
    {p : E → X} (hp : IsProperMap p) (hl : IsLocalHomeomorph p) : IsCoveringMap p := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  refine hp.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn (fun x _ => ?_)
    (by simpa using hl.isLocalHomeomorphOn)
  have hc : IsCompact (p ⁻¹' {x}) := hp.isCompact_preimage isCompact_singleton
  have hd : IsDiscrete (p ⁻¹' {x}) :=
    IsDiscrete.of_openPartialHomeomorph p (x := x) subset_rfl (fun e he => by
      obtain ⟨φ, hφ, hφe⟩ := hl e
      exact ⟨φ, hφ, hφe.symm⟩)
  exact hc.finite hd

/-- **Hadamard–Caccioppoli.**  A proper local homeomorphism from a nonempty `T2` preconnected
space into a real normed space (which is simply connected and locally path-connected) is a
homeomorphism. -/
theorem properLocalHomeo_homeomorph {E X : Type*} [TopologicalSpace E] [T2Space E]
    [PreconnectedSpace E] [NormedAddCommGroup X] [NormedSpace ℝ X] {p : E → X}
    (hp : IsProperMap p) (hl : IsLocalHomeomorph p) [Nonempty E] :
    ∃ e : E ≃ₜ X, ⇑e = p := by
  obtain ⟨e₀⟩ := ‹Nonempty E›
  have hb : Function.Bijective p := cover_bijective (proper_lh_cover hp hl) e₀
  exact ⟨hl.toHomeomorphOfBijective hb, rfl⟩

section Analytic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The local inverse-function chart of a real-analytic map at a point of invertible derivative:
an open partial homeomorphism that agrees with `f`, contains `x` in its source, and whose
inverse is analytic at `f x`. -/
theorem exists_analytic_chart {f : E → F} {x : E} (hf : AnalyticAt ℝ f x)
    (hd : (fderiv ℝ f x).IsInvertible) :
    ∃ e : OpenPartialHomeomorph E F, x ∈ e.source ∧ (⇑e = f) ∧ AnalyticAt ℝ e.symm (f x) := by
  obtain ⟨i, hi⟩ := hd
  have hfd : HasFDerivAt f (i : E →L[ℝ] F) x := by
    rw [hi]; exact (hf.differentiableAt).hasFDerivAt
  have hc : ContDiffAt ℝ ω f x := hf.contDiffAt
  have hmem := hc.mem_toOpenPartialHomeomorph_source hfd (by simp)
  exact ⟨hc.toOpenPartialHomeomorph f hfd (by simp), hmem, rfl,
    (hc.toOpenPartialHomeomorph f hfd (by simp)).analyticAt_symm' hmem hf hi.symm⟩

/-- A real-analytic map with everywhere invertible derivative is a local homeomorphism. -/
theorem isLocalHomeomorph_of_analytic_fderiv {f : E → F} (hf : AnalyticOnNhd ℝ f Set.univ)
    (hd : ∀ x, (fderiv ℝ f x).IsInvertible) : IsLocalHomeomorph f := by
  intro x
  obtain ⟨e, hx, hef, -⟩ := exists_analytic_chart (hf x trivial) (hd x)
  exact ⟨e, hx, hef.symm⟩

/-- **Global analytic inverse.**  A bijective real-analytic map between real Banach spaces
with everywhere invertible derivative has a real-analytic inverse. -/
theorem analytic_inverse_of_global {f : E → F} (hf : AnalyticOnNhd ℝ f Set.univ)
    (hd : ∀ x, (fderiv ℝ f x).IsInvertible) (hb : Function.Bijective f) :
    AnalyticOnNhd ℝ (Equiv.ofBijective f hb).symm Set.univ := by
  intro y _
  set g := Equiv.ofBijective f hb with hg
  obtain ⟨x, rfl⟩ := hb.2 y
  obtain ⟨e, hx, hef, han⟩ := exists_analytic_chart (hf x trivial) (hd x)
  have hev : e.symm =ᶠ[𝓝 (f x)] g.symm := by
    have ht : e.target ∈ 𝓝 (f x) :=
      e.open_target.mem_nhds (by rw [← hef]; exact e.map_source hx)
    filter_upwards [ht] with z hz
    have h1 : f (e.symm z) = z := by rw [← hef]; exact e.right_inv hz
    have h2 : g (e.symm z) = z := h1
    exact (g.symm_apply_eq.mpr h2.symm).symm
  exact han.congr hev
/-- **Assembly.**  A proper real-analytic map between real Banach spaces with everywhere
invertible derivative is a homeomorphism with real-analytic inverse. -/
theorem properAnalytic_homeomorph {f : E → F} (hf : AnalyticOnNhd ℝ f Set.univ)
    (hd : ∀ x, (fderiv ℝ f x).IsInvertible) (hp : IsProperMap f) :
    ∃ e : E ≃ₜ F, ⇑e = f ∧ AnalyticOnNhd ℝ e.symm Set.univ := by
  obtain ⟨e, he⟩ := properLocalHomeo_homeomorph hp (isLocalHomeomorph_of_analytic_fderiv hf hd)
  have hb : Function.Bijective f := he ▸ e.bijective
  refine ⟨e, he, ?_⟩
  have h := analytic_inverse_of_global hf hd hb
  have : ⇑e.symm = ⇑(Equiv.ofBijective f hb).symm := by
    funext y
    apply e.injective
    rw [e.apply_symm_apply, he]
    exact ((Equiv.ofBijective f hb).apply_symm_apply y).symm
  rw [this]; exact h

end Analytic

/-! ## Regression probes -/

section Probes

/-- Probe: for the identity map the homeomorphism of `properLocalHomeo_homeomorph` is the
identity. -/
theorem probe_id_homeomorph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∃ e : E ≃ₜ E, ⇑e = id ∧ ∀ x, e x = x := by
  obtain ⟨e, he⟩ := properLocalHomeo_homeomorph (E := E) (X := E) (p := id) isProperMap_id
    (Homeomorph.refl E).isLocalHomeomorph
  exact ⟨e, he, fun x => by rw [he]; rfl⟩

/-- Probe: the identity map of a Banach space has the identity as analytic inverse. -/
theorem probe_id_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] :
    AnalyticOnNhd ℝ (Equiv.ofBijective (id : E → E) Function.bijective_id).symm Set.univ := by
  refine analytic_inverse_of_global (f := (id : E → E)) analyticOnNhd_id (fun x => ?_)
    Function.bijective_id
  rw [fderiv_id]; exact ContinuousLinearMap.isInvertible_equiv (f := ContinuousLinearEquiv.refl ℝ E)

/-- Probe: a continuous linear isomorphism is proper and a local homeomorphism, the resulting
homeomorphism is the map itself, and the inverse is real-analytic. -/
theorem probe_linear_iso {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (L : E ≃L[ℝ] F) :
    ∃ e : E ≃ₜ F, ⇑e = ⇑L ∧ (∀ x, e x = L x) ∧ AnalyticOnNhd ℝ e.symm Set.univ := by
  have hana : AnalyticOnNhd ℝ (⇑L) Set.univ := fun x _ =>
    (L : E →L[ℝ] F).analyticAt x
  have hd : ∀ x, (fderiv ℝ (⇑L) x).IsInvertible := fun x => by
    rw [L.fderiv]; exact ContinuousLinearMap.isInvertible_equiv
  obtain ⟨e, he, han⟩ := properAnalytic_homeomorph hana hd L.toHomeomorph.isProperMap
  exact ⟨e, he, fun x => by rw [he], han⟩

/-- Probe (nonlinear, explicit value): `x ↦ x³ + x` on `ℝ` is an analytic bijection with
invertible derivative `3x² + 1`; its inverse is analytic and sends `2` to `1` and `0` to `0`. -/
theorem probe_cubic :
    ∃ g : ℝ → ℝ, AnalyticOnNhd ℝ g Set.univ ∧ (∀ x, g (x ^ 3 + x) = x) ∧ g 2 = 1 ∧ g 0 = 0 := by
  set f : ℝ → ℝ := fun x => x ^ 3 + x with hfdef
  have hana : AnalyticOnNhd ℝ f Set.univ := fun x _ => by
    show AnalyticAt ℝ (fun x : ℝ => x ^ 3 + x) x
    fun_prop
  have hder : ∀ x, HasDerivAt f (3 * x ^ 2 + 1) x := fun x => by
    have := ((hasDerivAt_id x).fun_pow 3).add (hasDerivAt_id x)
    convert this using 1
    · funext y; simp [hfdef]
    · simp
  have hd : ∀ x, (fderiv ℝ f x).IsInvertible := fun x => by
    have hne : (3 * x ^ 2 + 1 : ℝ) ≠ 0 := by positivity
    have h1 : fderiv ℝ f x = (3 * x ^ 2 + 1 : ℝ) • (ContinuousLinearMap.id ℝ ℝ) := by
      rw [(hder x).hasFDerivAt.fderiv]
      apply ContinuousLinearMap.ext_ring
      simp
    rw [h1]
    exact ContinuousLinearMap.IsInvertible.of_inverse
      (g := (3 * x ^ 2 + 1 : ℝ)⁻¹ • (ContinuousLinearMap.id ℝ ℝ))
      (by ext; simp [hne]) (by ext; simp [hne])
  have hmono : StrictMono f := fun a b hab => by
    simp only [hfdef]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg a, sq_nonneg b,
      mul_pos (sub_pos.2 hab) (sub_pos.2 hab)]
  have hcont : Continuous f := continuousOn_univ.mp hana.continuousOn
  have htop : Filter.Tendsto f Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono' _ (by
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
      simp only [hfdef, id]; nlinarith [pow_nonneg hx 3]) Filter.tendsto_id
  have hbot : Filter.Tendsto f Filter.atBot Filter.atBot :=
    Filter.tendsto_atBot_mono' _ (by
      filter_upwards [Filter.eventually_le_atBot (0 : ℝ)] with x hx
      simp only [hfdef, id]; nlinarith [Odd.pow_nonpos (by decide : Odd 3) hx]) Filter.tendsto_id
  have hb : Function.Bijective f := ⟨hmono.injective, hcont.surjective htop hbot⟩
  refine ⟨(Equiv.ofBijective f hb).symm, analytic_inverse_of_global hana hd hb, fun x => ?_, ?_, ?_⟩
  · exact (Equiv.ofBijective f hb).symm_apply_apply x
  · rw [Equiv.symm_apply_eq]; show (2 : ℝ) = 1 ^ 3 + 1; norm_num
  · rw [Equiv.symm_apply_eq]; show (0 : ℝ) = 0 ^ 3 + 0; norm_num

end Probes

end NlsGge.GK38.Lib
