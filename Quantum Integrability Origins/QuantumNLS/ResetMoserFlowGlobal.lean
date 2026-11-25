import QuantumNLS.ResetMoserFlowLocal
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# `thm:reset-moser` (LOCAL-017), stage 2b-ii: all-time differentiability of the flow in the initial point, and the variational equation

Continuation of `ResetMoserFlowLocal` (read-only import). For `H : FlowOn f φ U` (flow of a `C¹` field on an open set, solutions
for initial points of `U`):

* `lip_on_compact`: a `C¹` field on an open set is Lipschitz on every compact subset;
* `group_law`: `φ (s + h) v = φ h (φ s v)` for `v ∈ U` (uniqueness of the ODE on the compact union of the two trajectories,
  mathlib `ODE_solution_unique_of_mem_Icc`);
* `FlowOn.rev`: the time-reversed flow `φ (−t)` of `−f`;
* `diffAt_nonneg`/`diffAt`: for `z ∈ U` and **every** real `t`, `φ t` is Fréchet differentiable at `z` (continuation along the
  compact trajectory from the short-time `local_diff_on`, via the group law; negative times by the reversed flow);
* `fderiv_group`: `Dφ^{s+t}(z) = Dφ^t(φ^s z) ∘ Dφ^s(z)`;
* `variational`: **the variational equation** `d/ds Dφ^s(z) = Df(φ^s z) ∘ Dφ^s(z)` (two-sided, every `s`).

The source: "The full variational equation and Gronwall's inequality" and "variation of the integral of a one-form along this
loop" (`symplectic_correction.tex`, periods subsection and invariant-ball subsection).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Filter Topology Set Metric
open scoped NNReal

noncomputable section

namespace QuantumNLS.ResetMoserFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {f : E → E} {φ : ℝ → E → E} {U : Set E}

omit [CompleteSpace E] in
theorem lip_on_compact {f : E → E} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) {Kc : Set E}
    (hK : IsCompact Kc) (hKU : Kc ⊆ U) : ∃ L : ℝ≥0, LipschitzOnWith L f Kc := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
  intro x hx
  obtain ⟨K, t, ht, hlip⟩ := (hf.contDiffAt (hU.mem_nhds (hKU hx))).exists_lipschitzOnWith
  exact ⟨K, t, nhdsWithin_le_nhds ht, hlip⟩

omit [CompleteSpace E] in
theorem FlowOn.continuous_time (H : FlowOn f φ U) {v : E} (hv : v ∈ U) : Continuous (fun s => φ s v) :=
  continuous_iff_continuousAt.2 fun s => (H.deriv v hv s).continuousAt

/-- The group law of the flow. -/
theorem group_law (H : FlowOn f φ U) {v : E} (hv : v ∈ U) (s h : ℝ) : φ (s + h) v = φ h (φ s v) := by
  set T : ℝ := |h| + 1 with hT
  have hT0 : 0 < T := by positivity
  have hsU : φ s v ∈ U := H.mem v hv s
  have hc1 : Continuous (fun t => φ (s + t) v) := (H.continuous_time hv).comp (continuous_const.add continuous_id)
  have hc2 : Continuous (fun t => φ t (φ s v)) := H.continuous_time hsU
  have hd1 : ∀ t, HasDerivAt (fun t => φ (s + t) v) (f (φ (s + t) v)) t := fun t =>
    HasDerivAt.comp_const_add s t (H.deriv v hv (s + t))
  have hd2 : ∀ t, HasDerivAt (fun t => φ t (φ s v)) (f (φ t (φ s v))) t := fun t => H.deriv _ hsU t
  set Kc : Set E := (fun t => φ (s + t) v) '' Icc (-T) T ∪ (fun t => φ t (φ s v)) '' Icc (-T) T with hKc
  have hKcomp : IsCompact Kc := (isCompact_Icc.image hc1).union (isCompact_Icc.image hc2)
  have hKU : Kc ⊆ U := by
    rintro x (⟨t, -, rfl⟩ | ⟨t, -, rfl⟩)
    · exact H.mem v hv _
    · exact H.mem _ hsU _
  obtain ⟨L, hL⟩ := lip_on_compact H.isOpen H.cd hKcomp hKU
  have hEq := ODE_solution_unique_of_mem_Icc (v := fun _ z => f z) (s := fun _ => Kc) (K := L)
    (f := fun t => φ (s + t) v) (g := fun t => φ t (φ s v)) (a := -T) (b := T) (t₀ := 0)
    (fun _ _ => hL) (by constructor <;> linarith) hc1.continuousOn (fun t _ => hd1 t)
    (fun t ht => Or.inl ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩) hc2.continuousOn (fun t _ => hd2 t)
    (fun t ht => Or.inr ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩) (by simp [H.zero _ hsU])
  have hh : h ∈ Icc (-T) T := ⟨by have := neg_abs_le h; linarith, by have := le_abs_self h; linarith⟩
  exact hEq hh

/-- The time-reversed flow. -/
theorem FlowOn.rev (H : FlowOn f φ U) : FlowOn (fun v => -f v) (fun t v => φ (-t) v) U where
  isOpen := H.isOpen
  cd := H.cd.neg
  deriv := fun v hv t => by
    have h := (H.deriv v hv (-t)).scomp t (hasDerivAt_neg t)
    exact h.congr_deriv (by simp)
  mem := fun v hv t => H.mem v hv (-t)
  zero := fun v hv => by simpa using H.zero v hv

/-- Differentiability for nonnegative times (continuation along the trajectory). -/
theorem diffAt_nonneg (H : FlowOn f φ U) {z : E} (hz : z ∈ U) (t0 : ℝ) (ht0 : 0 ≤ t0) :
    DifferentiableAt ℝ (φ t0) z := by
  by_contra hbad
  let S : Set ℝ := {T | 0 ≤ T ∧ ∀ t ∈ Icc 0 T, DifferentiableAt ℝ (φ t) z}
  have h0 : (0 : ℝ) ∈ S := by
    refine ⟨le_rfl, fun t ht => ?_⟩
    have : t = 0 := le_antisymm ht.2 ht.1
    subst this
    have : φ 0 =ᶠ[𝓝 z] id := Filter.eventuallyEq_of_mem (H.isOpen.mem_nhds hz) (fun v hv => H.zero v hv)
    exact (differentiableAt_id.congr_of_eventuallyEq this)
  have hbdd : BddAbove S := by
    refine ⟨t0, fun T hT => ?_⟩
    by_contra hlt
    exact hbad (hT.2 t0 ⟨ht0, (not_le.1 hlt).le⟩)
  set Ts := sSup S with hTs
  have hTs0 : 0 ≤ Ts := le_csSup hbdd h0
  set p := φ Ts z with hp
  have hpU : p ∈ U := H.mem z hz Ts
  obtain ⟨ρ, hρ, τ, hτ, hJ⟩ := local_diff_on H hpU
  have hcont := H.continuous_time hz
  obtain ⟨δ, hδ, hδb⟩ := Metric.continuousAt_iff.1 (hcont.continuousAt (x := Ts)) ρ hρ
  set ε' : ℝ := min δ τ / 2 with hε'
  have hε'0 : 0 < ε' := by have := lt_min hδ hτ; positivity
  have hε'δ : ε' < δ := by have := min_le_left δ τ; have := lt_min hδ hτ; linarith
  have hε'τ : ε' ≤ τ / 2 := by have := min_le_right δ τ; linarith
  obtain ⟨s0, hs0S, hs0⟩ := exists_lt_of_lt_csSup ⟨0, h0⟩ (show Ts - ε' < Ts by linarith)
  have hs0le : s0 ≤ Ts := le_csSup hbdd hs0S
  have hdist : dist s0 Ts < δ := by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  have hu : φ s0 z ∈ ball p ρ := mem_ball.2 (hδb hdist)
  obtain ⟨J, -, -, -, hJf⟩ := hJ (φ s0 z) hu
  have hmem : s0 + τ ∈ S := by
    refine ⟨by linarith [hs0S.1], fun t ht => ?_⟩
    by_cases hts : t ≤ s0
    · exact hs0S.2 t ⟨ht.1, hts⟩
    · have ht' : t - s0 ∈ Icc 0 τ := ⟨by linarith, by linarith [ht.2]⟩
      have hd1 : DifferentiableAt ℝ (φ (t - s0)) (φ s0 z) := (hJf _ ht').differentiableAt
      have hd2 : DifferentiableAt ℝ (φ s0) z := hs0S.2 s0 ⟨hs0S.1, le_rfl⟩
      have heq : φ t =ᶠ[𝓝 z] fun v => φ (t - s0) (φ s0 v) :=
        Filter.eventuallyEq_of_mem (H.isOpen.mem_nhds hz) (fun v hv => by
          have := group_law H hv s0 (t - s0)
          rwa [add_sub_cancel] at this)
      exact (hd1.comp z hd2).congr_of_eventuallyEq heq
  have hle : s0 + τ ≤ Ts := le_csSup hbdd hmem
  linarith

theorem diffAt (H : FlowOn f φ U) {z : E} (hz : z ∈ U) (t : ℝ) : DifferentiableAt ℝ (φ t) z := by
  rcases le_total 0 t with h | h
  · exact diffAt_nonneg H hz t h
  · have := diffAt_nonneg H.rev hz (-t) (by linarith)
    simpa using this

theorem fderiv_group (H : FlowOn f φ U) {z : E} (hz : z ∈ U) (s t : ℝ) :
    fderiv ℝ (φ (s + t)) z = (fderiv ℝ (φ t) (φ s z)).comp (fderiv ℝ (φ s) z) := by
  have heq : φ (s + t) =ᶠ[𝓝 z] fun v => φ t (φ s v) :=
    Filter.eventuallyEq_of_mem (H.isOpen.mem_nhds hz) (fun v hv => group_law H hv s t)
  rw [heq.fderiv_eq]
  exact fderiv_comp z (diffAt H (H.mem z hz s) t) (diffAt H hz s)

theorem variational_right (H : FlowOn f φ U) {z : E} (hz : z ∈ U) (s : ℝ) :
    HasDerivWithinAt (fun r => fderiv ℝ (φ r) z) ((fderiv ℝ f (φ s z)).comp (fderiv ℝ (φ s) z))
      (Ici s) s := by
  have hu : φ s z ∈ U := H.mem z hz s
  obtain ⟨ρ, hρ, τ, hτ, hJ⟩ := local_diff_on H hu
  obtain ⟨J, hJc, hJ0, hJd, hJf⟩ := hJ (φ s z) (mem_ball_self hρ)
  set A := fderiv ℝ (φ s) z with hA
  have hF : ∀ r ∈ Icc s (s + τ), fderiv ℝ (φ r) z = (J (r - s)).comp A := by
    intro r hr
    have ht : r - s ∈ Icc 0 τ := ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have := fderiv_group H hz s (r - s)
    rw [add_sub_cancel] at this
    rw [this, (hJf _ ht).fderiv]
  have h1 : HasDerivWithinAt J ((fderiv ℝ f (φ s z)).comp (ContinuousLinearMap.id ℝ E)) (Icc 0 τ) 0 := by
    have := hJd 0 ⟨le_rfl, hτ.le⟩
    rwa [H.zero _ hu, hJ0] at this
  have h1' : HasDerivWithinAt J ((fderiv ℝ f (φ s z)).comp (ContinuousLinearMap.id ℝ E)) (Icc 0 τ) (s - s) := by
    rwa [sub_self]
  have h2 : HasDerivWithinAt (fun r : ℝ => r - s) 1 (Icc s (s + τ)) s :=
    ((hasDerivAt_id s).sub_const s).hasDerivWithinAt
  have h3 := HasDerivWithinAt.scomp (h := fun r : ℝ => r - s) s h1' h2
    (fun r hr => (⟨by linarith [hr.1], by linarith [hr.2]⟩ : r - s ∈ Icc 0 τ))
  have h4 := h3.clm_comp (hasDerivWithinAt_const s (Icc s (s + τ)) A)
  have h5 : HasDerivWithinAt (fun r => fderiv ℝ (φ r) z) ((fderiv ℝ f (φ s z)).comp A) (Icc s (s + τ)) s := by
    refine (h4.congr_deriv ?_).congr (fun r hr => hF r hr) (hF s ⟨le_rfl, by linarith⟩)
    simp [hJ0]
  exact h5.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE (by linarith))

/-- **The variational equation**, two-sided. -/
theorem variational (H : FlowOn f φ U) {z : E} (hz : z ∈ U) (s : ℝ) :
    HasDerivAt (fun r => fderiv ℝ (φ r) z) ((fderiv ℝ f (φ s z)).comp (fderiv ℝ (φ s) z)) s := by
  have hR := variational_right H hz s
  have hRev := variational_right H.rev hz (-s)
  have h2 := hRev.scomp s (hasDerivAt_neg s).hasDerivWithinAt
    (fun r (hr : r ∈ Iic s) => (by simpa using hr : -r ∈ Ici (-s)))
  have hL : HasDerivWithinAt (fun r => fderiv ℝ (φ r) z)
      ((fderiv ℝ f (φ s z)).comp (fderiv ℝ (φ s) z)) (Iic s) s := by
    refine (h2.congr_deriv ?_).congr (fun r _ => ?_) ?_
    · simp [fderiv_neg]
    · simp
    · simp
  have := hL.union hR
  rw [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this
  exact this

end QuantumNLS.ResetMoserFlow

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoserFlow.lip_on_compact
#print axioms QuantumNLS.ResetMoserFlow.group_law
#print axioms QuantumNLS.ResetMoserFlow.diffAt
#print axioms QuantumNLS.ResetMoserFlow.fderiv_group
#print axioms QuantumNLS.ResetMoserFlow.variational
