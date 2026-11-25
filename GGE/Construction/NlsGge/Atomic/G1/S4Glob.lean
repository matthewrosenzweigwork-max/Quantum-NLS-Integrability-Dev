import Mathlib

                                                                                            
                                                                                                                       
                                                                                                         
set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.Atomic.G1081S4Glob
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem forward_analytic (φ : ℝ → E → E)
    (hgrp : ∀ s t v, φ (s + t) v = φ s (φ t v))
    (hcont : ∀ v, Continuous (fun t => φ t v))
    (hloc : ∀ w, AnalyticAt ℝ (fun p : ℝ × E => φ p.1 p.2) (0, w)) (u1 : E) :
    ∀ T : ℝ, 0 ≤ T → ∀ s ∈ Icc (0 : ℝ) T, AnalyticAt ℝ (fun p : ℝ × E => φ p.1 p.2) (s, u1) := by
  set Φ : ℝ × E → E := fun p => φ p.1 p.2 with hΦ
  let S : Set ℝ := {T | 0 ≤ T ∧ ∀ s ∈ Icc (0 : ℝ) T, AnalyticAt ℝ Φ (s, u1)}
  have hS0 : (0 : ℝ) ∈ S := by
    refine ⟨le_rfl, fun s hs => ?_⟩
    have : s = 0 := le_antisymm hs.2 hs.1
    subst this; exact hloc u1
  have hSdown : ∀ T ∈ S, ∀ T' : ℝ, 0 ≤ T' → T' ≤ T → T' ∈ S :=
    fun T hT T' h0 hle => ⟨h0, fun s hs => hT.2 s ⟨hs.1, hs.2.trans hle⟩⟩
  suffices h : ∀ T : ℝ, 0 ≤ T → T ∈ S from fun T hT s hs => (h T hT).2 s hs
  by_contra hcon
  push_neg at hcon
  obtain ⟨T1, hT1, hT1S⟩ := hcon
  have hbdd : BddAbove S := ⟨T1, fun T hT => by
    by_contra hlt
    push_neg at hlt
    exact hT1S (hSdown T hT T1 hT1 hlt.le)⟩
  set Ts := sSup S with hTs
  have hTs0 : 0 ≤ Ts := le_csSup hbdd hS0
  set ws := φ Ts u1 with hws
  have hev : ∀ᶠ q in 𝓝 ((0 : ℝ), ws), AnalyticAt ℝ Φ q := (hloc ws).eventually_analyticAt
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hev
  obtain ⟨δ, hδ, hδA⟩ := Metric.mem_nhds_iff.mp hA
  have hcw : Tendsto (fun t => φ t u1) (𝓝 Ts) (𝓝 ws) := (hcont u1).tendsto Ts
  have hBev : ∀ᶠ t in 𝓝 Ts, φ t u1 ∈ B := hcw.eventually hB
  obtain ⟨η, hη, hηB⟩ := Metric.eventually_nhds_iff.mp hBev
  obtain ⟨s0, hs0S, hs0lt⟩ := exists_lt_of_lt_csSup ⟨0, hS0⟩
    (show Ts - min η (δ / 2) < Ts by
      have : 0 < min η (δ / 2) := lt_min hη (by linarith)
      linarith)
  have hs0le : s0 ≤ Ts := le_csSup hbdd hs0S
  have hη' : min η (δ / 2) ≤ η := min_le_left _ _
  have hδ' : min η (δ / 2) ≤ δ / 2 := min_le_right _ _
  have hs0B : φ s0 u1 ∈ B := by
    apply hηB
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hφs0 : AnalyticAt ℝ (φ s0) u1 := by
    have h1 : AnalyticAt ℝ (fun v : E => ((s0, v) : ℝ × E)) u1 :=
      analyticAt_const.prod analyticAt_id
    exact (hs0S.2 s0 ⟨hs0S.1, le_rfl⟩).comp h1
  have hbig : Ts + δ / 2 ∈ S := by
    refine ⟨by linarith, fun s hs => ?_⟩
    by_cases hss : s ≤ s0
    · exact hs0S.2 s ⟨hs.1, hss⟩
    · push_neg at hss
      have hmem : (s - s0, φ s0 u1) ∈ A ×ˢ B := by
        refine ⟨?_, hs0B⟩
        apply hδA
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
        constructor <;> linarith [hs.2]
      have hΦa : AnalyticAt ℝ Φ (s - s0, φ s0 u1) := hAB hmem
      have hin : AnalyticAt ℝ (fun p : ℝ × E => (p.1 - s0, φ s0 p.2)) (s, u1) :=
        (analyticAt_fst.sub analyticAt_const).prod (hφs0.comp analyticAt_snd)
      have hcomp : AnalyticAt ℝ (Φ ∘ fun p : ℝ × E => (p.1 - s0, φ s0 p.2)) (s, u1) :=
        AnalyticAt.comp (g := Φ) (f := fun p : ℝ × E => (p.1 - s0, φ s0 p.2)) hΦa hin
      refine hcomp.congr (Eventually.of_forall fun p => ?_)
      simp only [Function.comp, hΦ]
      rw [← hgrp]; congr 1; ring
  have := le_csSup hbdd hbig
  linarith [hδ]

theorem analytic_of_local_flow (φ : ℝ → E → E)
    (hgrp : ∀ s t v, φ (s + t) v = φ s (φ t v))
    (hcont : ∀ v, Continuous (fun t => φ t v))
    (hloc : ∀ w, AnalyticAt ℝ (fun p : ℝ × E => φ p.1 p.2) (0, w)) :
    AnalyticOnNhd ℝ (fun p : ℝ × E => φ p.1 p.2) univ := by
  intro ⟨t, u⟩ _
  rcases le_total 0 t with ht | ht
  · exact forward_analytic φ hgrp hcont hloc u t ht t ⟨ht, le_rfl⟩
  · have hgrp' : ∀ s t v, (fun r v => φ (-r) v) (s + t) v =
        (fun r v => φ (-r) v) s ((fun r v => φ (-r) v) t v) := by
      intro s t v
      simp only
      rw [show -(s + t) = -s + -t by ring]
      exact hgrp _ _ _
    have hcont' : ∀ v, Continuous (fun t => (fun r v => φ (-r) v) t v) := fun v =>
      (hcont v).comp continuous_neg
    have hloc' : ∀ w, AnalyticAt ℝ
        (fun p : ℝ × E => (fun r v => φ (-r) v) p.1 p.2) (0, w) := by
      intro w
      have h1 : AnalyticAt ℝ (fun p : ℝ × E => ((-p.1, p.2) : ℝ × E)) (0, w) :=
        (analyticAt_fst.neg).prod analyticAt_snd
      have h2 : AnalyticAt ℝ (fun p : ℝ × E => φ p.1 p.2) (-(0:ℝ), w) := by
        rw [neg_zero]; exact hloc w
      exact AnalyticAt.comp (g := fun p : ℝ × E => φ p.1 p.2) (f := fun p : ℝ × E => ((-p.1, p.2) : ℝ × E)) h2 h1
    have hf := forward_analytic (fun r v => φ (-r) v) hgrp' hcont' hloc' u (-t) (by linarith)
      (-t) ⟨by linarith, le_rfl⟩
    have h1 : AnalyticAt ℝ (fun p : ℝ × E => ((-p.1, p.2) : ℝ × E)) (t, u) :=
      (analyticAt_fst.neg).prod analyticAt_snd
    have h3 : AnalyticAt ℝ ((fun p : ℝ × E => φ (-p.1) p.2) ∘ fun p : ℝ × E => ((-p.1, p.2) : ℝ × E)) (t, u) :=
      AnalyticAt.comp (g := fun p : ℝ × E => φ (-p.1) p.2) (f := fun p : ℝ × E => ((-p.1, p.2) : ℝ × E)) (by simpa using hf) h1
    refine h3.congr (Eventually.of_forall fun p => ?_)
    simp

end
end NlsGge.Atomic.G1081S4Glob
