import Mathlib
import NlsGge.Hierarchy.ALFreeDeterminant38
/- AL-090 PRODUCTION01 (proof development landing kit; HELD for landing). Source: proof development/AL-090_PROOF02_RUN01.lean (author proof development; independent review proof development/REVIEW_BATCH_AL_LIB01.md), byte-identical except this header and the removed `#print axioms` line plus the appended wrapper theorem.
   Target NlsGge/Atomic/AL/AL090.lean. -/

/- AL-090 PROOF01 (proof development). Pro's statement (STATEMENTS/AL.md, AL-090), verbatim; no elaboration adaptation.
   Route: clause 1 is alFreeDetIntegrand_continuous38; clause 2 from alMeshStep_tendsto38 since N h = 1/2 - h/2;
   clause 3 is alRiemann_tendsto38 (scaled by 8); clause 4 is the continuity of the primitive x -> int_0^x g. No sorry. -/

set_option autoImplicit false

open NlsGge.AblowitzLadik Filter Topology MeasureTheory

namespace NlsGge.Atomic.AL.AL090

theorem al090_helper :
    Continuous alFreeDetIntegrand38 ∧
    Tendsto (fun N : ℕ => (N : ℝ) * alMeshStep38 N) atTop (𝓝 (1 / 2 : ℝ)) ∧
    Tendsto (fun N : ℕ => 8 * alMeshStep38 N *
      ∑ k ∈ Finset.Icc 1 N, alFreeDetIntegrand38 ((k : ℝ) * alMeshStep38 N))
      atTop (𝓝 (8 * ∫ x in (0 : ℝ)..1 / 2, alFreeDetIntegrand38 x)) ∧
    Tendsto (fun N : ℕ =>
      ∫ x in ((N : ℝ) * alMeshStep38 N)..(1 / 2 : ℝ), alFreeDetIntegrand38 x)
      atTop (𝓝 0) := by
  have hc : Continuous alFreeDetIntegrand38 := alFreeDetIntegrand_continuous38
  have hmesh := alMeshStep_tendsto38
  have h2 : Tendsto (fun N : ℕ => (N : ℝ) * alMeshStep38 N) atTop (𝓝 (1 / 2 : ℝ)) := by
    have h0 : Tendsto (fun N : ℕ => (1 / 2 : ℝ) - (1 / 2) * alMeshStep38 N) atTop
        (𝓝 ((1 / 2 : ℝ) - (1 / 2) * 0)) :=
      tendsto_const_nhds.sub (hmesh.const_mul (1 / 2))
    rw [mul_zero, sub_zero] at h0
    refine Tendsto.congr (fun N => ?_) h0
    unfold alMeshStep38
    field_simp
    ring
  have h3 : Tendsto (fun N : ℕ => 8 * alMeshStep38 N *
      ∑ k ∈ Finset.Icc 1 N, alFreeDetIntegrand38 ((k : ℝ) * alMeshStep38 N))
      atTop (𝓝 (8 * ∫ x in (0 : ℝ)..1 / 2, alFreeDetIntegrand38 x)) := by
    have h0 := (alRiemann_tendsto38 alFreeDetIntegrand38 hc).const_mul 8
    refine Tendsto.congr (fun N => ?_) h0
    ring
  have hFc : Continuous (fun x : ℝ => ∫ t in (0 : ℝ)..x, alFreeDetIntegrand38 t) :=
    intervalIntegral.continuous_primitive (fun a b => hc.intervalIntegrable a b) 0
  have h4 : Tendsto (fun N : ℕ =>
      ∫ x in ((N : ℝ) * alMeshStep38 N)..(1 / 2 : ℝ), alFreeDetIntegrand38 x) atTop (𝓝 0) := by
    have hT : Tendsto (fun N : ℕ => ∫ t in (0 : ℝ)..((N : ℝ) * alMeshStep38 N), alFreeDetIntegrand38 t)
        atTop (𝓝 (∫ t in (0 : ℝ)..(1 / 2 : ℝ), alFreeDetIntegrand38 t)) :=
      (hFc.tendsto (1 / 2 : ℝ)).comp h2
    have hS := (tendsto_const_nhds (x := ∫ t in (0 : ℝ)..(1 / 2 : ℝ), alFreeDetIntegrand38 t)).sub hT
    rw [sub_self] at hS
    refine Tendsto.congr (fun N => ?_) hS
    exact intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
  exact ⟨hc, h2, h3, h4⟩

end NlsGge.Atomic.AL.AL090

namespace NlsGge.ThirdConsultation.AL

open NlsGge.AblowitzLadik Filter Topology MeasureTheory

theorem al090 :
    Continuous alFreeDetIntegrand38 ∧
    Tendsto (fun N : ℕ => (N : ℝ) * alMeshStep38 N) atTop (𝓝 (1 / 2 : ℝ)) ∧
    Tendsto (fun N : ℕ => 8 * alMeshStep38 N *
      ∑ k ∈ Finset.Icc 1 N, alFreeDetIntegrand38 ((k : ℝ) * alMeshStep38 N))
      atTop (𝓝 (8 * ∫ x in (0 : ℝ)..1 / 2, alFreeDetIntegrand38 x)) ∧
    Tendsto (fun N : ℕ =>
      ∫ x in ((N : ℝ) * alMeshStep38 N)..(1 / 2 : ℝ), alFreeDetIntegrand38 x)
      atTop (𝓝 0) :=
  NlsGge.Atomic.AL.AL090.al090_helper

end NlsGge.ThirdConsultation.AL
