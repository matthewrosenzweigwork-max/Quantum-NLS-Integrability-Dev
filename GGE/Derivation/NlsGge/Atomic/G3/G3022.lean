import Mathlib
import NlsGge.ThirdConsultation.G3.G3022Support
import NlsGge.Atomic.G3.G3016
import NlsGge.Atomic.G3.G3017
import NlsGge.Atomic.G4.G4008
import NlsGge.Atomic.G4.G4009
import NlsGge.GK38.TauGammaSpectralDerivatives
import NlsGge.GK38.AngleDirichletAnalytic

/- G3_022 PRODUCTION01 (proof development, AUTHOR; not semantically reviewed by its author).
   Target NlsGge/Atomic/G3/G3022.lean, namespace NlsGge.GKDefinitionDesign.
   Head VERBATIM from followup8 design STATEMENTS/G3.md:357-368 (rounds 9/10 do not touch G3-022; same text in followup7/5).
   Route (source GK 15.2 p. 84 last paragraph; see G3022_ROUTE.md; the analytic anchor gkSourceBeta_analytic38 is not used here):
   (1) zero conjunct: G3_016 value zero at endpointSet.
   (2) if every point of the disc is an endpoint, beta = 0 on the disc (analytic).  Otherwise the analytic function
       E z = perChar (a+zv) (mu (a+zv)) is not identically zero on the disc, so (landed G4-008) its zero set is finite on every
       compact subdisc, i.e. locally finite in the disc.
   (3) off the zeros: G3_017 gives beta = r0 * collapsedBetaFinalSegment locally with r0 locally constant; the segment integral is
       analytic in z by G3022Support.J_analytic (landed G4-012 parameter integral).
   (4) continuity on the disc: analytic off the zeros, and G3_016 ContinuousAt at the zeros.
   (5) landed G4-009 removable singularities gives analyticity on the whole disc.  No hypothesis beyond the head. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G3_022 (n m : ℤ) (hmn : m ≠ n) (a v : PotPair) (c : ℂ) (r : ℝ)
    (hr : 0 < r)
    (hd : ∀ z ∈ ball c r, a+z • v ∈ collapsedSet m) :
  AnalyticOnNhd ℂ (fun z : ℂ => offDiagonalBeta n m (a+z • v)) (ball c r) ∧
  ((∀ z ∈ ball c r, a+z • v ∈ endpointSet m) →
    ∀ z ∈ ball c r, offDiagonalBeta n m (a+z • v) = 0) := by
  have hzero : (∀ z ∈ ball c r, a+z • v ∈ endpointSet m) →
      ∀ z ∈ ball c r, offDiagonalBeta n m (a+z • v) = 0 :=
    fun h z hz => (G3_016 n m hmn _ (h z hz)).1
  refine ⟨?_, hzero⟩
  have hφc : Continuous (fun z : ℂ => a + z • v) := by fun_prop
  have hφA : ∀ z : ℂ, AnalyticAt ℂ (fun z : ℂ => a + z • v) z := fun z =>
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  by_cases hall : ∀ z ∈ ball c r, a + z • v ∈ endpointSet m
  · have h0 := hzero hall
    exact (analyticOnNhd_const (v := (0 : ℂ))).congr isOpen_ball (fun z hz => (h0 z hz).symm)
  · push Not at hall
    obtain ⟨z1, hz1, hz1n⟩ := hall
    have hE : AnalyticOnNhd ℂ
        (fun z : ℂ => perChar (a + z • v) (muSeq (a + z • v) m)) (ball c r) := by
      intro z hz
      have hgk : a + z • v ∈ gkW := sourceFamily.W_gk (hd z hz).1
      have hμ : AnalyticAt ℂ (fun z : ℂ => muSeq (a + z • v) m) z :=
        AnalyticAt.comp (g := fun φ : PotPair => muSeq φ m) (f := fun z : ℂ => a + z • v)
          (analyticOnNhd_muSeq_complex38 m _ hgk) (hφA z)
      exact AnalyticAt.comp (g := fun p : PotPair × ℂ => perChar p.1 p.2)
        (f := fun z : ℂ => (a + z • v, muSeq (a + z • v) m))
        (analyticOnNhd_perChar_joint38 _ (mem_univ _)) ((hφA z).prod hμ)
    have hEnz : ∃ z ∈ ball c r, perChar (a + z • v) (muSeq (a + z • v) m) ≠ 0 :=
      ⟨z1, hz1, fun h => hz1n ⟨(hd z1 hz1).1, h⟩⟩
    have hfin : NlsGge.Atomic.G4009.LocallyFiniteWithin (ball c r)
        {z | perChar (a + z • v) (muSeq (a + z • v) m) = 0} := by
      intro z hz
      obtain ⟨ρ, hρ, hb⟩ := Metric.isOpen_iff.1 isOpen_ball z hz
      have hρ2 : 0 < ρ / 2 := by positivity
      refine ⟨closedBall z (ρ / 2), closedBall_mem_nhds z hρ2, ?_⟩
      have hF := NlsGge.Atomic.G4.analytic_disc_zeros_finite_on_compact hr hE
        (isCompact_closedBall z (ρ / 2))
        (fun w hw => hb (closedBall_subset_ball (by linarith) hw)) hEnz
      exact hF.subset (fun w hw => ⟨hw.1, hw.2.2⟩)
    have han : AnalyticOnNhd ℂ (fun z : ℂ => offDiagonalBeta n m (a + z • v))
        (ball c r \ {z | perChar (a + z • v) (muSeq (a + z • v) m) = 0}) := by
      intro z0 hz0
      obtain ⟨hz0b, hz0S⟩ := hz0
      have hz0c : a + z0 • v ∈ collapsedSet m \ endpointSet m :=
        ⟨hd z0 hz0b, fun h => hz0S h.2⟩
      obtain ⟨-, -, -, -, V, hVo, hφV, hVW, hV⟩ := G3_017 n m hmn _ hz0c
      set N : Set ℂ := ball c r ∩ (fun z : ℂ => a + z • v) ⁻¹' V with hNdef
      have hNo : IsOpen N := isOpen_ball.inter (hVo.preimage hφc)
      have hz0N : z0 ∈ N := ⟨hz0b, hφV⟩
      have hNc : ∀ z ∈ N, a + z • v ∈ collapsedSet m \ endpointSet m := fun z hz =>
        ⟨hd z hz.1, fun h => (hVW hz.2).2 h⟩
      have hJ := G3022Aux.J_analytic n m hmn a v N hNo hNc
      have hlin : AnalyticOnNhd ℂ (fun z : ℂ => offDiagonalBeta n m (a + z • v)) N := by
        refine ((analyticOnNhd_const (v :=
          antiDiscrim (a + z0 • v) (muSeq (a + z0 • v) m) /
            canonRoot38 (a + z0 • v) (muSeq (a + z0 • v) m))).mul hJ).congr hNo ?_
        intro z hz
        have h4 := (G3_017 n m hmn _ (hNc z hz)).2.2.2.1
        have h5 := (hV (a + z • v) ⟨hz.2, (hNc z hz).1⟩).2
        beta_reduce
        rw [h4, h5]
      exact hlin z0 hz0N
    have hcont : ContinuousOn (fun z : ℂ => offDiagonalBeta n m (a + z • v)) (ball c r) := by
      intro z hz
      by_cases hS : perChar (a + z • v) (muSeq (a + z • v) m) = 0
      · have h := (G3_016 n m hmn _ ⟨(hd z hz).1, hS⟩).2.2
        have h' : ContinuousAt (fun z : ℂ => offDiagonalBeta n m (a + z • v)) z :=
          ContinuousAt.comp (g := offDiagonalBeta n m) (f := fun z : ℂ => a + z • v) h
            hφc.continuousAt
        exact h'.continuousWithinAt
      · exact (han z ⟨hz, hS⟩).continuousAt.continuousWithinAt
    exact NlsGge.Atomic.G4009.analyticOnNhd_of_continuousOn_of_locallyFiniteWithin
      isOpen_ball hcont hfin han

end
end NlsGge.GKDefinitionDesign
