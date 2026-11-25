import Mathlib
import NlsGge.Atomic.M.M011
import NlsGge.Atomic.M.M012

/- M-013 PRODUCTION01 (proof development, AUTHOR; not reviewed).  Head VERBATIM from Pro round 14
   (PRO_DEFINITION_RESPONSE_FP80_14.md, cluster 7, "### M-013").
   Route (Molnar Lemma 3(i), Appendix A): at every point of the cut-free domain the landed primitive has a local analytic
   representative in ψ at fixed z (noncollapsed base gap: M011Support2.base_good; collapsed: M012Support1.base_good_collapsed;
   both propagated by M011Support1.good_of_good).  The joint representative is
   `F (ψ, w) = F0 ψ + (w - z0) ∫_0^1 omega ψ (z0 + s (w - z0)) ds`, jointly analytic by the landed segment-integral
   analyticity (G4022) and equal to the primitive by the cut-free FTC (M011Support1.primitive_sub_eq_integral).
   This replaces the removable-extension step of the source by an explicit analytic formula at collapsed gaps;
   see M013_ROUTE.md. -/
set_option autoImplicit false
open Set Filter MeasureTheory Metric
open scoped Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M

theorem primitive_analytic :
    ∀ p : PotPair × ℂ, p ∈ primitiveDomain →
      ∃ (U : Set (PotPair × ℂ)) (hU : IsOpen U), p ∈ U ∧
        ∃ F : PotPair × ℂ → ℂ,
          U ⊆ primitiveDomain ∧
          (∀ q : PotPair × ℂ, ∀ hq : q ∈ U,
            ∃ hp : q.1 ∈ gkW ∧ q.2 ∈ MPrimitive.endpointClosureFiber q.1,
              F q = primitive ⟨q, hp⟩) ∧
          AnalyticOnNhd ℂ F U := by
  intro p hpd
  have hd : p ∈ rootDomain38 := hpd
  have hg : M011Aux.Good p.1 p.2 := by
    by_cases hgap : lamPlus p.1 0 - lamMinus p.1 0 = 0
    · obtain ⟨z1, hz1, hg1⟩ := M012Aux.base_good_collapsed p.1 hd.1 hgap
      exact M011Aux.good_of_good hd.1 hz1 hd.2 hg1
    · obtain ⟨z1, hz1, hg1⟩ := M011Aux.base_good p.1 hd.1 hgap
      exact M011Aux.good_of_good hd.1 hz1 hd.2 hg1
  obtain ⟨V, hV, hφV, F0, hF0, hF0an⟩ := hg
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_rootDomain38 p hd
  have hb : ball p.1 ε ×ˢ ball p.2 ε ⊆ rootDomain38 := by rw [ball_prod_same]; exact hball
  set U : Set (PotPair × ℂ) := (V ∩ ball p.1 ε) ×ˢ ball p.2 ε with hUdef
  have hUo : IsOpen U := (hV.inter isOpen_ball).prod isOpen_ball
  have hpU : p ∈ U := ⟨⟨hφV, mem_ball_self hε⟩, mem_ball_self hε⟩
  have hseg : ∀ q ∈ U, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      (q.1, p.2 + (s : ℂ) * (q.2 - p.2)) ∈ rootDomain38 := by
    intro q hq s hs
    refine hb ⟨hq.1.2, ?_⟩
    have := (convex_ball p.2 ε).add_smul_sub_mem (mem_ball_self hε) hq.2 hs
    simpa [Complex.real_smul] using this
  have hH : AnalyticOnNhd ℂ (fun x : (PotPair × ℂ) × ℂ => MContour.omega x.1.1 x.2)
      {x : (PotPair × ℂ) × ℂ | (x.1.1, x.2) ∈ rootDomain38} := fun x hx =>
    AnalyticAt.comp (g := fun q : PotPair × ℂ => MContour.omega q.1 q.2)
      (f := fun x : (PotPair × ℂ) × ℂ => (x.1.1, x.2)) (M011Aux.omega_joint_analytic _ hx)
      ((analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd)
  have hI := NlsGge.G4022Support.segment_integral_analytic hUo hH
    (τ := fun _ => p.2) (ℓ := fun u => u.2) analyticOnNhd_const (fun u _ => analyticAt_snd)
    (fun u hu s hs => hseg u hu s hs)
  refine ⟨U, hUo, hpU,
    fun q => F0 q.1 + (q.2 - p.2) * ∫ s in (0 : ℝ)..1, MContour.omega q.1 (p.2 + (s : ℂ) * (q.2 - p.2)),
    fun q hq => hb ⟨hq.1.2, hq.2⟩, fun q hq => ?_, ?_⟩
  · have hq' : (q.1, q.2) ∈ rootDomain38 := hb ⟨hq.1.2, hq.2⟩
    refine ⟨⟨hq'.1, Or.inl hq'.2⟩, ?_⟩
    have ha : p.2 ∈ MPrimitive.endpointClosureFiber q.1 := by
      have h0 := hseg q hq 0 ⟨le_rfl, zero_le_one⟩
      simp only [Complex.ofReal_zero, zero_mul, add_zero] at h0
      exact Or.inl h0.2
    have h := M011Aux.primitive_sub_eq_integral hq'.1 (fun s hs => (hseg q hq s hs).2) ha
      (Or.inl hq'.2)
    show F0 q.1 + _ = _
    rw [(hF0 q.1 hq.1.1).2 ⟨hq'.1, ha⟩]
    exact h.symm
  · intro q hq
    have h1 : AnalyticAt ℂ (fun q : PotPair × ℂ => F0 q.1) q :=
      (hF0an q.1 hq.1.1).comp analyticAt_fst
    have h2 : AnalyticAt ℂ (fun q : PotPair × ℂ => q.2 - p.2) q := analyticAt_snd.sub analyticAt_const
    exact h1.add (h2.mul (hI q hq))

end NlsGge.ThirdConsultation.M
