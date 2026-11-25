import NlsGge.GK38.AbelianFullNumeratorVariation
import NlsGge.GK38.AbelianHilbert

/-! UNCOMPILED actual full-period scalar coordinates. Parent owns the genuine
full numerator/variation. This leaf earns actual contour integrability and
scalar joint analyticity, before any Hilbert bundle or Qstar is constructed. -/
set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38
noncomputable section

theorem p6FullNumerator_entire38 (s : Lib.L2Seq) :
    AnalyticOnNhd ℂ (P6FullNumeratorVariation.fullNumerator s) univ := by
  intro z _
  exact AnalyticAt.comp
    (g := fun p : ℂ × Lib.L2Seq => P6FullNumeratorVariation.fullNumerator p.2 p.1)
    (f := fun w : ℂ => (w,s))
    (P6FullNumeratorVariation.fullNumerator_joint_analytic (z,s) (mem_univ _))
    (analyticAt_id.prod analyticAt_const)

def p6FullPeriodCoordinate38 (p : PotPair × Lib.L2Seq) (m : ℤ) : ℂ :=
  abelianPeriod38 m p.1 (P6FullNumeratorVariation.fullNumerator p.2)

theorem p6FullPeriod_integrable38 (m : ℤ) (φ : PotPair) (hφ : φ ∈ gkW)
    (s : Lib.L2Seq) :
    CircleIntegrable
      (fun z : ℂ => P6FullNumeratorVariation.fullNumerator s z/canonRoot38 φ z)
      (discC φ m) (discR φ m) :=
  (abelianPeriod_fullfamily_realization38 φ hφ (discC φ) (discC φ)
    (discR φ) (discR φ) (isolating_family38 φ hφ) (isolating_family38 φ hφ)
    m (P6FullNumeratorVariation.fullNumerator s) (p6FullNumerator_entire38 s)).1

theorem p6FullQuotient_joint_analytic38 :
    AnalyticOnNhd ℂ
      (fun p : (PotPair × Lib.L2Seq) × ℂ =>
        P6FullNumeratorVariation.fullNumerator p.1.2 p.2/canonRoot38 p.1.1 p.2)
      {p : (PotPair × Lib.L2Seq) × ℂ | (p.1.1,p.2) ∈ rootDomain38} := by
  intro p hp
  have hps : AnalyticAt ℂ (fun q : (PotPair × Lib.L2Seq) × ℂ => q.1.2) p :=
    AnalyticAt.comp (g := fun q : PotPair × Lib.L2Seq => q.2)
      (f := fun q : (PotPair × Lib.L2Seq) × ℂ => q.1) analyticAt_snd analyticAt_fst
  have hpf : AnalyticAt ℂ (fun q : (PotPair × Lib.L2Seq) × ℂ => q.1.1) p :=
    AnalyticAt.comp (g := fun q : PotPair × Lib.L2Seq => q.1)
      (f := fun q : (PotPair × Lib.L2Seq) × ℂ => q.1) analyticAt_fst analyticAt_fst
  have hnum := AnalyticAt.comp
    (g := fun q : ℂ × Lib.L2Seq => P6FullNumeratorVariation.fullNumerator q.2 q.1)
    (f := fun q : (PotPair × Lib.L2Seq) × ℂ => (q.2,q.1.2))
    (P6FullNumeratorVariation.fullNumerator_joint_analytic (p.2,p.1.2) (mem_univ _))
    (analyticAt_snd.prod hps)
  have hroot := AnalyticAt.comp (g := fun q : PotPair × ℂ => canonRoot38 q.1 q.2)
    (f := fun q : (PotPair × Lib.L2Seq) × ℂ => (q.1.1,q.2))
    (canonRoot_analytic38 (p.1.1,p.2) hp) (hpf.prod analyticAt_snd)
  exact hnum.div hroot (canonRoot_ne_zero38 p.1.1 hp.1 p.2 hp.2)

theorem p6FullPeriodCoordinate_analytic38 (m : ℤ) :
    AnalyticOnNhd ℂ (fun p : PotPair × Lib.L2Seq => p6FullPeriodCoordinate38 p m)
      (gkW ×ˢ (univ : Set Lib.L2Seq)) := by
  intro p hp
  obtain ⟨V,hV,hVW,hVo,_hVc,C,R,c,N,hgeom,hspec⟩ :=
    local_isolatingFamily_common38 p.1 hp.1
  have hf : ∀ φ ∈ V, IsolatingFamily38 φ C R := fun φ hφ => ⟨c,N,hgeom,hspec φ hφ⟩
  have hpV : p.1 ∈ V := mem_of_mem_nhds hV
  have hjoint : AnalyticOnNhd ℂ
      (Function.uncurry (fun q : PotPair × Lib.L2Seq => fun z : ℂ =>
        P6FullNumeratorVariation.fullNumerator q.2 z/canonRoot38 q.1 z))
      ((V ×ˢ (univ : Set Lib.L2Seq)) ×ˢ sphere (C m) (R m)) := by
    intro q hq
    exact p6FullQuotient_joint_analytic38 q
      ⟨hVW hq.1.1,fixed_sphere_subset q.1.1 C R (hf q.1.1 hq.1.1) m hq.2⟩
  have hi := Lib.parametricCircleAnalytic38 (PotPair × Lib.L2Seq)
    (V ×ˢ (univ : Set Lib.L2Seq)) (C m) (R m)
    (fun q : PotPair × Lib.L2Seq => fun z : ℂ =>
      P6FullNumeratorVariation.fullNumerator q.2 z/canonRoot38 q.1 z)
    (hVo.prod isOpen_univ) (isolating_radius_pos38 (hf p.1 hpV) m) hjoint
  apply (hi.2 p ⟨hpV,mem_univ _⟩).congr
  filter_upwards [(hVo.prod isOpen_univ).mem_nhds (⟨hpV,mem_univ p.2⟩)] with q hq
  have hφ := hVW hq.1
  exact (abelianPeriod_fullfamily_realization38 q.1 hφ (discC q.1) C (discR q.1) R
    (isolating_family38 q.1 hφ) (hf q.1 hq.1) m
    (P6FullNumeratorVariation.fullNumerator q.2) (p6FullNumerator_entire38 q.2)).2.2.symm

end
end NlsGge.GK38
