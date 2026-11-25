import NlsGge.GK38.AbelianSpace
import NlsGge.GK38.ContourAction
import NlsGge.GK38.Lib.ParamCircleAnalytic

/-! Actual P2 numerator and Abelian periods. UNCOMPILED prospective proof checkpoint. -/
set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38
noncomputable section

def abelianPeriod38 (m : ℤ) (φ : PotPair) (f : ℂ → ℂ) : ℂ :=
  circleIntegral (fun z : ℂ => f z/canonRoot38 φ z) (discC φ m) (discR φ m)

def p2FullNumerator38 (n : ℤ) (s : Lib.L2Seq) (z : ℂ) : ℂ :=
  -2*Lib.omitProd n s z

def p2Numerator38 (n : ℤ) (s : P2Space38 n) (z : ℂ) : ℂ :=
  p2FullNumerator38 n (p2Extend38 n s) z

def p2FnCoord38 (n : ℤ) (p : PotPair × P2Space38 n) (m : P2Index38 n) : ℂ :=
  (((n-m.1:ℤ):ℂ))*abelianPeriod38 m.1 p.1 (p2Numerator38 n p.2)

theorem p2FullNumerator_joint_analytic38 (n : ℤ) :
    AnalyticOnNhd ℂ (fun p : ℂ × Lib.L2Seq => p2FullNumerator38 n p.2 p.1) univ := by
  exact analyticOnNhd_const.mul (Lib.analyticOnNhd_omitProd n)

theorem p2FullNumerator_entire38 (n : ℤ) (s : Lib.L2Seq) :
    AnalyticOnNhd ℂ (p2FullNumerator38 n s) univ := by
  intro z _
  exact AnalyticAt.comp
    (g := fun p : ℂ × Lib.L2Seq => p2FullNumerator38 n p.2 p.1)
    (f := fun w : ℂ => (w,s)) (p2FullNumerator_joint_analytic38 n (z,s) trivial)
    (analyticAt_id.prod analyticAt_const)

/-- Entire numerator divided by the ACTUAL root, on its ACTUAL full cut complement. -/
theorem p2Quotient_analytic38 (φ : PotPair) (hφ : φ ∈ gkW) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f univ) :
    AnalyticOnNhd ℂ (fun z : ℂ => f z/canonRoot38 φ z) (actionCutDomain38 φ) := by
  intro z hz
  have hR := AnalyticAt.comp (g := fun p : PotPair × ℂ => canonRoot38 p.1 p.2)
    (f := fun w : ℂ => (φ,w)) (canonRoot_analytic38 (φ,z) ⟨hφ,hz⟩)
    (analyticAt_const.prod analyticAt_id)
  exact (hf z trivial).div hR (canonRoot_ne_zero38 φ hφ z hz)

/-- Both integrabilities are earned before the two full-family periods are compared. -/
theorem abelianPeriod_fullfamily_realization38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C0 C1 : ℤ → ℂ) (R0 R1 : ℤ → ℝ)
    (h0 : IsolatingFamily38 φ C0 R0) (h1 : IsolatingFamily38 φ C1 R1)
    (m : ℤ) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ) :
    CircleIntegrable (fun z : ℂ => f z/canonRoot38 φ z) (C0 m) (R0 m) ∧
    CircleIntegrable (fun z : ℂ => f z/canonRoot38 φ z) (C1 m) (R1 m) ∧
    circleIntegral (fun z : ℂ => f z/canonRoot38 φ z) (C0 m) (R0 m) =
      circleIntegral (fun z : ℂ => f z/canonRoot38 φ z) (C1 m) (R1 m) := by
  have hr := action_contour_radii_pos38 φ C0 C1 R0 R1 h0 h1 m
  exact NlsGge.Analysis.circleIntegral_eq_of_affine_circle_homotopy
    (isOpen_actionCutDomain38 φ hφ) (p2Quotient_analytic38 φ hφ f hf) hr.1 hr.2
    (fun t ht => action_contour_sphere_subset38 φ C0 C1 R0 R1 h0 h1 m t ht)

theorem p2Period_integrable38 (m n : ℤ) (φ : PotPair) (hφ : φ ∈ gkW) (s : Lib.L2Seq) :
    CircleIntegrable (fun z : ℂ => p2FullNumerator38 n s z/canonRoot38 φ z)
      (discC φ m) (discR φ m) :=
  (abelianPeriod_fullfamily_realization38 φ hφ (discC φ) (discC φ) (discR φ) (discR φ)
    (isolating_family38 φ hφ) (isolating_family38 φ hφ) m (p2FullNumerator38 n s)
    (p2FullNumerator_entire38 n s)).1

/-- Joint Banach-parameter numerator/root analyticity, before circle integration. -/
theorem p2Quotient_joint_analytic38 (n : ℤ) :
    AnalyticOnNhd ℂ
      (fun p : (PotPair × Lib.L2Seq) × ℂ => p2FullNumerator38 n p.1.2 p.2/canonRoot38 p.1.1 p.2)
      {p : (PotPair × Lib.L2Seq) × ℂ | (p.1.1,p.2) ∈ rootDomain38} := by
  intro p hp
  have hps : AnalyticAt ℂ (fun q : (PotPair × Lib.L2Seq) × ℂ => q.1.2) p :=
    AnalyticAt.comp (g := fun q : PotPair × Lib.L2Seq => q.2)
      (f := fun q : (PotPair × Lib.L2Seq) × ℂ => q.1) analyticAt_snd analyticAt_fst
  have hpf : AnalyticAt ℂ (fun q : (PotPair × Lib.L2Seq) × ℂ => q.1.1) p :=
    AnalyticAt.comp (g := fun q : PotPair × Lib.L2Seq => q.1)
      (f := fun q : (PotPair × Lib.L2Seq) × ℂ => q.1) analyticAt_fst analyticAt_fst
  have hnum := AnalyticAt.comp
    (g := fun q : ℂ × Lib.L2Seq => p2FullNumerator38 n q.2 q.1)
    (f := fun q : (PotPair × Lib.L2Seq) × ℂ => (q.2,q.1.2))
    (p2FullNumerator_joint_analytic38 n (p.2,p.1.2) trivial)
    (analyticAt_snd.prod hps)
  have hroot := AnalyticAt.comp (g := fun q : PotPair × ℂ => canonRoot38 q.1 q.2)
    (f := fun q : (PotPair × Lib.L2Seq) × ℂ => (q.1.1,q.2))
    (canonRoot_analytic38 (p.1.1,p.2) hp) (hpf.prod analyticAt_snd)
  exact hnum.div hroot (canonRoot_ne_zero38 p.1.1 hp.1 p.2 hp.2)

/-- Global arbitrary selectors are replaced locally by an earned original fixed FULL family. -/
theorem p2FullCoordinate_analytic38 (n m : ℤ) :
    AnalyticOnNhd ℂ
      (fun p : PotPair × Lib.L2Seq => (((n-m:ℤ):ℂ))*
        abelianPeriod38 m p.1 (p2FullNumerator38 n p.2))
      (gkW ×ˢ (univ : Set Lib.L2Seq)) := by
  intro p hp
  obtain ⟨V,hV,hVW,hVo,_hVc,C,R,c,N,hgeom,hspec⟩ := local_isolatingFamily_common38 p.1 hp.1
  have hf : ∀ φ ∈ V, IsolatingFamily38 φ C R := fun φ hφ => ⟨c,N,hgeom,hspec φ hφ⟩
  have hpV : p.1 ∈ V := mem_of_mem_nhds hV
  have hjoint : AnalyticOnNhd ℂ
      (Function.uncurry (fun q : PotPair × Lib.L2Seq => fun z : ℂ =>
        p2FullNumerator38 n q.2 z/canonRoot38 q.1 z))
      ((V ×ˢ (univ : Set Lib.L2Seq)) ×ˢ sphere (C m) (R m)) := by
    intro q hq
    exact p2Quotient_joint_analytic38 n q
      ⟨hVW hq.1.1,fixed_sphere_subset q.1.1 C R (hf q.1.1 hq.1.1) m hq.2⟩
  have hi := Lib.parametricCircleAnalytic38 (PotPair × Lib.L2Seq)
    (V ×ˢ (univ : Set Lib.L2Seq)) (C m) (R m)
    (fun q : PotPair × Lib.L2Seq => fun z : ℂ => p2FullNumerator38 n q.2 z/canonRoot38 q.1 z)
    (hVo.prod isOpen_univ) (isolating_radius_pos38 (hf p.1 hpV) m) hjoint
  have ha : AnalyticAt ℂ (fun q : PotPair × Lib.L2Seq => (((n-m:ℤ):ℂ))*
      circleIntegral (fun z : ℂ => p2FullNumerator38 n q.2 z/canonRoot38 q.1 z) (C m) (R m)) p :=
    analyticAt_const.mul (hi.2 p ⟨hpV,mem_univ _⟩)
  apply ha.congr
  filter_upwards [(hVo.prod isOpen_univ).mem_nhds (⟨hpV,mem_univ p.2⟩)] with q hq
  have hφ := hVW hq.1
  have he := abelianPeriod_fullfamily_realization38 q.1 hφ (discC q.1) C (discR q.1) R
    (isolating_family38 q.1 hφ) (hf q.1 hq.1) m (p2FullNumerator38 n q.2)
    (p2FullNumerator_entire38 n q.2)
  exact congrArg (fun a : ℂ => (((n-m:ℤ):ℂ))*a) he.2.2.symm

#print axioms p2FullNumerator_joint_analytic38
#print axioms abelianPeriod_fullfamily_realization38
#print axioms p2Period_integrable38
#print axioms p2FullCoordinate_analytic38
end
end NlsGge.GK38
