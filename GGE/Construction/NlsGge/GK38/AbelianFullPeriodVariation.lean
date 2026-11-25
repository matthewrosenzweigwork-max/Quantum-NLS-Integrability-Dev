import NlsGge.GK38.AbelianFullPeriodScalarAnalytic
import NlsGge.GK38.AbelianFullNumeratorColumns
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! UNCOMPILED actual full-period variation. This transports the parent's
genuine full numerator derivative through the ACTUAL Abelian integral.
Scalar and CLM contour integrabilities precede integral evaluation. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38.P6FullPeriodDerivative
noncomputable section
open P6FullNumeratorVariation

theorem variation_circleIntegrable (m : ℤ) (φ : PotPair) (hφ : φ ∈ gkW)
    (s h : Lib.L2Seq) :
    CircleIntegrable (fun z => fullVariation s h z/canonRoot38 φ z)
      (discC φ m) (discR φ m) :=
  (abelianPeriod_fullfamily_realization38 φ hφ (discC φ) (discC φ)
    (discR φ) (discR φ) (isolating_family38 φ hφ) (isolating_family38 φ hφ)
    m (fullVariation s h) (fullVariation_entire s h)).1

theorem quotient_joint_analytic (φ : PotPair) (hφ : φ ∈ gkW) :
    AnalyticOnNhd ℂ
      (fun p : Lib.L2Seq × ℂ => fullNumerator p.1 p.2/canonRoot38 φ p.2)
      (univ ×ˢ actionCutDomain38 φ) := by
  intro p hp
  exact AnalyticAt.comp
    (g := fun q : (PotPair × Lib.L2Seq) × ℂ => fullNumerator q.1.2 q.2/canonRoot38 q.1.1 q.2)
    (f := fun q : Lib.L2Seq × ℂ => ((φ,q.1),q.2))
    (p6FullQuotient_joint_analytic38 ((φ,p.1),p.2) ⟨hφ,hp.2⟩)
    ((analyticAt_const.prod analyticAt_fst).prod analyticAt_snd)

theorem quotient_partial_apply (φ : PotPair) (hφ : φ ∈ gkW)
    (s h : Lib.L2Seq) (z : ℂ) (hz : z ∈ actionCutDomain38 φ) :
    Lib.paramCircleDerivative38 (fun t w => fullNumerator t w/canonRoot38 φ w) s z h =
      fullVariation s h z/canonRoot38 φ z := by
  have ha := quotient_joint_analytic φ hφ (s,z) ⟨mem_univ _,hz⟩
  have hd := Lib.paramCircle_hasFDerivAt38
    (F := fun t w => fullNumerator t w/canonRoot38 φ w) ha
  have hline : HasDerivAt (fun t : ℂ => s+t • h) h 0 := by
    simpa only [one_smul] using! (((hasDerivAt_id (0 : ℂ)).smul_const h).const_add s)
  have hc := hd.comp_hasDerivAt_of_eq 0 hline (by simp)
  exact hc.unique ((fullVariation_hasDerivAt s h z).div_const (canonRoot38 φ z))

theorem period_hasDerivAt (m : ℤ) (φ : PotPair) (hφ : φ ∈ gkW)
    (s h : Lib.L2Seq) :
    HasDerivAt (fun t : ℂ => abelianPeriod38 m φ (fullNumerator (s+t • h)))
      (abelianPeriod38 m φ (fullVariation s h)) 0 := by
  let F : Lib.L2Seq → ℂ → ℂ := fun t z => fullNumerator t z/canonRoot38 φ z
  let T : ((Lib.L2Seq × ℂ) →L[ℂ] ℂ) →L[ℂ] (Lib.L2Seq →L[ℂ] ℂ) :=
    (ContinuousLinearMap.compL ℂ Lib.L2Seq (Lib.L2Seq × ℂ) ℂ).flip
      (ContinuousLinearMap.inl ℂ Lib.L2Seq ℂ)
  have hr := isolating_radius_pos38 (isolating_family38 φ hφ) m
  have hsphere : sphere (discC φ m) (discR φ m) ⊆ actionCutDomain38 φ :=
    fixed_sphere_subset φ (discC φ) (discR φ) (isolating_family38 φ hφ) m
  have hA : AnalyticOnNhd ℂ (Function.uncurry F)
      (univ ×ˢ sphere (discC φ m) (discR φ m)) :=
    (quotient_joint_analytic φ hφ).mono (prod_mono_right hsphere)
  have hpartial : CircleIntegrable (Lib.paramCircleDerivative38 F s)
      (discC φ m) (discR φ m) := by
    apply ContinuousOn.circleIntegrable hr.le
    intro z hz
    have ha : AnalyticAt ℂ (fun p : Lib.L2Seq × ℂ => T (fderiv ℂ (Function.uncurry F) p))
        (s,z) := (T.analyticAt _).comp ((hA (s,z) ⟨mem_univ _,hz⟩).fderiv)
    exact (AnalyticAt.comp
      (g := fun p : Lib.L2Seq × ℂ => T (fderiv ℂ (Function.uncurry F) p))
      (f := fun w : ℂ => (s,w)) ha (analyticAt_const.prod analyticAt_id)).continuousAt.continuousWithinAt
  have _hi := variation_circleIntegrable m φ hφ s h
  have hd := Lib.paramCircle_integral_hasFDerivAt38 isOpen_univ hr hA (mem_univ s)
  rw [← circleIntegral_def_Icc (Lib.paramCircleDerivative38 F s) (discC φ m) (discR φ m)] at hd
  have hline : HasDerivAt (fun t : ℂ => s+t • h) h 0 := by
    simpa only [one_smul] using! (((hasDerivAt_id (0 : ℂ)).smul_const h).const_add s)
  have hderiv := hd.comp_hasDerivAt_of_eq 0 hline (by simp)
  have heval : (circleIntegral (Lib.paramCircleDerivative38 F s) (discC φ m) (discR φ m)) h =
      abelianPeriod38 m φ (fullVariation s h) := by
    unfold circleIntegral abelianPeriod38
    rw [ContinuousLinearMap.intervalIntegral_apply hpartial.out h]
    apply intervalIntegral.integral_congr
    intro θ _
    have hz := circleMap_mem_sphere (discC φ m) hr.le θ
    change deriv (circleMap (discC φ m) (discR φ m)) θ *
      Lib.paramCircleDerivative38 F s (circleMap (discC φ m) (discR φ m) θ) h = _
    rw [quotient_partial_apply φ hφ s h _ (hsphere hz)]
    rfl
  rw [heval] at hderiv
  exact hderiv

theorem scalar_fderiv_apply (m : ℤ) (φ : PotPair) (hφ : φ ∈ gkW)
    (s h : Lib.L2Seq) :
    (fderiv ℂ (fun t : Lib.L2Seq => p6FullPeriodCoordinate38 (φ,t) m) s) h =
      abelianPeriod38 m φ (fullVariation s h) := by
  have ha : AnalyticAt ℂ
      (fun t : Lib.L2Seq => p6FullPeriodCoordinate38 (φ,t) m) s :=
    AnalyticAt.comp
      (g := fun p : PotPair × Lib.L2Seq => p6FullPeriodCoordinate38 p m)
      (f := fun t : Lib.L2Seq => (φ,t))
      (p6FullPeriodCoordinate_analytic38 m (φ,s) ⟨hφ,mem_univ _⟩)
      (analyticAt_const.prod analyticAt_id)
  have hline : HasDerivAt (fun t : ℂ => s+t • h) h 0 := by
    simpa only [one_smul] using! (((hasDerivAt_id (0 : ℂ)).smul_const h).const_add s)
  have hd := ha.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  exact hd.unique (period_hasDerivAt m φ hφ s h)

theorem scalar_unit_column (m r : ℤ) (φ : PotPair) (hφ : φ ∈ gkW)
    (s : Lib.L2Seq) :
    (fderiv ℂ (fun t : Lib.L2Seq => p6FullPeriodCoordinate38 (φ,t) m) s)
      (lp.single 2 r (1 : ℂ)) =
        abelianPeriod38 m φ (fun z : ℂ => (-2/(Real.pi : ℂ))*Lib.omitProd r s z) := by
  rw [scalar_fderiv_apply m φ hφ s (lp.single 2 r (1 : ℂ))]
  congr 1
  funext z
  exact fullVariation_unit_column r s z

end
end NlsGge.GK38.P6FullPeriodDerivative
