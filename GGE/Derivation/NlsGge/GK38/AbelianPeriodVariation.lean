import NlsGge.GK38.AbelianNumeratorVariation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Actual Abelian period differentiation for arbitrary genuine lp2 directions.
The scalar and CLM contour integrabilities precede integral evaluation. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38.P4NumeratorVariation
noncomputable section

theorem variation_circleIntegrable (n m : ℤ) (φ : PotPair) (hφ : φ ∈ gkW)
    (s h : Lib.L2Seq) :
    CircleIntegrable (fun z => p4NumeratorVariation38 n s h z/canonRoot38 φ z)
      (discC φ m) (discR φ m) :=
  (abelianPeriod_fullfamily_realization38 φ hφ (discC φ) (discC φ)
    (discR φ) (discR φ) (isolating_family38 φ hφ) (isolating_family38 φ hφ)
    m (p4NumeratorVariation38 n s h) (variation_entire n s h)).1

theorem quotient_joint_analytic (n : ℤ) (φ : PotPair) (hφ : φ ∈ gkW) :
    AnalyticOnNhd ℂ
      (fun p : Lib.L2Seq × ℂ => p2FullNumerator38 n p.1 p.2/canonRoot38 φ p.2)
      (univ ×ˢ actionCutDomain38 φ) := by
  intro p hp
  exact AnalyticAt.comp
    (g := fun q : (PotPair × Lib.L2Seq) × ℂ =>
      p2FullNumerator38 n q.1.2 q.2/canonRoot38 q.1.1 q.2)
    (f := fun q : Lib.L2Seq × ℂ => ((φ,q.1),q.2))
    (p2Quotient_joint_analytic38 n ((φ,p.1),p.2) ⟨hφ,hp.2⟩)
    ((analyticAt_const.prod analyticAt_fst).prod analyticAt_snd)

theorem quotient_partial_apply (n : ℤ) (φ : PotPair) (hφ : φ ∈ gkW)
    (s h : Lib.L2Seq) (z : ℂ) (hz : z ∈ actionCutDomain38 φ) :
    Lib.paramCircleDerivative38
      (fun t w => p2FullNumerator38 n t w/canonRoot38 φ w) s z h =
        p4NumeratorVariation38 n s h z/canonRoot38 φ z := by
  have ha := quotient_joint_analytic n φ hφ (s,z) ⟨mem_univ _,hz⟩
  have hd := Lib.paramCircle_hasFDerivAt38
    (F := fun t w => p2FullNumerator38 n t w/canonRoot38 φ w) ha
  have hline : HasDerivAt (fun t : ℂ => s+t • h) h 0 := by
    simpa only [one_smul] using! (((hasDerivAt_id (0 : ℂ)).smul_const h).const_add s)
  have hc := hd.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hv := (variation_hasDerivAt n s h z).div_const (canonRoot38 φ z)
  exact hc.unique hv

theorem period_hasDerivAt (n m : ℤ) (φ : PotPair) (hφ : φ ∈ gkW)
    (s h : Lib.L2Seq) :
    HasDerivAt (fun t : ℂ => abelianPeriod38 m φ (p2FullNumerator38 n (s+t • h)))
      (abelianPeriod38 m φ (p4NumeratorVariation38 n s h)) 0 := by
  let F : Lib.L2Seq → ℂ → ℂ := fun t z => p2FullNumerator38 n t z/canonRoot38 φ z
  let T : ((Lib.L2Seq × ℂ) →L[ℂ] ℂ) →L[ℂ] (Lib.L2Seq →L[ℂ] ℂ) :=
    (ContinuousLinearMap.compL ℂ Lib.L2Seq (Lib.L2Seq × ℂ) ℂ).flip
      (ContinuousLinearMap.inl ℂ Lib.L2Seq ℂ)
  have hr := isolating_radius_pos38 (isolating_family38 φ hφ) m
  have hsphere : sphere (discC φ m) (discR φ m) ⊆ actionCutDomain38 φ :=
    fixed_sphere_subset φ (discC φ) (discR φ) (isolating_family38 φ hφ) m
  have hA : AnalyticOnNhd ℂ (Function.uncurry F)
      (univ ×ˢ sphere (discC φ m) (discR φ m)) :=
    (quotient_joint_analytic n φ hφ).mono (prod_mono_right hsphere)
  have hpartial : CircleIntegrable (Lib.paramCircleDerivative38 F s)
      (discC φ m) (discR φ m) := by
    apply ContinuousOn.circleIntegrable hr.le
    intro z hz
    have ha : AnalyticAt ℂ (fun p : Lib.L2Seq × ℂ => T (fderiv ℂ (Function.uncurry F) p))
        (s,z) := (T.analyticAt _).comp ((hA (s,z) ⟨mem_univ _,hz⟩).fderiv)
    exact (AnalyticAt.comp
      (g := fun p : Lib.L2Seq × ℂ => T (fderiv ℂ (Function.uncurry F) p))
      (f := fun w : ℂ => (s,w)) ha (analyticAt_const.prod analyticAt_id)).continuousAt.continuousWithinAt
  have _hi := variation_circleIntegrable n m φ hφ s h
  have hd := Lib.paramCircle_integral_hasFDerivAt38 isOpen_univ hr hA (mem_univ s)
  rw [← circleIntegral_def_Icc (Lib.paramCircleDerivative38 F s) (discC φ m) (discR φ m)] at hd
  have hline : HasDerivAt (fun t : ℂ => s+t • h) h 0 := by
    simpa only [one_smul] using! (((hasDerivAt_id (0 : ℂ)).smul_const h).const_add s)
  have hderiv := hd.comp_hasDerivAt_of_eq 0 hline (by simp)
  have heval : (circleIntegral (Lib.paramCircleDerivative38 F s) (discC φ m) (discR φ m)) h =
      abelianPeriod38 m φ (p4NumeratorVariation38 n s h) := by
    unfold circleIntegral abelianPeriod38
    rw [ContinuousLinearMap.intervalIntegral_apply hpartial.out h]
    apply intervalIntegral.integral_congr
    intro θ _
    have hz := circleMap_mem_sphere (discC φ m) hr.le θ
    change deriv (circleMap (discC φ m) (discR φ m)) θ *
      Lib.paramCircleDerivative38 F s (circleMap (discC φ m) (discR φ m) θ) h = _
    rw [quotient_partial_apply n φ hφ s h _ (hsphere hz)]
    rfl
  rw [heval] at hderiv
  exact hderiv

end
end NlsGge.GK38.P4NumeratorVariation
