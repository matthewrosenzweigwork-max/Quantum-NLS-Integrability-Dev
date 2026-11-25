import NlsGge.GK38.AbelianFullWeightedDecay

/-! Source-only Qstar-side full numerator and its genuine infinite-dimensional
directional derivative. No bounded matrix, kernel, or inverse oracle. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38.P6FullNumeratorVariation
noncomputable section

def fullNumerator (s : Lib.L2Seq) (z : ℂ) : ℂ :=
  (-2 / (Real.pi : ℂ))*Lib.entProdJ (z,s)

theorem fullNumerator_joint_analytic :
    AnalyticOnNhd ℂ (fun p : ℂ × Lib.L2Seq => fullNumerator p.2 p.1) univ :=
  analyticOnNhd_const.mul Lib.analyticOnNhd_entProd_joint

theorem fullNumerator_factor (n : ℤ) (s : Lib.L2Seq) (z : ℂ) :
    fullNumerator s z = ((Lib.sigmaOf s n-z)/(Real.pi : ℂ))*p2FullNumerator38 n s z := by
  unfold fullNumerator Lib.entProdJ p2FullNumerator38
  rw [Lib.entProd_eq_mul_omitProd n]
  ring

def fullVariation (s h : Lib.L2Seq) (z : ℂ) : ℂ :=
  fderiv ℂ (fun p : ℂ × Lib.L2Seq => fullNumerator p.2 p.1) (z,s) (0,h)

theorem fullVariation_entire (s h : Lib.L2Seq) :
    AnalyticOnNhd ℂ (fullVariation s h) univ := by
  let ev : ((ℂ × Lib.L2Seq) →L[ℂ] ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.apply ℂ ℂ (0,h)
  intro z _
  have hd := (fullNumerator_joint_analytic (z,s) (mem_univ _)).fderiv
  have he : AnalyticAt ℂ
      (fun p : ℂ × Lib.L2Seq => ev
        (fderiv ℂ (fun q : ℂ × Lib.L2Seq => fullNumerator q.2 q.1) p)) (z,s) :=
    (ev.analyticAt _).comp hd
  exact AnalyticAt.comp
    (g := fun p : ℂ × Lib.L2Seq => ev
      (fderiv ℂ (fun q : ℂ × Lib.L2Seq => fullNumerator q.2 q.1) p))
    (f := fun w : ℂ => (w,s)) he (analyticAt_id.prod analyticAt_const)

theorem fullVariation_hasDerivAt (s h : Lib.L2Seq) (z : ℂ) :
    HasDerivAt (fun t : ℂ => fullNumerator (s+t • h) z) (fullVariation s h z) 0 := by
  have hline : HasDerivAt (fun t : ℂ => (z,s+t • h)) (0,h) 0 := by
    simpa only [one_smul] using!
      (hasDerivAt_const 0 z).prodMk
        (((hasDerivAt_id (0 : ℂ)).smul_const h).const_add s)
  have hf := (fullNumerator_joint_analytic (z,s) (mem_univ _)).differentiableAt.hasFDerivAt
  have hf' : HasFDerivAt
      (fun p : ℂ × Lib.L2Seq => fullNumerator p.2 p.1)
      (fderiv ℂ (fun p : ℂ × Lib.L2Seq => fullNumerator p.2 p.1) (z,s))
      (z,s+(0 : ℂ) • h) := by simpa only [zero_smul,add_zero] using hf
  exact hf'.comp_hasDerivAt 0 hline

/-- The finite factor is differentiated without dividing by sigma_n-z.
The two summands already have honest decay theorems on counting circles. -/
theorem fullVariation_factor (n : ℤ) (s h : Lib.L2Seq) (z : ℂ) :
    fullVariation s h z =
      ((h n)*p2FullNumerator38 n s z+
        (Lib.sigmaOf s n-z)*p4NumeratorVariation38 n s h z)/(Real.pi : ℂ) := by
  have heq : (fun t : ℂ => Lib.sigmaOf (s+t • h) n-z) =
      (fun t : ℂ => (Lib.sigmaOf s n-z)+t*h n) := by
    funext t
    rw [Lib.sigmaOf_line]
    ring
  have hs : HasDerivAt (fun t : ℂ => Lib.sigmaOf (s+t • h) n-z) (h n) 0 := by
    rw [heq]
    simpa only [one_mul] using!
      (((hasDerivAt_id (0 : ℂ)).mul_const (h n)).const_add (Lib.sigmaOf s n-z))
  have hd : HasDerivAt
      (fun t : ℂ => ((Lib.sigmaOf (s+t • h) n-z)/(Real.pi : ℂ))*
        p2FullNumerator38 n (s+t • h) z)
      ((h n/(Real.pi : ℂ))*p2FullNumerator38 n s z+
        ((Lib.sigmaOf s n-z)/(Real.pi : ℂ))*p4NumeratorVariation38 n s h z) 0 := by
    simpa only [zero_smul,add_zero] using!
      (hs.div_const (Real.pi : ℂ)).mul (P4NumeratorVariation.variation_hasDerivAt n s h z)
  have he : (fun t : ℂ => fullNumerator (s+t • h) z) =
      (fun t : ℂ => ((Lib.sigmaOf (s+t • h) n-z)/(Real.pi : ℂ))*
        p2FullNumerator38 n (s+t • h) z) := funext (fun t => fullNumerator_factor n (s+t • h) z)
  rw [← he] at hd
  exact ((fullVariation_hasDerivAt s h z).unique hd).trans (by ring)

end
end NlsGge.GK38.P6FullNumeratorVariation
