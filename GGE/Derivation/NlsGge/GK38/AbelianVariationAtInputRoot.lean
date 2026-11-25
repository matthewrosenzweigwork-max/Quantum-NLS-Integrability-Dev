import NlsGge.GK38.AbelianDirectionSeries

/-! Collision-safe recovery at an actual input root. Analyticity of the remaining
finite factor is earned before differentiating the exact product identity. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38.P4NumeratorVariation
noncomputable section

theorem column_input_analytic (n r : ℤ) (z : ℂ) :
    AnalyticOnNhd ℂ (fun s : Lib.L2Seq => p3NumeratorColumn38 n r s z) univ := by
  intro s _
  have hs : AnalyticAt ℂ (fun q : Lib.L2Seq => Lib.sOmit n q z) s :=
    AnalyticAt.comp
      (g := fun p : ℂ × Lib.L2Seq => Lib.sOmit n p.2 p.1)
      (f := fun q : Lib.L2Seq => (z,q))
      (Lib.analyticOnNhd_sOmit n (z,s) trivial)
      (analyticAt_const.prod analyticAt_id)
  have ho : AnalyticAt ℂ
      (fun q : Lib.L2Seq => Lib.omitProd r (Lib.sOmit n q z) z) s :=
    AnalyticAt.comp
      (g := fun p : ℂ × Lib.L2Seq => Lib.omitProd r p.2 p.1)
      (f := fun q : Lib.L2Seq => (z,Lib.sOmit n q z))
      (Lib.analyticOnNhd_omitProd r (z,Lib.sOmit n s z) trivial)
      (analyticAt_const.prod hs)
  exact analyticAt_const.mul ho

theorem variation_at_input_root (n r : ℤ) (hrn : r ≠ n)
    (s h : Lib.L2Seq) :
    p4NumeratorVariation38 n s h (Lib.sigmaOf s r) =
      h r * p3NumeratorColumn38 n r s (Lib.sigmaOf s r) := by
  let z : ℂ := Lib.sigmaOf s r
  let g : ℂ → ℂ := fun t => p3NumeratorColumn38 n r (s+t • h) z
  have hline : AnalyticAt ℂ (fun t : ℂ => s+t • h) 0 :=
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hgA : AnalyticAt ℂ g 0 := by
    have hcol : AnalyticAt ℂ (fun q : Lib.L2Seq => p3NumeratorColumn38 n r q z)
        (s+(0 : ℂ) • h) := by
      simpa only [zero_smul,add_zero] using column_input_analytic n r z s trivial
    exact AnalyticAt.comp
      (g := fun q : Lib.L2Seq => p3NumeratorColumn38 n r q z)
      (f := fun t : ℂ => s+t • h) hcol hline
  have hg : HasDerivAt g (deriv g 0) 0 := hgA.differentiableAt.hasDerivAt
  have hfactor : (fun t : ℂ => Lib.sigmaOf (s+t • h) r-z) =
      (fun t : ℂ => t*h r) := by
    funext t
    simp only [Lib.sigmaOf,lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,
      Pi.smul_apply,smul_eq_mul,z]
    ring
  have hd := (((hasDerivAt_id (0 : ℂ)).mul_const (h r)).mul hg)
  change HasDerivAt (fun t : ℂ => (t*h r)*g t)
    (1*h r*g 0+(0*h r)*deriv g 0) 0 at hd
  have he : (fun t : ℂ => p2FullNumerator38 n (s+t • h) z) =
      (fun t : ℂ => (t*h r)*g t) := by
    funext t
    rw [P3JacobianColumns.numerator_factor n r hrn]
    rw [congrFun hfactor t]
  rw [← he] at hd
  have hd' : HasDerivAt (fun t : ℂ => p2FullNumerator38 n (s+t • h) z)
      (h r*p3NumeratorColumn38 n r s z) 0 := by
    simpa only [one_mul,zero_mul,zero_add,add_zero,zero_smul,g] using hd
  exact (variation_hasDerivAt n s h z).unique hd'

end
end NlsGge.GK38.P4NumeratorVariation
