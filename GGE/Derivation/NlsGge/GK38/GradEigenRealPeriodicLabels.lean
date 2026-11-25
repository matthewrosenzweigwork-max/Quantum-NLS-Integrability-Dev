import NlsGge.GK38.GradEigenRealPeriodicHelpers
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem parity_square (n : ℤ) : (parity n)^2=1 := by
  simp only [parity,neg_one_zpow_eq_ite]
  split_ifs <;> norm_num

theorem parity_star (n : ℤ) : star (parity n)=parity n := by simp [parity]

theorem endpoint_discrim_value (u : PhysicalL2) (n : ℤ) (upper : Bool) :
    discrim (realSlice u) (endpoint u n upper : ℂ)=2*parity n := by
  have hc : (Real.cos ((n : ℝ)*Real.pi) : ℂ)=parity n := by
    rw [Real.cos_int_mul_pi]
    simp [parity]
  cases upper
  · simpa only [endpoint,Bool.false_eq_true,if_false,hc] using (gap_discrim_endpoint_values38 u n).1
  · simpa only [endpoint,if_true,hc] using (gap_discrim_endpoint_values38 u n).2

theorem endpoint_continuous (n : ℤ) (upper : Bool) :
    Continuous (fun u : PhysicalL2 => endpoint u n upper) := by
  cases upper
  · simpa only [endpoint,Bool.false_eq_true,if_false] using (gapEndpoints_L2_continuous38 n).1
  · simpa only [endpoint,if_true] using (gapEndpoints_L2_continuous38 n).2

theorem endpoint_root (u : PhysicalL2) (n : ℤ) (upper : Bool) :
    perChar (realSlice u) (endpoint u n upper : ℂ)=0 := by
  cases upper
  · simpa only [endpoint,Bool.false_eq_true,if_false] using (gap_endpoint_roots38 u n).1
  · simpa only [endpoint,if_true] using (gap_endpoint_roots38 u n).2

theorem endpoint_discrim_deriv_ne_zero (u : PhysicalL2) (n : ℤ) (upper : Bool)
    (hgap : actualGapLowerAllE02_38 u n<actualGapUpperAllE02_38 u n) :
    deriv (discrim (realSlice u)) (endpoint u n upper : ℂ) ≠ 0 := by
  apply perChar_order_one_noncritical38 _ _ (endpoint_root u n upper)
  cases upper
  · simpa only [endpoint,Bool.false_eq_true,if_false,hgap,if_true] using order_at_gapEnd u n
  · simpa only [endpoint,if_true,hgap] using order_at_gapUpper38 u n

theorem endpoint_perChar_deriv_ne_zero (u : PhysicalL2) (n : ℤ) (upper : Bool)
    (hgap : actualGapLowerAllE02_38 u n<actualGapUpperAllE02_38 u n) :
    deriv (perChar (realSlice u)) (endpoint u n upper : ℂ) ≠ 0 := by
  have hc : parity n ≠ 0 := zpow_ne_zero n (by norm_num : (-1 : ℂ) ≠ 0)
  rw [periodic_perChar_deriv,endpoint_discrim_value]
  exact mul_ne_zero (mul_ne_zero two_ne_zero (mul_ne_zero two_ne_zero hc))
    (endpoint_discrim_deriv_ne_zero u n upper hgap)

def periodicRealChar (n : ℤ) (p : PhysicalL2 × ℝ) : ℝ :=
  (discrim (realSlice p.1) (p.2 : ℂ)).re-(2*parity n).re

theorem analyticAt_periodicRealChar (n : ℤ) (p : PhysicalL2 × ℝ) :
    AnalyticAt ℝ (periodicRealChar n) p := by
  have hA : AnalyticAt ℝ (fun q : PhysicalL2 × ℝ => (realSlice q.1,(q.2 : ℂ))) p :=
    ((realSlice.analyticAt p.1).comp (analyticAt_fst (𝕜 := ℝ))).prod
      ((Complex.ofRealCLM.analyticAt p.2).comp (analyticAt_snd (𝕜 := ℝ)))
  have hΔ := AnalyticAt.comp
    (g := fun q : PotPair × ℂ => discrim q.1 q.2)
    (f := fun q : PhysicalL2 × ℝ => (realSlice q.1,(q.2 : ℂ)))
    ((analyticOnNhd_discrim (realSlice p.1,(p.2 : ℂ)) (mem_univ _)).restrictScalars (𝕜 := ℝ)) hA
  have hcomp := AnalyticAt.comp (g := fun z : ℂ => z.re)
    (f := fun q : PhysicalL2 × ℝ => discrim (realSlice q.1) (q.2 : ℂ))
    (Complex.reCLM.analyticAt _) hΔ
  change AnalyticAt ℝ (fun q : PhysicalL2 × ℝ =>
    (discrim (realSlice q.1) (q.2 : ℂ)).re-(2*parity n).re) p
  convert! hcomp.sub (analyticAt_const (v := (2*parity n).re)) using 1 <;> rfl

theorem periodicRealChar_partial_ne_zero (u : PhysicalL2) (n : ℤ) (upper : Bool)
    (hgap : actualGapLowerAllE02_38 u n<actualGapUpperAllE02_38 u n) :
    (fderiv ℝ (periodicRealChar n) (u,endpoint u n upper)) (0,1) ≠ 0 := by
  let x := endpoint u n upper
  have hD := (analyticAt_periodicRealChar n (u,x)).differentiableAt.hasFDerivAt
  have hcurve : HasDerivAt (fun r : ℝ => (u,r)) (0,1) x :=
    (hasDerivAt_const x u).prodMk (hasDerivAt_id x)
  have hρ : HasDerivAt (fun r : ℝ => periodicRealChar n (u,r))
      ((fderiv ℝ (periodicRealChar n) (u,x)) (0,1)) x := by
    simpa only [Function.comp_def] using hD.comp_hasDerivAt x hcurve
  have hr := ((discrim_realRestriction_deriv38 u x).2.1).sub_const ((2*parity n).re)
  have hp : (fderiv ℝ (periodicRealChar n) (u,x)) (0,1) =
      (deriv (discrim (realSlice u)) (x : ℂ)).re := hρ.unique hr
  intro hz
  apply endpoint_discrim_deriv_ne_zero u n upper hgap
  apply Complex.ext
  · exact hp.symm.trans hz
  · exact (discrim_realRestriction_deriv38 u x).2.2

theorem analyticAt_endpoint (u : PhysicalL2) (n : ℤ) (upper : Bool)
    (hgap : actualGapLowerAllE02_38 u n<actualGapUpperAllE02_38 u n) :
    AnalyticAt ℝ (fun v : PhysicalL2 => endpoint v n upper) u := by
  apply real_root_label_analyticAt (periodicRealChar n) (fun v => endpoint v n upper) u
    (analyticAt_periodicRealChar n _) (endpoint_continuous n upper).continuousAt
  · intro v
    simp only [periodicRealChar,endpoint_discrim_value,sub_self]
  · exact periodicRealChar_partial_ne_zero u n upper hgap

end
end NlsGge.GK38.GradEigen38
