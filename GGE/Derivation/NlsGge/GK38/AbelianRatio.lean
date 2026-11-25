import NlsGge.GK38.AbelianPeriods
import NlsGge.GK38.XiSqLocal

/-! Actual arbitrary-sequence numerator/root quotient for P2.
UNCOMPILED prospective source. This is NOT the critical-point-only A5 chi. -/
set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38
noncomputable section

/-- pi_m cancels the library omitProd's existing 1/pi_m, exactly once. -/
def p2OmittedRatio38 (m : ℤ) (p : (PotPair × Lib.L2Seq) × ℂ) : ℂ :=
  ((Lib.piN m:ℂ)*Lib.omitProd m p.1.2 p.2)/a5OmittedRootProduct38 m (p.1.1,p.2)

 theorem p2OmittedRatio_analytic38 (m : ℤ) :
    AnalyticOnNhd ℂ (p2OmittedRatio38 m)
      {p : (PotPair × Lib.L2Seq) × ℂ | (p.1.1,p.2) ∈ a5OmittedRootDomain38 m} := by
  intro p hp
  have hps : AnalyticAt ℂ (fun q : (PotPair × Lib.L2Seq) × ℂ => q.1.2) p :=
    AnalyticAt.comp (g := fun q : PotPair × Lib.L2Seq => q.2)
      (f := fun q : (PotPair × Lib.L2Seq) × ℂ => q.1) analyticAt_snd analyticAt_fst
  have hpf : AnalyticAt ℂ (fun q : (PotPair × Lib.L2Seq) × ℂ => q.1.1) p :=
    AnalyticAt.comp (g := fun q : PotPair × Lib.L2Seq => q.1)
      (f := fun q : (PotPair × Lib.L2Seq) × ℂ => q.1) analyticAt_fst analyticAt_fst
  have hn : AnalyticAt ℂ (fun q : (PotPair × Lib.L2Seq) × ℂ =>
      (Lib.piN m:ℂ)*Lib.omitProd m q.1.2 q.2) p := analyticAt_const.mul (AnalyticAt.comp
    (g := fun q : ℂ × Lib.L2Seq => Lib.omitProd m q.2 q.1)
    (f := fun q : (PotPair × Lib.L2Seq) × ℂ => (q.2,q.1.2))
    (Lib.analyticOnNhd_omitProd m (p.2,p.1.2) trivial)
    (analyticAt_snd.prod hps))
  have hd := AnalyticAt.comp (g := a5OmittedRootProduct38 m)
    (f := fun q : (PotPair × Lib.L2Seq) × ℂ => (q.1.1,q.2))
    (a5OmittedRoot_analytic38 m (p.1.1,p.2) hp) (hpf.prod analyticAt_snd)
  exact hn.div hd (a5OmittedRoot_ne_zero38 m (p.1.1,p.2) hp)

/-- The arbitrary numerator ratio is analytic on the entire ORIGINAL own disc,
including its own cut; every OTHER actual cut is earned excluded. -/
theorem p2OmittedRatio_own_disc_analytic38 (m : ℤ) (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 φ C R) (s : Lib.L2Seq) :
    AnalyticOnNhd ℂ (fun z => p2OmittedRatio38 m ((φ,s),z)) (closedBall (C m) (R m)) := by
  intro z hz
  exact (p2OmittedRatio_analytic38 m ((φ,s),z)
    (a5OwnClosedBall_omittedDomain38 φ hφ C R hfam m z hz)).comp
    ((analyticAt_const).prod analyticAt_id)

/-- Actual product identity before any quotient cancellation. -/
theorem p2Omit_cross_identity38 (n m : ℤ) (s : Lib.L2Seq) (z : ℂ) :
    (Lib.sigmaOf s n-z)*Lib.omitProd n s z =
      (Lib.sigmaOf s m-z)*Lib.omitProd m s z :=
  (Lib.entProd_eq_mul_omitProd n s z).symm.trans (Lib.entProd_eq_mul_omitProd m s z)

/-- Exact book factorization on the actual root domain, with no gap division.
The sigma_n denominator premise will be earned for the uniform tail; exceptional
finite labels must be handled through the original entire numerator instead. -/
theorem p2FullNumerator_div_root38 (n m : ℤ) (s : Lib.L2Seq)
    (φ : PotPair) (z : ℂ) (hp : (φ,z) ∈ rootDomain38)
    (hsn : Lib.sigmaOf s n-z ≠ 0) :
    p2FullNumerator38 n s z/canonRoot38 φ z =
      Complex.I*((Lib.sigmaOf s m-z)/stdRoot38 (tauN φ m) (gamma2 φ m) z)*
        p2OmittedRatio38 m ((φ,s),z)/(Lib.sigmaOf s n-z) := by
  have hp' : (φ,z) ∈ a5OmittedRootDomain38 m :=
    ⟨hp.1,fun j _ => rootDomain_avoids38 hp j⟩
  have hD := a5OmittedRoot_ne_zero38 m (φ,z) hp'
  have hS : stdRoot38 (tauN φ m) (gamma2 φ m) z ≠ 0 := by
    have hs := stdRoot_ne_zero38 (lamMinus φ m) (lamPlus φ m) z (rootDomain_avoids38 hp m)
    simpa only [add_comm (lamMinus φ m),← tauN_value38 φ hp.1 m,
      ← gamma2_value38 φ hp.1 m] using hs
  have hc := p2Omit_cross_identity38 n m s z
  rw [a5CanonRoot_omitted_factorization38 m (φ,z) hp]
  unfold p2FullNumerator38 p2OmittedRatio38 rootFactor38
  field_simp [hD,hS,hsn,Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero m),Complex.I_ne_zero]
  simp only [Complex.I_sq] at *
  linear_combination -hc

#print axioms p2OmittedRatio_analytic38
#print axioms p2OmittedRatio_own_disc_analytic38
#print axioms p2Omit_cross_identity38
#print axioms p2FullNumerator_div_root38
end
end NlsGge.GK38
