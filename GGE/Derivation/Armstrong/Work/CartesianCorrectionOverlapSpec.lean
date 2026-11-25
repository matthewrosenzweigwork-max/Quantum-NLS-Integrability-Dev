import Armstrong.Work.CartesianContinuationSpec
import Armstrong.Work.CartesianTerminalRootSpec
import Armstrong.Work.RawBetaOverlap
import NlsGge.GK38.AbelianPaddedPeriodMapBound
import Mathlib.Analysis.Convex.PathConnected

/-!
# Weighted correction comparison on certified disc overlaps

Ordinary speculative infrastructure for the sign-explicit Section16 route.
Equal actual omitted numerators give the same positive quotient q. The existing
shared-ODE invariant is applied to Q(z)=(z-a)(z-b) on the convex overlap of two
certified own discs, both containing the lower tip and the actual Dirichlet
terminal. It gives equality of H*T(mu), with the literal terminal H, including
collapsed gaps and H=0. No coefficient uniqueness or division by H/gap is used.

The final wrapper retains the same supplied F and its own period, comparing its
literal zero extension on the original phi-disc with a full completion on any
supplied certified family. The family geometry is an explicit producer input;
the local correction theorem does not itself export that internal certificate.
No eta or whole Cartesian source theorem is asserted here.
-/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

/-- Full numerator equality implies equality of the positive own quotient on
all spectral parameters, without requiring a denominator cancellation. -/
theorem gk16_own_ratio_eq_of_full_numerator_eq38
    (n : ℤ) (phi : PotPair) (s t : Lib.L2Seq)
    (hnum : p2FullNumerator38 n s = p2FullNumerator38 n t) :
    (fun z : ℂ => p2OmittedRatio38 n ((phi,s),z)) =
      (fun z : ℂ => p2OmittedRatio38 n ((phi,t),z)) := by
  funext z
  have homit : Lib.omitProd n s z = Lib.omitProd n t z := by
    have h := congrFun hnum z
    change (-2 : ℂ)*Lib.omitProd n s z = (-2 : ℂ)*Lib.omitProd n t z at h
    exact mul_left_cancel₀ (by norm_num : (-2 : ℂ) ≠ 0) h
  simp only [p2OmittedRatio38,homit]

/-- The weighted terminal correction is independent of both the certified
own disc and the full completion, provided their actual entire numerators
agree and have the normalized own period. Collapse is included. -/
theorem gk16_weighted_correction_independent38
    (n : ℤ) (phi : PotPair) (hphi : phi ∈ gkW)
    (C0 C1 : ℤ → ℂ) (rho0 rho1 : ℤ → ℝ)
    (hfamily0 : IsolatingFamily38 phi C0 rho0)
    (hfamily1 : IsolatingFamily38 phi C1 rho1)
    (s t : Lib.L2Seq)
    (hnum : p2FullNumerator38 n s = p2FullNumerator38 n t)
    (hperiod : abelianPeriod38 n phi (p2FullNumerator38 n s) =
      2*(Real.pi : ℂ)) :
    gk16TerminalRoot38 n phi *
      gk16OwnCorrectionCoefficient38 phi n s (C0 n) (rho0 n) (muSeq phi n) =
    gk16TerminalRoot38 n phi *
      gk16OwnCorrectionCoefficient38 phi n t (C1 n) (rho1 n) (muSeq phi n) := by
  let a := lamMinus phi n
  let b := lamPlus phi n
  let Q : ℂ → ℂ := fun z => (z-a)*(z-b)
  let T0 := gk16OwnCorrectionCoefficient38 phi n s (C0 n) (rho0 n)
  let T1 := gk16OwnCorrectionCoefficient38 phi n t (C1 n) (rho1 n)
  have hperiod1 : abelianPeriod38 n phi (p2FullNumerator38 n t) =
      2*(Real.pi : ℂ) := by
    rw [← hnum]
    exact hperiod
  have hT0 := gk16_own_correction_coefficient38 phi hphi C0 rho0 hfamily0 n s hperiod
  have hT1 := gk16_own_correction_coefficient38 phi hphi C1 rho1 hfamily1 n t hperiod1
  have hq := gk16_own_ratio_eq_of_full_numerator_eq38 n phi s t hnum
  obtain ⟨c0,N0,hgeom0,hspec0⟩ := hfamily0
  obtain ⟨c1,N1,hgeom1,hspec1⟩ := hfamily1
  have ha0 : a ∈ ball (C0 n) (rho0 n) :=
    (hspec0.1 n).1 (left_mem_segment ℝ _ _)
  have ha1 : a ∈ ball (C1 n) (rho1 n) :=
    (hspec1.1 n).1 (left_mem_segment ℝ _ _)
  have hmu0 : muSeq phi n ∈ ball (C0 n) (rho0 n) := (hspec0.1 n).2.1
  have hmu1 : muSeq phi n ∈ ball (C1 n) (rho1 n) := (hspec1.1 n).2.1
  let U : Set ℂ := ball (C0 n) (rho0 n) ∩ ball (C1 n) (rho1 n)
  have hU : IsOpen U := isOpen_ball.inter isOpen_ball
  have hUc : IsPreconnected U :=
    ((convex_ball (C0 n) (rho0 n)).inter (convex_ball (C1 n) (rho1 n))).isPreconnected
  have hQd (z : ℂ) : HasDerivAt Q ((z-b)+(z-a)) z := by
    simpa only [Q,Pi.mul_def,id_eq,one_mul,mul_one] using
      (((hasDerivAt_id z).sub_const a).mul ((hasDerivAt_id z).sub_const b))
  have hQhalf (z : ℂ) : deriv Q z / 2 = z-(a+b)/2 := by
    rw [(hQd z).deriv]
    ring
  have hQ : DifferentiableOn ℂ Q U :=
    fun z _hz => (hQd z).differentiableAt.differentiableWithinAt
  exact rawBetaTerminalEqualityOfSharedODE38 U hU hUc Q T0 T1
    (fun z => p2OmittedRatio38 n ((phi,s),z)-1) hQ
    (hT0.1.differentiableOn.mono inter_subset_left)
    (hT1.1.differentiableOn.mono inter_subset_right)
    (fun z hz => by
      rw [hQhalf z]
      exact hT0.2 z hz.1)
    (fun z hz => by
      rw [hQhalf z]
      calc
        _ = p2OmittedRatio38 n ((phi,t),z)-1 := hT1.2 z hz.2
        _ = p2OmittedRatio38 n ((phi,s),z)-1 := by rw [congrFun hq z])
    a (muSeq phi n) (gk16TerminalRoot38 n phi)
    ⟨ha0,ha1⟩ ⟨hmu0,hmu1⟩
    (by simp only [Q,sub_self,zero_mul])
    (gk16_terminal_root_sq38 n phi hphi)

/-- The same F's original-disc correction and a supplied completion's
fixed-disc correction have the same actual terminal exponent. The literal
numerator equality is earned from restriction and extend/restrict invariance. -/
theorem gk16_actual_original_fixed_weighted_correction38
    (n : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k)
    (phi : GKPotential38) (s : Lib.L2Seq)
    (hrestrict : F n phi.1 = p2Restrict38 n s)
    (C : ℤ → ℂ) (rho : ℤ → ℝ)
    (hfamily : IsolatingFamily38 phi.1 C rho)
    (hperiod : abelianPeriod38 n phi.1
      (p6PsiNumerator38 n (F n) phi.1) = 2*(Real.pi : ℂ)) :
    gk16TerminalRoot38 n phi.1 *
      gk16OwnCorrectionCoefficient38 phi.1 n (p2Extend38 n (F n phi.1))
        (discC phi.1 n) (discR phi.1 n) (muSeq phi.1 n) =
    gk16TerminalRoot38 n phi.1 *
      gk16OwnCorrectionCoefficient38 phi.1 n s (C n) (rho n) (muSeq phi.1 n) := by
  have hnum : p2FullNumerator38 n (p2Extend38 n (F n phi.1)) =
      p2FullNumerator38 n s := by
    rw [hrestrict]
    exact p6Numerator_extend_restrict38 n s
  exact gk16_weighted_correction_independent38 n phi.1 phi.2
    (discC phi.1) C (discR phi.1) rho (isolating_family38 phi.1 phi.2) hfamily
    (p2Extend38 n (F n phi.1)) s hnum hperiod

/-- Both signed terminal models are unchanged by the same-F original/fixed
comparison. Arbitrary eps is harmless here: only equality of H*T is used. -/
theorem gk16_actual_original_fixed_terminal_models38
    (n : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k)
    (phi : GKPotential38) (s : Lib.L2Seq)
    (hrestrict : F n phi.1 = p2Restrict38 n s)
    (C : ℤ → ℂ) (rho : ℤ → ℝ)
    (hfamily : IsolatingFamily38 phi.1 C rho)
    (hperiod : abelianPeriod38 n phi.1
      (p6PsiNumerator38 n (F n) phi.1) = 2*(Real.pi : ℂ)) :
    let H := gk16TerminalRoot38 n phi.1
    let mu := muSeq phi.1 n
    let tau := (lamMinus phi.1 n+lamPlus phi.1 n)/2
    let Torig := gk16OwnCorrectionCoefficient38 phi.1 n
      (p2Extend38 n (F n phi.1)) (discC phi.1 n) (discR phi.1 n)
    let Tfixed := gk16OwnCorrectionCoefficient38 phi.1 n s (C n) (rho n)
    ∀ eps : ℂ,
      (2*(tau-mu)-2*eps*H)*Complex.exp (eps*H*Torig mu) =
      (2*(tau-mu)-2*eps*H)*Complex.exp (eps*H*Tfixed mu) := by
  dsimp only
  intro eps
  have h := gk16_actual_original_fixed_weighted_correction38
    n F phi s hrestrict C rho hfamily hperiod
  simpa only [mul_assoc] using congrArg
    (fun z : ℂ =>
      (2*((lamMinus phi.1 n+lamPlus phi.1 n)/2-muSeq phi.1 n)-
        2*eps*gk16TerminalRoot38 n phi.1)*Complex.exp (eps*z)) h

end
end NlsGge.GK38
