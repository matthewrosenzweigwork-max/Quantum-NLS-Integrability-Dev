import NlsGge.GK38.AbelianFullPeriodHilbert
import NlsGge.GK38.AbelianJacobianGeometry
import NlsGge.GK38.AbelianJacobianPeriods
import NlsGge.GK38.AbelianFullColumnPeriods

/-! UNCOMPILED genuine full-space padding and exact finite-factor difference
columns. This is algebra of actual derivatives, without a Qn/Qstar norm-limit
or inverse assumption and without any sigma-z division. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38
noncomputable section

def p6PaddedJacobian38 (n : ℤ) (φ : PotPair) (s : Lib.L2Seq) :
    Lib.L2Seq →L[ℂ] Lib.L2Seq :=
  ((p2Extend38 n).comp
    ((fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (φ,t)) (p2Restrict38 n s)).comp
      (p2Restrict38 n))) +
    (2 : ℂ) • ((lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 n).comp
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n))

theorem p6PaddedJacobian_matrix38 (n : ℤ) (φ : PotPair) (hφ : φ ∈ gkW)
    (s : Lib.L2Seq) (m r : P2Index38 n) :
    p6PaddedJacobian38 n φ s (lp.single 2 r.val (1 : ℂ)) m.val =
      (((n-m.val : ℤ) : ℂ))*abelianPeriod38 m.val φ (p3NumeratorColumn38 n r.val s) := by
  have hr : p2Restrict38 n (lp.single 2 r.val (1 : ℂ))=lp.single 2 r (1 : ℂ) := by
    simpa only [one_smul] using P3FreeDerivative.restrict_single n r 1
  have hzero : (lp.single (E := fun _ : ℤ => ℂ) 2 r.val (1 : ℂ)) n=0 :=
    lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 r.val (1 : ℂ) (Ne.symm r.property)
  have hcol : p3NumeratorColumn38 n r.val (p2Extend38 n (p2Restrict38 n s)) =
      p3NumeratorColumn38 n r.val s :=
    funext (P3JacobianColumns.column_extend_restrict n r.val s)
  have hpad : (((2 : ℂ) •
      ((lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 n).comp
        (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n)))
      (lp.single 2 r.val (1 : ℂ))) m.val=0 := by
    change (2 : ℂ)*(lp.single (E := fun _ : ℤ => ℂ) 2 n
      ((lp.single (E := fun _ : ℤ => ℂ) 2 r.val (1 : ℂ)) n)) m.val=0
    rw [hzero,lp.single_zero]
    simp
  unfold p6PaddedJacobian38
  rw [add_apply]
  change (p2Extend38 n
      ((fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (φ,t)) (p2Restrict38 n s))
        (p2Restrict38 n (lp.single 2 r.val (1 : ℂ))))) m.val+_ = _
  rw [hpad,add_zero,p2Extend_at38,hr,
    P3JacobianColumns.matrix_coordinate n m r φ hφ (p2Restrict38 n s),hcol]

theorem p6Full_column_factor38 (n r : ℤ) (hrn : r ≠ n) (s : Lib.L2Seq) (z : ℂ) :
    (-2/(Real.pi : ℂ))*Lib.omitProd r s z =
      ((Lib.sigmaOf s n-z)/(Real.pi : ℂ))*p3NumeratorColumn38 n r s z := by
  have hf := P6FullNumeratorVariation.fullVariation_factor n s
    (lp.single 2 r (1 : ℂ)) z
  rw [P6FullNumeratorVariation.fullVariation_unit_column,
    P4NumeratorVariation.variation_unit_column n r hrn] at hf
  rw [lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 r (1 : ℂ) (Ne.symm hrn),
    zero_mul,zero_add] at hf
  exact hf.trans (by ring)

theorem p6Scaled_column_difference38 (n m r : ℤ) (hrn : r ≠ n)
    (s : Lib.L2Seq) (z : ℂ) :
    (((n-m : ℤ) : ℂ))*p3NumeratorColumn38 n r s z-
      (-2/(Real.pi : ℂ))*Lib.omitProd r s z =
        ((z-(m : ℂ)*(Real.pi : ℂ)-s n)/(Real.pi : ℂ))*p3NumeratorColumn38 n r s z := by
  rw [p6Full_column_factor38 n r hrn s z]
  dsimp [Lib.sigmaOf]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring

def p6DifferenceColumn38 (n m r : ℤ) (s : Lib.L2Seq) (z : ℂ) : ℂ :=
  ((z-(m : ℂ)*(Real.pi : ℂ)-s n)/(Real.pi : ℂ))*p3NumeratorColumn38 n r s z

theorem p6DifferenceColumn_entire38 (n m r : ℤ) (s : Lib.L2Seq) :
    AnalyticOnNhd ℂ (p6DifferenceColumn38 n m r s) univ := by
  intro z _
  exact (((analyticAt_id.sub analyticAt_const).sub analyticAt_const).div_const).mul
    (P3JacobianColumns.column_entire n r s z (mem_univ _))

theorem p6DifferenceColumn_integrable38 (n m r : ℤ)
    (φ : PotPair) (hφ : φ ∈ gkW) (s : Lib.L2Seq) :
    CircleIntegrable (fun z => p6DifferenceColumn38 n m r s z/canonRoot38 φ z)
      (discC φ m) (discR φ m) :=
  (abelianPeriod_fullfamily_realization38 φ hφ (discC φ) (discC φ)
    (discR φ) (discR φ) (isolating_family38 φ hφ) (isolating_family38 φ hφ)
    m (p6DifferenceColumn38 n m r s) (p6DifferenceColumn_entire38 n m r s)).1

theorem p6Padded_minus_Qstar_matrix_period38 (n : ℤ) (φ : PotPair) (hφ : φ ∈ gkW)
    (s : Lib.L2Seq) (m r : P2Index38 n) :
    (p6PaddedJacobian38 n φ s-p6Qstar38 φ s) (lp.single 2 r.val (1 : ℂ)) m.val =
      abelianPeriod38 m.val φ (p6DifferenceColumn38 n m.val r.val s) := by
  have hc := P3JacobianColumns.column_integrable m.val n r.val φ hφ s
  have hscaled : CircleIntegrable
      (fun z => (((n-m.val : ℤ) : ℂ))*(p3NumeratorColumn38 n r.val s z/canonRoot38 φ z))
      (discC φ m.val) (discR φ m.val) := by
    simpa only [Pi.smul_apply,smul_eq_mul] using! hc.const_smul (a := (((n-m.val : ℤ) : ℂ)))
  have hstar := P6FullJacobian.fullColumn_circleIntegrable m.val r.val φ hφ s
  have _hdiff := p6DifferenceColumn_integrable38 n m.val r.val φ hφ s
  change p6PaddedJacobian38 n φ s (lp.single 2 r.val (1 : ℂ)) m.val-
    p6Qstar38 φ s (lp.single 2 r.val (1 : ℂ)) m.val = _
  rw [p6PaddedJacobian_matrix38 n φ hφ s m r,p6Qstar_unit_column38 φ hφ s m.val r.val]
  change (((n-m.val : ℤ) : ℂ))*abelianPeriod38 m.val φ (p3NumeratorColumn38 n r.val s)-
    abelianPeriod38 m.val φ (P6FullJacobian.fullColumn r.val s)=_
  have he :
      (fun z => (((n-m.val : ℤ) : ℂ))*(p3NumeratorColumn38 n r.val s z/canonRoot38 φ z)-
        P6FullJacobian.fullColumn r.val s z/canonRoot38 φ z) =
      (fun z => p6DifferenceColumn38 n m.val r.val s z/canonRoot38 φ z) := by
    funext z
    have h := p6Scaled_column_difference38 n m.val r.val r.property s z
    change (((n-m.val : ℤ) : ℂ))*(p3NumeratorColumn38 n r.val s z/canonRoot38 φ z)-
      ((-2/(Real.pi : ℂ))*Lib.omitProd r.val s z)/canonRoot38 φ z =
        (((z-(m.val : ℂ)*(Real.pi : ℂ)-s n)/(Real.pi : ℂ))*
          p3NumeratorColumn38 n r.val s z)/canonRoot38 φ z
    rw [← h]
    ring
  unfold abelianPeriod38
  rw [← circleIntegral.integral_const_mul,← circleIntegral.integral_sub hscaled hstar,he]

end
end NlsGge.GK38
