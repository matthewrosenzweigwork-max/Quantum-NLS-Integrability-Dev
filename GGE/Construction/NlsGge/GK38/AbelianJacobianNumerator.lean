import NlsGge.GK38.AbelianFreeDerivative

/-! Actual double-omitted numerator columns for the Abelian Jacobian.
UNCOMPILED source preparation. Every formula is concrete product algebra;
no derivative or invertibility oracle is supplied. -/
set_option autoImplicit false
open Set Filter Topology SummationFilter
namespace NlsGge.GK38
noncomputable section

/-- The actual derivative numerator after removing the n-th and r-th factors. -/
def p3NumeratorColumn38 (n r : ℤ) (s : Lib.L2Seq) (z : ℂ) : ℂ :=
  (-2 / (Lib.piN n : ℂ)) * Lib.omitProd r (Lib.sOmit n s z) z

namespace P3JacobianColumns

theorem sOmit_other_add_single (n r : ℤ) (hrn : r ≠ n)
    (s : Lib.L2Seq) (z t : ℂ) :
    Lib.sOmit n (s + t • lp.single 2 r (1 : ℂ)) z =
      Lib.sOmit n s z + t • lp.single 2 r (1 : ℂ) := by
  have hn : (s + t • lp.single 2 r (1 : ℂ) : Lib.L2Seq) n = s n := by
    simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul, lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 r (1 : ℂ) (Ne.symm hrn),
      mul_zero, add_zero]
  unfold Lib.sOmit
  rw [hn]
  abel

theorem sigmaOf_sOmit_other (n r : ℤ) (hrn : r ≠ n)
    (s : Lib.L2Seq) (z : ℂ) :
    Lib.sigmaOf (Lib.sOmit n s z) r = Lib.sigmaOf s r := by
  simp only [Lib.sigmaOf, Lib.sOmit_apply, hrn, ite_false, add_zero]

theorem column_add_single (n r : ℤ) (hrn : r ≠ n)
    (s : Lib.L2Seq) (z t : ℂ) :
    p3NumeratorColumn38 n r (s + t • lp.single 2 r (1 : ℂ)) z =
      p3NumeratorColumn38 n r s z := by
  unfold p3NumeratorColumn38
  rw [sOmit_other_add_single n r hrn s z t, Lib.omitProd_add_single]

/-- Extract a genuine finite factor before differentiating: no sigma-z division. -/
theorem numerator_factor (n r : ℤ) (hrn : r ≠ n)
    (s : Lib.L2Seq) (z : ℂ) :
    p2FullNumerator38 n s z =
      (Lib.sigmaOf s r - z) * p3NumeratorColumn38 n r s z := by
  have he : Lib.omitProd n s z =
      (1 / (Lib.piN n : ℂ)) * Lib.entProdJ (z, Lib.sOmit n s z) := by
    unfold Lib.omitProd
    rw [Lib.omitProd_eq_entProdJ]
  unfold p2FullNumerator38 p3NumeratorColumn38
  rw [he]
  unfold Lib.entProdJ
  rw [Lib.entProd_eq_mul_omitProd r, sigmaOf_sOmit_other n r hrn s z]
  ring

/-- The exact affine line formula is valid even when sigma_r=z. -/
theorem numerator_add_single (n r : ℤ) (hrn : r ≠ n)
    (s : Lib.L2Seq) (z t : ℂ) :
    p2FullNumerator38 n (s + t • lp.single 2 r (1 : ℂ)) z =
      p2FullNumerator38 n s z + t * p3NumeratorColumn38 n r s z := by
  rw [numerator_factor n r hrn, column_add_single n r hrn s z t,
    numerator_factor n r hrn s z]
  have hσ : Lib.sigmaOf (s + t • lp.single 2 r (1 : ℂ)) r =
      Lib.sigmaOf s r + t := by
    simp only [Lib.sigmaOf, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul, lp.single_apply_self, mul_one]
    ring
  rw [hσ]
  ring

theorem column_entire (n r : ℤ) (s : Lib.L2Seq) :
    AnalyticOnNhd ℂ (p3NumeratorColumn38 n r s) univ := by
  intro z _
  have hs : AnalyticAt ℂ (fun w : ℂ => Lib.sOmit n s w) z :=
    AnalyticAt.comp
      (g := fun q : ℂ × Lib.L2Seq => Lib.sOmit n q.2 q.1)
      (f := fun w : ℂ => (w,s))
      (Lib.analyticOnNhd_sOmit n (z,s) trivial)
      (analyticAt_id.prod analyticAt_const)
  have ho : AnalyticAt ℂ
      (fun w : ℂ => Lib.omitProd r (Lib.sOmit n s w) w) z :=
    AnalyticAt.comp
      (g := fun q : ℂ × Lib.L2Seq => Lib.omitProd r q.2 q.1)
      (f := fun w : ℂ => (w,Lib.sOmit n s w))
      (Lib.analyticOnNhd_omitProd r (z,Lib.sOmit n s z) trivial)
      (analyticAt_id.prod hs)
  exact analyticAt_const.mul ho

/-- Integrability is earned before the affine period identity is used. -/
theorem column_integrable (m n r : ℤ) (φ : PotPair) (hφ : φ ∈ gkW)
    (s : Lib.L2Seq) :
    CircleIntegrable (fun z => p3NumeratorColumn38 n r s z / canonRoot38 φ z)
      (discC φ m) (discR φ m) :=
  (abelianPeriod_fullfamily_realization38 φ hφ (discC φ) (discC φ)
    (discR φ) (discR φ) (isolating_family38 φ hφ) (isolating_family38 φ hφ)
    m (p3NumeratorColumn38 n r s) (column_entire n r s)).1

end P3JacobianColumns
end
end NlsGge.GK38
