import NlsGge.GK38.AbelianFullNumeratorVariation

/-! Source-only actual scalar column of the full Qstar numerator. Extracting
the finite factor earns the affine line formula even at an input collision. -/
set_option autoImplicit false
namespace NlsGge.GK38.P6FullNumeratorVariation
noncomputable section

theorem fullNumerator_add_single (r : ℤ) (s : Lib.L2Seq) (z t : ℂ) :
    fullNumerator (s+t • lp.single 2 r (1 : ℂ)) z=
      fullNumerator s z+t*((-2/(Real.pi : ℂ))*Lib.omitProd r s z) := by
  have hn : p2FullNumerator38 r (s+t • lp.single 2 r (1 : ℂ)) z=
      p2FullNumerator38 r s z := by
    unfold p2FullNumerator38
    rw [Lib.omitProd_add_single]
  rw [fullNumerator_factor r,fullNumerator_factor r,hn,Lib.sigmaOf_line]
  simp only [lp.single_apply_self,mul_one]
  unfold p2FullNumerator38
  ring

theorem fullVariation_unit_column (r : ℤ) (s : Lib.L2Seq) (z : ℂ) :
    fullVariation s (lp.single 2 r (1 : ℂ)) z=
      (-2/(Real.pi : ℂ))*Lib.omitProd r s z := by
  have he : (fun t : ℂ => fullNumerator (s+t • lp.single 2 r (1 : ℂ)) z)=
      (fun t : ℂ => fullNumerator s z+t*((-2/(Real.pi : ℂ))*Lib.omitProd r s z)) :=
    funext (fullNumerator_add_single r s z)
  have hd : HasDerivAt
      (fun t : ℂ => fullNumerator s z+t*((-2/(Real.pi : ℂ))*Lib.omitProd r s z))
      ((-2/(Real.pi : ℂ))*Lib.omitProd r s z) 0 := by
    simpa only [one_mul] using!
      (((hasDerivAt_id (0 : ℂ)).mul_const ((-2/(Real.pi : ℂ))*Lib.omitProd r s z)).const_add
        (fullNumerator s z))
  rw [← he] at hd
  exact (fullVariation_hasDerivAt s _ z).unique hd

end
end NlsGge.GK38.P6FullNumeratorVariation
