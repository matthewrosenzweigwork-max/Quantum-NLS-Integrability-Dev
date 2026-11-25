import NlsGge.GK38.AbelianRatio
import NlsGge.GK38.XiSqRootCorrection

/-! Genuine arbitrary sigma/tau ratio factorization, preserving piN and products.
UNCOMPILED prospective source. Ratio convergence remains an honest helper input
until earned for actual arbitrary sigma by P2ActualC3Draft. -/
set_option autoImplicit false
open Set Filter Topology Metric SummationFilter
namespace NlsGge.GK38
noncomputable section

 theorem p2OmittedNumerator_product38 (n : ℤ) (s : Lib.L2Seq) (z : ℂ) :
    (Lib.piN n:ℂ)*Lib.omitProd n s z =
      ∏'[symmetricIcc ℤ] j : ℤ, if j=n then 1 else (Lib.sigmaOf s j-z)/(Lib.piN j:ℂ) := by
  have _convergence := Lib.multipliable_omit n s z
  unfold Lib.omitProd
  rw [← mul_assoc,mul_one_div_cancel (Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero n)),one_mul]
  rfl

/-- Both genuine factor-family products precede their termwise multiplication. -/
theorem p2SigmaTau_ratio_product38 (n : ℤ) (φ : PotPair) (s : Lib.L2Seq) (z : ℂ)
    (hp : (φ,z) ∈ a5OmittedRootDomain38 n)
    (hprod : Multipliable (Lib.ratioFam (Lib.sigmaOf s) (tauN φ) n z) (symmetricIcc ℤ)) :
    (Lib.piN n:ℂ)*Lib.omitProd n s z =
      a5TauNumerator38 n (φ,z)*Lib.ratioProd (Lib.sigmaOf s) (tauN φ) n z := by
  have hτ := a5TauNumerator_multipliable38 n (φ,z) hp.1
  have hfactor (j : ℤ) :
      (if j=n then 1 else (tauN φ j-z)/(Lib.piN j:ℂ))*
        Lib.ratioFam (Lib.sigmaOf s) (tauN φ) n z j =
      (if j=n then 1 else (Lib.sigmaOf s j-z)/(Lib.piN j:ℂ)) := by
    by_cases hj : j=n
    · simp only [hj,Lib.ratioFam,ite_true,one_mul]
    · have ht : tauN φ j-z ≠ 0 := by
        intro he
        apply hp.2 j hj
        rw [← sub_eq_zero.mp he]
        exact a5Tau_mem_segment38 φ hp.1 j
      simp only [hj,ite_false,Lib.ratioFam]
      field_simp [ht]
  rw [p2OmittedNumerator_product38,a5TauNumerator_product38 n (φ,z) hp.1]
  unfold Lib.ratioProd
  rw [← hτ.tprod_mul hprod]
  exact tprod_congr (fun j => (hfactor j).symm)

/-- The root correction is independent of the arbitrary sequence; its actual nonzero
factorization earns cancellation, also on the own slit in the omitted domain. -/
theorem p2OmittedRatio_ratioQ38 (n : ℤ) (φ : PotPair) (s : Lib.L2Seq) (z : ℂ)
    (hp : (φ,z) ∈ a5OmittedRootDomain38 n) (c : ℝ) (hc : 0 < c)
    (hsep : ∀ j : ℤ, j ≠ n → c⁻¹*|(j:ℝ)-n| ≤ ‖tauN φ j-z‖)
    (hprod : Multipliable (Lib.ratioFam (Lib.sigmaOf s) (tauN φ) n z) (symmetricIcc ℤ)) :
    p2OmittedRatio38 n ((φ,s),z) =
      Lib.ratioProd (Lib.sigmaOf s) (tauN φ) n z/a5QCorrectionProduct38 n (φ,z) := by
  unfold p2OmittedRatio38
  rw [p2SigmaTau_ratio_product38 n φ s z hp hprod,
    a5OmittedRoot_tauQ_factorization38 n (φ,z) hp c hc hsep]
  have hT := a5TauNumerator_ne_zero38 n (φ,z) hp
  have hQ := a5QCorrectionProduct_ne_zero38 n (φ,z) hp c hc hsep
  field_simp [hT,hQ]

#print axioms p2OmittedNumerator_product38
#print axioms p2SigmaTau_ratio_product38
#print axioms p2OmittedRatio_ratioQ38
end
end NlsGge.GK38
