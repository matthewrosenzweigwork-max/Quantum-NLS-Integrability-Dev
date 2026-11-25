import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS017Support1
import NlsGge.ThirdConsultation.KSPS.KSPS014Support5
import NlsGge.GK38.GradFundamentalSpectralDerivative

                                                                                                                    
                                                                                                       
                                                                                                                
                                                                                                  
                                                                                                                   
                                                                                                      
                                                                                                                          
set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators Topology

namespace NlsGge.ThirdConsultation.KSPS017W
noncomputable section
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation.KSPS

/-- The zero-filled endpoint remainder component as a function of the spectral parameter. -/
def Rfun {N : ℕ} (φ : SobolevC N) (b : Bool) (i : Fin 2) (z : ℂ) : ℂ :=
  if hz : z = 0 then (0 : ℂ) else KSPSWKB.sourceRemainderVector φ b ⟨z, hz⟩ 1 i

/-- The explicit (non-remainder) part of the WKB column at x = 1. -/
def explicitOne {N : ℕ} (φ : SobolevC N) (b : Bool) (z : ℂ) : Fin 2 → ℂ :=
  if b then
    (Complex.exp (Complex.I * z * ((1 : ℝ) : ℂ)) *
      NlsGge.ThirdConsultation.KSPSRiccati.phaseFactor φ true z 1) • ![KSPSWKB.beta φ z 1, 1]
  else
    (Complex.exp (-(Complex.I * z * ((1 : ℝ) : ℂ))) *
      NlsGge.ThirdConsultation.KSPSRiccati.phaseFactor φ false z 1) • ![1, KSPSWKB.alpha φ z 1]

theorem wkbColumn_one_eq {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : {z : ℂ // z ≠ 0}) :
    KSPSWKB.wkbColumn φ b lam 1 = explicitOne φ b lam.1 +
      ((2 * Complex.I * lam.1) ^ N)⁻¹ • KSPSWKB.sourceRemainderVector φ b lam 1 := by
  cases b <;> rfl

theorem remainder_one_eq {N : ℕ} (φ : SobolevC N) (b : Bool) (z : ℂ) (hz : z ≠ 0) (i : Fin 2) :
    KSPSWKB.sourceRemainderVector φ b ⟨z, hz⟩ 1 i =
      (2 * Complex.I * z) ^ N *
        ((fundPair (toPotPair φ) z ⟨1, zero_le_one, le_rfl⟩ * KSPSWKB.initialColumns φ z) i
            (if b then 1 else 0) - explicitOne φ b z i) := by
  have hcols := wkbColumns_eq_fundPair_mul N φ ⟨z, hz⟩ 1 ⟨zero_le_one, le_rfl⟩
  have hcol : KSPSWKB.wkbColumns φ ⟨z, hz⟩ 1 i (if b then 1 else 0) =
      KSPSWKB.wkbColumn φ b ⟨z, hz⟩ 1 i := by
    cases b <;> simp [KSPSWKB.wkbColumns]
  have hpow : (2 * Complex.I * z) ^ N ≠ 0 := pow_ne_zero _ (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hz)
  rw [← hcols, hcol, wkbColumn_one_eq]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
  field_simp

theorem differentiableAt_invPowSum (N : ℕ) (c : ℕ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℂ (fun w : ℂ => ∑ k ∈ Finset.Icc 1 N, ((2 * Complex.I * w) ^ k)⁻¹ * c k) z :=
  (hasDerivAt_invPowSum N c hz).differentiableAt

theorem differentiableAt_alpha {N : ℕ} (φ : SobolevC N) (x : ℝ) {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℂ (fun w : ℂ => KSPSWKB.alpha φ w x) z := by
  unfold KSPSWKB.alpha
  exact (differentiableAt_invPowSum N (fun k => KSPSWKB.coefficientTrace φ false k x) hz).const_mul _

theorem differentiableAt_beta {N : ℕ} (φ : SobolevC N) (x : ℝ) {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℂ (fun w : ℂ => KSPSWKB.beta φ w x) z := by
  unfold KSPSWKB.beta
  exact (differentiableAt_invPowSum N (fun k => KSPSWKB.coefficientTrace φ true k x) hz).const_mul _

theorem differentiableAt_phaseFactor {N : ℕ} (φ : SobolevC N) (b : Bool) (x : ℝ) {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℂ (fun w : ℂ => NlsGge.ThirdConsultation.KSPSRiccati.phaseFactor φ b w x) z := by
  unfold NlsGge.ThirdConsultation.KSPSRiccati.phaseFactor
  exact ((differentiableAt_invPowSum N
    (fun k => NlsGge.ThirdConsultation.KSPSRiccati.«prefix» φ b k x) hz).const_mul _).cexp

theorem differentiableAt_initialColumns {N : ℕ} (φ : SobolevC N) (l j : Fin 2) {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℂ (fun w : ℂ => KSPSWKB.initialColumns φ w l j) z := by
  fin_cases l <;> fin_cases j
  · simp [KSPSWKB.initialColumns]
  · simpa [KSPSWKB.initialColumns] using differentiableAt_beta φ 0 hz
  · simpa [KSPSWKB.initialColumns] using differentiableAt_alpha φ 0 hz
  · simp [KSPSWKB.initialColumns]

theorem differentiableAt_fundOne {N : ℕ} (φ : SobolevC N) (i l : Fin 2) (z : ℂ) :
    DifferentiableAt ℂ (fun w : ℂ => fundPair (toPotPair φ) w ⟨1, zero_le_one, le_rfl⟩ i l) z :=
  (hasDerivAt_fundSpectralIntegral38 (toPotPair φ) z ⟨1, zero_le_one, le_rfl⟩ i l).differentiableAt

theorem differentiableAt_explicitOne {N : ℕ} (φ : SobolevC N) (b : Bool) (i : Fin 2) {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℂ (fun w : ℂ => explicitOne φ b w i) z := by
  have he1 : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (Complex.I * w * ((1 : ℝ) : ℂ))) z := by
    fun_prop
  have he2 : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (-(Complex.I * w * ((1 : ℝ) : ℂ)))) z := by
    fun_prop
  cases b <;> fin_cases i
  · simpa [explicitOne] using he2.fun_mul (differentiableAt_phaseFactor φ false 1 hz)
  · simpa [explicitOne] using (he2.fun_mul (differentiableAt_phaseFactor φ false 1 hz)).fun_mul
      (differentiableAt_alpha φ 1 hz)
  · simpa [explicitOne] using (he1.fun_mul (differentiableAt_phaseFactor φ true 1 hz)).fun_mul
      (differentiableAt_beta φ 1 hz)
  · simpa [explicitOne] using he1.fun_mul (differentiableAt_phaseFactor φ true 1 hz)

/-- The holomorphic representative of the remainder component on lam != 0. -/
theorem Rfun_eventuallyEq {N : ℕ} (φ : SobolevC N) (b : Bool) (i : Fin 2) {lam : ℂ} (hlam : lam ≠ 0) :
    Rfun φ b i =ᶠ[𝓝 lam] fun z : ℂ => (2 * Complex.I * z) ^ N *
        ((∑ l : Fin 2, fundPair (toPotPair φ) z ⟨1, zero_le_one, le_rfl⟩ i l *
            KSPSWKB.initialColumns φ z l (if b then 1 else 0)) - explicitOne φ b z i) := by
  filter_upwards [eventually_ne_nhds hlam] with z hz
  unfold Rfun
  rw [dif_neg hz, remainder_one_eq φ b z hz i, Matrix.mul_apply]

/-- S017-1. -/
theorem sourceRemainder_one_differentiableAt {N : ℕ} (φ : SobolevC N) (b : Bool) (i : Fin 2)
    (lam : ℂ) (hlam : lam ≠ 0) :
    DifferentiableAt ℂ (fun z : ℂ => if hz : z = 0 then (0 : ℂ) else
      KSPSWKB.sourceRemainderVector φ b ⟨z, hz⟩ 1 i) lam := by
  have hG : DifferentiableAt ℂ (fun z : ℂ => (2 * Complex.I * z) ^ N *
        ((∑ l : Fin 2, fundPair (toPotPair φ) z ⟨1, zero_le_one, le_rfl⟩ i l *
            KSPSWKB.initialColumns φ z l (if b then 1 else 0)) - explicitOne φ b z i)) lam := by
    refine DifferentiableAt.mul (by fun_prop) (DifferentiableAt.sub ?_ (differentiableAt_explicitOne φ b i hlam))
    simp only [Fin.sum_univ_two]
    exact ((differentiableAt_fundOne φ i 0 lam).mul (differentiableAt_initialColumns φ 0 _ hlam)).add
      ((differentiableAt_fundOne φ i 1 lam).mul (differentiableAt_initialColumns φ 1 _ hlam))
  exact hG.congr_of_eventuallyEq (Rfun_eventuallyEq φ b i hlam)

theorem Rfun_differentiableAt {N : ℕ} (φ : SobolevC N) (b : Bool) (i : Fin 2)
    {lam : ℂ} (hlam : lam ≠ 0) : DifferentiableAt ℂ (Rfun φ b i) lam :=
  sourceRemainder_one_differentiableAt φ b i lam hlam

end
end NlsGge.ThirdConsultation.KSPS017W
