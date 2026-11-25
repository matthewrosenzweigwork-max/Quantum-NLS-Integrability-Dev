import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS007Host
import NlsGge.Atomic.G1.G1005
import NlsGge.Atomic.G1.G1007
import NlsGge.Atomic.G1.G1010
import NlsGge.Atomic.G1.G1011
import NlsGge.Atomic.G1.G1022

/- KSPS-007 SUPPORT01 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS007Support.lean.
   Bridge between the KSPSVolterra Picard objects and the landed G1 Neumann series (G1-005/G1-010/G1-011):
   term k = potentialVolterraTerm38, fundamental = Mf for x >= 0, det fundamental = 1 (G1-010, NOT assumed),
   hence the adjugate2 of the fundamental matrix is its genuine inverse. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Volterra NlsGge.Atomic.G1011S2

namespace NlsGge.ThirdConsultation.KSPS007Support

theorem E_eq_freeE (lam : ℂ) (t : ℝ) : KSPSVolterra.E lam t = freeE lam t := rfl

theorem R_eq_Rm : KSPSVolterra.R = Rm := rfl

theorem R_mul_phi (p : PotPair) (t : ℝ) : KSPSVolterra.R * KSPSVolterra.phi p t = PCm p t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [KSPSVolterra.R, KSPSVolterra.phi, PCm, rawPotCoeff38, Matrix.mul_apply, Fin.sum_univ_two]

theorem term_eq_pot (p : PotPair) (lam : ℂ) : ∀ (k : ℕ) (x : ℝ),
    KSPSVolterra.term k x lam p = potentialVolterraTerm38 p lam k x := by
  intro k
  induction k with
  | zero =>
    intro x
    show KSPSVolterra.E lam x = freeZsFundamentalComplex lam x
    rw [← freeE_eq]
    rfl
  | succ k ih =>
    intro x
    funext i j
    show (∫ t in (0 : ℝ)..x, (KSPSVolterra.E lam (x - t) * KSPSVolterra.R * KSPSVolterra.phi p t *
        KSPSVolterra.term k t lam p) i j) =
      ∫ s in (0 : ℝ)..x, (freeZsFundamentalComplex lam (x - s) *
        rawPotCoeff38 (potRepFst38 p) (potRepSnd38 p) s * freeKernelVolterraTerm38 (potRepFst38 p)
          (potRepSnd38 p) lam k s) i j
  
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    have h1 : KSPSVolterra.term k t lam p = freeKernelVolterraTerm38 (potRepFst38 p) (potRepSnd38 p) lam k t :=
      ih t
    simp only [h1]
    rw [Matrix.mul_assoc (KSPSVolterra.E lam (x - t)) KSPSVolterra.R, R_mul_phi, ← freeE_eq]
    rfl

theorem summable_pot (p : PotPair) (lam : ℂ) {x : ℝ} (hx : 0 ≤ x) (i j : Fin 2) :
    Summable (fun n : ℕ => potentialVolterraTerm38 p lam n x i j) :=
  (((NlsGge.Atomic.G1005.G1005_restricted p lam).1 x hx).1 i j)

theorem fundamental_eq_Mf (φ : KSPSVolterra.SobolevC 1) (lam : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    KSPSVolterra.fundamental φ x lam = Mf (KSPSVolterra.toPair φ) lam x := by
  have hS : Summable (fun n : ℕ => potentialVolterraTerm38 (KSPSVolterra.toPair φ) lam n x) :=
    Pi.summable.2 fun i => Pi.summable.2 fun j => summable_pot (KSPSVolterra.toPair φ) lam hx i j
  ext i j
  have hcont : Continuous (Matrix.entryLinearMap ℂ ℂ i j : PairMat38 →ₗ[ℂ] ℂ) :=
    (continuous_id.matrix_elem i j)
  have h1 : HasSum (fun n : ℕ => potentialVolterraTerm38 (KSPSVolterra.toPair φ) lam n x i j)
      ((∑' n : ℕ, potentialVolterraTerm38 (KSPSVolterra.toPair φ) lam n x) i j) :=
    hS.hasSum.map (Matrix.entryLinearMap ℂ ℂ i j : PairMat38 →ₗ[ℂ] ℂ) hcont
  unfold KSPSVolterra.fundamental Mf
  simp only [term_eq_pot]
  exact h1.tsum_eq

theorem det_fundamental (φ : KSPSVolterra.SobolevC 1) (lam : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    (KSPSVolterra.fundamental φ x lam).det = 1 := by
  rw [fundamental_eq_Mf φ lam hx]
  exact NlsGge.Atomic.G1010.G1010_det (KSPSVolterra.toPair φ) lam hx

theorem inverseFundamental_eq_inv (φ : KSPSVolterra.SobolevC 1) (lam : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    KSPSVolterra.inverseFundamental φ x lam = (KSPSVolterra.fundamental φ x lam)⁻¹ := by
  have h1 : KSPSVolterra.inverseFundamental φ x lam = (KSPSVolterra.fundamental φ x lam).adjugate := by
    unfold KSPSVolterra.inverseFundamental KSPSVolterra.adjugate2
    rw [Matrix.adjugate_fin_two]
  rw [h1, Matrix.inv_def, det_fundamental φ lam hx]
  simp

end NlsGge.ThirdConsultation.KSPS007Support
