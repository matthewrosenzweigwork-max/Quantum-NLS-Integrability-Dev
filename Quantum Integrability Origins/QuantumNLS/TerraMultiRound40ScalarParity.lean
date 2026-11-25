import QuantumNLS.TerraMultiRound40LogParity
import QuantumNLS.TerraMultiRound40SignedODE
import QuantumNLS.TerraMultiRound40Conjugation
import QuantumNLS.RiccatiExpansions

/-! Scalar parity for signed fixed points when their product lies in the
principal logarithm disk. The large-parameter bound is a separate step. -/
set_option autoImplicit false
noncomputable section
open Complex ComplexConjugate MeasureTheory
namespace QuantumNLS.TerraMultiRound40ScalarParity
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.RiccatiPointwiseDisc QuantumNLS.RiccatiExpansions
open QuantumNLS.TerraMultiRound39PhysicalBall QuantumNLS.TerraMultiRound40SignedODE
open QuantumNLS.TerraMultiRound40Conjugation QuantumNLS.TerraMultiRound40LogParity

def scalar (L a : ℝ) (u r : Ell2) : ℂ :=
  ∫ x in 0..L, conj (physRep L a u x) * physRep L a r x

/-- Opposite signed physical fixed points have conjugate-odd scalar integrals
once their product is inside the logarithm disk. -/
theorem scalar_parity_of_small_product (L : ℝ) [hLf : Fact (0 < L)] {a Y κ : ℝ}
    (ha : 1 / 2 < a) (hY : 0 < |Y|) (hκ : κ ≠ 0) (u r s : Ell2)
    (hr : physicalT hLf.out ha hY κ u r = r)
    (hs : physicalT hLf.out ha (by simpa using hY : 0 < |-Y|) κ u s = s)
    (hsmall : ∀ x, ‖(κ : ℂ) * physRep L a r x * conj (physRep L a s x)‖ < 1) :
    scalar L a u r = -conj (scalar L a u s) := by
  have hs' := physical_fixed_conj hLf.out ha (by simpa using hY : 0 < |-Y|) κ u s hs
  have hsode := physical_signed_ode L ha (by simpa using hY : 0 < |-Y|) κ (jEll u) (jEll s) hs'
  have hrode := physical_signed_ode L ha hY κ u r hr
  have hz (x : ℝ) : HasDerivAt (physRep L a (jEll s))
      (conj (physRep L a u x) + (Y : ℂ) * physRep L a (jEll s) x -
        (κ : ℂ) * physRep L a u x * physRep L a (jEll s) x ^ 2) x := by
    apply (hsode.1 x).congr_deriv
    simp only [physRep_jEll, Complex.conj_conj]
    push_cast
    ring
  have hsmall' : ∀ x, ‖(κ : ℂ) * physRep L a r x * physRep L a (jEll s) x‖ < 1 := by
    simpa only [physRep_jEll] using hsmall
  have hrder (x : ℝ) : HasDerivAt (physRep L a r)
      (physRep L a u x - (Y : ℂ) * physRep L a r x -
        (κ : ℂ) * conj (physRep L a u x) * physRep L a r x ^ 2) x := by
    apply (hrode.1 x).congr_deriv
    ring
  have h := periodic_riccati_integrals L Y κ hκ (physRep L a u) (physRep L a r)
    (physRep L a (jEll s)) (physRep_continuous L ha u) hrder hz hrode.2 hsode.2 hsmall'
  have hc := (Complex.conjLIE.toLinearIsometry.intervalIntegral_comp_comm
    (μ := volume) (a := 0) (b := L)
    (fun x => conj (physRep L a u x) * physRep L a s x))
  change (∫ x in 0..L, conj (conj (physRep L a u x) * physRep L a s x)) =
    conj (∫ x in 0..L, conj (physRep L a u x) * physRep L a s x) at hc
  simp only [map_mul, Complex.conj_conj] at hc
  simp only [physRep_jEll] at h
  change scalar L a u r = _ at h
  rw [hc] at h
  simpa only [scalar] using h

end QuantumNLS.TerraMultiRound40ScalarParity
#print axioms QuantumNLS.TerraMultiRound40ScalarParity.scalar_parity_of_small_product
