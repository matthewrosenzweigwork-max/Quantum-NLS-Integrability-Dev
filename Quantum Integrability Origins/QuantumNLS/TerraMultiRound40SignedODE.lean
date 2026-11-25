import QuantumNLS.TerraMultiRound39SignedGain
import QuantumNLS.RiccatiPointwiseDisc

/-! The physical Riccati ODE for both signs of the real spectral parameter. -/
set_option autoImplicit false
noncomputable section
open Complex ComplexConjugate
namespace QuantumNLS.TerraMultiRound40SignedODE
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1
open QuantumNLS.RiccatiSobolevE2b QuantumNLS.RiccatiPointwiseCoef
open QuantumNLS.RiccatiPointwise QuantumNLS.RiccatiPointwiseRep
open QuantumNLS.RiccatiPointwiseDisc QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.TerraMultiRound38SignedPicard QuantumNLS.TerraMultiRound39PhysicalBall

theorem signed_denom_ne (L Y : ℝ) (hY : 0 < |Y|) (k : ℤ) :
    (Y : ℂ) + Complex.I * (freq L k : ℂ) ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp at hr
  exact (abs_pos.mp hY) hr

theorem signed_fixed_coord {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (hY : 0 < |Y|) (κ : ℝ) {u v r : Ell2}
    (hr : signedT hL ha hY κ u v r = r) (k : ℤ) :
    r k * ((Y : ℂ) + Complex.I * (freq L k : ℂ)) =
      u k - (κ : ℂ) * mulBil hL ha v (mulBil hL ha r r) k := by
  have hD := signed_denom_ne L Y hY k
  have h := congrArg (fun x : Ell2 => x k) hr
  change u k / ((Y : ℂ) + Complex.I * (freq L k : ℂ)) -
    (κ : ℂ) * (mulBil hL ha v (mulBil hL ha r r) k /
      ((Y : ℂ) + Complex.I * (freq L k : ℂ))) = r k at h
  rw [← h]
  field_simp

theorem signed_series_ode {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (hY : 0 < |Y|) (κ : ℝ) {u v r : Ell2}
    (hr : signedT hL ha hY κ u v r = r) (x : ℝ) :
    HasDerivAt (fun t : ℝ => series L (toField L a r) t)
      (-(Y : ℂ) * series L (toField L a r) x +
        (series L (toField L a u) x - (κ : ℂ) *
          (series L (toField L a v) x * series L (toField L a r) x ^ 2))) x := by
  have hrec (k : ℤ) :
      (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) / (L : ℂ)) * toField L a r k =
        Complex.I * ((Y : ℂ) * Complex.I) * toField L a r k + rhsD L a κ u v r k := by
    have h := signed_fixed_coord hL ha hY κ hr k
    have hW := congrFun (toField_mulBil_eq hL ha v r) k
    have hc : toField L a r k * ((Y : ℂ) + Complex.I * (freq L k : ℂ)) =
        rhsD L a κ u v r k := by
      unfold rhsD
      rw [← hW]
      unfold toField
      rw [div_mul_eq_mul_div, h]
      ring
    have hf : ((freq L k : ℝ) : ℂ) = 2 * (Real.pi : ℂ) * (k : ℂ) / (L : ℂ) := by
      unfold freq
      push_cast
      ring
    rw [hf] at hc
    have he : Complex.I * ((Y : ℂ) * Complex.I) = -(Y : ℂ) := by
      calc
        Complex.I * ((Y : ℂ) * Complex.I) = (Y : ℂ) * (Complex.I * Complex.I) := by ring
        _ = -(Y : ℂ) := by simp [← pow_two, Complex.I_sq]
    rw [he]
    linear_combination hc
  have h := series_hasDerivAt (L := L) (summable_norm_toField hL ha r)
    (summable_norm_rhsD hL ha κ u v r) hrec x
  rw [series_rhsD hL ha κ u v r x] at h
  have he : Complex.I * ((Y : ℂ) * Complex.I) = -(Y : ℂ) := by
    calc
      Complex.I * ((Y : ℂ) * Complex.I) = (Y : ℂ) * (Complex.I * Complex.I) := by ring
      _ = -(Y : ℂ) := by simp [← pow_two, Complex.I_sq]
  rw [he] at h
  exact h

/-- Signed fixed points have a periodic differentiable physical representative. -/
theorem physical_signed_ode (L : ℝ) [hLf : Fact (0 < L)] {a Y : ℝ}
    (ha : 1 / 2 < a) (hY : 0 < |Y|) (κ : ℝ) (u r : Ell2)
    (hr : physicalT hLf.out ha hY κ u r = r) :
    (∀ x : ℝ, HasDerivAt (physRep L a r)
      (-(Y : ℂ) * physRep L a r x + physRep L a u x -
        (κ : ℂ) * conj (physRep L a u x) * physRep L a r x ^ 2) x) ∧
      physRep L a r L = physRep L a r 0 := by
  constructor
  · intro x
    have h := (signed_series_ode hLf.out ha hY (κ / L) hr x).const_mul
      (((Real.sqrt L)⁻¹ : ℝ) : ℂ)
    have hs := sqrt_inv_sq_mul L hLf.out
    have hV : (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * series L (toField L a (jEll u)) x =
        conj ((((Real.sqrt L)⁻¹ : ℝ) : ℂ) * series L (toField L a u) x) := by
      rw [series_jEll, map_mul, Complex.conj_ofReal]
    have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hLf.out.ne'
    have hκ' : ((κ / L : ℝ) : ℂ) * (L : ℂ) = (κ : ℂ) := by
      rw [Complex.ofReal_div, div_mul_cancel₀ _ hL0]
    change HasDerivAt (physRep L a r) _ x at h
    convert h using 1
    simp only [physRep]
    rw [← hV, ← hκ']
    linear_combination (-((κ / L : ℝ) : ℂ) * (((Real.sqrt L)⁻¹ : ℝ) : ℂ) *
      series L (toField L a (jEll u)) x * series L (toField L a r) x ^ 2) * hs
  · exact physRep_periodic hLf.out r

end QuantumNLS.TerraMultiRound40SignedODE
#print axioms QuantumNLS.TerraMultiRound40SignedODE.signed_fixed_coord
#print axioms QuantumNLS.TerraMultiRound40SignedODE.signed_series_ode
#print axioms QuantumNLS.TerraMultiRound40SignedODE.physical_signed_ode
