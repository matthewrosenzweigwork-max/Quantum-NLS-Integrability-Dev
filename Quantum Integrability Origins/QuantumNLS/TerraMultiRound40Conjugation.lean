import QuantumNLS.TerraMultiRound39ConjugateResolvent
import QuantumNLS.RiccatiPointwiseDisc

/-! Conjugation covariance of signed physical fixed points. -/
set_option autoImplicit false
noncomputable section
open Complex ComplexConjugate
namespace QuantumNLS.TerraMultiRound40Conjugation
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1
open QuantumNLS.RiccatiSobolevE2b QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.RiccatiPointwiseDisc QuantumNLS.TerraMultiRound38SignedPicard
open QuantumNLS.TerraMultiRound39ConjugateResolvent QuantumNLS.TerraMultiRound39PhysicalBall

theorem jEll_invol (x : Ell2) : jEll (jEll x) = x := by
  apply lp.ext
  funext k
  simp

theorem jEll_sub (x y : Ell2) : jEll (x - y) = jEll x - jEll y := by
  apply lp.ext
  funext k
  simp

theorem jEll_real_smul (c : ℝ) (x : Ell2) : jEll ((c : ℂ) • x) = (c : ℂ) • jEll x := by
  apply lp.ext
  funext k
  simp only [jEll_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]

/-- Fourier convolution commutes with physical conjugation. -/
theorem jEll_mulBil {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (x y : Ell2) :
    jEll (mulBil hL ha x y) = mulBil hL ha (jEll x) (jEll y) := by
  have hfields : toField L a (jEll (mulBil hL ha x y)) =
      toField L a (mulBil hL ha (jEll x) (jEll y)) := by
    funext k
    rw [toField_jEll, mulBil_apply, toField_mulEll, mulBil_apply, toField_mulEll]
    simp only [convC, toField_jEll, RCLike.conj_tsum, map_mul]
    rw [← (Equiv.neg ℤ).tsum_eq (fun j : ℤ =>
      conj (toField L a x j) * conj (toField L a y (-k - j)))]
    apply tsum_congr
    intro j
    change conj (toField L a x (-j)) * conj (toField L a y (-k - -j)) =
      conj (toField L a x (-j)) * conj (toField L a y (-(k - j)))
    rw [show -k - -j = -(k - j) by omega]
  apply lp.ext
  funext k
  have h := congrFun hfields k
  dsimp [toField] at h
  have hp := pw_ne_zero L a k
  have hm := congrArg (fun z : ℂ => z * ((pw L a k : ℝ) : ℂ)) h
  simpa only [div_mul_cancel₀ _ hp, jEll_apply] using hm

/-- The physical signed map intertwines conjugation of both field and solution. -/
theorem physicalT_jEll {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (hY : 0 < |Y|) (κ : ℝ) (u r : Ell2) :
    jEll (physicalT hL ha hY κ u r) = physicalT hL ha hY κ (jEll u) (jEll r) := by
  simp only [physicalT, signedT, jEll_sub, jEll_real_smul, signedCLM_jEll,
    jEll_mulBil, jEll_invol]

theorem physical_fixed_conj {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (hY : 0 < |Y|) (κ : ℝ) (u r : Ell2)
    (hr : physicalT hL ha hY κ u r = r) :
    physicalT hL ha hY κ (jEll u) (jEll r) = jEll r := by
  rw [← physicalT_jEll, hr]

end QuantumNLS.TerraMultiRound40Conjugation
#print axioms QuantumNLS.TerraMultiRound40Conjugation.jEll_mulBil
#print axioms QuantumNLS.TerraMultiRound40Conjugation.physicalT_jEll
#print axioms QuantumNLS.TerraMultiRound40Conjugation.physical_fixed_conj
