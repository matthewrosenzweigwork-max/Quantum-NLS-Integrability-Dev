import QuantumNLS.TerraMultiRound42PositiveExpansion
import QuantumNLS.TerraMultiRound41Coefficients
import QuantumNLS.RiccatiChargeIdent

/-! Identification of the positive-height native model polynomial with the
literal recursively defined signed physical coefficients. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Complex Finset
namespace QuantumNLS.TerraMultiRound42Polynomial
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1
open QuantumNLS.RiccatiSobolevE2 QuantumNLS.RiccatiSobolevE2b
open QuantumNLS.RiccatiChargeLevels QuantumNLS.RiccatiRemainder
open QuantumNLS.RiccatiExpansions QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.ClassicalCharges
open QuantumNLS.RiccatiChargeIdent QuantumNLS.TerraMultiRound41Coefficients

/-- The physical representatives of the native charge coefficients are the
classical recursive coefficients, through any prescribed finite order. -/
theorem model_coefficients {L a S : ℝ} {M : ℕ} (hL : 0 < L)
    (ha : 1 / 2 < a) (haS : a + (M : ℝ) + 1 ≤ S) (hM : 1 ≤ M)
    (κ : ℝ) (u : Ell2) (D : Ell2 →ₗ[ℂ] Ell2)
    (hD : ∀ y : dDom L, D (y : Ell2) = dmulEll L y) (f : ℝ → ℂ)
    (hrep : physRep L a (lowT L a S u) = f) :
    ∀ n : ℕ, 1 ≤ n → n ≤ M →
      physRep L a (Wc S hL ha κ u (jEll u) D n) = vseq κ f n := by
  obtain ⟨h1, hrec⟩ := printed_recursion hL ha haS hM κ u (jEll u) D hD
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn hnm
    rcases n with _ | n
    · omega
    rcases n with _ | n
    · simpa only [Nat.zero_add, vseq_one] using h1.trans hrep
    · funext t
      rw [hrec n hnm t, vseq_succ, ← neg_mul]
      rw [ih (n + 1) (by omega) (by omega) (by omega)]
      have hs : Finset.Ico 1 (n + 1) = Finset.Icc 1 n := by ext j; simp
      rw [hs, lowT_jEll, physRep_jEll, hrep]
      congr 2
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_Icc.mp hj
      rw [ih j (by omega) (by omega) (by omega),
        ih (n + 1 - j) (by omega) (by omega) (by omega)]

/-- At positive imaginary spectral height, the model truncation is exactly
the signed physical inverse-power polynomial. -/
theorem positive_polynomial {L a S Y : ℝ} {M : ℕ} (hL : 0 < L)
    (ha : 1 / 2 < a) (haS : a + (M : ℝ) + 1 ≤ S) (hM : 1 ≤ M)
    (κ : ℝ) (u : Ell2) (D : Ell2 →ₗ[ℂ] Ell2)
    (hD : ∀ y : dDom L, D (y : Ell2) = dmulEll L y) (f : ℝ → ℂ)
    (hrep : physRep L a (lowT L a S u) = f) (t : ℝ) :
    physRep L a (rMsum (wAbs (mulLin hL ha) D (jEll (lowT L a S u))
        (lowT L a S u) ((κ / L : ℝ) : ℂ)) (((Y : ℂ) * Complex.I)⁻¹) M) t =
      ∑ n ∈ Finset.Icc 1 M, aseq κ f n t * ((Y : ℂ)⁻¹) ^ n := by
  rw [physRep_rMsum hL ha, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' := (Finset.mem_Icc.mp hn).1
  have hc := congrFun (model_coefficients hL ha haS hM κ u D hD f hrep n hn'
    (Finset.mem_Icc.mp hn).2) t
  change physRep L a (wAbs (mulLin hL ha) D (lowT L a S (jEll u))
    (lowT L a S u) ((κ / L : ℝ) : ℂ) n) t = vseq κ f n t at hc
  rw [lowT_jEll] at hc
  rw [hc]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [aseq, Nat.succ_sub_one, mul_inv_rev, Complex.inv_I, mul_pow, pow_succ]
  have hI : Complex.I * -Complex.I = 1 := by simp [Complex.I_mul_I]
  calc
    _ = (Complex.I * -Complex.I) * ((-Complex.I) ^ m * vseq κ f (m + 1) t *
        (((Y : ℂ)⁻¹) ^ m * (Y : ℂ)⁻¹)) := by ring
    _ = _ := by rw [hI]; simp

#print axioms model_coefficients
#print axioms positive_polynomial
end QuantumNLS.TerraMultiRound42Polynomial
