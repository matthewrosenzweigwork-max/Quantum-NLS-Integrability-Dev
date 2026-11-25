import NlsGge.GK38.PairAsymptoticsSeqPerturbed
import NlsGge.GK38.PairAsymptoticsVolterra

/-!
# F5: square mass of the first Volterra forcing

The finite-window estimate follows from the two signs of the perturbed Fourier estimate.
The potential mass is the sum of component squares, distinct from the product sup norm.
-/

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace NlsGge.GK38

noncomputable section

def seqMass38 (N : PairCont38) (s : ℝ) : ℝ :=
  ‖ext38 N s 0 0‖ ^ 2 + ‖ext38 N s 0 1‖ ^ 2 +
    ‖ext38 N s 1 0‖ ^ 2 + ‖ext38 N s 1 1‖ ^ 2

theorem seqMass38_nonneg (N : PairCont38) (s : ℝ) : 0 ≤ seqMass38 N s := by
  unfold seqMass38
  positivity

theorem continuous_seqMass38 (N : PairCont38) : Continuous (seqMass38 N) := by
  have h := continuous_ext38 N
  unfold seqMass38
  fun_prop

theorem seq_pairForce38_diagonal (φ : PotPair) (z : ℂ) (t : Set.Icc (0 : ℝ) 1) (i : Fin 2) :
    pairForce38 φ z t i i = 0 := by
  rw [pairForce38_entry]
  fin_cases i <;> simp [freeE, potCoeff38, Matrix.mul_apply, Fin.sum_univ_two]

theorem pairForce38_upper (φ : PotPair) (z : ℂ) (t : Set.Icc (0 : ℝ) 1) :
    pairForce38 φ z t 0 1 = Complex.I * seqOsc38 (potRepFst38 φ) (-z) t := by
  rw [pairForce38_entry, seqOsc38, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  simp [freeE, potCoeff38, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem pairForce38_lower (φ : PotPair) (z : ℂ) (t : Set.Icc (0 : ℝ) 1) :
    pairForce38 φ z t 1 0 = -Complex.I * seqOsc38 (potRepSnd38 φ) z t := by
  rw [pairForce38_entry, seqOsc38, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  simp [freeE, potCoeff38, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem seqMass38_pairForce (φ : PotPair) (z : ℂ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    seqMass38 (pairForce38 φ z) t =
      ‖seqOsc38 (potRepFst38 φ) (-z) t‖ ^ 2 + ‖seqOsc38 (potRepSnd38 φ) z t‖ ^ 2 := by
  simp [seqMass38, ext38_of_mem _ ht, seq_pairForce38_diagonal,
    pairForce38_upper, pairForce38_lower]

theorem seqMass38_force_sum_le (φ : PotPair) {c : ℝ} (hc : 0 ≤ c)
    (υ : ℤ → ℂ) (hυ : ∀ n : ℤ, ‖υ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ c)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (T : Finset ℤ) :
    ∑ n ∈ T, seqMass38 (pairForce38 φ (υ n)) t ≤ Real.exp c ^ 2 * potNormSq38 φ := by
  have h1 := seqOsc38_neg_sum_sq_le (stronglyMeasurable_coverRep38 φ.1).aestronglyMeasurable
    (intervalIntegrable_coverRep38_sq_one φ.1) ht hc υ hυ T
  have h2 := seqOsc38_sum_sq_le (stronglyMeasurable_coverRep38 φ.2).aestronglyMeasurable
    (intervalIntegrable_coverRep38_sq_one φ.2) ht hc υ hυ T
  rw [integral_sq_coverRep38_one] at h1 h2
  simp_rw [seqMass38_pairForce φ _ ht]
  rw [Finset.sum_add_distrib]
  change (∑ n ∈ T, ‖seqOsc38 (coverRep38 φ.1) (-υ n) t‖ ^ 2) +
    (∑ n ∈ T, ‖seqOsc38 (coverRep38 φ.2) (υ n) t‖ ^ 2) ≤ _
  exact (add_le_add h1 h2).trans_eq (by unfold potNormSq38; ring)

end

end NlsGge.GK38
