import QuantumNLS.TerraMultiRound59RCompatibility

/-! Real polynomials as finite sums of diagonals of continuous multilinear maps. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound59PolynomialProperty
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.TranslatedCorrelation
open QuantumNLS.TerraMultiRound59CoefficientPolynomial QuantumNLS.TerraMultiRound59MinimalPolynomial
open QuantumNLS.TerraMultiRound59SobolevCoordinates QuantumNLS.TerraMultiRound59RCompatibility

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

inductive RealPolynomial : (E → ℝ) → Prop
  | zero : RealPolynomial (fun _ => 0)
  | diagonal (n : ℕ) (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ) :
      RealPolynomial (fun x => p (fun _ => x))
  | add {f g : E → ℝ} : RealPolynomial f → RealPolynomial g → RealPolynomial (fun x => f x + g x)
  | scale (c : ℝ) {f : E → ℝ} : RealPolynomial f → RealPolynomial (fun x => c * f x)

theorem polynomial_sum {ι : Type*} (S : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i ∈ S, RealPolynomial (f i)) : RealPolynomial (fun x => ∑ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (RealPolynomial.zero (E := E))
  | @insert a S ha ih =>
    have hp := RealPolynomial.add (hf a (Finset.mem_insert_self a S))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))
    simpa [Finset.sum_insert, ha] using hp

variable {L : ℝ} [Fact (0 < L)]

theorem coefficient_polynomial_precomp {k : ℕ} (hk : 1 ≤ k) (κ : ℝ) (s n : ℕ)
    (T : E →L[ℝ] Ell2) :
    RealPolynomial (fun x => coefficientPolynomial (L := L) hk κ s n (T x)) := by
  unfold coefficientPolynomial
  apply polynomial_sum
  intro ell hell
  apply polynomial_sum
  intro d hd
  by_cases he : 2 * ell + 1 + d = n
  · simp only [he, ↓reduceIte]
    by_cases hdk : d ≤ 2 * k
    · simp only [hdk, ↓reduceDIte]
      apply polynomial_sum
      intro t ht
      let P := (realTreeForm (L := L) hk hdk κ t).compContinuousLinearMap (fun _ => T)
      have hP := RealPolynomial.diagonal ((2 * t.numNodes + 1) + 1) P
      exact hP
    · simp only [hdk, ↓reduceDIte]
      exact RealPolynomial.zero
  · simp only [he, ↓reduceIte]
    exact RealPolynomial.zero

theorem Rfield_polynomial (j : ℕ) (hj : 2 ≤ j) (κ : ℝ) :
    RealPolynomial (Rfield (L := L) j hj κ) := by
  exact RealPolynomial.scale ((-1 : ℝ) ^ j)
    (coefficient_polynomial_precomp (L := L) (E := Hk L (j - 1)) (k := j - 1)
      (by omega) κ j (2 * j + 1) ((coordinates (L := L) (j - 1)).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ))

theorem R1field_polynomial (κ : ℝ) : RealPolynomial (R1field (L := L) κ) := by
  have hp := coefficient_polynomial_precomp (L := L) (E := Hk L 1) (k := 1) (by omega) κ 2 3
    ((coordinates (L := L) 1).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)
  have hp' := RealPolynomial.scale (-1) hp
  convert hp' using 1
  funext v
  change -coefficientPolynomial (L := L) (k := 1) (by omega) κ 2 3 (coordinates (L := L) 1 v) =
    (-1 : ℝ) * coefficientPolynomial (L := L) (k := 1) (by omega) κ 2 3 (coordinates (L := L) 1 v)
  ring

#print axioms RealPolynomial
#print axioms polynomial_sum
#print axioms coefficient_polynomial_precomp
#print axioms Rfield_polynomial
#print axioms R1field_polynomial
end QuantumNLS.TerraMultiRound59PolynomialProperty
