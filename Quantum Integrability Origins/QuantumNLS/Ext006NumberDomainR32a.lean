import QuantumNLS.Ext006HSVacuumR32a

/-! Exponential number-weighted summability of the constructed vacuum follows
from the original HS strict-contraction hypotheses. This supplies an analytic
domain estimate needed before applying transformed creation polynomials; it
does not construct an implementer or assume its Heisenberg action. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Ext006NumberDomainR32a
open Occupation Ext006PairCoreCommutator Ext006FormalVacuumR31a
open Ext006CompressionR32a Ext006HSVacuumR32a TraceClass

lemma pairCreator_scale (S : Finset ℤ) (K : ℤ → ℤ → ℂ) (c : ℂ) :
    pairCreator S (fun i j => c*K i j) = c • pairCreator S K := by
  simp [pairCreator, Finset.smul_sum, smul_smul]

lemma coreTerm_scale (S : Finset ℤ) (K : ℤ → ℤ → ℂ) (c : ℂ) (n : ℕ) :
    coreTerm S (fun i j => c*K i j) n = c^n • coreTerm S K n := by
  rw [coreTerm, pairCreator_scale, smul_pow]
  simp only [coreTerm, LinearMap.smul_apply, smul_smul]
  rw [mul_comm]

/-- Homogeneity in each even degree, with exactly the source coefficient -1/2
in the underlying finite-core exponential. -/
lemma coefficient_scale_even (K : ℤ → ℤ → ℂ)
    (hK : ∀ i j, K i j = K j i) (c : ℂ) (m : Occ) {n : ℕ} (hm : total m = 2*n) :
    coefficient (fun i j => c*K i j) m = c^n * coefficient K m := by
  have hc : ∀ i j, c*K i j = c*K j i := fun i j => congrArg (c*·) (hK i j)
  rw [coefficient_even hc m.support m (Finset.Subset.refl _) hm,
    coefficient_even hK m.support m (Finset.Subset.refl _) hm, coreTerm_scale]
  rfl

/-- A finite exponential weight controls every polynomial number weight. -/
theorem summable_polynomial_of_exponential {I : Type*} (N : I → ℕ) (a : I → ℝ)
    (ha : ∀ i, 0 ≤ a i) (t : ℝ) (ht : 1 < t)
    (hs : Summable (fun i => t^(N i)*a i)) (p : ℕ) :
    Summable (fun i => (N i : ℝ)^p*a i) := by
  have ht0 : 0 < t := by linarith
  have hr : ‖t⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht0)]
    exact (inv_lt_one₀ ht0).mpr ht
  have hg := summable_pow_mul_geometric_of_norm_lt_one p hr
  let C : ℝ := ∑' n : ℕ, (n : ℝ)^p*(t⁻¹)^n
  have hb : ∀ n : ℕ, (n : ℝ)^p ≤ C*t^n := by
    intro n
    have h := hg.le_tsum n (fun j _ => by positivity)
    have he : (t⁻¹)^n*t^n = 1 := by
      rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero n ht0.ne')]
    calc
      (n : ℝ)^p = ((n : ℝ)^p*(t⁻¹)^n)*t^n := by rw [mul_assoc, he, mul_one]
      _ ≤ C*t^n := mul_le_mul_of_nonneg_right h (pow_nonneg ht0.le n)
  apply Summable.of_nonneg_of_le (fun i => mul_nonneg (pow_nonneg (Nat.cast_nonneg _) p) (ha i))
    (fun i => (mul_le_mul_of_nonneg_right (hb (N i)) (ha i)).trans_eq ?_) (hs.mul_left C)
  ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma hsSq_scale (b : HilbertBasis ℤ ℂ H) (K : H →L[ℂ] H) (c : ℂ) :
    hsSq b (c • K) = ENNReal.ofReal (‖c‖^2) * hsSq b K := by
  simp only [hsSq, smul_apply, norm_smul, mul_pow,
    ENNReal.ofReal_mul (sq_nonneg _), ENNReal.tsum_mul_left]

omit [CompleteSpace H] in
lemma coordinates_scale (b : HilbertBasis ℤ ℂ H) (K : H →L[ℂ] H) (c : ℂ) :
    coordinates b (c • K) = fun i j => c*coordinates b K i j := by
  funext i j
  simp [coordinates]

omit [CompleteSpace H] in
/-- Scaling by a positive real t multiplies the squared coefficient in particle
number N by t^N. Odd sectors vanish on both sides. -/
lemma coefficient_scale_norm_sq (b : HilbertBasis ℤ ℂ H) (K : H →L[ℂ] H)
    (hSym : ∀ i j, coordinates b K i j = coordinates b K j i)
    (t : ℝ) (ht : 0 ≤ t) (m : Occ) :
    ‖coefficient (coordinates b ((t : ℂ) • K)) m‖^2 =
      t^(total m) * ‖coefficient (coordinates b K) m‖^2 := by
  rw [coordinates_scale]
  by_cases hm : Even (total m)
  · obtain ⟨n, hn⟩ := hm
    have hn' : total m = 2*n := by omega
    rw [coefficient_scale_even _ hSym _ m hn', norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht, mul_pow, ← pow_mul, hn']
    simp only [Nat.mul_comm]
  · rw [coefficient_odd _ hm, coefficient_odd _ hm]
    simp

/-- There is an actual exponential particle-number weight with finite sum,
under the original HS condition and norm<1, regardless of HS norm size. -/
theorem exists_exponential_weight (b : HilbertBasis ℤ ℂ H) (K : H →L[ℂ] H)
    (hSym : ∀ i j, coordinates b K i j = coordinates b K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq b K ≠ ⊤) :
    ∃ t : ℝ, 1 < t ∧ Summable (fun m : Occ =>
      t^(total m) * ‖coefficient (coordinates b K) m‖^2) := by
  let t : ℝ := 2/(1+‖K‖)
  have ht : 1 < t := (lt_div_iff₀ (by positivity)).mpr (by linarith)
  have ht0 : 0 ≤ t := by linarith
  have htn : t*‖K‖ < 1 := by
    dsimp [t]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    linarith
  have hs : ∀ i j, coordinates b ((t : ℂ) • K) i j =
      coordinates b ((t : ℂ) • K) j i := by
    rw [coordinates_scale]
    intro i j
    change (t : ℂ)*coordinates b K i j = (t : ℂ)*coordinates b K j i
    rw [hSym]
  have hn' : ‖(t : ℂ) • K‖ < 1 := by
    simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0] using htn
  have hHS' : hsSq b ((t : ℂ) • K) ≠ ⊤ := by
    rw [hsSq_scale]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hHS
  refine ⟨t, ht, ?_⟩
  have h := summable_coefficients b ((t : ℂ) • K) hs hn' hHS'
  exact h.congr (coefficient_scale_norm_sq b K hSym t ht0)

/-- The same exponential domain estimate for the normalized vector that was
constructed in R32a. Its normalization scalar is finite and proved nonzero. -/
theorem normalized_exponential_weight (b : HilbertBasis ℤ ℂ H) (K : H →L[ℂ] H)
    (hSym : ∀ i j, coordinates b K i j = coordinates b K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq b K ≠ ⊤) :
    ∃ t : ℝ, 1 < t ∧ Summable (fun m : Occ =>
      t^(total m) * ‖normalized b K hSym hn hHS m‖^2) := by
  obtain ⟨t, ht, hs⟩ := exists_exponential_weight b K hSym hn hHS
  refine ⟨t, ht, ?_⟩
  have h := hs.mul_left (‖(‖coefficientExponential b K hSym hn hHS‖⁻¹ : ℂ)‖^2)
  convert h using 1
  ext m
  change t^(total m) * ‖(‖coefficientExponential b K hSym hn hHS‖⁻¹ : ℂ) *
    coefficient (coordinates b K) m‖^2 = _
  rw [norm_mul, mul_pow]
  ring

/-- In particular, all polynomial number weights of the constructed normalized
vacuum are summable. No transformed creation domains are postulated. -/
theorem normalized_polynomial_weight (b : HilbertBasis ℤ ℂ H) (K : H →L[ℂ] H)
    (hSym : ∀ i j, coordinates b K i j = coordinates b K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq b K ≠ ⊤) (p : ℕ) :
    Summable (fun m : Occ => (total m : ℝ)^p * ‖normalized b K hSym hn hHS m‖^2) := by
  obtain ⟨t, ht, hs⟩ := normalized_exponential_weight b K hSym hn hHS
  exact summable_polynomial_of_exponential total _ (fun _ => sq_nonneg _) t ht hs p

section Physical
variable {L : ℝ} [Fact (0 < L)]

/-- The constructed physical state has a finite expectation of an exponential
particle-number weight, in the existing physical spectral-number definition. -/
theorem physical_exponential_weight
    (K : PhysicalTensor.L2T L →L[ℂ] PhysicalTensor.L2T L)
    (hSym : ∀ i j, coordinates (Ext006KernelHilbertSchmidt.physicalBasis L) K i j =
      coordinates (Ext006KernelHilbertSchmidt.physicalBasis L) K j i)
    (hn : ‖K‖ < 1)
    (hHS : hsSq (Ext006KernelHilbertSchmidt.physicalBasis L) K ≠ ⊤) :
    ∃ t : ℝ, 1 < t ∧
      Ext006NumberPhase.numberExpectation (fun n => ENNReal.ofReal (t^n))
        (physicalNormalized K hSym hn hHS) ≠ ⊤ := by
  obtain ⟨t, ht, hs⟩ := normalized_exponential_weight
    (Ext006KernelHilbertSchmidt.physicalBasis L) K hSym hn hHS
  refine ⟨t, ht, ?_⟩
  have ht0 : 0 ≤ t := by linarith
  rw [Prop023FiniteModeLimit.numberExpectation_eq_occupation]
  simp only [Prop023FiniteModeLimit.mass, physicalNormalized_coefficient]
  simp_rw [← ENNReal.ofReal_mul (pow_nonneg ht0 _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => mul_nonneg
    (pow_nonneg ht0 _) (sq_nonneg _)) hs]
  exact ENNReal.ofReal_ne_top

end Physical
end QuantumNLS.Ext006NumberDomainR32a

#print axioms QuantumNLS.Ext006NumberDomainR32a.coreTerm_scale
#print axioms QuantumNLS.Ext006NumberDomainR32a.coefficient_scale_even
#print axioms QuantumNLS.Ext006NumberDomainR32a.summable_polynomial_of_exponential
#print axioms QuantumNLS.Ext006NumberDomainR32a.hsSq_scale
#print axioms QuantumNLS.Ext006NumberDomainR32a.coefficient_scale_norm_sq
#print axioms QuantumNLS.Ext006NumberDomainR32a.exists_exponential_weight
#print axioms QuantumNLS.Ext006NumberDomainR32a.normalized_exponential_weight
#print axioms QuantumNLS.Ext006NumberDomainR32a.normalized_polynomial_weight
#print axioms QuantumNLS.Ext006NumberDomainR32a.physical_exponential_weight

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006NumberDomainR32a." then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Round32a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
