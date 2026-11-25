import QuantumNLS.Ext006CompressionR32a
import QuantumNLS.Ext006PhysFockCoord

/-! Source-HS existence of the canonical weak squeezed vacuum. The source
symplectic map supplies the squeeze and its bounds; neither a vacuum nor a
unitary implementer is an input. The physical vector below is constructed by
its literal finite-core exponential coefficients. Identification with the
completed pair-creator exponential, its Fredholm norm, and construction of a
unitary implementer are separate obligations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Ext006HSVacuumR32a
open Ext006CompressionR32a Ext006KernelHilbertSchmidt TraceClass
open Ext006FormalVacuumR31a Ext006VacuumRecurrence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Arbitrarily large finite HS sum is allowed. -/
theorem exists_normalized (b : HilbertBasis ℤ ℂ H) (K : H →L[ℂ] H)
    (hSym : ∀ i j, coordinates b K i j = coordinates b K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq b K ≠ ⊤) :
    ∃ x : Fock, WeakVacuum (coordinates b K) x ∧ ‖x‖ = 1 := by
  apply Ext006CoreMajorantR31a.exists_normalized_of_compression_trace_bound
    (coordinates b K) hSym (hsSq b K).toReal (‖K‖^2) ENNReal.toReal_nonneg (sq_nonneg _)
  · nlinarith [norm_nonneg K]
  · exact compression_trace_power_le b K hHS

/-- Summability is a conclusion of the actual operator HS and strict norm
conditions. There is no small-HS hypothesis or supplied weak vacuum. -/
theorem summable_coefficients (b : HilbertBasis ℤ ℂ H) (K : H →L[ℂ] H)
    (hSym : ∀ i j, coordinates b K i j = coordinates b K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq b K ≠ ⊤) :
    Summable (fun m => ‖coefficient (coordinates b K) m‖^2) :=
  (exists_normalized_iff hSym).mp (exists_normalized b K hSym hn hHS)

/-- Unnormalized vector with all literal exponential coefficients. -/
def coefficientExponential (b : HilbertBasis ℤ ℂ H) (K : H →L[ℂ] H)
    (hSym : ∀ i j, coordinates b K i j = coordinates b K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq b K ≠ ⊤) : Fock :=
  vector (coordinates b K) (summable_coefficients b K hSym hn hHS)

lemma coefficientExponential_apply (b : HilbertBasis ℤ ℂ H) (K : H →L[ℂ] H)
    (hSym : ∀ i j, coordinates b K i j = coordinates b K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq b K ≠ ⊤) (m : Occupation.Occ) :
    coefficientExponential b K hSym hn hHS m = coefficient (coordinates b K) m := rfl

lemma coefficientExponential_ne_zero (b : HilbertBasis ℤ ℂ H) (K : H →L[ℂ] H)
    (hSym : ∀ i j, coordinates b K i j = coordinates b K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq b K ≠ ⊤) :
    coefficientExponential b K hSym hn hHS ≠ 0 :=
  vector_ne_zero _ _

lemma coefficientExponential_weak (b : HilbertBasis ℤ ℂ H) (K : H →L[ℂ] H)
    (hSym : ∀ i j, coordinates b K i j = coordinates b K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq b K ≠ ⊤) :
    WeakVacuum (coordinates b K) (coefficientExponential b K hSym hn hHS) :=
  vector_weak hSym _

/-- Exact norm as the finite-mode, all-degree exponential norm supremum.
This is not yet its Fredholm determinant evaluation. -/
theorem coefficientExponential_norm_sq (b : HilbertBasis ℤ ℂ H) (K : H →L[ℂ] H)
    (hSym : ∀ i j, coordinates b K i j = coordinates b K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq b K ≠ ⊤) :
    ENNReal.ofReal (‖coefficientExponential b K hSym hn hHS‖^2) =
      ⨆ S : Finset ℤ, ∑' n : ℕ,
        ENNReal.ofReal ((Ext006CoreNorm.cc S (coordinates b K) n).re) := by
  rw [← Ext006VacuumMassR31a.mass_eq_iSup_core_series hSym]
  have hv := lp.hasSum_norm (p := 2) (by norm_num)
    (coefficientExponential b K hSym hn hHS)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hv
  rw [Ext006VacuumMassR31a.mass, ← hv.tsum_eq,
    ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hv.summable]
  rfl

/-- The constructed vector is the norm limit of its finite occupation sums.
Every summand is computed by the literal finite-core exponential. -/
theorem coefficientExponential_hasSum (b : HilbertBasis ℤ ℂ H) (K : H →L[ℂ] H)
    (hSym : ∀ i j, coordinates b K i j = coordinates b K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq b K ≠ ⊤) :
    HasSum (fun m : Occupation.Occ => lp.single 2 m (coefficient (coordinates b K) m))
      (coefficientExponential b K hSym hn hHS) :=
  lp.hasSum_single ENNReal.ofNat_ne_top _

/-- In every finite mode set and every even degree, the constructed vector
has precisely the original factorial-normalized pair-creation coefficient. -/
theorem coefficientExponential_even (b : HilbertBasis ℤ ℂ H) (K : H →L[ℂ] H)
    (hSym : ∀ i j, coordinates b K i j = coordinates b K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq b K ≠ ⊤) (S : Finset ℤ) (m : Occupation.Occ)
    (hm : m.support ⊆ S) {n : ℕ} (hmn : Occupation.total m = 2*n) :
    coefficientExponential b K hSym hn hHS m =
      Ext006PairCoreCommutator.coreTerm S (coordinates b K) n m :=
  coefficient_even hSym S m hm hmn

/-- Canonical normalization with strictly positive vacuum coefficient. -/
def normalized (b : HilbertBasis ℤ ℂ H) (K : H →L[ℂ] H)
    (hSym : ∀ i j, coordinates b K i j = coordinates b K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq b K ≠ ⊤) : Fock :=
  (‖coefficientExponential b K hSym hn hHS‖⁻¹ : ℂ) •
    coefficientExponential b K hSym hn hHS

lemma normalized_weak (b : HilbertBasis ℤ ℂ H) (K : H →L[ℂ] H)
    (hSym : ∀ i j, coordinates b K i j = coordinates b K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq b K ≠ ⊤) :
    WeakVacuum (coordinates b K) (normalized b K hSym hn hHS) :=
  (coefficientExponential_weak b K hSym hn hHS).smul _

lemma normalized_norm (b : HilbertBasis ℤ ℂ H) (K : H →L[ℂ] H)
    (hSym : ∀ i j, coordinates b K i j = coordinates b K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq b K ≠ ⊤) : ‖normalized b K hSym hn hHS‖ = 1 := by
  have hz := norm_ne_zero_iff.mpr (coefficientExponential_ne_zero b K hSym hn hHS)
  rw [normalized, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hz]

lemma normalized_vacuum_positive (b : HilbertBasis ℤ ℂ H) (K : H →L[ℂ] H)
    (hSym : ∀ i j, coordinates b K i j = coordinates b K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq b K ≠ ⊤) :
    0 < (normalized b K hSym hn hHS 0).re := by
  change 0 < ((‖coefficientExponential b K hSym hn hHS‖⁻¹ : ℂ) *
    coefficient (coordinates b K) 0).re
  rw [coefficient_zero, mul_one, ← Complex.ofReal_inv, Complex.ofReal_re]
  exact inv_pos.mpr (norm_pos_iff.mpr (coefficientExponential_ne_zero b K hSym hn hHS))

section Source
attribute [local instance 2000] InnerProductSpace.complexToReal

/-- The original single-map source hypotheses now construct a normalized weak
vacuum. This theorem does not assert unitary implementation of that map. -/
theorem source_weak_vacuum (b : HilbertBasis ℤ ℂ H) (S : H ≃L[ℝ] H)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : hsSq b (beta b S) ≠ ⊤) :
    ∃ x : Fock, WeakVacuum (coordinates b (squeeze b S hS)) x ∧ ‖x‖ = 1 := by
  obtain ⟨hSym, hn, hHS, _, _⟩ := «FIN-CORE-BD-02-kernel» b S hS hβ
  exact exists_normalized b _ hSym hn hHS

end Source

section Physical
variable {L : ℝ} [Fact (0 < L)]

/-- Actual physical Fock vector, using the fixed free Fourier occupation basis. -/
def physicalNormalized (K : PhysicalTensor.L2T L →L[ℂ] PhysicalTensor.L2T L)
    (hSym : ∀ i j, coordinates (physicalBasis L) K i j = coordinates (physicalBasis L) K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq (physicalBasis L) K ≠ ⊤) : Ext025B3PhysicalSectors.Fock L :=
  Ext006PhysFockCoord.Phi.symm (normalized (physicalBasis L) K hSym hn hHS)

lemma physicalNormalized_coefficient (K : PhysicalTensor.L2T L →L[ℂ] PhysicalTensor.L2T L)
    (hSym : ∀ i j, coordinates (physicalBasis L) K i j = coordinates (physicalBasis L) K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq (physicalBasis L) K ≠ ⊤) (m : Occupation.Occ) :
    Ext006PhysicalVacuum.coefficient (physicalNormalized K hSym hn hHS) m =
      normalized (physicalBasis L) K hSym hn hHS m := by
  change Ext006PhysFockCoord.Phi (Ext006PhysFockCoord.Phi.symm _) m = _
  rw [LinearIsometryEquiv.apply_symm_apply]

lemma physicalNormalized_weak (K : PhysicalTensor.L2T L →L[ℂ] PhysicalTensor.L2T L)
    (hSym : ∀ i j, coordinates (physicalBasis L) K i j = coordinates (physicalBasis L) K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq (physicalBasis L) K ≠ ⊤) :
    Ext006PhysicalVacuum.PhysicalWeakVacuum (coordinates (physicalBasis L) K)
      (physicalNormalized K hSym hn hHS) := by
  have he : Ext006PhysicalVacuum.coefficient (physicalNormalized K hSym hn hHS) =
      (normalized (physicalBasis L) K hSym hn hHS : Occupation.Occ → ℂ) :=
    funext (physicalNormalized_coefficient K hSym hn hHS)
  rw [Ext006PhysicalVacuum.PhysicalWeakVacuum, he]
  exact normalized_weak _ _ hSym hn hHS

lemma physicalNormalized_norm (K : PhysicalTensor.L2T L →L[ℂ] PhysicalTensor.L2T L)
    (hSym : ∀ i j, coordinates (physicalBasis L) K i j = coordinates (physicalBasis L) K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq (physicalBasis L) K ≠ ⊤) :
    ‖physicalNormalized K hSym hn hHS‖ = 1 := by
  rw [physicalNormalized, LinearIsometryEquiv.norm_map, normalized_norm]

/-- Any normalized physical weak vacuum with this squeeze equals the
constructed vector up to phase. No implementer existence is inferred. -/
theorem physical_unique_phase (K : PhysicalTensor.L2T L →L[ℂ] PhysicalTensor.L2T L)
    (hSym : ∀ i j, coordinates (physicalBasis L) K i j = coordinates (physicalBasis L) K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq (physicalBasis L) K ≠ ⊤)
    {x : Ext025B3PhysicalSectors.Fock L}
    (hx : Ext006PhysicalVacuum.PhysicalWeakVacuum (coordinates (physicalBasis L) K) x)
    (hxn : ‖x‖ = 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ x = c • physicalNormalized K hSym hn hHS :=
  Ext006PhysicalVacuum.physical_normalized_unique_phase
    (physicalNormalized_weak K hSym hn hHS) hx (physicalNormalized_norm K hSym hn hHS) hxn

local instance physicalRealNormedSpace : NormedSpace ℝ (PhysicalTensor.L2T L) :=
  (InnerProductSpace.complexToReal : InnerProductSpace ℝ (PhysicalTensor.L2T L)).toNormedSpace

/-- Physical source specialization, with precisely the source symplectic and
HS conditions and the already fixed source squeeze convention. -/
theorem source_physical_weak_vacuum
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    ∃ x : Ext025B3PhysicalSectors.Fock L,
      Ext006PhysicalVacuum.PhysicalWeakVacuum
        (coordinates (physicalBasis L) (squeeze (physicalBasis L) S hS)) x ∧ ‖x‖ = 1 := by
  obtain ⟨hSym, hn, hHS, _, _⟩ := «FIN-CORE-BD-02-kernel» (physicalBasis L) S hS hβ
  exact ⟨physicalNormalized _ hSym hn hHS, physicalNormalized_weak _ hSym hn hHS,
    physicalNormalized_norm _ hSym hn hHS⟩

end Physical
end QuantumNLS.Ext006HSVacuumR32a

#print axioms QuantumNLS.Ext006HSVacuumR32a.exists_normalized
#print axioms QuantumNLS.Ext006HSVacuumR32a.summable_coefficients
#print axioms QuantumNLS.Ext006HSVacuumR32a.coefficientExponential_norm_sq
#print axioms QuantumNLS.Ext006HSVacuumR32a.coefficientExponential_hasSum
#print axioms QuantumNLS.Ext006HSVacuumR32a.coefficientExponential_even
#print axioms QuantumNLS.Ext006HSVacuumR32a.normalized_vacuum_positive
#print axioms QuantumNLS.Ext006HSVacuumR32a.source_weak_vacuum
#print axioms QuantumNLS.Ext006HSVacuumR32a.physical_unique_phase
#print axioms QuantumNLS.Ext006HSVacuumR32a.source_physical_weak_vacuum

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006HSVacuumR32a." then
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
