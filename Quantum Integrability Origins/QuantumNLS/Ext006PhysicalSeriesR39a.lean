import QuantumNLS.Ext006FiniteExponentialR39a

/-! Norm convergence of the literal completed physical pair exponential for every
symmetric HS strict contraction, and its exact coefficient-vector identification.
The Fredholm evaluation is a separate open step. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped InnerProductSpace
open Filter Topology
namespace QuantumNLS.Ext006PhysicalSeriesR39a
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Occupation Ext006PhysFockCoord Ext006KernelHilbertSchmidt
open Ext006PhysicalApproximationR38a Ext006PhysicalExponentialTerms
open Ext006FiniteExponentialR39a Ext006CompressionR32a Ext006HSVacuumR32a
open Ext006PhysicalNormBridge.PairTensor TraceClass
variable {L : ℝ} [Fact (0 < L)]

/-- Evaluation of a free occupation coefficient is a bounded physical Fock functional. -/
def coefficientEval (m : Occ) : Fock L →L[ℂ] ℂ :=
  (lp.evalCLM (E := fun _ : Occ => ℂ) (p := 2) ℂ m) ∘L
    (Phi (L := L)).toContinuousLinearEquiv.toContinuousLinearMap

lemma coefficient_physCore (v : FS) (m : Occ) :
    Ext006PhysicalVacuum.coefficient (physCore (L := L) v) m = v m := by
  have h : ∀ v : FS, Ext006PhysicalVacuum.coreEmbedding v m = v m := by
    intro v
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simp only [map_add, lp.coeFn_add, Pi.add_apply, Finsupp.add_apply, hv, hw]
    | single a c =>
      simp [Ext006PhysicalVacuum.coreEmbedding, lp.single_apply, Pi.single_apply, Finsupp.single_apply, eq_comm]
  change Phi (physCore v) m = v m
  change Phi (Phi.symm (Ext006PhysicalVacuum.coreEmbedding v)) m = v m
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact h v

/-- All-degree physical finite-mode norm identity, derived from the physical/core bridge. -/
theorem finite_physical_norm_sq (K : L2T L →L[ℂ] L2T L) (S : Finset ℤ) (n : ℕ) :
    ‖term (finitePair (physicalBasis L) K S) n‖^2 =
      (Ext006CoreNorm.cc S (coordinates (physicalBasis L) K) n).re := by
  classical
  rw [← fockTerm_norm, finite_physical_exponential, ← sum_sq_eq, Ext006CoreLimit.cc_re_eq]
  simp_rw [coefficient_physCore, Complex.sq_norm]
  apply tsum_eq_sum
  intro m hm
  simp only [Finsupp.notMem_support_iff.mp hm, Complex.normSq_zero]

/-- The all-degree norm/trace recurrence on actual finite-mode physical tensors. -/
theorem finite_physical_trace_recurrence (K : L2T L →L[ℂ] L2T L)
    (hSym : ∀ i j, coordinates (physicalBasis L) K i j = coordinates (physicalBasis L) K j i)
    (S : Finset ℤ) (n : ℕ) :
    2 * (n : ℝ) * ‖term (finitePair (physicalBasis L) K S) n‖^2 =
      ∑ j ∈ Finset.range n, ‖term (finitePair (physicalBasis L) K S) (n-1-j)‖^2 *
        (((Ext006CoreNorm.Tm S (coordinates (physicalBasis L) K))^(j+1)).trace).re := by
  simp only [finite_physical_norm_sq]
  exact Ext006CoreLimit.rec_real S _ (fun i _ j _ => hSym i j) n

/-- Every actual completed exponential degree has exactly the constructed
factorial-normalized finite-core coefficients. -/
theorem physical_degree_coefficient (K : L2T L →L[ℂ] L2T L)
    (hSym : ∀ i j, coordinates (physicalBasis L) K i j = coordinates (physicalBasis L) K j i)
    (hHS : hsSq (physicalBasis L) K ≠ ⊤) (n : ℕ) (m : Occ) :
    Ext006PhysicalVacuum.coefficient
      (fockTerm (physicalPair (physicalBasis L) K hHS hSym) n) m =
      if total m = 2*n then Ext006FormalVacuumR31a.coefficient (coordinates (physicalBasis L) K) m else 0 := by
  classical
  have hp := (Ext006PhysicalContinuityR38a.continuous_fockTerm (L := L) n).continuousAt.tendsto.comp
    (finitePair_tendsto (physicalBasis L) K hHS hSym)
  have hc := (coefficientEval (L := L) m).continuous.continuousAt.tendsto.comp hp
  change Tendsto (fun S : Finset ℤ => Ext006PhysicalVacuum.coefficient
    (fockTerm (finitePair (physicalBasis L) K S) n) m) atTop
    (𝓝 (Ext006PhysicalVacuum.coefficient
      (fockTerm (physicalPair (physicalBasis L) K hHS hSym) n) m)) at hc
  have he : ∀ᶠ S : Finset ℤ in atTop,
      Ext006PhysicalVacuum.coefficient (fockTerm (finitePair (physicalBasis L) K S) n) m =
        if total m = 2*n then Ext006FormalVacuumR31a.coefficient (coordinates (physicalBasis L) K) m else 0 := by
    refine eventually_atTop.2 ⟨m.support, fun S hS => ?_⟩
    rw [finite_physical_exponential, coefficient_physCore]
    split_ifs with hm
    · exact (Ext006FormalVacuumR31a.coefficient_even hSym S m hS hm).symm
    · by_contra hz
      exact hm (Ext006CoreLimit.coreTerm_support S _ n m hz).2
  exact tendsto_nhds_unique hc (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he))

/-- The physical vector constructed from the explicit all-degree core coefficients. -/
def physicalExponential (K : L2T L →L[ℂ] L2T L)
    (hSym : ∀ i j, coordinates (physicalBasis L) K i j = coordinates (physicalBasis L) K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq (physicalBasis L) K ≠ ⊤) : Fock L :=
  (Phi (L := L)).symm (coefficientExponential (physicalBasis L) K hSym hn hHS)

lemma physicalExponential_coefficient (K : L2T L →L[ℂ] L2T L)
    (hSym : ∀ i j, coordinates (physicalBasis L) K i j = coordinates (physicalBasis L) K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq (physicalBasis L) K ≠ ⊤) (m : Occ) :
    Ext006PhysicalVacuum.coefficient (physicalExponential K hSym hn hHS) m =
      Ext006FormalVacuumR31a.coefficient (coordinates (physicalBasis L) K) m := by
  change Phi (physicalExponential K hSym hn hHS) m = _
  rw [physicalExponential, LinearIsometryEquiv.apply_symm_apply]
  rfl

lemma coefficient_inclusion (x : Fock L) (N : ℕ) (m : Occ) :
    Ext006PhysicalVacuum.coefficient (inclusion L N (x N)) m =
      if total m = N then Ext006PhysicalVacuum.coefficient x m else 0 := by
  classical
  by_cases h : total m = N
  · subst N
    have he : (inclusion L (total m) (x (total m))) (total m) = x (total m) :=
      lp.single_apply_self _ _ _
    simp [Ext006PhysicalVacuum.coefficient, he]
  · have he : (inclusion L N (x N)) (total m) = 0 := lp.single_apply_ne _ _ _ h
    simp [Ext006PhysicalVacuum.coefficient, he, h]

lemma physical_degree_eq_sector (K : L2T L →L[ℂ] L2T L)
    (hSym : ∀ i j, coordinates (physicalBasis L) K i j = coordinates (physicalBasis L) K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq (physicalBasis L) K ≠ ⊤) (n : ℕ) :
    fockTerm (physicalPair (physicalBasis L) K hHS hSym) n =
      inclusion L (2*n) (physicalExponential K hSym hn hHS (2*n)) := by
  apply (Phi (L := L)).injective
  apply lp.ext
  funext m
  change Ext006PhysicalVacuum.coefficient _ m = Ext006PhysicalVacuum.coefficient _ m
  rw [physical_degree_coefficient, coefficient_inclusion, physicalExponential_coefficient]

lemma physicalExponential_off_even (K : L2T L →L[ℂ] L2T L)
    (hSym : ∀ i j, coordinates (physicalBasis L) K i j = coordinates (physicalBasis L) K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq (physicalBasis L) K ≠ ⊤) (N : ℕ)
    (hN : N ∉ Set.range (fun n : ℕ => 2*n)) : physicalExponential K hSym hn hHS N = 0 := by
  apply (occupationCoefficient (freeBasis L N)).injective
  rw [map_zero]
  apply lp.ext
  funext m
  rcases m with ⟨v,hv⟩
  have hm : ¬ Even (total v) := by
    rintro ⟨n,he⟩
    apply hN
    refine ⟨n, ?_⟩
    change 2*n = N
    change total v = N at hv
    omega
  have hc := physicalExponential_coefficient K hSym hn hHS v
  rw [Ext006FormalVacuumR31a.coefficient_odd _ hm] at hc
  change total v = N at hv
  subst N
  exact hc

/-- Norm convergence of the COMPLETED physical operator exponential with its
literal -1/2 and factorial, for every symmetric HS strict contraction. -/
theorem physical_exponential_hasSum (K : L2T L →L[ℂ] L2T L)
    (hSym : ∀ i j, coordinates (physicalBasis L) K i j = coordinates (physicalBasis L) K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq (physicalBasis L) K ≠ ⊤) :
    HasSum (fockTerm (physicalPair (physicalBasis L) K hHS hSym))
      (physicalExponential K hSym hn hHS) := by
  have hi : Function.Injective (fun n : ℕ => 2*n) := by intro i j h; change 2*i=2*j at h; omega
  have hz : ∀ N : ℕ, N ∉ Set.range (fun n : ℕ => 2*n) →
      lp.single 2 N (physicalExponential K hSym hn hHS N) = 0 := by
    intro N hN
    rw [physicalExponential_off_even K hSym hn hHS N hN, lp.single_zero]
  have h := (hi.hasSum_iff hz).mpr (lp.hasSum_single ENNReal.ofNat_ne_top
    (physicalExponential K hSym hn hHS))
  convert h using 1
  funext n
  exact physical_degree_eq_sector K hSym hn hHS n

theorem physical_exponential_truncations_tendsto (K : L2T L →L[ℂ] L2T L)
    (hSym : ∀ i j, coordinates (physicalBasis L) K i j = coordinates (physicalBasis L) K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq (physicalBasis L) K ≠ ⊤) :
    Tendsto (truncation (physicalPair (physicalBasis L) K hHS hSym)) atTop
      (𝓝 (physicalExponential K hSym hn hHS)) :=
  (physical_exponential_hasSum K hSym hn hHS).tendsto_sum_nat

/-- The physical squared norm is the sum of ALL literal exponential degree norms. -/
theorem all_degree_physical_norm_hasSum (K : L2T L →L[ℂ] L2T L)
    (hSym : ∀ i j, coordinates (physicalBasis L) K i j = coordinates (physicalBasis L) K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq (physicalBasis L) K ≠ ⊤) :
    HasSum (fun n : ℕ => ‖term (physicalPair (physicalBasis L) K hHS hSym) n‖^2)
      (‖physicalExponential K hSym hn hHS‖^2) := by
  have hi : Function.Injective (fun n : ℕ => 2*n) := by intro i j h; change 2*i=2*j at h; omega
  have hz : ∀ N : ℕ, N ∉ Set.range (fun n : ℕ => 2*n) →
      ‖physicalExponential K hSym hn hHS N‖^2 = 0 := by
    intro N hN
    rw [physicalExponential_off_even K hSym hn hHS N hN, norm_zero]
    norm_num
  have hs := lp.hasSum_norm (p := 2) (by norm_num) (physicalExponential K hSym hn hHS)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs
  have h := (hi.hasSum_iff hz).mpr hs
  convert h using 1
  funext n
  have he := congrArg norm (physical_degree_eq_sector K hSym hn hHS n)
  rw [fockTerm_norm, (inclusion L (2*n)).norm_map] at he
  exact congrArg (fun r : ℝ => r^2) he

/-- Exact physical norm as the all-mode, all-degree finite-core norm supremum.
Evaluating this supremum as a Fredholm determinant remains separate. -/
theorem physicalExponential_norm_sq (K : L2T L →L[ℂ] L2T L)
    (hSym : ∀ i j, coordinates (physicalBasis L) K i j = coordinates (physicalBasis L) K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq (physicalBasis L) K ≠ ⊤) :
    ENNReal.ofReal (‖physicalExponential K hSym hn hHS‖^2) =
      ⨆ S : Finset ℤ, ∑' n : ℕ,
        ENNReal.ofReal ((Ext006CoreNorm.cc S (coordinates (physicalBasis L) K) n).re) := by
  rw [physicalExponential, LinearIsometryEquiv.norm_map]
  exact coefficientExponential_norm_sq (physicalBasis L) K hSym hn hHS

/-- The canonical normalized vector is the positive inverse-norm multiple of
this ACTUAL completed physical exponential. No determinant factor is assumed. -/
theorem physicalNormalized_eq_exponential (K : L2T L →L[ℂ] L2T L)
    (hSym : ∀ i j, coordinates (physicalBasis L) K i j = coordinates (physicalBasis L) K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq (physicalBasis L) K ≠ ⊤) :
    physicalNormalized K hSym hn hHS =
      (‖physicalExponential K hSym hn hHS‖⁻¹ : ℂ) • physicalExponential K hSym hn hHS := by
  simp only [physicalNormalized, normalized, physicalExponential,
    map_smul, LinearIsometryEquiv.norm_map]

end QuantumNLS.Ext006PhysicalSeriesR39a

#print axioms QuantumNLS.Ext006PhysicalSeriesR39a.physical_degree_coefficient

#print axioms QuantumNLS.Ext006PhysicalSeriesR39a.physical_exponential_hasSum

#print axioms QuantumNLS.Ext006PhysicalSeriesR39a.physical_exponential_truncations_tendsto

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006PhysicalSeriesR39a." then
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
  Lean.logInfo m!"Round39a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
