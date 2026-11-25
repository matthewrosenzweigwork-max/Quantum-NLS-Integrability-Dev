import QuantumNLS.Ext006PhysicalCoreR39a
import QuantumNLS.Ext006HSVacuumR32a

/-! Every literal finite-mode physical pair-exponential degree is exactly its
factorial-normalized frozen CCR core term. No physical/core identity is an input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006FiniteExponentialR39a
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Occupation Ext006PhysFockCoord Ext006KernelHilbertSchmidt
open Ext006PairPowerWick Ext006PhysicalCoreR39a Ext006PhysicalApproximationR38a
open Ext006PhysicalExponentialTerms Ext006PairCoreCommutator Ext006CompressionR32a
variable {L : ℝ} [Fact (0 < L)]

lemma creation_sum {I : Type*} (T : Finset I) (b : I → HN L 2) (N : ℕ) (x : HN L N) :
    Ext005PairSector.creation (∑ i ∈ T, b i) N x =
      ∑ i ∈ T, Ext005PairSector.creation (b i) N x := by
  classical
  apply Subtype.ext
  simp only [Ext006PhysicalNormBridge.CreationFormula.creation_eq_projection,
    Submodule.coe_smul, Submodule.coe_sum]
  change (Real.sqrt (((N : ℝ)+1)*((N : ℝ)+2)) : ℂ) •
    (physSector L (2+N)).starProjection
      (concat (∑ i ∈ T, (b i : HilbertTensorPower ℂ (L2T L) 2)) x) = _
  rw [← Ext006PairPowerWick.concatRightMap_apply]
  simp only [map_sum, Ext006PairPowerWick.concatRightMap_apply, Finset.smul_sum]
  rfl

lemma creation_smul (c : ℂ) (b : HN L 2) (N : ℕ) (x : HN L N) :
    Ext005PairSector.creation (c • b) N x = c • Ext005PairSector.creation b N x := by
  apply Subtype.ext
  simp only [Ext006PhysicalNormBridge.CreationFormula.creation_eq_projection,
    Submodule.coe_smul]
  change (Real.sqrt (((N : ℝ)+1)*((N : ℝ)+2)) : ℂ) •
    (physSector L (2+N)).starProjection
      (concat (c • (b : HilbertTensorPower ℂ (L2T L) 2)) x) = _
  rw [concat_smul_left, map_smul, smul_comm]
  rfl

lemma finite_pair_core_ket (K : L2T L →L[ℂ] L2T L) (S : Finset ℤ)
    {N : ℕ} (m : Arr N) :
    inclusion L (2+N) (Ext005PairSector.creation
      (finitePair (physicalBasis L) K S) N (sectorKet m)) =
      physCore (L := L) (pairCreator S (coordinates (physicalBasis L) K) (ket m.1)) := by
  simp only [finitePair, creation_sum, creation_smul, map_sum, map_smul,
    physical_pair_core_ket, pairCreator, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.End.mul_apply]
  rfl

lemma core_reconstruct (v : FS) :
    (∑ m ∈ v.support.attach, v m.1 • ket m.1) = v := by
  classical
  rw [Finset.sum_attach v.support (fun m => v m • ket m)]
  simpa only [ket, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.sum] using
    Finsupp.sum_single v

/-- The actual sector tensor of a homogeneous finite core vector. -/
def coreSector (N : ℕ) (v : FS) (hv : ∀ m, v m ≠ 0 → total m = N) : HN L N :=
  ∑ m ∈ v.support.attach, v m.1 • sectorKet ⟨m.1, hv m.1 (Finsupp.mem_support_iff.mp m.2)⟩

lemma inclusion_coreSector (N : ℕ) (v : FS) (hv : ∀ m, v m ≠ 0 → total m = N) :
    inclusion L N (coreSector N v hv) = physCore (L := L) v := by
  unfold coreSector
  simp only [map_sum, map_smul, ← physCore_ket_sector]
  conv_rhs => rw [← core_reconstruct v]
  simp only [map_sum, map_smul]

lemma finite_pair_core (K : L2T L →L[ℂ] L2T L) (S : Finset ℤ)
    (N : ℕ) (v : FS) (hv : ∀ m, v m ≠ 0 → total m = N) :
    inclusion L (2+N) (Ext005PairSector.creation (finitePair (physicalBasis L) K S) N
      (coreSector N v hv)) =
      physCore (L := L) (pairCreator S (coordinates (physicalBasis L) K) v) := by
  unfold coreSector
  simp only [map_sum, map_smul, finite_pair_core_ket]
  conv_rhs => rw [← core_reconstruct v]
  simp only [map_sum, map_smul]

lemma coreTerm_step (S : Finset ℤ) (K : ℤ → ℤ → ℂ) (n : ℕ) :
    coreTerm S K (n+1) = stepScalar n • pairCreator S K (coreTerm S K n) := by
  unfold coreTerm
  rw [pow_succ' (pairCreator S K) n, Module.End.mul_apply, map_smul, smul_smul]
  congr 1
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn : (n : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  simp only [stepScalar, Complex.ofReal_neg, Complex.ofReal_inv, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
  field_simp

lemma inclusion_sectorCast {k n : ℕ} (h : k = n) (x : HN L k) :
    inclusion L n (sectorCast h x) = inclusion L k x := by
  subst n
  rfl

lemma sectorKet_zero :
    sectorKet (L := L) (⟨0, by simp [IsArray, total]⟩ : Arr 0) =
      Ext006ZeroVacuum.sectorVacuum L := by
  apply (OccupationUnitary.physicalOccupation L 0).injective
  rw [sectorKet, LinearIsometryEquiv.apply_symm_apply]
  apply lp.ext
  funext m
  have hm : m.1 = 0 := (Finsupp.degree_eq_zero_iff m.1).mp m.2
  have he : m = (⟨0, by simp [IsArray, total]⟩ : Arr 0) := Subtype.ext hm
  subst m
  simp only [lp.single_apply_self, OccupationUnitary.physicalOccupation,
    LinearIsometryEquiv.trans_apply, Ext006ZeroVacuum.sectorVacuum,
    TensorFourier.U3_htpow, OccupationUnitary.U4_htpow]
  simp [OccupationUnitary.normalization, OccupationUnitary.multiplicityFactorial]

/-- Exact all-degree finite physical/core exponential identity. -/
theorem finite_physical_exponential (K : L2T L →L[ℂ] L2T L) (S : Finset ℤ) (n : ℕ) :
    fockTerm (finitePair (physicalBasis L) K S) n =
      physCore (L := L) (coreTerm S (coordinates (physicalBasis L) K) n) := by
  induction n with
  | zero =>
    rw [Ext006CoreNorm.coreTerm_zero, physCore_ket_sector
      (m := (⟨0, by simp [IsArray, total]⟩ : Arr 0)), sectorKet_zero]
    rfl
  | succ n ih =>
    let v := coreTerm S (coordinates (physicalBasis L) K) n
    have hv : ∀ m, v m ≠ 0 → total m = 2*n :=
      fun m hm => (Ext006CoreLimit.coreTerm_support S _ n m hm).2
    have ht : term (finitePair (physicalBasis L) K S) n = coreSector (2*n) v hv := by
      apply (inclusion L (2*n)).injective
      exact ih.trans (inclusion_coreSector (2*n) v hv).symm
    simp only [fockTerm, term_step, inclusion_sectorCast, map_smul, ht]
    rw [finite_pair_core, coreTerm_step, map_smul]

end QuantumNLS.Ext006FiniteExponentialR39a

#print axioms QuantumNLS.Ext006FiniteExponentialR39a.finite_physical_exponential

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006FiniteExponentialR39a." then
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
