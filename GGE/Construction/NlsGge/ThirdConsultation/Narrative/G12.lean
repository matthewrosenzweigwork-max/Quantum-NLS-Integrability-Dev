  
                                 

                                                           
                                                                        
                                                                   
  
import NlsGge.Atomic.S.S001
import NlsGge.Atomic.G2.G2040
import NlsGge.Atomic.R.R123
import NlsGge.Atomic.R.R124
import NlsGge.Birkhoff.W09Approx38b
import NlsGge.Atomic.KSPS.KSPS028
import NlsGge.Spectral.ActualSourceWeightedDomainLInfRepresentativeMatchesSourceV5
import NlsGge.Spectral.ActualSourceWeightedDomainPotentialAECoherenceMinimumV2

set_option autoImplicit false

namespace NlsGge.ThirdConsultation.Narrative

open Filter Topology
open NlsGge.Pilot NlsGge.Schur NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.S001
open NlsGge.Schur.TransportBridgeV4

noncomputable section

/-! ## G12: channel phases and the actual graph domain -/

/-- The two opposite half phases in the doubled physical carrier. -/
def groupedPhaseScalar (θ : ℝ) (b : Bool) : ℂ :=
  if b then Complex.exp (Complex.I * (θ / 2))
  else Complex.exp (-Complex.I * (θ / 2))

theorem groupedPhaseScalar_norm (θ : ℝ) (b : Bool) :
    ‖groupedPhaseScalar θ b‖ = 1 := by
  cases b <;> simp [groupedPhaseScalar, Complex.norm_exp]

theorem groupedPhaseScalar_neg_mul (θ : ℝ) (b : Bool) :
    groupedPhaseScalar (-θ) b * groupedPhaseScalar θ b = 1 := by
  cases b <;>
    simp only [groupedPhaseScalar, ite_true, ite_false, Bool.false_eq_true] <;>
    rw [← Complex.exp_add] <;>
    simp only [Complex.ofReal_neg] <;>
    ring_nf <;> simp

theorem groupedPhaseScalar_mul_neg (θ : ℝ) (b : Bool) :
    groupedPhaseScalar θ b * groupedPhaseScalar (-θ) b = 1 := by
  rw [mul_comm, groupedPhaseScalar_neg_mul]

/-- Diagonal multiplication by the phase factors on the actual two-channel
spectral L² carrier. -/
def groupedPhaseMap (θ : ℝ) : DoubledPair →ₗ[ℂ] DoubledPair where
  toFun x := WithLp.toLp 2 (fun b => groupedPhaseScalar θ b • x b)
  map_add' x y := by
    apply PiLp.ext
    intro b
    simp [groupedPhaseScalar]
  map_smul' c x := by
    apply PiLp.ext
    intro b
    cases b <;> simp [groupedPhaseScalar, smul_smul, mul_comm]

theorem groupedPhaseMap_leftInverse (θ : ℝ) (x : DoubledPair) :
    groupedPhaseMap (-θ) (groupedPhaseMap θ x) = x := by
  apply PiLp.ext
  intro b
  change groupedPhaseScalar (-θ) b • (groupedPhaseScalar θ b • x b) = x b
  rw [smul_smul, groupedPhaseScalar_neg_mul, one_smul]

theorem groupedPhaseMap_rightInverse (θ : ℝ) (x : DoubledPair) :
    groupedPhaseMap θ (groupedPhaseMap (-θ) x) = x := by
  apply PiLp.ext
  intro b
  change groupedPhaseScalar θ b • (groupedPhaseScalar (-θ) b • x b) = x b
  rw [smul_smul, groupedPhaseScalar_mul_neg, one_smul]

theorem groupedPhaseUnitary (θ : ℝ) :
    ∃ U : DoubledPair ≃ₗᵢ[ℂ] DoubledPair,
      (∀ x b, U x b = groupedPhaseScalar θ b • x b) := by
  have hnorm : ∀ x : DoubledPair, ‖groupedPhaseMap θ x‖ = ‖x‖ := by
    intro x
    have h1 := PiLp.norm_sq_eq_of_L2 (fun _ : Bool => SpectralScalarL2)
      (groupedPhaseMap θ x)
    have h2 := PiLp.norm_sq_eq_of_L2 (fun _ : Bool => SpectralScalarL2) x
    have h3 : ‖groupedPhaseMap θ x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [h1, h2]
      simp [Fintype.sum_bool, groupedPhaseMap, norm_smul,
        groupedPhaseScalar_norm, one_mul]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h3
  let e : DoubledPair ≃ₗ[ℂ] DoubledPair :=
    { toFun := groupedPhaseMap θ
      map_add' := (groupedPhaseMap θ).map_add
      map_smul' := (groupedPhaseMap θ).map_smul
      invFun := groupedPhaseMap (-θ)
      left_inv := groupedPhaseMap_leftInverse θ
      right_inv := groupedPhaseMap_rightInverse θ }
  refine ⟨⟨e, hnorm⟩, ?_⟩
  intro x b
  rfl

/-- Apply the same channelwise constants to the two source-interval
components. -/
def groupedSourcePairPhase (a : Bool → ℂ) (x : SourcePairL2) : SourcePairL2 :=
  WithLp.toLp 2 (fun b => a b • x b)

/-- The Fourier-coordinate phase action is diagonal in the Bool coordinate. -/
theorem groupedSourcePairRepr_phase (n : ℤ) (a : Bool → ℂ)
    (x : SourcePairL2) (i : Bool × Sector n) :
    sourcePairRepr n (groupedSourcePairPhase a x) i =
      a i.1 * sourcePairRepr n x i := by
  rcases i with ⟨b, m⟩
  cases b <;>
    simp [groupedSourcePairPhase, sourcePairRepr, parityPairIntervalEquiv,
      parityPairRepr_apply, map_smul]

/-- A unit-modulus multiplier on each Bool frequency channel preserves the
actual weighted free graph domain. -/
def groupedPhaseScaleSequence {n : ℤ} (a : Bool → ℂ)
    (ha : ∀ b, ‖a b‖ = 1) (x : SectorSquare n) : SectorSquare n := by
  let v : Bool × Sector n → ℂ := fun i => a i.1 * x i
  have hx : Memℓp (fun i : Bool × Sector n => x i) 2 := x.property
  have hvnorm : Memℓp (fun i : Bool × Sector n => ‖v i‖) 2 := by
    simpa [v, Complex.norm_mul, ha] using (Memℓp.norm hx)
  have hv : Memℓp v 2 := Memℓp.of_norm hvnorm
  exact ⟨v, hv⟩

theorem groupedPhaseWeightedDomain_mem {n : ℤ} (a : Bool → ℂ)
    (ha : ∀ b, ‖a b‖ = 1) (x : freeWeightedDomainPointwise n) :
    groupedPhaseScaleSequence a ha x.1 ∈ freeWeightedDomainPointwise n := by
  change Memℓp (freeWeightedCoordinates n (groupedPhaseScaleSequence a ha x.1)) 2
  have hw : Memℓp (fun i : Bool × Sector n =>
      ‖freeWeightedCoordinates n (groupedPhaseScaleSequence a ha x.1) i‖) 2 := by
    simpa [freeWeightedCoordinates, groupedPhaseScaleSequence,
      Complex.norm_mul, ha, mul_assoc] using (Memℓp.norm x.property)
  exact Memℓp.of_norm hw

/-- The actual source weighted domain is invariant under the two constant
channel phases. -/
theorem groupedRecoveredSourceDomain_phase_mem (n : ℤ) (θ : ℝ)
    (x : recoveredActualSourceFreeWeightedDomain n) :
    groupedSourcePairPhase (groupedPhaseScalar θ) x.1 ∈
      recoveredActualSourceFreeWeightedDomain n := by
  change sourcePairRepr n (groupedSourcePairPhase (groupedPhaseScalar θ) x.1) ∈
    freeWeightedDomainPointwise n
  have heq : sourcePairRepr n (groupedSourcePairPhase (groupedPhaseScalar θ) x.1) =
      groupedPhaseScaleSequence (groupedPhaseScalar θ)
        (groupedPhaseScalar_norm θ) (sourcePairRepr n x.1) := by
    apply lp.ext
    funext i
    exact groupedSourcePairRepr_phase n (groupedPhaseScalar θ) x.1 i
  rw [heq]
  exact groupedPhaseWeightedDomain_mem (groupedPhaseScalar θ)
    (groupedPhaseScalar_norm θ) ⟨sourcePairRepr n x.1, x.2⟩

/-- The full-period source assembly intertwines the physical channel phase
with the source-interval channel phase. -/
theorem groupedSourceAssembly_phase (θ : ℝ) (x : DoubledPair)
    (p : Fin 2) (b : Bool) :
    actualFullPeriodTwoSourceIntervalAssembly (groupedPhaseMap θ x) p b =
      groupedPhaseScalar θ b •
        actualFullPeriodTwoSourceIntervalAssembly x p b := by
  simp [groupedPhaseMap, actualFullPeriodTwoSourceIntervalAssembly_apply,
    map_smul]

/-- Forward invariance of the actual doubled-period graph domain under
channelwise constant phases. -/
theorem groupedPhaseMap_mem_actualDoubledDomain (θ : ℝ) (x : DoubledPair)
    (hx : x ∈ DoubledDomain) : groupedPhaseMap θ x ∈ DoubledDomain := by
  change actualFullPeriodTwoSourceIntervalAssembly x ∈
      actualFullPeriodTwoSourceBlockDomain at hx
  change actualFullPeriodTwoSourceIntervalAssembly (groupedPhaseMap θ x) ∈
      actualFullPeriodTwoSourceBlockDomain
  intro p
  have hp := hx p
  have hscaled :
      actualFullPeriodTwoSourceIntervalAssembly (groupedPhaseMap θ x) p =
        groupedSourcePairPhase (groupedPhaseScalar θ)
          (actualFullPeriodTwoSourceIntervalAssembly x p) := by
    apply PiLp.ext
    intro b
    exact groupedSourceAssembly_phase θ x p b
  rw [hscaled]
  exact groupedRecoveredSourceDomain_phase_mem (p.val : ℤ) θ
    ⟨actualFullPeriodTwoSourceIntervalAssembly x p, hp⟩

/-- The full actual doubled-period graph domain is invariant in both
directions under the phase isometry. -/
theorem groupedPhaseMap_mem_actualDoubledDomain_iff (θ : ℝ) (x : DoubledPair) :
    x ∈ DoubledDomain ↔ groupedPhaseMap θ x ∈ DoubledDomain := by
  constructor
  · exact groupedPhaseMap_mem_actualDoubledDomain θ x
  · intro hx
    have hback := groupedPhaseMap_mem_actualDoubledDomain (-θ)
      (groupedPhaseMap θ x) hx
    simpa only [groupedPhaseMap_leftInverse] using hback

private def groupedSourceDomainPhase (n : ℤ) (θ : ℝ)
    (x : recoveredActualSourceFreeWeightedDomain n) :
    recoveredActualSourceFreeWeightedDomain n :=
  ⟨groupedSourcePairPhase (groupedPhaseScalar θ) x.1,
    groupedRecoveredSourceDomain_phase_mem n θ x⟩

private theorem groupedPhaseScalar_true_mul_false (θ : ℝ) :
    groupedPhaseScalar θ true * groupedPhaseScalar θ false = 1 := by
  have ht : groupedPhaseScalar θ true = Complex.exp (Complex.I * (θ / 2)) := by
    simp [groupedPhaseScalar]
  have hf : groupedPhaseScalar θ false = Complex.exp (-Complex.I * (θ / 2)) := by
    simp [groupedPhaseScalar]
  rw [ht, hf, ← Complex.exp_add]
  rw [show Complex.I * (θ / 2) + -Complex.I * (θ / 2) = 0 by ring]
  simp

private theorem groupedPhaseScalar_true_mul_self (θ : ℝ) :
    groupedPhaseScalar θ true * groupedPhaseScalar θ true =
      Complex.exp (Complex.I * θ) := by
  have ht : groupedPhaseScalar θ true = Complex.exp (Complex.I * (θ / 2)) := by
    simp [groupedPhaseScalar]
  rw [ht]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem groupedPhaseScalar_true_star (θ : ℝ) :
    star (groupedPhaseScalar θ true) = groupedPhaseScalar θ false := by
  have ht : groupedPhaseScalar θ true = Complex.exp (Complex.I * (θ / 2)) := by
    simp [groupedPhaseScalar]
  have hf : groupedPhaseScalar θ false = Complex.exp (-Complex.I * (θ / 2)) := by
    simp [groupedPhaseScalar]
  rw [ht, hf, Complex.star_def, ← Complex.exp_conj]
  congr 1
  change (starRingEnd ℂ) (Complex.I * (θ / 2)) =
    -Complex.I * (θ / 2)
  rw [map_mul]
  simp [map_div₀, map_ofNat]

private theorem groupedPhysicalPotential_smul_ae (u : PhysicalL2) (c : ℂ) :
    (actualPhysicalL2SourcePotential (c • u) : ℝ → ℂ) =ᵐ[
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1))]
      fun t => c * actualPhysicalL2SourcePotential u t := by
  have hclass : actualPhysicalL2SourcePotential (c • u) =
      c • actualPhysicalL2SourcePotential u := by
    change scalarParityIntervalEquiv 0
        (⟨NlsGge.Analysis.naturalPhysicalCoverL2 (c • u),
          NlsGge.Analysis.naturalPhysicalCoverL2_mem_even (c • u)⟩ :
          scalarParity 0) =
      c • scalarParityIntervalEquiv 0
        (⟨NlsGge.Analysis.naturalPhysicalCoverL2 u,
          NlsGge.Analysis.naturalPhysicalCoverL2_mem_even u⟩ :
          scalarParity 0)
    have hsub :
        (⟨NlsGge.Analysis.naturalPhysicalCoverL2 (c • u),
          NlsGge.Analysis.naturalPhysicalCoverL2_mem_even (c • u)⟩ :
          scalarParity 0) =
        c • (⟨NlsGge.Analysis.naturalPhysicalCoverL2 u,
          NlsGge.Analysis.naturalPhysicalCoverL2_mem_even u⟩ :
          scalarParity 0) := by
      apply Subtype.ext
      exact NlsGge.Analysis.naturalPhysicalCoverL2.map_smul c u
    rw [hsub, map_smul]
  rw [hclass]
  exact (MeasureTheory.Lp.coeFn_smul c (actualPhysicalL2SourcePotential u)).mono
    fun t ht => by simpa only [Pi.smul_apply, smul_eq_mul] using ht

private theorem groupedSourcePotential_component_ae (n : ℤ)
    (u₁ u₂ : PhysicalL2) (x : recoveredActualSourceFreeWeightedDomain n)
    (b : Bool) :
    (actualSourcePotentialOnRecoveredWeightedDomainAfterAE n u₁ u₂ x b : ℝ → ℂ) =ᵐ[
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1))]
      fun t => actualPhysicalL2SourcePotential (if b then u₁ else u₂) t *
        (x.1 (!b) : ℝ → ℂ) t := by
  cases b
  · rw [actualSourcePotentialOnRecoveredWeightedDomain_apply,
      actualL2PotentialParityPairSourceOperator_apply_false]
    let f := actualSourceWeightedDomainLInfRepresentativeMap n
      (recoveredActualSourceWeightedDomainSequenceMapAfterAE n x)
    have hmul := actualSourceL2PotentialTimesLInf_ae u₂ (f true)
    have hrep := actualSourceWeightedDomainRepresentative_matches_source_ae n x true
    filter_upwards [hmul, hrep] with t hmul hrep
    calc
      actualSourceL2PotentialTimesLInf u₂ (f true) t =
          actualPhysicalL2SourcePotential u₂ t * f true t := hmul
      _ = actualPhysicalL2SourcePotential u₂ t * x.1 true t := by rw [hrep]
  · rw [actualSourcePotentialOnRecoveredWeightedDomain_apply,
      actualL2PotentialParityPairSourceOperator_apply_true]
    let f := actualSourceWeightedDomainLInfRepresentativeMap n
      (recoveredActualSourceWeightedDomainSequenceMapAfterAE n x)
    have hmul := actualSourceL2PotentialTimesLInf_ae u₁ (f false)
    have hrep := actualSourceWeightedDomainRepresentative_matches_source_ae n x false
    filter_upwards [hmul, hrep] with t hmul hrep
    calc
      actualSourceL2PotentialTimesLInf u₁ (f false) t =
          actualPhysicalL2SourcePotential u₁ t * f false t := hmul
      _ = actualPhysicalL2SourcePotential u₁ t * x.1 false t := by rw [hrep]

private theorem groupedSourceDomainPhase_sequence_apply (n : ℤ) (θ : ℝ)
    (x : recoveredActualSourceFreeWeightedDomain n) (i : Bool × Sector n) :
    (recoveredActualSourceWeightedDomainSequenceMapAfterAE n
      (groupedSourceDomainPhase n θ x)).val i =
      groupedPhaseScalar θ i.1 *
        (recoveredActualSourceWeightedDomainSequenceMapAfterAE n x).val i := by
  change sourcePairRepr n (groupedSourcePairPhase (groupedPhaseScalar θ) x.1) i =
    groupedPhaseScalar θ i.1 * sourcePairRepr n x.1 i
  exact groupedSourcePairRepr_phase n (groupedPhaseScalar θ) x.1 i

private theorem groupedSourceFree_phase (n : ℤ) (θ : ℝ)
    (x : recoveredActualSourceFreeWeightedDomain n) :
    actualSourceFreeDiracMapAfterAE n (groupedSourceDomainPhase n θ x) =
      groupedSourcePairPhase (groupedPhaseScalar θ)
        (actualSourceFreeDiracMapAfterAE n x) := by
  apply (sourcePairRepr n).injective
  apply lp.ext
  funext i
  rw [actualSourceFreeDiracMapAfterAE_repr_apply]
  rw [groupedSourcePairRepr_phase]
  rw [actualSourceFreeDiracMapAfterAE_repr_apply]
  rw [freeCoordinateDirac_apply, freeCoordinateDirac_apply]
  rw [groupedSourceDomainPhase_sequence_apply]
  ring

/-- The scalar identity for the off-diagonal potential, before passing to
almost-everywhere representatives. -/
private theorem groupedPhasePotential_pointwise (θ : ℝ) (b : Bool) (v w : ℂ) :
    ((groupedPhaseScalar θ b * groupedPhaseScalar θ b) * v) *
        (groupedPhaseScalar θ (!b) * w) =
      groupedPhaseScalar θ b * (v * w) := by
  have h : groupedPhaseScalar θ b * groupedPhaseScalar θ (!b) = 1 := by
    cases b
    · simpa only [Bool.not_false, mul_comm] using groupedPhaseScalar_true_mul_false θ
    · exact groupedPhaseScalar_true_mul_false θ
  calc
    _ = ((groupedPhaseScalar θ b * groupedPhaseScalar θ b) *
        groupedPhaseScalar θ (!b)) * (v * w) := by ring
    _ = groupedPhaseScalar θ b * (v * w) := by
      rw [mul_assoc (groupedPhaseScalar θ b), h, mul_one]

private theorem groupedSourcePotential_phase (n : ℤ) (θ : ℝ)
    (u₁ u₂ : PhysicalL2) (x : recoveredActualSourceFreeWeightedDomain n) :
    actualSourcePotentialOnRecoveredWeightedDomainAfterAE n
        ((groupedPhaseScalar θ true * groupedPhaseScalar θ true) • u₁)
        ((groupedPhaseScalar θ false * groupedPhaseScalar θ false) • u₂)
        (groupedSourceDomainPhase n θ x) =
      groupedSourcePairPhase (groupedPhaseScalar θ)
        (actualSourcePotentialOnRecoveredWeightedDomainAfterAE n u₁ u₂ x) := by
  apply PiLp.ext
  intro b
  apply MeasureTheory.Lp.ext
  have hleft := groupedSourcePotential_component_ae n
    ((groupedPhaseScalar θ true * groupedPhaseScalar θ true) • u₁)
    ((groupedPhaseScalar θ false * groupedPhaseScalar θ false) • u₂)
    (groupedSourceDomainPhase n θ x) b
  have hchoice :
      (if b then (groupedPhaseScalar θ true * groupedPhaseScalar θ true) • u₁
        else (groupedPhaseScalar θ false * groupedPhaseScalar θ false) • u₂) =
      (groupedPhaseScalar θ b * groupedPhaseScalar θ b) •
        (if b then u₁ else u₂) := by cases b <;> rfl
  rw [hchoice] at hleft
  have hpot := groupedPhysicalPotential_smul_ae (if b then u₁ else u₂)
    (groupedPhaseScalar θ b * groupedPhaseScalar θ b)
  have hin : ((groupedSourceDomainPhase n θ x).1 (!b) : ℝ → ℂ) =ᵐ[
      MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)]
      (fun t => groupedPhaseScalar θ (!b) * (x.1 (!b) : ℝ → ℂ) t) := by
    change ((groupedPhaseScalar θ (!b) • x.1 (!b) : SourceIntervalL2) : ℝ → ℂ)
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)] _
    exact (MeasureTheory.Lp.coeFn_smul (groupedPhaseScalar θ (!b)) (x.1 (!b))).mono
      fun t ht => by simpa only [Pi.smul_apply, smul_eq_mul] using ht
  have hright := groupedSourcePotential_component_ae n u₁ u₂ x b
  have hout := MeasureTheory.Lp.coeFn_smul (groupedPhaseScalar θ b)
    (actualSourcePotentialOnRecoveredWeightedDomainAfterAE n u₁ u₂ x b)
  filter_upwards [hleft, hpot, hin, hright, hout] with t hleft hpot hin hright hout
  change _ = (groupedPhaseScalar θ b •
    actualSourcePotentialOnRecoveredWeightedDomainAfterAE n u₁ u₂ x b) t
  simp only [Pi.smul_apply, smul_eq_mul] at hout
  rw [hleft, hpot, hin, hout, hright]
  exact groupedPhasePotential_pointwise θ b
    (actualPhysicalL2SourcePotential (if b then u₁ else u₂) t) (x.1 (!b) t)

private theorem groupedSourcePerturbed_phase (n : ℤ) (θ : ℝ)
    (u₁ u₂ : PhysicalL2) (x : recoveredActualSourceFreeWeightedDomain n) :
    actualSourcePerturbedDiracPMapAfterAE n
        ((groupedPhaseScalar θ true * groupedPhaseScalar θ true) • u₁)
        ((groupedPhaseScalar θ false * groupedPhaseScalar θ false) • u₂)
        (groupedSourceDomainPhase n θ x) =
      groupedSourcePairPhase (groupedPhaseScalar θ)
        (actualSourcePerturbedDiracPMapAfterAE n u₁ u₂ x) := by
  change actualSourceFreeDiracMapAfterAE n (groupedSourceDomainPhase n θ x) +
      actualSourcePotentialOnRecoveredWeightedDomainAfterAE n
        ((groupedPhaseScalar θ true * groupedPhaseScalar θ true) • u₁)
        ((groupedPhaseScalar θ false * groupedPhaseScalar θ false) • u₂)
        (groupedSourceDomainPhase n θ x) =
    groupedSourcePairPhase (groupedPhaseScalar θ)
      (actualSourceFreeDiracMapAfterAE n x +
        actualSourcePotentialOnRecoveredWeightedDomainAfterAE n u₁ u₂ x)
  rw [groupedSourceFree_phase, groupedSourcePotential_phase]
  apply PiLp.ext
  intro b
  simp [groupedSourcePairPhase, smul_add]

private def groupedSourceBlockPairPhase (θ : ℝ)
    (x : ActualFullPeriodTwoSourcePair) : ActualFullPeriodTwoSourcePair :=
  WithLp.toLp 2 (fun p : Fin 2 =>
    groupedSourcePairPhase (groupedPhaseScalar θ) (x p))

private def groupedSourceBlockDomainPhase (θ : ℝ)
    (x : actualFullPeriodTwoSourceBlockDomain) :
    actualFullPeriodTwoSourceBlockDomain :=
  ⟨groupedSourceBlockPairPhase θ x.1, fun p =>
    groupedRecoveredSourceDomain_phase_mem (p.val : ℤ) θ ⟨x.1 p, x.2 p⟩⟩

private theorem groupedSourceBlockAction_phase (θ : ℝ) (u₁ u₂ : PhysicalL2)
    (x : actualFullPeriodTwoSourceBlockDomain) :
    actualFullPeriodTwoSourceBlockAction
        ((groupedPhaseScalar θ true * groupedPhaseScalar θ true) • u₁)
        ((groupedPhaseScalar θ false * groupedPhaseScalar θ false) • u₂)
        (groupedSourceBlockDomainPhase θ x) =
      groupedSourceBlockPairPhase θ (actualFullPeriodTwoSourceBlockAction u₁ u₂ x) := by
  apply PiLp.ext
  intro p
  change actualSourcePerturbedDiracPMapAfterAE (p.val : ℤ)
      ((groupedPhaseScalar θ true * groupedPhaseScalar θ true) • u₁)
      ((groupedPhaseScalar θ false * groupedPhaseScalar θ false) • u₂)
      (groupedSourceDomainPhase (p.val : ℤ) θ ⟨x.1 p, x.2 p⟩) =
    groupedSourcePairPhase (groupedPhaseScalar θ)
      (actualSourcePerturbedDiracPMapAfterAE (p.val : ℤ) u₁ u₂
        ⟨x.1 p, x.2 p⟩)
  exact groupedSourcePerturbed_phase (p.val : ℤ) θ u₁ u₂ ⟨x.1 p, x.2 p⟩

private def groupedSourceDomainTransport (x : DoubledDomain) :
    actualFullPeriodTwoSourceBlockDomain :=
  ⟨actualFullPeriodTwoSourceIntervalAssembly x.1, x.2⟩

private theorem groupedSourceAssemblyPhase (θ : ℝ) (x : DoubledPair) :
    actualFullPeriodTwoSourceIntervalAssembly (groupedPhaseMap θ x) =
      groupedSourceBlockPairPhase θ (actualFullPeriodTwoSourceIntervalAssembly x) := by
  apply PiLp.ext
  intro p
  apply PiLp.ext
  intro b
  exact groupedSourceAssembly_phase θ x p b

/-- The actual physical doubled-period Dirac action is covariant under the
constant half-phase unitary. The witness domain is the actual assembled
weighted graph domain, invariant in both directions. -/
theorem grouped_phase_operator_conjugacy (u : PhysicalL2) (θ : ℝ) :
    ∃ U : DoubledPair ≃ₗᵢ[ℂ] DoubledPair,
      (∀ x b, U x b = groupedPhaseScalar θ b • x b) ∧
      ∃ hdom : ∀ x : DoubledPair,
        x ∈ DoubledDomain ↔ U x ∈ DoubledDomain,
        ∀ x : DoubledDomain,
          physicalDiracAction (Complex.exp (Complex.I * θ) • u)
            ⟨U x, (hdom x).mp x.property⟩ =
          U (physicalDiracAction u x) := by
  obtain ⟨U, hU⟩ := groupedPhaseUnitary θ
  have hUmap (y : DoubledPair) : (U y : DoubledPair) = groupedPhaseMap θ y := by
    apply PiLp.ext
    intro b
    exact hU y b
  have hdom : ∀ y : DoubledPair,
      y ∈ DoubledDomain ↔ U y ∈ DoubledDomain := by
    intro y
    rw [hUmap y]
    exact groupedPhaseMap_mem_actualDoubledDomain_iff θ y
  refine ⟨U, hU, hdom, ?_⟩
  intro x
  let xθ : DoubledDomain :=
    ⟨groupedPhaseMap θ x.1,
      groupedPhaseMap_mem_actualDoubledDomain θ x.1 x.2⟩
  have hxθ : (⟨U x, (hdom x).mp x.property⟩ : DoubledDomain) = xθ := by
    apply Subtype.ext
    exact hUmap x
  have htransport : groupedSourceDomainTransport xθ =
      groupedSourceBlockDomainPhase θ (groupedSourceDomainTransport x) := by
    apply Subtype.ext
    exact groupedSourceAssemblyPhase θ x.1
  have hphaseSq := groupedPhaseScalar_true_mul_self θ
  have hpot₁ : -(Complex.exp (Complex.I * θ) • u) =
      (groupedPhaseScalar θ true * groupedPhaseScalar θ true) • (-u) := by
    rw [← hphaseSq]
    simp
  have hpot₂ : star ((groupedPhaseScalar θ true * groupedPhaseScalar θ true) • (-u)) =
      (groupedPhaseScalar θ false * groupedPhaseScalar θ false) • star (-u) := by
    rw [NlsGge.GKDefinitionDesign.g2040_star_smul]
    change star (groupedPhaseScalar θ true * groupedPhaseScalar θ true) • star (-u) = _
    rw [show star (groupedPhaseScalar θ true * groupedPhaseScalar θ true) =
        groupedPhaseScalar θ false * groupedPhaseScalar θ false by
      calc
        _ = star (groupedPhaseScalar θ true) * star (groupedPhaseScalar θ true) :=
          map_mul (starRingEnd ℂ) _ _
        _ = _ := by rw [groupedPhaseScalar_true_star]]
  rw [hxθ, hUmap]
  change -actualFullPeriodTwoDoubledCirclePerturbedDiracAction
      (-(Complex.exp (Complex.I * θ) • u))
      (star (-(Complex.exp (Complex.I * θ) • u))) xθ =
    groupedPhaseMap θ
      (-actualFullPeriodTwoDoubledCirclePerturbedDiracAction (-u) (star (-u)) x)
  rw [(groupedPhaseMap θ).map_neg, neg_inj, hpot₁, hpot₂]
  apply actualFullPeriodTwoSourceIntervalAssembly.injective
  rw [actualFullPeriodTwoDoubledCirclePerturbedDiracAction_repr,
    groupedSourceAssemblyPhase,
    actualFullPeriodTwoDoubledCirclePerturbedDiracAction_repr]
  change actualFullPeriodTwoSourceBlockAction
      ((groupedPhaseScalar θ true * groupedPhaseScalar θ true) • (-u))
      ((groupedPhaseScalar θ false * groupedPhaseScalar θ false) • star (-u))
      (groupedSourceDomainTransport xθ) =
    groupedSourceBlockPairPhase θ
      (actualFullPeriodTwoSourceBlockAction (-u) (star (-u))
        (groupedSourceDomainTransport x))
  rw [htransport]
  exact groupedSourceBlockAction_phase θ (-u) (star (-u))
    (groupedSourceDomainTransport x)

end

end NlsGge.ThirdConsultation.Narrative

