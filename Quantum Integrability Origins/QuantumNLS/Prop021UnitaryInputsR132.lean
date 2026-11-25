import QuantumNLS.Prop021TransportR132

/-! The two predecessor inputs in unitary coordinates, with exact
equivalences to their R131 forms on the reference Hilbert space. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 150000
open scoped InnerProductSpace ENNReal

namespace QuantumNLS.Prop021UnitaryInputsR132
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop022GTensor Prop022AIsoTensor Prop022GClassical Prop022AFock Prop022OVacuum
open Prop021MomentsR132 Prop021UnitaryR132

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

/-- The exact printed pair input, with arbitrary source data in unitary coordinates. -/
def UnitaryPairInput : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (U : H ≃ₗᵢ[ℂ] L2T L) (A M : ℝ) (hA : 0 < A) (hM : 1 ≤ M)
    (K : Kernels H) (hK : KBound K M A) (hs : KSelfAdj K)
    (u₀ : H) (hu₀ : ‖u₀‖ = 1) (T P : ℝ) (hP : 1 ≤ P),
    Prop024WeylConventionR55.Prop022PairInput (kernelsL U K) M A hM hA
      (fun i => (norm_conjSym_le U (i+1) (K i)).trans (hK i))
      (fun i => conjSym_adjoint U (i+1) (K i) (hs i)) (sphL U u₀ hu₀) T P hP

theorem unitaryPair_iff_torus :
    UnitaryPairInput (L := L) ↔ Prop021AssemblyR131.Prop022PairFamily (L := L) := by
  constructor
  · intro h A M hA hM K hK hs u₀ T P hP
    have h' := h (L2T L) (torusId L) A M hA hM K hK hs u₀.val u₀.property T P hP
    have hu : sphL (torusId L) u₀.val u₀.property = u₀ := Subtype.ext rfl
    have transfer (B : Kernels (L2T L)) (hB : KBound B M A) (hsB : KSelfAdj B)
        (v : Prop001.Sphere (L2T L)) (eh : B = K) (ev : v = u₀)
        (input : Prop024WeylConventionR55.Prop022PairInput B M A hM hA
          (fun n => hB n) (fun n => hsB n) v T P hP) :
        Prop024WeylConventionR55.Prop022PairInput K M A hM hA hK hs u₀ T P hP := by
      subst B
      subst v
      exact input
    exact transfer (kernelsL (torusId L) K)
      (fun i => (norm_conjSym_le (torusId L) (i+1) (K i)).trans (hK i))
      (fun i => conjSym_adjoint (torusId L) (i+1) (K i) (hs i))
      (sphL (torusId L) u₀.val u₀.property) (kernelsL_refl K) hu h'
  · intro h E _ _ _ U A M hA hM K hK hs u₀ hu₀ T P hP
    exact h A M hA hM (kernelsL U K)
      (fun i => (norm_conjSym_le U (i+1) (K i)).trans (hK i))
      (fun i => conjSym_adjoint U (i+1) (K i) (hs i)) (sphL U u₀ hu₀) T P hP

/-- One instance of the strong shifted-Hamiltonian identity in physical coordinates. -/
def PhysicalRemainder (B : ∀ n, HN L n →L[ℂ] HN L n) (N : ℕ) (u : L2T L)
    (y : Fock L) (bound : ℝ) : Prop :=
  let W := printedWeyl ((Real.sqrt N : ℂ) • u)
  let ℍ := Prop021ManyBodyR129.hamiltonian B N
  ∃ (hx : Ext006ModeDomainR33a.Smooth (Ext006PhysicalVacuum.coefficient y))
    (h₂ : y ∈ Ext005Moments.momentDomain (L := L) 2)
    (hd : W y ∈ ℍ.domain) (R : Fock L),
    ℍ ⟨W y,hd⟩ = W (Prop021RemainderInputR131.lowOrders B N u y hx h₂ + R) ∧ ‖R‖ ≤ bound

/-- Q7B:lem:remainder in unitary coordinates. In these coordinates the
remainder determines the same-norm remainder on the source Fock space by Γ(U)⁻¹. -/
def RemainderEstimateUnitary (U : H ≃ₗᵢ[ℂ] L2T L) (A CA' : ℝ) : Prop :=
  ∀ (B : ∀ n, SymSector ℂ H n →L[ℂ] SymSector ℂ H n) (M : ℝ), 1 ≤ M →
    (∀ n, 1 ≤ n → ‖B n‖ ≤ M * A^n / Real.sqrt ((2*n).factorial : ℝ)) →
    (∀ n, (B n).adjoint = B n) →
  ∀ (N : ℕ) (Q : ℝ), 1 ≤ Q → 256 * Real.exp 1 * A * Q ≤ N →
  ∀ (u : H), ‖u‖ = 1 → ∀ (x : FockSpace H), NumberMoments Q x →
    PhysicalRemainder (fun n => conjSym U n (B n)) N (U u) (gam U x)
      (CA' * M * (N : ℝ)^(-(1/2 : ℝ)) * Q^(3/2 : ℝ))

def UnitaryRemainderInput (A CA' : ℝ) : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    ∀ U : H ≃ₗᵢ[ℂ] L2T L, RemainderEstimateUnitary U A CA'

theorem unitaryRemainder_iff_torus (A C : ℝ) :
    UnitaryRemainderInput (L := L) A C ↔ Prop021RemainderInputR131.RemainderEstimate (L := L) A C := by
  constructor
  · intro h B M hM hB hs N Q hQ hN u hu x hm
    have hS := h (L2T L) (torusId L) B M hM hB hs N Q hQ hN u hu x
      ((numberMoments_torus Q x).mpr hm)
    have hB' : (fun n => conjSym (torusId L) n (B n)) = B := by
      funext n
      apply ContinuousLinearMap.ext
      intro y
      obtain ⟨z,rfl⟩ := (symMap (torusId L) n).surjective y
      rw [conjSym_apply, LinearIsometryEquiv.symm_apply_apply, symMap_refl, symMap_refl]
    have hid : torusId L u = u := rfl
    rw [hB', gam_refl, hid] at hS
    exact hS
  · intro h E _ _ _ U B M hM hB hs N Q hQ hN u hu x hm
    let B' := fun n => conjSym U n (B n)
    have hB' : Prop022FactorialCoefficientsR115.FactorialBound B' M A :=
      fun n hn => (norm_conjSym_le U n (B n)).trans (hB n hn)
    have hs' : ∀ n, (B' n).adjoint = B' n :=
      fun n => conjSym_adjoint U n (B n) (hs n)
    have hm' : Prop021RemainderInputR131.NumberMoments Q (gam U x) := by
      apply (numberMoments_torus Q (gam U x)).mp
      have hI := (numberMoments_transport U.toLinearIsometry Q x).mpr hm
      rw [fockMapI_equiv] at hI
      exact hI
    exact h B' M hM hB' hs' N Q hQ hN (U u)
      ((U.norm_map u).trans hu) (gam U x) hm'

end QuantumNLS.Prop021UnitaryInputsR132

#print axioms QuantumNLS.Prop021UnitaryInputsR132.unitaryPair_iff_torus
#print axioms QuantumNLS.Prop021UnitaryInputsR132.unitaryRemainder_iff_torus

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let moduleName := "Prop021UnitaryInputsR132"
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith ("QuantumNLS." ++ moduleName ++ ".") ||
        n.toString.startsWith ("_private.QuantumNLS." ++ moduleName ++ ".") then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").contains "HeldGP14Tonelli" ||
          (n.toString.splitOn ".").contains "RegularCut" then
        throwError "Forbidden held dependency: {n}"
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
  Lean.logInfo m!"R132 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
