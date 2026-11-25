import QuantumNLS.Prop021CoherentComparisonR131
import QuantumNLS.Prop021CoherentCoreR131
import QuantumNLS.Prop021ExcitationWeylR131
import QuantumNLS.Prop021MarginalProductR131
import QuantumNLS.Prop025OInputs

/-! Intermediate torus PROP-021, with the two exact named inputs and
the statement consumed by PROP-025. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Prop021AssemblyR131

open PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors TensorCarrier TraceClass
open Prop022PositiveDataR126 Prop022FactorialMajorantR115 Prop022ClassicalFlowR126 Prop022ActualProfileR117
open Prop022FlowDifferentialR126 Prop022OVacuum Ext006NumberPhase Ext006PhysFockCoord Ext005Moments
open Prop021RemainderInputR131 Prop021CoherentComparisonR131 Prop021QuadraticBindingR129
open Prop021ManyBodyR129 Prop021RatesR128 Prop021ExcitationR130 Prop021ExcitationFockR130
open Prop021MarginalR128 Prop025OInputs Prop024WeylConventionR55
variable {L : ℝ} [Fact (0 < L)]

/-- Universal closure of the existing exact named PROP-022 input. -/
def Prop022PairFamily : Prop :=
  ∀ (A M : ℝ) (hA : 0 < A) (hM : 1 ≤ M)
    (K : ∀ n, HN L (n+1) →L[ℂ] HN L (n+1))
    (hK : ∀ n, ‖K n‖ ≤ M * A^(n+1) / Real.sqrt ((2*(n+1)).factorial : ℝ))
    (hsK : ∀ n, (K n).adjoint = K n) (u₀ : Prop001.Sphere (L2T L)) (T P : ℝ) (hP : 1 ≤ P),
    Prop022PairInput K M A hM hA hK hsK u₀ T P hP

private lemma wvec_unit (u : L2T L) (hu : ‖u‖ = 1) (N : ℕ) :
    ‖HighMomentsOps.wvec N u‖ = 1 := by
  change ‖(htpow N u : HilbertTensorPower ℂ (L2T L) N)‖ = 1
  rw [norm_htpow, hu, one_pow]

section PositiveRanks

variable (K : ∀ n, HN L (n+1) →L[ℂ] HN L (n+1)) (M A : ℝ)
    (hM : 1 ≤ M) (hA : 0 < A)
    (hK : ∀ n, ‖K n‖ ≤ M * A^(n+1) / Real.sqrt ((2*(n+1)).factorial : ℝ))
    (hsK : ∀ n, (K n).adjoint = K n) (u₀ : Prop001.Sphere (L2T L))
    (T P : ℝ) (hP : 1 ≤ P) (N : ℕ)
local notation "B" => positiveExtension K
local notation "hB" => positiveExtension_bound K M A hK
local notation "hs" => positiveExtension_selfAdjoint K hsK
local notation "hM₀" => (zero_le_one.trans hM)
local notation "Q" => Qpar A T M P
local notation "E" => manyBodyEvolution B hs N
local notation "u" => profile B M A hA.le hB hs u₀
local notation "ξ" => fluctuation B M A hM₀ hA.le hB hs u₀
local notation "v" => Prop021PhaseR130.center B M A hA.le hB hs u₀ N
local notation "p" => Prop021PhaseR130.phase B M A hA.le hB hs u₀ N
local notation "app" => approximate B M A hM₀ hA.le hB hs u₀ N
local notation "init" => HighMomentsOps.wvec N (u₀ : L2T L)

include hP in
private theorem approx_contraction_bound (hT : 0 ≤ T)
    (hS : ∀ r q : ℝ, |r| ≤ T → |q| ≤ T →
      ‖fderiv ℝ (classicalFlow B M A hA.le hB hs (r - q)) (u q)‖ ≤ P)
    (hN : 1 ≤ N) (t : ℝ) (ht : |t| ≤ T) :
    ‖contraction (u t) N (app t N)‖ ≤ Real.sqrt (Q/N) := by
  have hu := (profile_spec B M A hA.le hB hs u₀).2.2.1 t
  have hξ := (fluctuation_initial_norm_smooth B M A hM₀ hA.le hB hs u₀).2.2.1 t
  have hmem := (Prop021DisplacementR129.common_domain (ξ t)).mp hξ 2
  let z := printedWeyl (v t) (ξ t)
  obtain ⟨hξr, hz, he⟩ := Prop021ExcitationWeylR131.root_weyl_norm (u t) (v t) hu
    (Real.sqrt N : ℂ) rfl (ξ t) hmem
  let R := root (u t)
  have happ : app t ∈ R.domain := R.domain.smul_mem (p t) hz
  have hnorm : ‖R ⟨app t,happ⟩‖ = ‖R ⟨ξ t,hξr⟩‖ := by
    change ‖R ((p t) • (⟨z,hz⟩ : R.domain))‖ = _
    rw [LinearPMap.map_smul, norm_smul, Prop021PhaseR130.phase_norm, one_mul]
    exact he
  have hdep := vacuumRoot_bound B M A hM₀ hA.le hB hs u₀ T P hT hP
    (fun r q hr hq => by rw [flow_eq_fderiv]; exact hS r q hr hq) t ht
  change ‖R ⟨ξ t,hξr⟩‖^2 ≤ Q-1 at hdep
  have hQ : 0 ≤ Q := zero_le_one.trans (one_le_numberParameter (pairMajorant A) T M P)
  have hfull : ‖R ⟨app t,happ⟩‖ ≤ Real.sqrt Q := by
    rw [hnorm]
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg Q)).mp
    rw [Real.sq_sqrt hQ]
    exact hdep.trans (sub_le_self _ zero_le_one)
  have hsec : ‖excitationRoot (u t) N (app t N)‖ ≤ ‖R ⟨app t,happ⟩‖ :=
    lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (R ⟨app t,happ⟩) N
  rw [normalized_root _ N hN, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    Real.sqrt_div hQ, div_eq_mul_inv, mul_comm (Real.sqrt Q)]
  exact mul_le_mul_of_nonneg_left (hsec.trans hfull) (by positivity)

private theorem sector_marginal_bound (hT : 0 ≤ T)
    (hPair : Prop022PairInput K M A hM hA hK hsK u₀ T P hP)
    (hS : ∀ r q : ℝ, |r| ≤ T → |q| ≤ T →
      ‖fderiv ℝ (classicalFlow B M A hA.le hB hs (r - q)) (u q)‖ ≤ P)
    (C : ℝ) (hC : 0 ≤ C) (hRem : RemainderEstimate (L := L) A C)
    (hN : 1 ≤ N) (hNQ : 256 * Real.exp 1 * A * Q ≤ N)
    (k : ℕ) (hk : k ≤ N) (t : ℝ) (ht : |t| ≤ T) :
    traceNorm (reducedDensityN N k hk (nEvolution B N t init).val - tensorProj k (u t)) ≤
      ENNReal.ofReal ((2*Real.sqrt (Real.exp 1)*max (T*C) 1) *
        Real.sqrt k * (N : ℝ)^(-(1/4 : ℝ)) * (M * Q^(3/2 : ℝ)+Real.sqrt Q)) := by
  let x := E t (printedWeyl ((Real.sqrt N : ℂ) • (u₀ : L2T L)) vac)
  let ψ := nEvolution B N t init
  let J := contraction (u t) N
  have hu := (profile_spec B M A hA.le hB hs u₀).2.2.1 t
  have hψ : ‖ψ‖ = 1 :=
    ((sectorEvolution B hs N N t).norm_map init).trans (wvec_unit _ u₀.property N)
  have hcontract (z : HN L N) : ‖J z‖ ≤ ‖z‖ :=
    (ContinuousLinearMap.le_opNorm J z).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (contraction_norm (u t) hu N) (norm_nonneg z))
  have hxy := coherent_bound K M A hM hA hK hsK u₀ T P hP N hT hPair hS
    C hC hRem hNQ t ht
  have hx := exact_sector_extraction B hs N t
    (printedWeyl ((Real.sqrt N : ℂ) • (u₀ : L2T L)) vac) init _
    (Prop021CoherentCoreR131.coherent_number_sector N (u₀ : L2T L) u₀.property)
  have hproj := Prop021SectorTransferR128.coherent_contraction_transfer N hN J hcontract ψ x (app t) hx hxy
  have hb := approx_contraction_bound K M A hM hA hK hsK u₀ T P hP N hT hS hN t ht
  have hscale : 0 ≤ Real.sqrt (Real.exp 1) * (N : ℝ)^(1/4 : ℝ) := by positivity
  have hJ := hproj.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hb) hscale)
  have htrace := Prop021MarginalProductR131.marginal_distance (u t) hu N k hN hk ψ hψ
  apply htrace.trans
  apply ENNReal.ofReal_le_ofReal
  apply (mul_le_mul_of_nonneg_left hJ (by positivity : 0 ≤ 2 * Real.sqrt (k : ℝ))).trans
  exact source_marginal_rate (by exact_mod_cast (show 0 < N by omega))
    (zero_le_one.trans (one_le_numberParameter (pairMajorant A) T M P)) hM₀ (T*C) k

end PositiveRanks

/-- Intermediate PROP-021 with the same torus proposition used directly
as PROP-025's input type. -/
theorem prop021 (hPair : Prop022PairFamily (L := L)) (hRemainder : Prop024RemainderInput (L := L)) :
    Prop025OInputs.Prop021Input (L := L) := by
  intro A hA
  obtain ⟨C,hC,hRem⟩ := hRemainder A hA
  refine ⟨256 * Real.exp 1 * A, ?_⟩
  intro T hT
  let CAT := 2*Real.sqrt (Real.exp 1)*max (T*C) 1
  refine ⟨CAT, ?_⟩
  intro K M hM hK hsK u₀ P hP hS N hN hNQ
  let B := positiveExtension K
  let hB := positiveExtension_bound K M A hK
  let hs := positiveExtension_selfAdjoint K hsK
  have hM₀ := zero_le_one.trans hM
  let u := profile B M A hA.le hB hs u₀
  let ξ := fluctuation B M A hM₀ hA.le hB hs u₀
  let θ := Prop021PhaseR130.theta B M A hA.le hB hs u₀ N
  have hPair' := hPair A M hA hM K hK hsK u₀ T P hP
  have hη := fluctuation_initial_norm_smooth B M A hM₀ hA.le hB hs u₀
  have hQ : 0 ≤ Qpar A T M P := zero_le_one.trans
    (one_le_numberParameter (pairMajorant A) T M P)
  have hCAT : 0 ≤ CAT := mul_nonneg (by positivity) (zero_le_one.trans (le_max_right _ _))
  have hc : T*C ≤ CAT := by
    have he : 1 ≤ Real.sqrt (Real.exp 1) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1))
    have hm : T*C ≤ max (T*C) 1 := le_max_left _ _
    have hn : 0 ≤ max (T*C) 1 := zero_le_one.trans (le_max_right _ _)
    dsimp [CAT]
    nlinarith [mul_nonneg (sub_nonneg.mpr he) hn]
  have hMarg := sector_marginal_bound K M A hM hA hK hsK u₀ T P hP N hT.le hPair'
    (fun r q hr hq => hS q r hq hr) C hC hRem hN hNQ
  refine ⟨⟨θ,ξ,hη.1,?_,?_,?_⟩,?_,?_⟩
  · intro t _
    have h := Prop021QuadraticR130.quadratic_vacuum B M A hM₀ hA.le hB hs u₀ t
    exact ⟨h.2.1,h.1⟩
  · intro t ht
    have h := coherent_bound K M A hM hA hK hsK u₀ T P hP N hT.le hPair'
      (fun r q hr hq => hS q r hq hr) C hC hRem hNQ t ht
    have hh := h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc hM₀) (Real.rpow_nonneg (Nat.cast_nonneg N) _))
      (Real.rpow_nonneg hQ _))
    rw [← neg_mul Complex.I (θ t : ℂ)]
    exact hh
  · intro t ht
    have hv := Prop021QuadraticR130.quadratic_vacuum B M A hM₀ hA.le hB hs u₀ t
    rw [← ENNReal.ofReal_toReal hv.2.2.2]
    apply ENNReal.ofReal_le_ofReal
    apply Prop021QuadraticR130.quadratic_depletion B M A hM₀ hA.le hB hs u₀ T P hT.le hP _ t ht
    intro r q hr hq
    rw [flow_eq_fderiv]
    exact hS q r hq hr
  · intro k _ hk t ht
    exact hMarg k hk t ht
  · intro k _ hk ψ hψ t ht
    let U := (sectorEvolution B hs N N t).toLinearIsometry
    let init := HighMomentsOps.wvec N (u₀ : L2T L)
    have h := preparation_target N k hk U init ψ (wvec_unit _ u₀.property N) hψ (tensorProj k (u t))
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    exact h.trans (add_le_add (hMarg k hk t ht) le_rfl)

end QuantumNLS.Prop021AssemblyR131

#print axioms QuantumNLS.Prop021AssemblyR131.prop021

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if ["Prop021AssemblyR131"].any
        (fun m => n.toString.startsWith ("QuantumNLS." ++ m ++ ".") ||
          n.toString.startsWith ("_private.QuantumNLS." ++ m ++ ".")) then
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
  Lean.logInfo m!"R131 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
