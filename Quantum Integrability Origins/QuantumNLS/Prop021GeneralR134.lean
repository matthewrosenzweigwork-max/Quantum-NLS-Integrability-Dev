import QuantumNLS.Prop021PairR134
import QuantumNLS.Prop024GeneralR134

/-! Q7B:thm:main on a separable complex Hilbert space, using the
intrinsic Weyl exponential and its canonical quadratic vacuum. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5500000
set_option synthInstance.maxHeartbeats 180000
open scoped InnerProductSpace ENNReal
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop021GeneralR134
open PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop022GTensor Prop022GClassical Prop022GHilbert Prop022AIsoTensor Prop022BExist
open Prop022BIso Prop022BClass1 Prop022BClass2 Prop022BFock1 Prop022BFock2 Prop022BFock3 Prop022AFock
open Prop022PositiveDataR126 Prop022ActualProfileR117 Prop022OVacuum Ext006PhysQuasifree Ext006PhysFockCoord
open Prop022CWeyl Prop022CIntrinsic Prop022GAntiHS
open Prop021StatementR132 Prop021CoherentTransportR132 Prop021ManyBodyTransportR132
open Prop025OInputs Prop021RatesR128 Prop022FactorialMajorantR115
open Prop024CanonicalWeylR133

variable {L : ℝ} [Fact (0 < L)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- Both the unitary realization and the canonical H-level Weyl family
are the time-one group of the same intrinsic generator. -/
theorem unitary_weyl (U : H ≃ₗᵢ[ℂ] L2T L) (v : H) :
    WH U v = weyl v :=
  weylOp_unique (WH_isWeylOp U v) (Prop024GeneralR134.weyl_isWeylOp v)

/-- The coherent and marginal estimates, with the intrinsic quadratic
propagator and the same vacuum as the coherent bound. -/
def AtConstants (J : H →ₗᵢ[ℂ] L2T L) (A : ℝ) (hA : 0 < A) (cA T CAT : ℝ) : Prop :=
  (∀ v : H, IsWeylOp v (weyl v)) ∧
  ∀ (K : Kernels H) (M : ℝ) (hM : 1 ≤ M)
    (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1) (P : ℝ), 1 ≤ P →
    let S := SJ J K M A hA.le hK hs u₀ hu₀
    let u := profJ J K M A hA.le hK hs u₀ hu₀
    let V := VJ J K M A hM hA hK hs u₀ hu₀
    let Ω := vacJ J
    IsVacuum Ω ∧
    IntrinsicFock V (aSymJ J K M A hA hK hs u₀ hu₀) (bSymJ J K M A hA hK hs u₀ hu₀)
      S Ω (fun t => antiHS (TraceClass.refBasis H) (betaJ J K M A hA.le hK hs u₀ hu₀ t 0)) ∧
    ((∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ‖S t s‖ ≤ P) →
      ∀ N : ℕ, 1 ≤ N → cA * Qpar A T M P ≤ N →
        Bounds K hs u₀ u (fun v x => weyl v x) Ω PureQuasifreeH A T M P CAT N ∧
        ∃ θ, CoherentWitness K hs u₀ u (fun v x => weyl v x) Ω PureQuasifreeH
          A T M P CAT N θ (fun t => V t 0 Ω))

private theorem transfer_at_constants (J : H →ₗᵢ[ℂ] L2T L)
    (A : ℝ) (hA : 0 < A) (cA T CAT C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hcut : 256 * Real.exp 1 * A ≤ cA) (hCAT : T * C ≤ CAT)
    (hTorus : TorusAtConstants (L := L) A hA cA T CAT)
    (hPair : Prop021AssemblyR131.Prop022PairFamily (L := L))
    (hRem : Prop021RemainderInputR131.RemainderEstimate (L := L) A C) :
    AtConstants J A hA cA T CAT := by
  refine ⟨Prop024GeneralR134.weyl_isWeylOp, ?_⟩
  intro K M hM hK hs u₀ hu₀ P hP
  have hFock := Prop022CMain.intrinsic_of_J J K M A hM hA hK hs u₀ hu₀ T P hP
    (TraceClass.refBasis H)
  refine ⟨Prop022CMain.isVacuum_vacJ J, hFock, ?_⟩
  intro hS N hN hNQ
  obtain ⟨-, hmarg, hprep⟩ :=
    Prop021IsometryR132.transfer_at_constants J A hA cA T CAT C hT hC hcut hCAT
      hTorus hPair hRem K M hM hK hs u₀ hu₀ P hP hS N hN hNQ
  let B := kernelsL (UI L) (kernelsI J K)
  have hB : KBound B M A := fun i =>
    (norm_conjSym_le (UI L) (i+1) (kernelsI J K i)).trans (hKJ J K M A hK i)
  have hsB : KSelfAdj B :=
    fun i => conjSym_adjoint (UI L) (i+1) (kernelsI J K i) (hsJ J K hs i)
  let u₀L := sphL (UI L) (J u₀) (hJu J u₀ hu₀)
  let u := profJ J K M A hA.le hK hs u₀ hu₀
  let ξ := fun t => VJ J K M A hM hA hK hs u₀ hu₀ t 0 (vacJ J)
  let θ := Prop021PhaseR130.theta (positiveExtension B) M A hA.le
    (positiveExtension_bound B M A hB) (positiveExtension_selfAdjoint B hsB) u₀L N
  have hQ : 0 ≤ Qpar A T M P := zero_le_one.trans (one_le_numberParameter (pairMajorant A) T M P)
  have hNlarge : 256 * Real.exp 1 * A * Qpar A T M P ≤ N :=
    (mul_le_mul_of_nonneg_right hcut hQ).trans hNQ
  have hCanon := canonical_torus B A M hA hM hB hsB u₀L T P hT.le hP
    (hPair A M hA hM B hB hsB u₀L T P hP)
    (Prop021IsometryR132.embedded_variational J K M A hA hK hs u₀ hu₀ T P hP hS)
    C hC hRem N hNlarge
  have hCore : CoherentWitness B hsB (J u₀) (fun t => J (u t))
      (fun v x => printedWeyl v x) vac PhysicalQuasifreeSource
      A T M P (T*C) N θ (fun t => fockMapI J (ξ t)) := by
    rw [funext (Prop021IsometryR132.embedded_profile J K M A hA hK hs u₀ hu₀),
      funext (Prop021IsometryR132.embedded_fluctuation J K M A hM hA hK hs u₀ hu₀)]
    exact hCanon
  have hB' : B = extendKernels J K := Prop021IsometryR132.ambient_kernels J K
  have hBody (t : ℝ) (x : Fock L) : manyBodyEvolution B hsB N t x =
      manyBodyEvolution (extendKernels J K) (extendKernels_selfAdj J K hs) N t x := by
    apply lp.ext
    funext n
    change sectorEvolution B N n t (x n) = sectorEvolution (extendKernels J K) N n t (x n)
    rw [hB']
  have hPhys : CoherentWitness (extendKernels J K) (extendKernels_selfAdj J K hs)
      (J u₀) (fun t => J (u t)) (fun v x => printedWeyl v x) vac PhysicalQuasifreeSource
      A T M P (T*C) N θ (fun t => fockMapI J (ξ t)) := by
    obtain ⟨h0, hn, he, hd⟩ := hCore
    exact ⟨h0, hn, fun t ht => (by simpa only [hBody] using he t ht), hd⟩
  obtain ⟨h0, hn, he, hd⟩ := restrict_coherent J K hs u₀ u (fun v x => weyl v x) (vacJ J)
    (fun v x => isometry_intrinsic_gam J v (weyl v) (Prop024GeneralR134.weyl_isWeylOp v) x)
    (gam_vacJ J) A T M P (T*C) N θ ξ hPhys
  have hWitness : CoherentWitness K hs u₀ u (fun v x => weyl v x) (vacJ J)
      PureQuasifreeH A T M P CAT N θ ξ := by
    refine ⟨h0, fun t ht => ⟨(hn t ht).1, (hFock.quasifree t).1⟩, ?_, hd⟩
    intro t ht
    apply (he t ht).trans
    have hM₀ := zero_le_one.trans hM
    gcongr
  exact ⟨⟨⟨θ, ξ, hWitness⟩, hmarg, hprep⟩, ⟨θ, hWitness⟩⟩

/-- The same constants work for all separable carriers and every
isometric realization. The bounds use the intrinsic Fock operators. -/
def Prop021 (L : ℝ) [Fact (0 < L)] : Prop :=
  ∀ (A : ℝ) (hA : 0 < A), ∃ cA : ℝ, ∀ T : ℝ, 0 < T → ∃ CAT : ℝ,
  ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H],
    Nonempty (H →ₗᵢ[ℂ] L2T L) ∧
    ∀ J : H →ₗᵢ[ℂ] L2T L, AtConstants J A hA cA T CAT

private theorem enlarge_constants (A : ℝ) (hA : 0 < A) (c₁ c₂ T C₁ C₂ : ℝ)
    (hc : c₁ ≤ c₂) (hC : C₁ ≤ C₂) (h : TorusAtConstants (L := L) A hA c₁ T C₁) :
    TorusAtConstants (L := L) A hA c₂ T C₂ := by
  intro K M hM hK hs u₀ P hP hS N hN hNQ
  have hM₀ : 0 ≤ M := zero_le_one.trans hM
  have hQ : 0 ≤ Qpar A T M P := zero_le_one.trans (one_le_numberParameter (pairMajorant A) T M P)
  obtain ⟨⟨θ,ξ,h0,hn,he,hd⟩,hmarg,hprep⟩ :=
    h K M hM hK hs u₀ P hP hS N hN ((mul_le_mul_of_nonneg_right hc hQ).trans hNQ)
  refine ⟨⟨θ,ξ,h0,hn,?_,hd⟩,?_,?_⟩
  · intro t ht
    apply (he t ht).trans
    gcongr
  · intro k hk0 hk t ht
    apply (hmarg k hk0 hk t ht).trans
    apply ENNReal.ofReal_le_ofReal
    gcongr
  · intro k hk0 hk ψ hψ t ht
    apply (hprep k hk0 hk ψ hψ t ht).trans
    apply ENNReal.ofReal_le_ofReal
    gcongr

/-- The finite-isometry remainder of R133 supplies the exact R132
remainder family, including its torus specialization. -/
theorem prop021 : Prop021 L := by
  have hPair := Prop021PairR134.pair_family (L := L)
  have hRem := Prop024TransferR133.remainderInput (L := L)
  have hTorus := (torus_statement (L := L)).mpr
    (Prop021AssemblyR131.prop021 hPair (Prop021ContractsR132.remainder_torus hRem))
  intro A hA
  obtain ⟨cA,hcA⟩ := hTorus A hA
  obtain ⟨C,hC,hRemA⟩ := Prop021ContractsR132.remainder_torus hRem A hA
  let cutoff := 256 * Real.exp 1 * A
  refine ⟨max cA cutoff, fun T hT => ?_⟩
  obtain ⟨CAT,hCAT⟩ := hcA T hT
  let estimate := max CAT (T*C)
  have h := enlarge_constants A hA cA (max cA cutoff) T CAT estimate
    (le_max_left cA cutoff) (le_max_left CAT (T*C)) hCAT
  refine ⟨estimate, fun H _ _ _ _ => ⟨?_, fun J => ?_⟩⟩
  · by_cases hH : FiniteDimensional ℂ H
    · exact exists_isometry_fin hH L
    · obtain ⟨U⟩ := exists_unitary_L2T L hH
      exact ⟨U.toLinearIsometry⟩
  · exact transfer_at_constants J A hA (max cA cutoff) T estimate C hT hC
      (le_max_right cA cutoff) (le_max_right CAT (T*C)) h hPair hRemA

end QuantumNLS.Prop021GeneralR134

#print axioms QuantumNLS.Prop021GeneralR134.unitary_weyl
#print axioms QuantumNLS.Prop021GeneralR134.prop021
