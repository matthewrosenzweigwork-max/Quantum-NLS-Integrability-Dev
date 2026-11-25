import QuantumNLS.Prop021UnitaryInputsR132
import QuantumNLS.Prop022BClass3
import QuantumNLS.Prop022BIndep
import QuantumNLS.Prop022BExist

/-! With zero-extended kernels, the classical flow is the identity on the
orthogonal complement at the linearized level. The physical Weyl and
quadratic flows preserve the second-quantized image. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5500000
set_option synthInstance.maxHeartbeats 150000
open scoped InnerProductSpace ENNReal
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop021IsometryR132
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop022GTensor Prop022GClassical Prop022GLinear Prop022AIsoTensor Prop022BIso
open Prop022BClass1 Prop022BClass2 Prop022BClass3 Prop022BFock1 Prop022BFock2 Prop022BIndep
open Prop022PositiveDataR126 Prop022ClassicalFlowR126 Prop022ActualProfileR117
open Prop022OVacuum Prop022AFock Ext006PhysQuasifree Ext006PhysFockCoord
open Prop021ManyBodyTransportR132 Prop021StatementR132 Prop021CoherentTransportR132
open Prop021RemainderInputR131 Prop021QuadraticBindingR129 Prop025OInputs

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

open Prop021UnitaryR132 (kernelsL_refl)

theorem ambient_kernels (J : H →ₗᵢ[ℂ] L2T L) (K : Kernels H) :
    kernelsL (UI L) (kernelsI J K) = extendKernels J K :=
  kernelsL_refl (kernelsI J K)

def AtConstants (J : H →ₗᵢ[ℂ] L2T L) (A : ℝ) (hA : 0 < A) (cA T CAT : ℝ) : Prop :=
  ∀ (K : Kernels H) (M : ℝ), 1 ≤ M →
  ∀ (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1) (P : ℝ), 1 ≤ P →
    (∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ‖SJ J K M A hA.le hK hs u₀ hu₀ t s‖ ≤ P) →
  ∀ N : ℕ, 1 ≤ N → cA * Qpar A T M P ≤ N →
    Bounds K hs u₀ (profJ J K M A hA.le hK hs u₀ hu₀)
      (fun v x => WJ J v x) (vacJ J) (QFJ J) A T M P CAT N

section Transfer

variable (J : H →ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A)
    (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1)
local notation "B" => kernelsL (UI L) (kernelsI J K)
local notation "hKJ'" => hKJ J K M A hK
local notation "hsJ'" => hsJ J K hs
local notation "bnd" => BL_bound (UI L) (kernelsI J K) M A hKJ'
local notation "sa" => BL_selfAdj (UI L) (kernelsI J K) hsJ'
local notation "uL0" => sphL (UI L) (J u₀) (hJu J u₀ hu₀)
local notation "uL" => profile (positiveExtension B) M A hA.le bnd sa uL0
local notation "u" => profJ J K M A hA.le hK hs u₀ hu₀
local notation "ξ" => VJ J K M A hM hA hK hs u₀ hu₀
local notation "z" => fluctuation (positiveExtension B) M A (zero_le_one.trans hM) hA.le bnd sa uL0

/-- The actual R131 witness compresses along the finite-dimensional
embedding. The identity also proves invariance for this vacuum. -/
theorem embedded_fluctuation (t : ℝ) :
    fockMapI J (ξ t 0 (vacJ J)) = z t := by
  rw [VJ, gam_compress, gam_vacJ]
  exact (fluctuation_eq (BL (UI L) (kernelsI J K)) M A (zero_le_one.trans hM)
    hA.le bnd sa uL0 t).symm

theorem embedded_profile (t : ℝ) : J (u t) = uL t :=
  J_profJ J K M A hA.le hK hs u₀ hu₀ t

theorem embedded_variational (T P : ℝ) (hP : 1 ≤ P)
    (hS : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ‖SJ J K M A hA.le hK hs u₀ hu₀ t s‖ ≤ P)
    (s t : ℝ) (hsT : |s| ≤ T) (htT : |t| ≤ T) :
    ‖fderiv ℝ (classicalFlow (positiveExtension B) M A hA.le bnd sa (t-s)) (uL s)‖ ≤ P :=
  norm_S'_le J K M A hA.le hK hs u₀ hu₀ T P hP t s (hS s t hsT htT)

end Transfer

/-- Compression of all three estimates, including the unchanged preparation
error. The constants are inherited from the physical proof. -/
theorem transfer_at_constants (J : H →ₗᵢ[ℂ] L2T L)
    (A : ℝ) (hA : 0 < A) (cA T CAT C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hcut : 256 * Real.exp 1 * A ≤ cA) (hCAT : T * C ≤ CAT)
    (hTorus : TorusAtConstants (L := L) A hA cA T CAT)
    (hPair : Prop021AssemblyR131.Prop022PairFamily (L := L))
    (hRem : RemainderEstimate (L := L) A C) :
    AtConstants J A hA cA T CAT := by
  intro K M hM hK hs u₀ hu₀ P hP hS N hN hNQ
  let B := kernelsL (UI L) (kernelsI J K)
  have hB : KBound B M A := fun i =>
    (norm_conjSym_le (UI L) (i+1) (kernelsI J K i)).trans (hKJ J K M A hK i)
  have hsB : KSelfAdj B :=
    fun i => conjSym_adjoint (UI L) (i+1) (kernelsI J K i) (hsJ J K hs i)
  let u₀L := sphL (UI L) (J u₀) (hJu J u₀ hu₀)
  let uL := profile (positiveExtension B) M A hA.le (positiveExtension_bound B M A hB)
    (positiveExtension_selfAdjoint B hsB) u₀L
  let u := profJ J K M A hA.le hK hs u₀ hu₀
  let ξ := fun t => VJ J K M A hM hA hK hs u₀ hu₀ t 0 (vacJ J)
  let z := fluctuation (positiveExtension B) M A (zero_le_one.trans hM) hA.le
    (positiveExtension_bound B M A hB) (positiveExtension_selfAdjoint B hsB) u₀L
  let θ := Prop021PhaseR130.theta (positiveExtension B) M A hA.le
    (positiveExtension_bound B M A hB) (positiveExtension_selfAdjoint B hsB) u₀L N
  have hu (t : ℝ) : J (u t) = uL t :=
    embedded_profile J K M A hA hK hs u₀ hu₀ t
  have hξ (t : ℝ) : fockMapI J (ξ t) = z t :=
    embedded_fluctuation J K M A hM hA hK hs u₀ hu₀ t
  have hSL := embedded_variational J K M A hA hK hs u₀ hu₀ T P hP hS
  have hM₀ : 0 ≤ M := zero_le_one.trans hM
  have hQ : 0 ≤ Qpar A T M P :=
    zero_le_one.trans (Prop021RatesR128.one_le_numberParameter
      (Prop022FactorialMajorantR115.pairMajorant A) T M P)
  have hNlarge : 256 * Real.exp 1 * A * Qpar A T M P ≤ N :=
    (mul_le_mul_of_nonneg_right hcut hQ).trans hNQ
  have hCanon := canonical_torus B A M hA hM hB hsB u₀L T P hT.le hP
    (hPair A M hA hM B hB hsB u₀L T P hP) hSL C hC hRem N hNlarge
  have hC' : CoherentWitness B hsB (J u₀) (fun t => J (u t))
      (fun v x => printedWeyl v x) vac PhysicalQuasifreeSource A T M P (T*C) N θ
      (fun t => fockMapI J (ξ t)) := by
    have huf : (fun t => J (u t)) = uL := funext hu
    have hξf : (fun t => fockMapI J (ξ t)) = z := funext hξ
    rw [huf, hξf]
    exact hCanon
  have hW : ∀ v x, fockMapI J (WJ J v x) = printedWeyl (J v) (fockMapI J x) :=
    fun v x => gam_compress J _ _ x
  have hB' : B = extendKernels J K := ambient_kernels J K
  have hBody (t : ℝ) (x : Fock L) : manyBodyEvolution B hsB N t x =
      manyBodyEvolution (extendKernels J K) (extendKernels_selfAdj J K hs) N t x := by
    apply lp.ext
    funext n
    change sectorEvolution B N n t (x n) = sectorEvolution (extendKernels J K) N n t (x n)
    rw [hB']
  have hC'' : CoherentWitness (extendKernels J K) (extendKernels_selfAdj J K hs)
      (J u₀) (fun t => J (u t)) (fun v x => printedWeyl v x) vac PhysicalQuasifreeSource
      A T M P (T*C) N θ (fun t => fockMapI J (ξ t)) := by
    obtain ⟨h0,hn,he,hd⟩ := hC'
    exact ⟨h0,hn,fun t ht => by simpa only [hBody] using he t ht,hd⟩
  obtain ⟨h0,hn,he,hd⟩ := restrict_coherent J K hs u₀ u (fun v x => WJ J v x) (vacJ J)
    hW (gam_vacJ J) A T M P (T*C) N θ ξ hC''
  obtain ⟨-,hmarg,hprep⟩ := hTorus B M hM hB hsB u₀L P hP hSL N hN hNQ
  refine ⟨⟨θ,ξ,h0,hn,?_,hd⟩,?_,?_⟩
  · intro t ht
    apply (he t ht).trans
    gcongr
  · intro k hk0 hk t ht
    have h := marginal_transport J K N k hk t (powerH N u₀) (u t)
    rw [← hB', power_transport, hu] at h
    rw [← h]
    exact hmarg k hk0 hk t ht
  · intro k hk0 hk ψ hψ t ht
    have h := marginal_transport J K N k hk t ψ (u t)
    rw [← hB', hu] at h
    rw [← h]
    have hp := hprep k hk0 hk (symMapI J N ψ) (by rw [LinearIsometry.norm_map, hψ]) t ht
    have hnorm : ‖symMapI J N ψ - powerH N (J u₀)‖ = ‖ψ - powerH N u₀‖ := by
      rw [← power_transport J N u₀, ← map_sub, LinearIsometry.norm_map]
    have hsp : (u₀L : L2T L) = J u₀ := rfl
    rw [hsp, hnorm] at hp
    exact hp

end QuantumNLS.Prop021IsometryR132

#print axioms QuantumNLS.Prop021IsometryR132.embedded_fluctuation
#print axioms QuantumNLS.Prop021IsometryR132.embedded_variational
#print axioms QuantumNLS.Prop021IsometryR132.transfer_at_constants

end

/-! General-carrier forms of the two named printed predecessor inputs.
The unitary formulation uses the exact frozen physical coordinates; the
isometric formulation quantifies states and coefficient directions on H. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 150000
open scoped InnerProductSpace ENNReal
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop021ContractsR132
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop022GTensor Prop022AIsoTensor Prop022GClassical Prop022GAntiHS Prop022AFock
open Prop022BIso Prop022BClass1 Prop022BClass2 Prop022BFock1 Prop022BFock2 Prop022BFock3
open Prop022OVacuum Prop022PositiveDataR126 Prop022FactorialMajorantR115
open Prop021ManyBodyTransportR132 Prop021IsometryR132 Prop021MomentsR132
open Prop021UnitaryInputsR132

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

/-- Q7B:lem:pair on the embedded carrier, with the Hilbert–Schmidt norm
evaluated in any Hilbert basis of H. -/
def PairInputIsometry (J : H →ₗᵢ[ℂ] L2T L) {ι : Type*} (e : HilbertBasis ι ℂ H)
    (K : Kernels H) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A)
    (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1) (T P : ℝ) : Prop :=
  let S := SJ J K M A hA.le hK hs u₀ hu₀
  let a := aJ J K M A hA.le hK hs u₀ hu₀
  let b := bJ J K M A hA.le hK hs u₀ hu₀
  let α := alphaJ J K M A hA.le hK hs u₀ hu₀
  let β := betaJ J K M A hA.le hK hs u₀ hu₀
  let V := VJ J K M A hM hA hK hs u₀ hu₀
  (∀ t, CLinear (a t) ∧ (∀ x y, ⟪x, a t y⟫_ℂ = ⟪a t x, y⟫_ℂ) ∧
    Antilinear (b t) ∧ (∀ x y, ⟪x, b t y⟫_ℂ = ⟪y, b t x⟫_ℂ) ∧
    antiHS e (b t) ≠ ⊤ ∧ Real.sqrt ((antiHS e (b t)).toReal) ≤ pairMajorant A * M ∧
    ‖a t‖ ≤ M * ∑' r : ℕ, (((r+1 : ℕ) : ℝ)^2 * A^(r+1) /
      Real.sqrt ((2*(r+1)).factorial : ℝ))) ∧
  (∀ s t x, Complex.I • deriv (fun r => S r s x) t = a t (S t s x) + b t (S t s x)) ∧
  (∀ s t, S t s = α t s + β t s ∧ CLinear (α t s) ∧ Antilinear (β t s)) ∧
  ((∀ s t, |s| ≤ T → |t| ≤ T → ‖S t s‖ ≤ P) → ∀ t, |t| ≤ T →
    antiHS e (β t 0) ≠ ⊤ ∧ Real.sqrt ((antiHS e (β t 0)).toReal) ≤ |t| * pairMajorant A * M * P) ∧
  (∀ s x, V s s x = x) ∧
  (∀ r s t x, V t s (V s r x) = V t r x) ∧
  (∀ s x, Continuous (fun t => V t s x)) ∧
  (∀ s t (x : FockSpace H), (∀ j : ℕ, x ∈ momentDomainH j) →
    HasDerivAt (fun r => V r s x) ((-Complex.I) •
      QJ J (aSymJ J K M A hA hK hs u₀ hu₀ t) (bSymJ J K M A hA hK hs u₀ hu₀ t) (V t s x)) t) ∧
  (∀ s t (v : H) (x : FockSpace H), V t s (WJ J v ((V t s).symm x)) = WJ J (S t s v) x) ∧
  (∀ t, QFJ J (V t 0 (vacJ J)) ∧ ‖V t 0 (vacJ J)‖ = 1 ∧
    numExpH (V t 0 (vacJ J)) = antiHS e (β t 0))

/-- The exact pair input for every separable carrier. Unitary charts transport
the frozen physical predicate and finite embeddings use the intrinsic data. -/
def Prop022PairInput : Prop :=
  UnitaryPairInput (L := L) ∧
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H], FiniteDimensional ℂ H →
  ∀ (A M : ℝ) (hA : 0 < A) (hM : 1 ≤ M) (K : Kernels H) (hK : KBound K M A)
    (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1) (T P : ℝ) (_hP : 1 ≤ P)
    (J : H →ₗᵢ[ℂ] L2T L),
    PairInputIsometry J (TraceClass.refBasis H) K M A hM hA hK hs u₀ hu₀ T P

theorem pair_torus (h : Prop022PairInput (L := L)) :
    Prop021AssemblyR131.Prop022PairFamily (L := L) :=
  (unitaryPair_iff_torus (L := L)).mp h.1

/-- The three lower orders of the shifted Hamiltonian, as vectors on H. -/
def lowOrders (J : H →ₗᵢ[ℂ] L2T L) (K : Kernels H) (N : ℕ) (u : H)
    (Q : ℝ) (x : FockSpace H) (hm : NumberMoments Q x) : FockSpace H :=
  let h := (numberMoments_torus Q (fockMapI J x)).mp ((numberMoments_transport J Q x).mpr hm)
  let hs := Prop021RemainderInputR131.smooth_of_numberMoments Q (fockMapI J x) h
  let h₂ := (Prop021DisplacementR129.common_domain (fockMapI J x)).mp hs 2
  Prop022BFock1.gamAdj J (Prop021RemainderInputR131.lowOrders
    (positiveExtension (extendKernels J K)) N (J u) (fockMapI J x) hs h₂)

/-- The finite-dimensional form of Q7B:lem:remainder, with the actual maximal
Hamiltonian, displaced domain, Hilbert-norm action, and remainder constant. -/
def RemainderEstimateIsometry (J : H →ₗᵢ[ℂ] L2T L) (A CA' : ℝ) : Prop :=
  ∀ (K : Kernels H) (M : ℝ), 1 ≤ M → KBound K M A → KSelfAdj K →
  ∀ (N : ℕ) (Q : ℝ), 1 ≤ Q → 256 * Real.exp 1 * A * Q ≤ N →
  ∀ (u : H), ‖u‖ = 1 → ∀ (x : FockSpace H) (hm : NumberMoments Q x),
    ∃ (hd : HamiltonianDomain K N (WJ J ((Real.sqrt N : ℂ) • u) x)) (R : FockSpace H),
      hamiltonian K N (WJ J ((Real.sqrt N : ℂ) • u) x) hd =
        WJ J ((Real.sqrt N : ℂ) • u) (lowOrders J K N u Q x hm + R) ∧
      ‖R‖ ≤ CA' * M * (N : ℝ)^(-(1/2 : ℝ)) * Q^(3/2 : ℝ)

/-- One constant depending on A, for all carriers. -/
def Prop024RemainderInput : Prop :=
  ∀ A : ℝ, 0 < A → ∃ CA' : ℝ, 0 ≤ CA' ∧ UnitaryRemainderInput (L := L) A CA' ∧
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      [TopologicalSpace.SeparableSpace H], FiniteDimensional ℂ H →
    ∀ J : H →ₗᵢ[ℂ] L2T L, RemainderEstimateIsometry J A CA'

/-- Restrict the universally quantified remainder to the torus. -/
theorem remainder_torus (h : Prop024RemainderInput (L := L)) :
    Prop021RemainderInputR131.Prop024RemainderInput (L := L) := by
  intro A hA
  obtain ⟨C,hC,hu,_⟩ := h A hA
  exact ⟨C,hC,(unitaryRemainder_iff_torus (L := L) A C).mp hu⟩

end QuantumNLS.Prop021ContractsR132

#print axioms QuantumNLS.Prop021ContractsR132.pair_torus
#print axioms QuantumNLS.Prop021ContractsR132.remainder_torus

end

/-! Q7B:thm:main for all complex separable Hilbert spaces. The same constants
work on every carrier, with no dimension or codimension restriction.
The only named inputs are the generalized printed PROP-022 and PROP-024. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 150000
open scoped InnerProductSpace ENNReal
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop021GeneralR132
open PhysicalTensor Prop022GClassical Prop022GHilbert Prop022BExist
open Prop021StatementR132 Prop021ContractsR132 Prop025OInputs
open Prop022FactorialMajorantR115 Prop021RatesR128

variable {L : ℝ} [Fact (0 < L)]

/-- Constants are fixed before the carrier, kernels, initial datum and
particle numbers are chosen. Both choices of realization are quantified. -/
def Prop021 : Prop :=
  ∀ (A : ℝ) (hA : 0 < A), ∃ cA : ℝ, ∀ T : ℝ, 0 < T → ∃ CAT : ℝ,
  ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H],
    ((¬ FiniteDimensional ℂ H) → Nonempty (H ≃ₗᵢ[ℂ] L2T L) ∧
      ∀ U : H ≃ₗᵢ[ℂ] L2T L, Prop021UnitaryR132.AtConstants U A hA cA T CAT) ∧
    (FiniteDimensional ℂ H → Nonempty (H →ₗᵢ[ℂ] L2T L) ∧
      ∀ J : H →ₗᵢ[ℂ] L2T L, Prop021IsometryR132.AtConstants J A hA cA T CAT)

private lemma torus_monotone (A : ℝ) (hA : 0 < A) (c₁ c₂ T C₁ C₂ : ℝ)
    (hc : c₁ ≤ c₂) (hC : C₁ ≤ C₂)
    (h : TorusAtConstants (L := L) A hA c₁ T C₁) :
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

/-- The general printed theorem with the two exact named inputs. -/
theorem prop021 (hPair : Prop022PairInput (L := L)) (hRem : Prop024RemainderInput (L := L)) :
    Prop021 (L := L) := by
  have hPairL := pair_torus hPair
  have hRemL := remainder_torus hRem
  have hTorus := (torus_statement (L := L)).mpr (Prop021AssemblyR131.prop021 hPairL hRemL)
  intro A hA
  obtain ⟨cA,hcA⟩ := hTorus A hA
  obtain ⟨C,hC,hRemA⟩ := hRemL A hA
  let cutoff := 256 * Real.exp 1 * A
  refine ⟨max cA cutoff, fun T hT => ?_⟩
  obtain ⟨CAT,hCAT⟩ := hcA T hT
  let estimate := max CAT (T*C)
  have h : TorusAtConstants (L := L) A hA (max cA cutoff) T estimate :=
    torus_monotone A hA cA (max cA cutoff) T CAT estimate
      (le_max_left cA cutoff) (le_max_left CAT (T*C)) hCAT
  refine ⟨estimate, fun H _ _ _ _ => ⟨?_,?_⟩⟩
  · intro hH
    exact ⟨exists_unitary_L2T L hH, fun U =>
      Prop021UnitaryR132.transfer_at_constants U A hA (max cA cutoff) T estimate h⟩
  · intro hH
    refine ⟨exists_isometry_fin hH L, fun J => ?_⟩
    exact Prop021IsometryR132.transfer_at_constants J A hA (max cA cutoff) T estimate C hT hC
      (le_max_right cA cutoff) (le_max_right CAT (T*C)) h hPairL hRemA

/-- Specialize through the identity unitary and recover the exact
frozen torus theorem used by PROP-025. -/
theorem specialize_torus (h : Prop021.{0} (L := L)) : Prop025OInputs.Prop021Input (L := L) := by
  have hSep := Prop022BExist.sep (L := L)
  apply (torus_statement (L := L)).mp
  intro A hA
  obtain ⟨cA,hcA⟩ := h A hA
  refine ⟨cA,fun T hT => ?_⟩
  obtain ⟨CAT,hCAT⟩ := hcA T hT
  have hL := @hCAT (L2T L) inferInstance inferInstance inferInstance hSep
  exact ⟨CAT, (Prop021UnitaryR132.torus_refl A hA cA T CAT).mp
    ((hL.1 (L2T_not_finiteDimensional L)).2 (Prop021UnitaryR132.torusId L))⟩

end QuantumNLS.Prop021GeneralR132

namespace QuantumNLS.Prop021GeneralR132
open PhysicalTensor
open Prop022BClass1 Prop022BClass3 Prop022BFock2 Prop022BIndep
open Prop022GClassical

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

/-- Two finite-dimensional embeddings yield the same classical data,
Weyl action, vacuum and normalized quadratic fluctuation. -/
theorem finite_data_indep (hH : FiniteDimensional ℂ H) (J J' : H →ₗᵢ[ℂ] L2T L)
    (K : Kernels H) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A) (hK : KBound K M A)
    (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1) :
    profJ J' K M A hA.le hK hs u₀ hu₀ = profJ J K M A hA.le hK hs u₀ hu₀ ∧
    (∀ t s, SJ J' K M A hA.le hK hs u₀ hu₀ t s = SJ J K M A hA.le hK hs u₀ hu₀ t s) ∧
    (∀ v, WJ J' v = WJ J v) ∧ vacJ J' = vacJ J ∧
    (∀ t, VJ J' K M A hM hA hK hs u₀ hu₀ t 0 (vacJ J') =
      VJ J K M A hM hA hK hs u₀ hu₀ t 0 (vacJ J)) ∧
    (∀ t, QFJ J' (VJ J K M A hM hA hK hs u₀ hu₀ t 0 (vacJ J))) := by
  obtain ⟨R,hR⟩ := Prop022BExist.exists_unitary_fixing hH J J'
  have hW := WJ_indep J J' R hR
  have hΩ := vacJ_indep J J' R hR
  have hV := VJ_indep J J' R hR K M A hM hA hK hs u₀ hu₀
  refine ⟨profJ_indep J J' K M A hA.le hK hs u₀ hu₀, ?_, hW, hΩ, ?_, ?_⟩
  · intro t s
    exact SJ_indep J J' K M A hA.le hK hs u₀ hu₀ t s
  · intro t
    rw [hV t 0, hΩ]
  · intro t
    exact QFJ_indep J J' R hR K M A hM hA hK hs u₀ hu₀ t

open TensorCarrier PhysicalTensor TraceClass
open Prop021ManyBodyTransportR132 Prop021StatementR132 LinearTailPhysicalEvolution

/-- The optional cap at two for the exact evolved particle state in PROP-021. -/
theorem cap_marginal (K : Kernels H) (hs : KSelfAdj K) (N k : ℕ) (hk : k ≤ N)
    (t : ℝ) (u₀ u : H) (h₀ : ‖u₀‖ = 1) (hu : ‖u‖ = 1) (b : ℝ≥0∞)
    (hb : traceNorm (reducedDensityN N k hk (sectorEvolution K N N t (powerH N u₀)).val -
      InnerProductSpace.rankOne ℂ (htpow k u) (htpow k u)) ≤ b) :
    traceNorm (reducedDensityN N k hk (sectorEvolution K N N t (powerH N u₀)).val -
      InnerProductSpace.rankOne ℂ (htpow k u) (htpow k u)) ≤ min b 2 := by
  have hi : ‖powerH N u₀‖ = 1 := by
    change ‖(htpow N u₀ : HilbertTensorPower ℂ H N)‖ = 1
    rw [norm_htpow,h₀,one_pow]
  have hsN : IsSelfAdjoint (sector K N N) := sector_adjoint K hs N N
  have hf : ‖(sectorEvolution K N N t (powerH N u₀)).val‖ = 1 :=
    (evolution_norm hsN t (powerH N u₀)).trans hi
  exact le_min hb (marginal_cap N k hk u hu _ hf)

end QuantumNLS.Prop021GeneralR132

#print axioms QuantumNLS.Prop021GeneralR132.prop021
#print axioms QuantumNLS.Prop021GeneralR132.specialize_torus
#print axioms QuantumNLS.Prop021GeneralR132.finite_data_indep
#print axioms QuantumNLS.Prop021GeneralR132.cap_marginal

end

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let modules := ["Prop021GeneralR132", "Prop021IsometryR132", "Prop021ContractsR132"]
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if modules.any (fun m => n.toString.startsWith ("QuantumNLS." ++ m ++ ".") ||
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
  Lean.logInfo m!"R132 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
