import QuantumNLS.Prop021GeneralR132
import QuantumNLS.Prop022BPairInput

/-! Existential PROP-022 and the fixed physical implementation used in
PROP-021. The comparison uses Weyl phase uniqueness only. The initial
condition, composition and strong equation of the fixed implementation
come from its own construction. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5500000
set_option synthInstance.maxHeartbeats 150000
open scoped InnerProductSpace ENNReal
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop021PairR133
open PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Ext005Moments Ext006KernelHilbertSchmidt Ext006PhysFockCoord Ext006PhysQuasifree
open Ext006SourceWeylR44a Ext006NaturalWeylR44a Ext006NumberPhase
open Prop022PositiveDataR126 Prop022FactorialCoefficientsR115 Prop022FactorialMajorantR115
open Prop022ActualProfileR117 Prop022ClassicalFlowR126 Prop022FlowDifferentialR126
open Prop022FockPropagatorR122 Prop022VariationalR123 Prop022PrintedCoefficientsR124
open Prop022PairHSR122 Prop022OCovariance Prop022OClassical Prop022OVacuum Prop022OQuadraticKet Prop022OWeakIdentity
open Prop022GClassical

variable {L : ℝ} [Fact (0 < L)]
variable (K : Kernels (L2T L)) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A)
  (hK : ∀ n, ‖K n‖ ≤ M * A^(n+1) / Real.sqrt ((2*(n+1)).factorial : ℝ))
  (hsK : ∀ n, (K n).adjoint = K n) (u₀ : Prop001.Sphere (L2T L)) (T P : ℝ)

local notation "B" => positiveExtension K
local notation "hB" => positiveExtension_bound K M A hK
local notation "hs" => positiveExtension_selfAdjoint K hsK
local notation "u" => profile B M A hA.le hB hs u₀
local notation "a" => fun t => numberOperator B (u t)
local notation "b" => fun t => pairKernel B (u t)
local notation "S" => fun t s => fderiv ℝ (classicalFlow B M A hA.le hB hs (t-s)) (u s)
local notation "β" => betaBlock B M A hA.le hB hs u₀
local notation "hb²" => fun t => TraceClass.hsSq (physicalBasis L) (β t 0)
local notation "V" => fun t s => propagator B M A (zero_le_one.trans hM) hA.le hB hs u₀ s t
local notation "Adv" => fun t s => flow B M A hA.le hB hs u₀ t s
local notation "quad" => fun t x => Qp (numberCoefficient B (u t)) (pairCoefficient B (u t)) x

/-- The printed bounds and existence of a unitary propagator of the
printed quadratic Hamiltonian. The evolution equation is tested in
matrix elements on the common number-moment core. The beta bound is
written with its standing interval bound as an implication. -/
def PrintedPair : Prop :=
  (∀ t, TraceClass.hsSq (physicalBasis L) (b t) ≠ ⊤ ∧
    Real.sqrt ((TraceClass.hsSq (physicalBasis L) (b t)).toReal) ≤ pairMajorant A * M ∧
    ‖a t‖ ≤ M * ∑' r : ℕ, (((r+1 : ℕ) : ℝ)^2 * A^(r+1) / Real.sqrt ((2*(r+1)).factorial : ℝ))) ∧
  ((∀ s t, |s| ≤ T → |t| ≤ T → ‖S t s‖ ≤ P) → ∀ t, |t| ≤ T →
    hb² t ≠ ⊤ ∧ Real.sqrt (hb² t).toReal ≤ |t| * pairMajorant A * M * P) ∧
  ∃ U : ℝ → ℝ → Fock L ≃ₗᵢ[ℂ] Fock L,
    (∀ s x, U s s x = x) ∧
    (∀ r s t x, U t s (U s r x) = U t r x) ∧
    (∀ s x, Continuous (fun t => U t s x)) ∧
    (∀ s t (x y : Fock L), (∀ j : ℕ, x ∈ momentDomain (L := L) j) →
      y ∈ momentDomain (L := L) 2 →
      HasDerivAt (fun r => ⟪y, U r s x⟫_ℂ) ((-Complex.I) * ⟪quad t y, U t s x⟫_ℂ) t) ∧
    (∀ s t v x, U t s (printedWeyl v ((U t s).symm x)) = printedWeyl (S t s v) x) ∧
    (∀ t, PhysicalQuasifreeSource (U t 0 vac) ∧
      numberExpectation (fun n => (n : ℝ≥0∞)) (U t 0 vac) = hb² t)

private theorem quasifree_phase {x : Fock L} (hx : PhysicalQuasifreeSource x)
    (z : ℂ) (hz : ‖z‖ = 1) : PhysicalQuasifreeSource (z • x) := by
  obtain ⟨U,a₀,b₀,hSym,hAnn,hCre,hx⟩ := hx
  exact ⟨phaseUnitary U z hz,a₀,b₀,hSym,heisAnn_phase U a₀ b₀ hAnn z hz,
    heisCre_phase U a₀ b₀ hCre z hz, by rw [hx, phaseUnitary_apply]⟩

/-- The stronger fixed-implementation predicate yields an existential
witness and its weak equation. -/
theorem printed_of_fixed (hP : 1 ≤ P)
    (h : Prop024WeylConventionR55.Prop022PairInput K M A hM hA hK hsK u₀ T P hP) :
    PrintedPair K M A hA hK hsK u₀ T P := by
  dsimp only [Prop024WeylConventionR55.Prop022PairInput] at h
  rcases h with ⟨hc,_,_,_,hβ,h0,hcomp,hcont,hder,himpl,hvac⟩
  refine ⟨fun t => (hc t).2.2, fun hS => hβ (fun r q hr hq => hS q r hq hr),
    V,h0,hcomp,hcont,?_,himpl,fun t => ⟨(hvac t).1,(hvac t).2.2⟩⟩
  intro s t x y hx hy
  have hdy := (hasDerivAt_const t y).inner ℂ (hder s t x hx)
  have hh : (V t s) x ∈ momentDomain (L := L) 2 := by
    apply (Prop022SmoothDomainR126.smooth_iff_moments _).mp _ 2
    exact (Prop022SmoothDomainR126.evolution_smooth_iff B M A (zero_le_one.trans hM)
      hA.le hB hs u₀ s t x).mpr ((Prop022SmoothDomainR126.smooth_iff_moments x).mpr hx)
  rw [Qp_symm _ (numberCoefficient_adjoint B hs (u t)) _ _ _ hy hh]
  simpa only [inner_zero_left, add_zero, inner_smul_right, Qp] using hdy

/-- The existential witness may have its own phase. Weyl uniqueness
transfers exactly its quasifree and number conclusions to the canonical
Hamiltonian solution. -/
theorem fixed_of_printed (hP : 1 ≤ P) (h : PrintedPair K M A hA hK hsK u₀ T P) :
    Prop024WeylConventionR55.Prop022PairInput K M A hM hA hK hsK u₀ T P hP := by
  obtain ⟨hc,hβ,U,_,_,_,_,himpl,hvac⟩ := h
  dsimp only [Prop024WeylConventionR55.Prop022PairInput]
  have hS (s t : ℝ) : S t s = (Adv t s).toContinuousLinearMap :=
    (flow_eq_fderiv B M A hA.le hB hs u₀ s t).symm
  have hV (s t : ℝ) : SourceWeylImplementer (Sp B M A hA.le hB hs u₀ t s) (V t s) :=
    propagator_implements B M A (zero_le_one.trans hM) hA.le hB hs u₀ s t
  refine ⟨fun t => ⟨numberOperator_adjoint B hs (u t), pairKernel_symmetric B (u t), hc t⟩,
    hS, ?_, ?_, fun hst => hβ (fun s t hsT htT => hst t s htT hsT),
    fun s x => evolution_self B M A (zero_le_one.trans hM) hA.le hB hs u₀ s x,
    fun r s t x => evolution_comp B M A (zero_le_one.trans hM) hA.le hB hs u₀ r s t x,
    fun s x => evolution_continuous B M A (zero_le_one.trans hM) hA.le hB hs u₀ s x,
    fun s t x hx => Prop022SmoothDomainR126.evolution_smooth_hasDerivAt B M A
      (zero_le_one.trans hM) hA.le hB hs u₀ s t x
      ((Prop022SmoothDomainR126.smooth_iff_moments x).mpr hx), ?_, ?_⟩
  · intro s t x
    have happ (r : ℝ) : S r s x = Adv r s x := DFunLike.congr_fun (hS s r) x
    have hf : (fun r => S r s x) = fun r => Adv r s x := funext happ
    calc
      Complex.I • deriv (fun r => S r s x) t =
          Complex.I • deriv (fun r => Adv r s x) t :=
        congrArg (fun f : ℝ → L2T L => Complex.I • deriv f t) hf
      _ = a t (Adv t s x) + b t (conjugation (physicalBasis L) (Adv t s x)) :=
        flow_printed_linearized B M A hA.le hB hs u₀ s t x
      _ = a t (S t s x) + b t (conjugation (physicalBasis L) (S t s x)) :=
        congrArg (fun y => a t y + b t (conjugation (physicalBasis L) y)) (happ t).symm
  · intro s t x
    exact (DFunLike.congr_fun (hS s t) x).trans (flow_blocks B M A hA.le hB hs u₀ t s x)
  · intro s t v x
    exact (printed_of_source _ _ (hV s t) (Adv t s) (Sp_negI B M A hA.le hB hs u₀ t s) v x).trans
      (congrArg (fun w => printedWeyl w x) (DFunLike.congr_fun (hS s t) v).symm)
  · intro t
    have hU : SourceWeylImplementer (Sp B M A hA.le hB hs u₀ t 0) (U t 0) := by
      intro f x
      let v := Complex.I • f
      have hf : (-Complex.I) • v = f := by
        dsimp [v]
        rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
      have hsp : Sp B M A hA.le hB hs u₀ t 0 f = (-Complex.I) • S t 0 v :=
        (congrArg (fun w => Sp B M A hA.le hB hs u₀ t 0 w) hf.symm).trans
          ((Sp_negI B M A hA.le hB hs u₀ t 0 v).trans
            (congrArg (fun w => (-Complex.I) • w) (DFunLike.congr_fun (hS 0 t) v).symm))
      calc
        U t 0 (sourceWeyl f ((U t 0).symm x)) = sourceWeyl ((-Complex.I) • S t 0 v) x := by
          simpa only [printedWeyl, hf] using himpl 0 t v x
        _ = _ := congrArg (fun w => sourceWeyl w x) hsp.symm
    obtain ⟨z,hz,hzV⟩ := sourceWeyl_unique_phase _ (U t 0) (V t 0) hU (hV 0 t)
    rw [hzV vac, expectedNumber_phase z hz]
    refine ⟨quasifree_phase (hvac t).1 z hz, ?_, (hvac t).2⟩
    rw [norm_smul, hz, one_mul, LinearIsometryEquiv.norm_map]
    rw [vac, physCore_ket, LinearIsometryEquiv.norm_map, lp.norm_single (by norm_num)]
    exact norm_one

/-- The printed predecessor premise used for PROP-021, restricted to the
reference carrier as required by the transfer proof. -/
def PrintedPairFamily : Prop :=
  ∀ (A M : ℝ) (_hA : 0 < A) (_hM : 1 ≤ M) (K : Kernels (L2T L))
    (hK : ∀ n, ‖K n‖ ≤ M * A^(n+1) / Real.sqrt ((2*(n+1)).factorial : ℝ))
  (hsK : ∀ n, (K n).adjoint = K n) (u₀ : Prop001.Sphere (L2T L)) (T P : ℝ)
    (_hP : 1 ≤ P), PrintedPair K M A _hA hK hsK u₀ T P

/-- Pointwise equivalence lifted to the precise family consumed by the
frozen torus proof. -/
theorem printed_iff_fixed :
    PrintedPairFamily (L := L) ↔ Prop021AssemblyR131.Prop022PairFamily (L := L) :=
  ⟨fun h A M hA hM K hK hsa₀ u₀ T P hP =>
    fixed_of_printed K M A hM hA hK hsa₀ u₀ T P hP (h A M hA hM K hK hsa₀ u₀ T P hP),
   fun h A M hA hM K hK hsa₀ u₀ T P hP =>
    printed_of_fixed K M A hM hA hK hsa₀ u₀ T P hP (h A M hA hM K hK hsa₀ u₀ T P hP)⟩

end QuantumNLS.Prop021PairR133
