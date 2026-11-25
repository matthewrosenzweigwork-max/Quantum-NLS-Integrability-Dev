import Mathlib
import QuantumNLS.Prop022BFock2

/-! PROP-022 route A, finite-dimensional case, stage B4b: support of the physical coefficient data in
`Sym(range J)` and the printed Fock-side conclusions 4-6 through `J`.

* `aSym_support`: `P₁ a' P₁ = a'` with `P₁ = Γ₁(J) Γ₁(J)*` (power-vector test, using the classical
  structure `numberOperator = J a_J J*`);
* `bSym_support`: `Γ₂(J) Γ₂(J)* b' = b'` (the pair coefficient is fixed by every rotation fixing `range J`,
  frozen `pairCoefficient_cov`, then `sector_mem_range`);
* `PROP022_fock_J`: unitarity/cocycle/continuity, the strong Schrödinger equation on the common moment
  domain, the implementation `V W_J(v) V⁻¹ = W_J(S_J v)`, and the pure quasifree vacuum with the number
  identity `⟨ξ, N ξ⟩ = ‖β_J(t,0)‖²_HS`. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
open scoped InnerProductSpace Topology NNReal ENNReal
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop022BFock3
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop022GTensor Prop022AIsoTensor Prop022GAntiHS Prop022GClassical Prop022GLinear
open Prop022BIso Prop022BClass1 Prop022BClass2 Prop022BFock1 Prop022BFock2
open Prop022FactorialCoefficientsR115 Prop022ActualProfileR117 Prop022FockPropagatorR122
open Prop022PositiveDataR126 Prop022AFock Prop022ACovIndep Prop022AWeyl Prop022OVacuum
open Ext006PhysFockCoord Ext006PhysQuasifree Prop022TensorCompressionR115 Prop022VariationalR123 Prop022PairHSR122
open Prop022PrintedCoefficientsR124 Prop022ACoherent Prop022ACovPhys Prop022AIndep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

section Data
variable (J : H →ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A)
  (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1)

lemma P1_power (n : ℕ) (y : L2T L) :
    symI J n (symAdj J n (powerH n y)) = powerH n (J (Jadj J y)) := by
  rw [symAdj_power, symI_power]

lemma P1_adj (n : ℕ) (a b : SymSector ℂ (L2T L) n) :
    ⟪symI J n (symAdj J n a), b⟫_ℂ = ⟪a, symI J n (symAdj J n b)⟫_ℂ := by
  rw [← inner_symAdj_right, inner_symAdj_left]

include hM

local notation "Bp" => BL (UI L) (kernelsI J K)
local notation "up" t => profile (BL (UI L) (kernelsI J K)) M A hA.le
  (BL_bound (UI L) (kernelsI J K) M A (hKJ J K M A hK))
  (BL_selfAdj (UI L) (kernelsI J K) (hsJ J K hs)) (sphL (UI L) (J u₀) (hJu J u₀ hu₀)) t

/-- The coefficient `a_t ∈ B(Sym¹ H)` through `J`. -/
def aSymJ (t : ℝ) : SymSector ℂ H 1 →L[ℂ] SymSector ℂ H 1 :=
  symAdj J 1 ∘L numberCoefficient (BL (UI L) (kernelsI J K))
    (profile (BL (UI L) (kernelsI J K)) M A hA.le
      (BL_bound (UI L) (kernelsI J K) M A (hKJ J K M A hK))
      (BL_selfAdj (UI L) (kernelsI J K) (hsJ J K hs)) (sphL (UI L) (J u₀) (hJu J u₀ hu₀)) t)
    ∘L symI J 1

/-- The coefficient `b_t ∈ Sym² H` through `J`. -/
def bSymJ (t : ℝ) : SymSector ℂ H 2 :=
  symAdj J 2 (pairCoefficient (BL (UI L) (kernelsI J K))
    (profile (BL (UI L) (kernelsI J K)) M A hA.le
      (BL_bound (UI L) (kernelsI J K) M A (hKJ J K M A hK))
      (BL_selfAdj (UI L) (kernelsI J K) (hsJ J K hs)) (sphL (UI L) (J u₀) (hJu J u₀ hu₀)) t))

lemma hprof (t : ℝ) : (up t) = J (profJ J K M A hA.le hK hs u₀ hu₀ t) :=
  (J_profJ J K M A hA.le hK hs u₀ hu₀ t).symm

lemma numberOperator_eq (t : ℝ) (z : L2T L) :
    numberOperator Bp (up t) z = J (aJ J K M A hA.le hK hs u₀ hu₀ t (Jadj J z)) := by
  have h := congrArg (fun T : L2T L →L[ℝ] L2T L => T z)
    ((aH_eq (UI L) (kernelsI J K) M A hA.le (hKJ J K M A hK) (hsJ J K hs) (J u₀)
      (hJu J u₀ hu₀) t).symm.trans (aH'_eq J K M A hA.le hK hs u₀ hu₀ t))
  exact h

/-- **Support of `a_t`**: `P₁ a' P₁ = a'`. -/
theorem aSym_support (t : ℝ) :
    ((symI J 1) ∘L (symAdj J 1)) ∘L (numberCoefficient Bp (up t)) ∘L
      ((symI J 1) ∘L (symAdj J 1)) = numberCoefficient Bp (up t) := by
  apply ContinuousLinearMap.ext_on (dense_powers 1)
  rintro _ ⟨y, rfl⟩
  have hz : ∀ g : L2T L, ⟪power 1 g,
      ((symI J 1 ∘L symAdj J 1) ∘L numberCoefficient Bp (up t) ∘L (symI J 1 ∘L symAdj J 1))
        (power 1 y) - numberCoefficient Bp (up t) (power 1 y)⟫_ℂ = 0 := by
    intro g
    rw [inner_sub_right]
    have e1 : ((symI J 1 ∘L symAdj J 1) ∘L numberCoefficient Bp (up t) ∘L
        (symI J 1 ∘L symAdj J 1)) (power 1 y) =
        symI J 1 (symAdj J 1 (numberCoefficient Bp (up t) (powerH 1 (J (Jadj J y))))) := by
      change symI J 1 (symAdj J 1 (numberCoefficient Bp (up t)
        (symI J 1 (symAdj J 1 (powerH 1 y))))) = _
      rw [P1_power]
    have hN1 : ⟪J (Jadj J g), numberOperator Bp (up t) (J (Jadj J y))⟫_ℂ =
        ⟪g, numberOperator Bp (up t) y⟫_ℂ := by
      rw [numberOperator_eq J K M A hM hA hK hs u₀ hu₀ t (J (Jadj J y)),
        numberOperator_eq J K M A hM hA hK hs u₀ hu₀ t y, Jadj_J,
        LinearIsometry.inner_map_map, inner_Jadj_left]
    have hp1 : ⟪powerH 1 (J (Jadj J g)), numberCoefficient Bp (up t) (powerH 1 (J (Jadj J y)))⟫_ℂ =
        ⟪J (Jadj J g), numberOperator Bp (up t) (J (Jadj J y))⟫_ℂ :=
      (numberOperator_pairing Bp (up t) _ _).symm
    have hp2 : ⟪powerH 1 g, numberCoefficient Bp (up t) (powerH 1 y)⟫_ℂ =
        ⟪g, numberOperator Bp (up t) y⟫_ℂ :=
      (numberOperator_pairing Bp (up t) _ _).symm
    rw [e1]
    change ⟪powerH 1 g, symI J 1 (symAdj J 1 (numberCoefficient Bp (up t)
        (powerH 1 (J (Jadj J y)))))⟫_ℂ - ⟪powerH 1 g, numberCoefficient Bp (up t) (powerH 1 y)⟫_ℂ = 0
    rw [← P1_adj J 1 (powerH 1 g), P1_power, hp1, hp2, hN1, sub_self]
  have h0 := powers_total 1 _ hz
  exact sub_eq_zero.mp h0

/-- **Support of `b_t`**: `Γ₂(J) Γ₂(J)* b' = b'`. -/
theorem bSym_support (t : ℝ) :
    symI J 2 (symAdj J 2 (pairCoefficient Bp (up t))) = pairCoefficient Bp (up t) := by
  apply sector_mem_range
  intro z hz
  have hR : Fixes J (rot J z hz) := fun v => rot_fixes J z hz v
  have hB : (fun m => conjSym (rot J z hz) m (BL (UI L) (kernelsI J K) m)) =
      BL (UI L) (kernelsI J K) := funext (BL_fix J K (rot J z hz) hR)
  have hu : (rot J z hz) (up t) = up t := by
    rw [hprof J K M A hM hA hK hs u₀ hu₀ t]
    exact hR _
  rw [Prop022ACovCoef.pairCoefficient_cov (rot J z hz) Bp (up t), hB, hu]

lemma conj_aSymJ (t : ℝ) :
    symI J 1 ∘L aSymJ J K M A hA hK hs u₀ hu₀ t ∘L symAdj J 1 =
      numberCoefficient Bp (up t) := by
  refine Eq.trans ?_ (aSym_support J K M A hM hA hK hs u₀ hu₀ t)
  refine ContinuousLinearMap.ext (fun y => ?_)
  rfl

lemma symI_bSymJ (t : ℝ) :
    symI J 2 (bSymJ J K M A hA hK hs u₀ hu₀ t) = pairCoefficient Bp (up t) :=
  bSym_support J K M A hM hA hK hs u₀ hu₀ t

end Data

lemma gam_mem_moment (J : H →ₗᵢ[ℂ] L2T L) (j : ℕ) (x : FockSpace H) (hx : x ∈ momentDomainH j) :
    fockMapI J x ∈ Ext005Moments.momentDomain (L := L) j := by
  rw [Ext005Moments.momentDomain_iff]
  change Summable (fun n : ℕ => Ext005Moments.momentWeight j n * ‖fockMapI J x n‖ ^ 2)
  simp only [fockMapI_apply, LinearIsometry.norm_map]
  exact hx

section Main
variable (J : H →ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A)
  (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1)

/-- **PROP-022 (Q7B:lem:pair), printed conclusions 4-6, through the isometric embedding `J`.** -/
theorem PROP022_fock_J {ι : Type*} (e : HilbertBasis ι ℂ H) (T P : ℝ) (hP : 1 ≤ P) :
    let V := VJ J K M A hM hA hK hs u₀ hu₀
    (∀ s x, V s s x = x) ∧
    (∀ r s t x, V t s (V s r x) = V t r x) ∧
    (∀ s x, Continuous (fun t => V t s x)) ∧
    (∀ s t (x : FockSpace H), (∀ j : ℕ, x ∈ momentDomainH j) →
      HasDerivAt (fun r => V r s x)
        ((-Complex.I) • QJ J (aSymJ J K M A hA hK hs u₀ hu₀ t)
          (bSymJ J K M A hA hK hs u₀ hu₀ t) (V t s x)) t) ∧
    (∀ s t (v : H) (x : FockSpace H),
      V t s (WJ J v ((V t s).symm x)) =
        WJ J (SJ J K M A hA.le hK hs u₀ hu₀ t s v) x) ∧
    (∀ t, QFJ J (V t 0 (vacJ J)) ∧ ‖V t 0 (vacJ J)‖ = 1 ∧
      numExpH (V t 0 (vacJ J)) = antiHS e (betaJ J K M A hA.le hK hs u₀ hu₀ t 0)) := by
  intro V
  have hK' : ∀ n, ‖kernelsL (UI L) (kernelsI J K) n‖ ≤
      M * A ^ (n + 1) / Real.sqrt ((2 * (n + 1)).factorial : ℝ) :=
    fun n => (norm_conjSym_le (UI L) (n + 1) (kernelsI J K n)).trans (hKJ J K M A hK n)
  have hs' : ∀ n, (kernelsL (UI L) (kernelsI J K) n).adjoint = kernelsL (UI L) (kernelsI J K) n :=
    fun n => conjSym_adjoint (UI L) (n + 1) (kernelsI J K n) (hsJ J K hs n)
  obtain ⟨-, hSeq, -, -, -, hV0, hVc, hVcont, hSchr, hImpl, hVac⟩ :=
    Prop022OMain.PROP022_physical_quadratic_propagator (kernelsL (UI L) (kernelsI J K)) M A hM hA
      hK' hs' (sphL (UI L) (J u₀) (hJu J u₀ hu₀)) T P hP
  have hGV : ∀ t s (z : FockSpace H),
      fockMapI J (V t s z) = Pr J K M A hM hA hK hs u₀ hu₀ s t (fockMapI J z) :=
    fun t s z => gam_compress J _ _ z
  have hVapp : ∀ t s (z : FockSpace H),
      V t s z = gamAdj J (Pr J K M A hM hA hK hs u₀ hu₀ s t (fockMapI J z)) := fun _ _ _ => rfl
  refine ⟨fun s x => ?_, fun r s t x => ?_, fun s x => ?_, fun s t x hx => ?_,
    fun s t v x => ?_, fun t => ?_⟩
  · apply (fockMapI J).injective
    rw [hGV]
    exact hV0 s (fockMapI J x)
  · apply (fockMapI J).injective
    rw [hGV, hGV, hGV]
    exact hVc r s t (fockMapI J x)
  · exact (gamAdj J).continuous.comp (hVcont s (fockMapI J x))
  · have h : HasDerivAt (fun r => Pr J K M A hM hA hK hs u₀ hu₀ s r (fockMapI J x))
        ((-Complex.I) • Prop022StrongOperatorR125.strongCoordinates
          (numberCoefficient (BL (UI L) (kernelsI J K))
            (profile (BL (UI L) (kernelsI J K)) M A hA.le
              (BL_bound (UI L) (kernelsI J K) M A (hKJ J K M A hK))
              (BL_selfAdj (UI L) (kernelsI J K) (hsJ J K hs))
              (sphL (UI L) (J u₀) (hJu J u₀ hu₀)) t))
          (pairCoefficient (BL (UI L) (kernelsI J K))
            (profile (BL (UI L) (kernelsI J K)) M A hA.le
              (BL_bound (UI L) (kernelsI J K) M A (hKJ J K M A hK))
              (BL_selfAdj (UI L) (kernelsI J K) (hsJ J K hs))
              (sphL (UI L) (J u₀) (hJu J u₀ hu₀)) t))
          (Ext005FormCutoffR109.rootLift 2 (Pr J K M A hM hA hK hs u₀ hu₀ s t (fockMapI J x)))) t :=
      hSchr s t (fockMapI J x) (fun j => gam_mem_moment J j x (hx j))
    have hd := ((gamAdj J).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h
    have hq : gamAdj J ((-Complex.I) • Prop022StrongOperatorR125.strongCoordinates
          (numberCoefficient (BL (UI L) (kernelsI J K))
            (profile (BL (UI L) (kernelsI J K)) M A hA.le
              (BL_bound (UI L) (kernelsI J K) M A (hKJ J K M A hK))
              (BL_selfAdj (UI L) (kernelsI J K) (hsJ J K hs))
              (sphL (UI L) (J u₀) (hJu J u₀ hu₀)) t))
          (pairCoefficient (BL (UI L) (kernelsI J K))
            (profile (BL (UI L) (kernelsI J K)) M A hA.le
              (BL_bound (UI L) (kernelsI J K) M A (hKJ J K M A hK))
              (BL_selfAdj (UI L) (kernelsI J K) (hsJ J K hs))
              (sphL (UI L) (J u₀) (hJu J u₀ hu₀)) t))
          (Ext005FormCutoffR109.rootLift 2 (Pr J K M A hM hA hK hs u₀ hu₀ s t (fockMapI J x)))) =
        (-Complex.I) • QJ J (aSymJ J K M A hA hK hs u₀ hu₀ t)
          (bSymJ J K M A hA hK hs u₀ hu₀ t) (V t s x) := by
      rw [map_smul]
      refine congrArg (fun z => (-Complex.I) • z) ?_
      unfold QJ
      rw [conj_aSymJ J K M A hM hA hK hs u₀ hu₀ t, symI_bSymJ J K M A hM hA hK hs u₀ hu₀ t, hGV]
    exact hd.congr_deriv hq
  · apply (fockMapI J).injective
    have e1 := hImpl s t (J v) (fockMapI J x)
    rw [hSeq s t] at e1
    have hS : (flow (BL (UI L) (kernelsI J K)) M A hA.le
        (BL_bound (UI L) (kernelsI J K) M A (hKJ J K M A hK))
        (BL_selfAdj (UI L) (kernelsI J K) (hsJ J K hs)) (sphL (UI L) (J u₀) (hJu J u₀ hu₀)) t s)
        (J v) = J (SJ J K M A hA.le hK hs u₀ hu₀ t s v) := by
      rw [← S_embed J K M A hA.le hK hs u₀ hu₀, SH_apply]
      rfl
    have hW : ∀ w z, fockMapI J (WJ J w z) = printedWeyl (J w) (fockMapI J z) :=
      fun w z => gam_compress J _ _ z
    have hGVsymm : ∀ t s (z : FockSpace H), fockMapI J ((V t s).symm z) =
        (Pr J K M A hM hA hK hs u₀ hu₀ s t).symm (fockMapI J z) :=
      fun t s z => gam_compress_symm J _ _ z
    rw [hGV, hW, hGVsymm, hW, ← hS]
    exact e1
  · have hxi : fockMapI J (V t 0 (vacJ J)) =
        Pr J K M A hM hA hK hs u₀ hu₀ 0 t (vac : Fock L) := by
      rw [hGV, gam_vacJ]
    obtain ⟨hq, hn, hnum'⟩ := hVac t
    have hb0 : antiHS (Ext006KernelHilbertSchmidt.physicalBasis L)
        (betaH (UI L) (kernelsI J K) M A hA.le (hKJ J K M A hK) (hsJ J K hs) (J u₀)
          (hJu J u₀ hu₀) t 0) =
        TraceClass.hsSq (Ext006KernelHilbertSchmidt.physicalBasis L)
          (betaBlock (BL (UI L) (kernelsI J K)) M A hA.le
            (BL_bound (UI L) (kernelsI J K) M A (hKJ J K M A hK))
            (BL_selfAdj (UI L) (kernelsI J K) (hsJ J K hs))
            (sphL (UI L) (J u₀) (hJu J u₀ hu₀)) t 0) := by
      rw [betaH, SH_eq, antilinearPart_pull,
        antiHS_pull (UI L) (antilinearPart_antilinear _)
          (Ext006KernelHilbertSchmidt.physicalBasis L)
          (Ext006KernelHilbertSchmidt.physicalBasis L), antiHS_eq_hsSq_beta]
      rfl
    have hb : antiHS e (betaJ J K M A hA.le hK hs u₀ hu₀ t 0) =
        TraceClass.hsSq (Ext006KernelHilbertSchmidt.physicalBasis L)
          (betaBlock (BL (UI L) (kernelsI J K)) M A hA.le
            (BL_bound (UI L) (kernelsI J K) M A (hKJ J K M A hK))
            (BL_selfAdj (UI L) (kernelsI J K) (hsJ J K hs))
            (sphL (UI L) (J u₀) (hJu J u₀ hu₀)) t 0) := by
      rw [← hb0, betaH'_eq J K M A hA.le hK hs u₀ hu₀ t 0]
      exact antiHS_embed J e (Ext006KernelHilbertSchmidt.physicalBasis L) _
        (antilinearPart_antilinear _)
    have hnum : numExpH (V t 0 (vacJ J)) =
        Ext006NumberPhase.numberExpectation (fun n => (n : ℝ≥0∞))
          (Pr J K M A hM hA hK hs u₀ hu₀ 0 t (vac : Fock L)) := by
      unfold numExpH Ext006NumberPhase.numberExpectation
      refine tsum_congr (fun n => ?_)
      rw [← hxi]
      simp only [fockMapI_apply, LinearIsometry.norm_map]
    refine ⟨?_, ?_, ?_⟩
    · unfold QFJ
      rw [hxi]
      exact hq
    · rw [← LinearIsometry.norm_map (fockMapI J), hxi]
      exact hn
    · rw [hnum, hb]
      exact hnum'

end Main

end QuantumNLS.Prop022BFock3

#print axioms QuantumNLS.Prop022BFock3.aSym_support
#print axioms QuantumNLS.Prop022BFock3.bSym_support
#print axioms QuantumNLS.Prop022BFock3.PROP022_fock_J
