import Mathlib
import QuantumNLS.Prop022OMain
import QuantumNLS.Prop022GMain

/-! PROP-022 route A, stage A1: the Fock side over a general complex Hilbert space `H`, by transport.

Fixed unitary `U : H ≃ₗᵢ[ℂ] L2T L` (infinite-dimensional separable `H`, see `Prop022GHilbert`).
With `Γ(U) = Prop022GTensor.fockMap U` (so `FockSpace (L2T L) = Fock L` by `rfl`):

* `WH U v := Γ(U)⁻¹ ∘ printedWeyl (U v) ∘ Γ(U)`   (the printed Weyl operator `exp(a*(v) - a(v))`);
* `VH ... t s := Γ(U)⁻¹ ∘ V_L(t,s) ∘ Γ(U)`         (R122 propagator, `propagator` of the transported data);
* `QH U a b := Γ(U)⁻¹ ∘ strongCoordinates (Γ₁ a Γ₁⁻¹) (Γ₂ b) ∘ rootLift 2 ∘ Γ(U)`
  (the quadratic generator `dΓ(a)+½(a*(b)+a(b))` for coefficient data `a ∈ B(Sym¹H)`, `b ∈ Sym²H`);
* `vacH U := Γ(U)⁻¹ vac`, `numExpH` the number expectation, `QFH U ξ := PhysicalQuasifreeSource (Γ(U) ξ)`.

`PROP022_fock_transport` states printed conclusions 4-6 for every such `U` (the data being the
frozen torus theorem `Prop022OMain.PROP022_physical_quadratic_propagator` applied to the transported
kernels `kernelsL U K`, trajectory `U u₀`).  Independence of `U` is NOT claimed here. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace Topology NNReal ENNReal
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop022AFock
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop022GTensor Prop022GAntiHS Prop022GClassical Prop022GLinear
open Prop022FactorialCoefficientsR115 Prop022ActualProfileR117 Prop022ClassicalFlowR126
open Prop022VariationalR123 Prop022PositiveDataR126 Prop022FockPropagatorR122
open Prop022OVacuum Ext006PhysQuasifree Ext006PhysFockCoord

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

/-- `Γ(U) : Fock(H) ≃ Fock(L²(𝕋_L))` as a map into the physical Fock space. -/
def gam (U : H ≃ₗᵢ[ℂ] L2T L) : FockSpace H ≃ₗᵢ[ℂ] Fock L := fockMap U

/-- Transported printed Weyl operator `W_H(v) = Γ(U)⁻¹ W_L(U v) Γ(U)`. -/
def WH (U : H ≃ₗᵢ[ℂ] L2T L) (v : H) : FockSpace H ≃ₗᵢ[ℂ] FockSpace H :=
  ((gam U).trans (printedWeyl (U v))).trans (gam U).symm

/-- The vacuum of `Fock(H)`. -/
def vacH (U : H ≃ₗᵢ[ℂ] L2T L) : FockSpace H := (gam U).symm (vac (L := L))

/-- Number expectation `⟨x, N x⟩` on `Fock(H)` (intrinsic: sector norms only). -/
def numExpH (x : FockSpace H) : ℝ≥0∞ := ∑' n : ℕ, (n : ℝ≥0∞) * ENNReal.ofReal (‖x n‖ ^ 2)

/-- Pure-quasifree predicate on `Fock(H)`, transported. -/
def QFH (U : H ≃ₗᵢ[ℂ] L2T L) (ξ : FockSpace H) : Prop := PhysicalQuasifreeSource (gam U ξ)

/-- The finite number-moment domain of order `j` (intrinsic: sector norms only). -/
def momentDomainH (j : ℕ) : Set (FockSpace H) :=
  {x | Summable (fun n : ℕ => Ext005Moments.momentWeight j n * ‖x n‖ ^ 2)}

lemma gam_mem_momentDomain (U : H ≃ₗᵢ[ℂ] L2T L) (j : ℕ) (x : FockSpace H) :
    gam U x ∈ Ext005Moments.momentDomain (L := L) j ↔ x ∈ momentDomainH j := by
  rw [Ext005Moments.momentDomain_iff]
  change Summable (fun n : ℕ => Ext005Moments.momentWeight j n * ‖fockMap U x n‖ ^ 2) ↔ _
  simp only [norm_fockMap_sector]
  rfl

/-- The transported quadratic generator `dΓ(a) + ½(a*(b)+a(b))`, `a ∈ B(Sym¹ H)`, `b ∈ Sym² H`,
acting on second-moment coordinates. -/
def QH (U : H ≃ₗᵢ[ℂ] L2T L) (a : SymSector ℂ H 1 →L[ℂ] SymSector ℂ H 1) (b : SymSector ℂ H 2)
    (y : FockSpace H) : FockSpace H :=
  (gam U).symm (Prop022StrongOperatorR125.strongCoordinates (conjSym U 1 a) (symMap U 2 b)
    (Ext005FormCutoffR109.rootLift 2 (gam U y)))

/-- Back-conjugation of an operator on the physical sector to `Sym^m H`. -/
def backConj (U : H ≃ₗᵢ[ℂ] L2T L) (m : ℕ) (X : HN L m →L[ℂ] HN L m) :
    SymSector ℂ H m →L[ℂ] SymSector ℂ H m :=
  (symMap U m).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L X ∘L
    (symMap U m).toContinuousLinearEquiv.toContinuousLinearMap

lemma conjSym_backConj (U : H ≃ₗᵢ[ℂ] L2T L) (m : ℕ) (X : HN L m →L[ℂ] HN L m) :
    conjSym U m (backConj U m X) = X := by
  ext y
  simp [conjSym_apply, backConj]

lemma norm_gam_symm_sector (U : H ≃ₗᵢ[ℂ] L2T L) (z : Fock L) (n : ℕ) :
    ‖(gam U).symm z n‖ = ‖z n‖ := by
  change ‖(fockMap U).symm z n‖ = _
  rw [fockMap_symm_apply]
  exact (symMap U n).symm.norm_map _

section Objects
variable (U : H ≃ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hA : 0 ≤ A) (hK : KBound K M A)
  (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1) (hM0 : 0 ≤ M)

/-- The physical propagator of the transported data. -/
def propL (s t : ℝ) : Fock L ≃ₗᵢ[ℂ] Fock L :=
  propagator (BL U K) M A hM0 hA (BL_bound U K M A hK) (BL_selfAdj U K hs) (sphL U u₀ hu₀) s t

/-- The propagator `V_H(t,s)` on `Fock(H)` (maps time `s` to time `t`). -/
def VH (t s : ℝ) : FockSpace H ≃ₗᵢ[ℂ] FockSpace H :=
  ((gam U).trans (propL U K M A hA hK hs u₀ hu₀ hM0 s t)).trans (gam U).symm

/-- The coefficient `a_t ∈ B(Sym¹ H)` of the quadratic generator. -/
def aSym (t : ℝ) : SymSector ℂ H 1 →L[ℂ] SymSector ℂ H 1 :=
  backConj U 1 (numberCoefficient (BL U K)
    (profile (BL U K) M A hA (BL_bound U K M A hK) (BL_selfAdj U K hs) (sphL U u₀ hu₀) t))

/-- The coefficient `b_t ∈ Sym² H` of the quadratic generator. -/
def bSym (t : ℝ) : SymSector ℂ H 2 :=
  (symMap U 2).symm (pairCoefficient (BL U K)
    (profile (BL U K) M A hA (BL_bound U K M A hK) (BL_selfAdj U K hs) (sphL U u₀ hu₀) t))

end Objects

/-- **PROP-022 (Q7B:lem:pair), printed conclusions 4-6, transported through `U`.** -/
theorem PROP022_fock_transport (U : H ≃ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hM : 1 ≤ M)
    (hA : 0 < A) (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1)
    (T P : ℝ) (hP : 1 ≤ P) {ι : Type*} (e : HilbertBasis ι ℂ H) :
    let hM0 : 0 ≤ M := by linarith
    let V := VH U K M A hA.le hK hs u₀ hu₀ hM0
    (∀ s x, V s s x = x) ∧
    (∀ r s t x, V t s (V s r x) = V t r x) ∧
    (∀ s x, Continuous (fun t => V t s x)) ∧
    (∀ s t (x : FockSpace H), (∀ j : ℕ, x ∈ momentDomainH j) →
      HasDerivAt (fun r => V r s x)
        ((-Complex.I) • QH U (aSym U K M A hA.le hK hs u₀ hu₀ t) (bSym U K M A hA.le hK hs u₀ hu₀ t)
          (V t s x)) t) ∧
    (∀ s t (v : H) (x : FockSpace H),
      V t s (WH U v ((V t s).symm x)) =
        WH U (SH U K M A hA.le hK hs u₀ hu₀ t s v) x) ∧
    (∀ t, QFH U (V t 0 (vacH U)) ∧ ‖V t 0 (vacH U)‖ = 1 ∧
      numExpH (V t 0 (vacH U)) = antiHS e (betaH U K M A hA.le hK hs u₀ hu₀ t 0)) := by
  intro hM0 V
  have hK' : ∀ n, ‖kernelsL U K n‖ ≤ M * A ^ (n+1) / Real.sqrt ((2*(n+1)).factorial : ℝ) :=
    fun n => (norm_conjSym_le U (n+1) (K n)).trans (hK n)
  have hs' : ∀ n, (kernelsL U K n).adjoint = kernelsL U K n :=
    fun n => conjSym_adjoint U (n+1) (K n) (hs n)
  obtain ⟨-, hSeq, -, -, -, hV0, hVc, hVcont, hSchr, hImpl, hVac⟩ :=
    Prop022OMain.PROP022_physical_quadratic_propagator (kernelsL U K) M A hM hA hK' hs'
      (sphL U u₀ hu₀) T P hP
  have hVapp : ∀ t s (z : FockSpace H), V t s z =
      (gam U).symm (propL U K M A hA.le hK hs u₀ hu₀ hM0 s t (gam U z)) := fun _ _ _ => rfl
  have hVsymm : ∀ t s (z : FockSpace H), (V t s).symm z =
      (gam U).symm ((propL U K M A hA.le hK hs u₀ hu₀ hM0 s t).symm (gam U z)) := by
    intro t s z
    rw [LinearIsometryEquiv.symm_apply_eq, hVapp, LinearIsometryEquiv.apply_symm_apply (gam U),
      LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.symm_apply_apply]
  have hWapp : ∀ v (z : FockSpace H), WH U v z = (gam U).symm (printedWeyl (U v) (gam U z)) :=
    fun _ _ => rfl
  refine ⟨fun s x => ?_, fun r s t x => ?_, fun s x => ?_, fun s t x hx => ?_,
    fun s t v x => ?_, fun t => ?_⟩
  · rw [hVapp]
    have h := hV0 s (gam U x)
    change propL U K M A hA.le hK hs u₀ hu₀ hM0 s s (gam U x) = gam U x at h
    rw [h]
    exact (gam U).symm_apply_apply x
  · rw [hVapp, hVapp, hVapp, LinearIsometryEquiv.apply_symm_apply (gam U)]
    have h := hVc r s t (gam U x)
    change propL U K M A hA.le hK hs u₀ hu₀ hM0 s t
        (propL U K M A hA.le hK hs u₀ hu₀ hM0 r s (gam U x)) =
      propL U K M A hA.le hK hs u₀ hu₀ hM0 r t (gam U x) at h
    rw [h]
  · exact (gam U).symm.continuous.comp (hVcont s (gam U x))
  · have h := hSchr s t (gam U x) (fun j => (gam_mem_momentDomain U j x).2 (hx j))
    have hd := ((gam U).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars
      ℝ).hasFDerivAt.comp_hasDerivAt t h
    have e3 : gam U (V t s x) = propL U K M A hA.le hK hs u₀ hu₀ hM0 s t (gam U x) := by
      rw [hVapp]
      exact LinearIsometryEquiv.apply_symm_apply (gam U) _
    have key : QH U (aSym U K M A hA.le hK hs u₀ hu₀ t) (bSym U K M A hA.le hK hs u₀ hu₀ t)
        (V t s x) = (gam U).symm (Prop022StrongOperatorR125.strongCoordinates
          (numberCoefficient (BL U K) (profile (BL U K) M A hA.le (BL_bound U K M A hK)
            (BL_selfAdj U K hs) (sphL U u₀ hu₀) t))
          (pairCoefficient (BL U K) (profile (BL U K) M A hA.le (BL_bound U K M A hK)
            (BL_selfAdj U K hs) (sphL U u₀ hu₀) t))
          (Ext005FormCutoffR109.rootLift 2
            (propL U K M A hA.le hK hs u₀ hu₀ hM0 s t (gam U x)))) := by
      unfold QH aSym bSym
      rw [conjSym_backConj, LinearIsometryEquiv.apply_symm_apply (symMap U 2), e3]
    rw [key]
    refine hd.congr_deriv ?_
    change (gam U).symm ((-Complex.I) • _) = _
    rw [map_smul]
    rfl
  · rw [hVsymm, hWapp v, LinearIsometryEquiv.apply_symm_apply (gam U), hVapp,
      LinearIsometryEquiv.apply_symm_apply (gam U), hWapp (SH U K M A hA.le hK hs u₀ hu₀ t s v) x]
    apply congrArg (gam U).symm
    have h := hImpl s t (U v) (gam U x)
    rw [hSeq s t] at h
    have hS : U (SH U K M A hA.le hK hs u₀ hu₀ t s v) =
        (flow (BL U K) M A hA.le (BL_bound U K M A hK) (BL_selfAdj U K hs) (sphL U u₀ hu₀) t s)
          (U v) := by
      rw [SH_apply, LinearIsometryEquiv.apply_symm_apply]
    rw [hS]
    exact h
  · have hz : V t 0 (vacH U) = (gam U).symm
        (propL U K M A hA.le hK hs u₀ hu₀ hM0 0 t (vac (L := L))) := by
      rw [hVapp]
      unfold vacH
      rw [LinearIsometryEquiv.apply_symm_apply (gam U)]
    have hnum : numExpH ((gam U).symm
        (propL U K M A hA.le hK hs u₀ hu₀ hM0 0 t (vac (L := L)))) =
        Ext006NumberPhase.numberExpectation (fun n => (n : ℝ≥0∞))
          (propL U K M A hA.le hK hs u₀ hu₀ hM0 0 t (vac (L := L))) := by
      unfold numExpH Ext006NumberPhase.numberExpectation
      refine tsum_congr (fun n => ?_)
      rw [norm_gam_symm_sector]
    have hb : antiHS e (betaH U K M A hA.le hK hs u₀ hu₀ t 0) =
        TraceClass.hsSq (Ext006KernelHilbertSchmidt.physicalBasis L)
          (betaBlock (BL U K) M A hA.le (BL_bound U K M A hK) (BL_selfAdj U K hs)
            (sphL U u₀ hu₀) t 0) := by
      rw [betaH, SH_eq, antilinearPart_pull,
        antiHS_pull U (antilinearPart_antilinear _) e (Ext006KernelHilbertSchmidt.physicalBasis L),
        antiHS_eq_hsSq_beta]
      rfl
    obtain ⟨hq, hn, hnum'⟩ := hVac t
    rw [hz]
    refine ⟨?_, ?_, ?_⟩
    · unfold QFH
      rw [LinearIsometryEquiv.apply_symm_apply (gam U)]
      exact hq
    · rw [LinearIsometryEquiv.norm_map]
      exact hn
    · rw [hnum, hb]
      exact hnum'

end QuantumNLS.Prop022AFock

#print axioms QuantumNLS.Prop022AFock.PROP022_fock_transport
