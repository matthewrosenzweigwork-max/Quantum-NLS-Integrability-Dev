import Mathlib
import QuantumNLS.Prop022GClassical

/-! PROP-022 general-scope transport, stage G3c: linearization on a general complex Hilbert
space `H` (fluctuations.tex:43-53, 81-92, 93-104, 124-130).

* `SH t s = DΦ_H(t-s)(u_s)` (literal real Fréchet derivative) equals `U⁻¹ S_L(t,s) U`
  (`SH_eq`); it solves the intrinsic variational equation `∂_t v = -i D(∇F_H)(u_t) v` and is its
  UNIQUE solution (`SH_variational`, `SH_unique`), hence independent of `U` (`SH_indep`).
* `aH t`, `bH t`: complex-linear and antilinear parts of the Hessian `D(∇F_H)(u_t)`
  (printed "interpreted intrinsically ... as an antilinear operator"); `aH` is Hermitian,
  `bH` is complex symmetric (`⟪x, b y⟫ = ⟪y, b x⟫`), the printed bounds hold with the HS norm
  of `bH` computed in ANY Hilbert basis of `H` (`bH_bounds`).
* printed linearized equation `i ∂_t S v = a_t S v + b_t (S v)` (`linearized`).
* `alphaH`, `betaH`: `(S - iSi)/2`, `(S + iSi)/2`; `S = α + β`; the β estimate
  `‖β(t,0)‖_HS ≤ |t| C_A M P` in any Hilbert basis (`beta_estimate`). -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop022GLinear
open TensorCarrier PhysicalTensor BetheCoefficientTransform Prop022GTensor Prop022GAntiHS
open Ext006Blocks Prop022GClassical
open Prop022FactorialCoefficientsR115 Prop022ActualProfileR117 Prop022GradientR118
open Prop022ClassicalFlowR126 Prop022FlowDifferentialR126 Prop022VariationalR123
open Prop022PrintedCoefficientsR124 Prop022PairHSR122 Prop022FactorialMajorantR115

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

lemma complexPart_split {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {N P : E →L[ℝ] E} (hN : CLinear N) (hP : Antilinear P) : complexPart (N + P) = N := by
  ext x
  simp only [complexPart_apply, add_apply, hN x, hP x, map_add, map_neg, J_sq]
  module

lemma antilinearPart_split {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {N P : E →L[ℝ] E} (hN : CLinear N) (hP : Antilinear P) : antilinearPart (N + P) = P := by
  ext x
  simp only [antilinearPart_apply, add_apply, hN x, hP x, map_add, map_neg, J_sq]
  module

section Objects
variable (U : H ≃ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hA : 0 ≤ A) (hK : KBound K M A)
  (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1)

/-- `S(t,s) = DΦ_{t-s}(u_s)` on `H`, the literal real Fréchet derivative. -/
def SH (t s : ℝ) : H →L[ℝ] H :=
  fderiv ℝ (flowH U K M A hA hK hs (t - s)) (profH U K M A hA hK hs u₀ hu₀ s)

/-- The Hessian operator `D(∇F_H)(u)` (real-linear). -/
def hessH (u : H) : H →L[ℝ] H := fderiv ℝ (gradH U K) u

/-- `a_t`: complex-linear part of the Hessian along the trajectory. -/
def aH (t : ℝ) : H →L[ℝ] H := complexPart (hessH U K (profH U K M A hA hK hs u₀ hu₀ t))

/-- `b_t`: antilinear part of the Hessian along the trajectory (printed `b_t v̄`). -/
def bH (t : ℝ) : H →L[ℝ] H := antilinearPart (hessH U K (profH U K M A hA hK hs u₀ hu₀ t))

/-- `α(t,s) = (S - iSi)/2`. -/
def alphaH (t s : ℝ) : H →L[ℝ] H := complexPart (SH U K M A hA hK hs u₀ hu₀ t s)

/-- `β(t,s) = (S + iSi)/2` (antilinear). -/
def betaH (t s : ℝ) : H →L[ℝ] H := antilinearPart (SH U K M A hA hK hs u₀ hu₀ t s)

/-- The physical-carrier objects for the transported kernels (notation, expanded at parse time). -/
local notation "Φᴸ" => flow (BL U K) M A hA (BL_bound U K M A hK) (BL_selfAdj U K hs) (sphL U u₀ hu₀)
local notation "uᴸ" => profile (BL U K) M A hA (BL_bound U K M A hK) (BL_selfAdj U K hs) (sphL U u₀ hu₀)

lemma U_profH (t : ℝ) : U (profH U K M A hA hK hs u₀ hu₀ t) = uᴸ t :=
  LinearIsometryEquiv.apply_symm_apply U _

lemma profile_norm_L (t : ℝ) : ‖uᴸ t‖ = 1 :=
  (profile_spec (BL U K) M A hA (BL_bound U K M A hK) (BL_selfAdj U K hs) (sphL U u₀ hu₀)).2.2.1 t

/-- **`S_H = U⁻¹ S_L U`.** -/
theorem SH_eq (t s : ℝ) :
    SH U K M A hA hK hs u₀ hu₀ t s = pull U (Φᴸ t s).toContinuousLinearMap := by
  have h := classicalFlow_hasFDerivAt (BL U K) M A hA (BL_bound U K M A hK) (BL_selfAdj U K hs)
    (sphL U u₀ hu₀) s t
  rw [← U_profH U K M A hA hK hs u₀ hu₀ s] at h
  have hc := (URinv U).hasFDerivAt.comp (profH U K M A hA hK hs u₀ hu₀ s)
    (h.comp (profH U K M A hA hK hs u₀ hu₀ s) (UR U).hasFDerivAt)
  have hc' : HasFDerivAt (flowH U K M A hA hK hs (t - s))
      (pull U (Φᴸ t s).toContinuousLinearMap)
      (profH U K M A hA hK hs u₀ hu₀ s) := hc
  exact hc'.fderiv

lemma SH_apply (t s : ℝ) (x : H) :
    SH U K M A hA hK hs u₀ hu₀ t s x = U.symm (Φᴸ t s (U x)) := by
  rw [SH_eq, pull_apply]
  rfl

lemma SH_self (s : ℝ) (x : H) : SH U K M A hA hK hs u₀ hu₀ s s x = x := by
  rw [SH_apply, flow_self, LinearIsometryEquiv.symm_apply_apply]

include M A hA hK hs in
lemma hessH_eq (u : H) :
    hessH U K u = pull U (gradientDerivative (BL U K) (U u)) := by
  have h := gradient_hasFDerivAt (BL U K) (BL_selfAdj U K hs) M A hA (BL_bound U K M A hK) (U u)
  have hc := (URinv U).hasFDerivAt.comp u (h.comp u (UR U).hasFDerivAt)
  have hc' : HasFDerivAt (gradH U K) (pull U (gradientDerivative (BL U K) (U u))) u := hc
  exact hc'.fderiv

include hs in
lemma hessH_profH (t : ℝ) :
    hessH U K (profH U K M A hA hK hs u₀ hu₀ t) =
      pull U (coefficientMap (BL U K) (uᴸ t)) := by
  rw [hessH_eq U K M A hA hK hs, U_profH,
    gradientDerivative_eq_coefficients (BL U K) (BL_selfAdj U K hs) M A hA (BL_bound U K M A hK)
      _ (profile_norm_L U K M A hA hK hs u₀ hu₀ t)]

/-- The physical number and pair blocks. -/
abbrev NL (t : ℝ) : L2T L →L[ℝ] L2T L :=
  (numberOperator (BL U K) (uᴸ t)).restrictScalars ℝ

abbrev PL (t : ℝ) : L2T L →L[ℝ] L2T L :=
  (pairKernel (BL U K) (uᴸ t)).restrictScalars ℝ ∘L
    Ext006KernelHilbertSchmidt.conjugation (Ext006KernelHilbertSchmidt.physicalBasis L)

lemma NL_clinear (t : ℝ) : CLinear (NL U K M A hA hK hs u₀ hu₀ t) := restrictScalars_clinear _

lemma PL_antilinear (t : ℝ) : Antilinear (PL U K M A hA hK hs u₀ hu₀ t) :=
  comp_conjugation_antilinear _ _

theorem aH_eq (t : ℝ) : aH U K M A hA hK hs u₀ hu₀ t = pull U (NL U K M A hA hK hs u₀ hu₀ t) := by
  rw [aH, hessH_profH, complexPart_pull, coefficientMap,
    complexPart_split (NL_clinear U K M A hA hK hs u₀ hu₀ t) (PL_antilinear U K M A hA hK hs u₀ hu₀ t)]

theorem bH_eq (t : ℝ) : bH U K M A hA hK hs u₀ hu₀ t = pull U (PL U K M A hA hK hs u₀ hu₀ t) := by
  rw [bH, hessH_profH, antilinearPart_pull, coefficientMap,
    antilinearPart_split (NL_clinear U K M A hA hK hs u₀ hu₀ t) (PL_antilinear U K M A hA hK hs u₀ hu₀ t)]

/-- **Printed linearized equation** `i ∂_t S(t,s)x = a_t S(t,s)x + b_t (S(t,s)x)`. -/
theorem linearized (s t : ℝ) (x : H) :
    Complex.I • deriv (fun r => SH U K M A hA hK hs u₀ hu₀ r s x) t =
      aH U K M A hA hK hs u₀ hu₀ t (SH U K M A hA hK hs u₀ hu₀ t s x) +
      bH U K M A hA hK hs u₀ hu₀ t (SH U K M A hA hK hs u₀ hu₀ t s x) := by
  have hfun : (fun r => SH U K M A hA hK hs u₀ hu₀ r s x) =
      fun r => U.symm (Φᴸ r s (U x)) :=
    funext (fun r => SH_apply U K M A hA hK hs u₀ hu₀ r s x)
  have hv := flow_variational (BL U K) M A hA (BL_bound U K M A hK) (BL_selfAdj U K hs)
    (sphL U u₀ hu₀) s t (U x)
  have hlin := flow_printed_linearized (BL U K) M A hA (BL_bound U K M A hK) (BL_selfAdj U K hs)
    (sphL U u₀ hu₀) s t (U x)
  rw [hv.deriv] at hlin
  rw [hfun, (hasDerivAt_symm U hv).deriv, aH_eq, bH_eq, SH_apply, pull_apply, pull_apply,
    LinearIsometryEquiv.apply_symm_apply]
  apply U.injective
  simp only [map_add, map_smul, LinearIsometryEquiv.apply_symm_apply]
  rw [hlin]
  all_goals rfl

/-- The real map `v ↦ -i D(∇F_H)(u_t) v`, i.e. the derivative of the vector field `-i∇F_H`. -/
lemma velocityDerivative_pull (t : ℝ) (y : L2T L) :
    fderiv ℝ (velocity (BL U K)) (uᴸ t) y =
      (-Complex.I) • gradientDerivative (BL U K) (uᴸ t) y := by
  rw [(velocity_hasFDerivAt (BL U K) (BL_selfAdj U K hs) M A hA (BL_bound U K M A hK) _).fderiv]
  rfl

/-- **Intrinsic variational equation** for `S_H`. -/
theorem SH_variational (s t : ℝ) (x : H) :
    HasDerivAt (fun r => SH U K M A hA hK hs u₀ hu₀ r s x)
      ((-Complex.I) • hessH U K (profH U K M A hA hK hs u₀ hu₀ t)
        (SH U K M A hA hK hs u₀ hu₀ t s x)) t := by
  have hfun : (fun r => SH U K M A hA hK hs u₀ hu₀ r s x) =
      fun r => U.symm (Φᴸ r s (U x)) :=
    funext (fun r => SH_apply U K M A hA hK hs u₀ hu₀ r s x)
  have hv := hasDerivAt_symm U (flow_variational (BL U K) M A hA (BL_bound U K M A hK)
    (BL_selfAdj U K hs) (sphL U u₀ hu₀) s t (U x))
  rw [velocityDerivative_pull U K M A hA hK hs u₀ hu₀, map_smul] at hv
  rw [hfun, hessH_eq U K M A hA hK hs, U_profH, SH_apply, pull_apply,
    LinearIsometryEquiv.apply_symm_apply]
  exact hv

/-- **Uniqueness**: `S_H(·,s)x` is the only solution of the intrinsic variational equation
with value `x` at time `s`. -/
theorem SH_unique (s : ℝ) (x : H) (v : ℝ → H)
    (hv : ∀ t, HasDerivAt v ((-Complex.I) • hessH U K (profH U K M A hA hK hs u₀ hu₀ t) (v t)) t)
    (hi : v s = x) : ∀ t, v t = SH U K M A hA hK hs u₀ hu₀ t s x := by
  have hw : ∀ t, HasDerivAt (fun r => U (v r))
      (fderiv ℝ (velocity (BL U K)) (uᴸ t) (U (v t))) t := by
    intro t
    have h := hasDerivAt_map U (hv t)
    rw [hessH_eq U K M A hA hK hs, U_profH, map_smul, pull_apply,
      LinearIsometryEquiv.apply_symm_apply] at h
    rw [velocityDerivative_pull U K M A hA hK hs u₀ hu₀]
    exact h
  have hu := flow_unique (BL U K) M A hA (BL_bound U K M A hK) (BL_selfAdj U K hs)
    (sphL U u₀ hu₀) s (U x) (fun r => U (v r)) hw (by simp only [hi])
  intro t
  rw [SH_apply, ← hu t, LinearIsometryEquiv.symm_apply_apply]

/-! ### The printed coefficient bounds, intrinsically on `H` -/

theorem aH_clinear (t : ℝ) : CLinear (aH U K M A hA hK hs u₀ hu₀ t) :=
  complexPart_clinear _

theorem bH_antilinear (t : ℝ) : Antilinear (bH U K M A hA hK hs u₀ hu₀ t) :=
  antilinearPart_antilinear _

/-- `a_t` is Hermitian. -/
theorem aH_hermitian (t : ℝ) (x y : H) :
    ⟪x, aH U K M A hA hK hs u₀ hu₀ t y⟫_ℂ = ⟪aH U K M A hA hK hs u₀ hu₀ t x, y⟫_ℂ := by
  rw [aH_eq, inner_pull, pull_apply, inner_symm_left]
  simp only [NL, ContinuousLinearMap.coe_restrictScalars']
  rw [← ContinuousLinearMap.adjoint_inner_left,
    numberOperator_adjoint (BL U K) (BL_selfAdj U K hs)]

/-- `b_t` is complex symmetric: `⟪x, b y⟫ = ⟪y, b x⟫`. -/
theorem bH_symmetric (t : ℝ) (x y : H) :
    ⟪x, bH U K M A hA hK hs u₀ hu₀ t y⟫_ℂ = ⟪y, bH U K M A hA hK hs u₀ hu₀ t x⟫_ℂ := by
  rw [bH_eq, inner_pull, inner_pull]
  simp only [PL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars']
  exact pairKernel_pairing_symmetric (BL U K) (uᴸ t) (U x) (U y)

/-- **Printed bounds** `‖b_t‖_HS ≤ C_A M` (in ANY Hilbert basis `e` of `H`) and
`‖a_t‖ ≤ M ∑ m² A^m/√(2m)!`. -/
theorem bH_bounds {ι : Type*} (e : HilbertBasis ι ℂ H) (t : ℝ) :
    antiHS e (bH U K M A hA hK hs u₀ hu₀ t) ≠ ⊤ ∧
    Real.sqrt ((antiHS e (bH U K M A hA hK hs u₀ hu₀ t)).toReal) ≤ pairMajorant A * M ∧
    ‖aH U K M A hA hK hs u₀ hu₀ t‖ ≤
      M * ∑' r : ℕ, (((r+1 : ℕ) : ℝ)^2 * A^(r+1) / Real.sqrt ((2*(r+1)).factorial : ℝ)) := by
  obtain ⟨h1, h2, h3⟩ := PROP022_printed_coefficient_bounds_R122 (BL U K) M A hA
    (BL_bound U K M A hK) (BL_selfAdj U K hs) (sphL U u₀ hu₀) t
  have hb : antiHS e (bH U K M A hA hK hs u₀ hu₀ t) =
      TraceClass.hsSq (Ext006KernelHilbertSchmidt.physicalBasis L)
        (pairKernel (BL U K) (uᴸ t)) := by
    rw [bH_eq, antiHS_pull U (PL_antilinear U K M A hA hK hs u₀ hu₀ t) e
      (Ext006KernelHilbertSchmidt.physicalBasis L), antiHS_comp_conjugation]
  rw [hb]
  refine ⟨h1, h2, ?_⟩
  rw [aH_eq, norm_pull, ContinuousLinearMap.norm_restrictScalars]
  exact (numberOperator_norm_le _ _).trans h3

/-! ### α, β and the β estimate -/

theorem SH_blocks (t s : ℝ) :
    SH U K M A hA hK hs u₀ hu₀ t s = alphaH U K M A hA hK hs u₀ hu₀ t s + betaH U K M A hA hK hs u₀ hu₀ t s ∧
    CLinear (alphaH U K M A hA hK hs u₀ hu₀ t s) ∧ Antilinear (betaH U K M A hA hK hs u₀ hu₀ t s) ∧
    ‖alphaH U K M A hA hK hs u₀ hu₀ t s‖ ≤ ‖SH U K M A hA hK hs u₀ hu₀ t s‖ ∧
    ‖betaH U K M A hA hK hs u₀ hu₀ t s‖ ≤ ‖SH U K M A hA hK hs u₀ hu₀ t s‖ :=
  ⟨(parts_sum _).symm, complexPart_clinear _, antilinearPart_antilinear _,
    complexPart_norm _, antilinearPart_norm _⟩

/-- **β estimate** `‖β(t,0)‖_HS ≤ |t| C_A M P` in ANY Hilbert basis of `H`, under the printed
hypothesis `sup_{|s|,|t|≤T} ‖S(t,s)‖ ≤ P`, including negative time. -/
theorem beta_estimate (hM : 1 ≤ M) {ι : Type*} (e : HilbertBasis ι ℂ H) (T P : ℝ) (hP : 1 ≤ P)
    (hS : ∀ r q : ℝ, |r| ≤ T → |q| ≤ T → ‖SH U K M A hA hK hs u₀ hu₀ r q‖ ≤ P)
    (t : ℝ) (ht : |t| ≤ T) :
    antiHS e (betaH U K M A hA hK hs u₀ hu₀ t 0) ≠ ⊤ ∧
    Real.sqrt ((antiHS e (betaH U K M A hA hK hs u₀ hu₀ t 0)).toReal) ≤
      |t| * pairMajorant A * M * P := by
  have hPhi : ∀ r q : ℝ, |r| ≤ T → |q| ≤ T →
      ‖fderiv ℝ (classicalFlow (BL U K) M A hA (BL_bound U K M A hK) (BL_selfAdj U K hs) (r-q))
        (uᴸ q)‖ ≤ P := by
    intro r q hr hq
    rw [← flow_eq_fderiv, ← norm_pull U, ← SH_eq]
    exact hS r q hr hq
  have h := printed_beta_bound_from_classical (BL U K) M A hA (BL_bound U K M A hK)
    (BL_selfAdj U K hs) (sphL U u₀ hu₀) (by linarith) T P hP hPhi t ht
  have hb : antiHS e (betaH U K M A hA hK hs u₀ hu₀ t 0) =
      TraceClass.hsSq (Ext006KernelHilbertSchmidt.physicalBasis L)
        (betaBlock (BL U K) M A hA (BL_bound U K M A hK) (BL_selfAdj U K hs) (sphL U u₀ hu₀) t 0) := by
    rw [betaH, SH_eq, antilinearPart_pull,
      antiHS_pull U (antilinearPart_antilinear _) e (Ext006KernelHilbertSchmidt.physicalBasis L),
      antiHS_eq_hsSq_beta]
    rfl
  rw [hb]
  exact h

end Objects

/-! ### Independence of the transporting unitary -/

section Indep
variable (U U' : H ≃ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hA : 0 ≤ A) (hK : KBound K M A)
  (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1)

include M A hA hK hs in
theorem hessH_indep : hessH U K = hessH U' K := by
  have h : gradH U K = gradH U' K := funext (gradH_indep U U' K M A hA hK hs)
  funext u
  rw [hessH, hessH, h]

theorem SH_indep (t s : ℝ) :
    SH U K M A hA hK hs u₀ hu₀ t s = SH U' K M A hA hK hs u₀ hu₀ t s := by
  ext x
  have h := SH_unique U K M A hA hK hs u₀ hu₀ s x (fun r => SH U' K M A hA hK hs u₀ hu₀ r s x)
    (fun r => by
      rw [hessH_indep U U' K M A hA hK hs, profH_indep U U' K M A hA hK hs u₀ hu₀]
      exact SH_variational U' K M A hA hK hs u₀ hu₀ s r x)
    (SH_self U' K M A hA hK hs u₀ hu₀ s x) t
  exact h.symm

theorem aH_indep (t : ℝ) : aH U K M A hA hK hs u₀ hu₀ t = aH U' K M A hA hK hs u₀ hu₀ t := by
  rw [aH, aH, hessH_indep U U' K M A hA hK hs, profH_indep U U' K M A hA hK hs u₀ hu₀]

theorem bH_indep (t : ℝ) : bH U K M A hA hK hs u₀ hu₀ t = bH U' K M A hA hK hs u₀ hu₀ t := by
  rw [bH, bH, hessH_indep U U' K M A hA hK hs, profH_indep U U' K M A hA hK hs u₀ hu₀]

theorem betaH_indep (t s : ℝ) :
    betaH U K M A hA hK hs u₀ hu₀ t s = betaH U' K M A hA hK hs u₀ hu₀ t s := by
  rw [betaH, betaH, SH_indep U U' K M A hA hK hs u₀ hu₀]

theorem alphaH_indep (t s : ℝ) :
    alphaH U K M A hA hK hs u₀ hu₀ t s = alphaH U' K M A hA hK hs u₀ hu₀ t s := by
  rw [alphaH, alphaH, SH_indep U U' K M A hA hK hs u₀ hu₀]

end Indep

end QuantumNLS.Prop022GLinear

#print axioms QuantumNLS.Prop022GLinear.SH_eq
#print axioms QuantumNLS.Prop022GLinear.linearized
#print axioms QuantumNLS.Prop022GLinear.SH_unique
#print axioms QuantumNLS.Prop022GLinear.bH_bounds
#print axioms QuantumNLS.Prop022GLinear.aH_hermitian
#print axioms QuantumNLS.Prop022GLinear.bH_symmetric
#print axioms QuantumNLS.Prop022GLinear.beta_estimate
#print axioms QuantumNLS.Prop022GLinear.SH_indep
#print axioms QuantumNLS.Prop022GLinear.aH_indep
#print axioms QuantumNLS.Prop022GLinear.bH_indep
