import Mathlib
import QuantumNLS.Prop022BIso
import QuantumNLS.Prop022GMain

/-! PROP-022 route A, finite-dimensional case, stage B3a: the classical side through an isometric
embedding `J : H →ₗᵢ[ℂ] L2T L`.

With `K' = kernelsI J K` (kernels `Γ_{n+1}(J) K_n Γ_{n+1}(J)*` on `L2T L`) and `U := refl` the frozen
`Prop022GClassical/GLinear` objects `gradH, flowH, profH, SH, hessH` on `L2T L` are available; this module
proves the structure relations (`G' w = J (gradJ (J* w))`, invariance of `range J` under the flow, the
variational flow and the Hessian, `S' = J S_J J* + (1 - J J*)`), and defines the `H`-level objects
`gradJ, flowJ, profJ, SJ, hessJ` by compression through `J`. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
open scoped InnerProductSpace
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop022BClass1
open TensorCarrier PhysicalTensor Prop022GTensor Prop022AIsoTensor Prop022GAntiHS
open Prop022GClassical Prop022GLinear Prop022BIso
open Prop022ClassicalFlowR126 Prop022FlowDifferentialR126 Prop022VariationalR123
open Prop022ActualProfileR117 Prop022GradientR118 Prop022PositiveDataR126

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

/-- The identity unitary of `L2T L`. -/
abbrev UI (L : ℝ) [Fact (0 < L)] : L2T L ≃ₗᵢ[ℂ] L2T L := LinearIsometryEquiv.refl ℂ (L2T L)

/-- `J` as a bounded real-linear map. -/
def Jr (J : H →ₗᵢ[ℂ] L2T L) : H →L[ℝ] L2T L := (J.toContinuousLinearMap).restrictScalars ℝ

/-- `J*` as a bounded real-linear map. -/
def Jar (J : H →ₗᵢ[ℂ] L2T L) : L2T L →L[ℝ] H := (Jadj J).restrictScalars ℝ

@[simp] lemma Jr_apply (J : H →ₗᵢ[ℂ] L2T L) (x : H) : Jr J x = J x := rfl
@[simp] lemma Jar_apply (J : H →ₗᵢ[ℂ] L2T L) (y : L2T L) : Jar J y = Jadj J y := rfl

lemma hasDerivAt_J (J : H →ₗᵢ[ℂ] L2T L) {f : ℝ → H} {f' : H} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun r => J (f r)) (J f') t :=
  (Jr J).hasFDerivAt.comp_hasDerivAt t hf

lemma hasDerivAt_Jadj (J : H →ₗᵢ[ℂ] L2T L) {f : ℝ → L2T L} {f' : L2T L} {t : ℝ}
    (hf : HasDerivAt f f' t) : HasDerivAt (fun r => Jadj J (f r)) (Jadj J f') t :=
  (Jar J).hasFDerivAt.comp_hasDerivAt t hf

section Setup
variable (J : H →ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hA : 0 ≤ A) (hK : KBound K M A)
  (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1)

include hK in
lemma hKJ : KBound (kernelsI J K) M A := KBound_kernelsI J K M A hK
include hs in
lemma hsJ : KSelfAdj (kernelsI J K) := KSelfAdj_kernelsI J K hs
include hu₀ in
lemma hJu : ‖J u₀‖ = 1 := by rw [LinearIsometry.norm_map]; exact hu₀

local notation "G'" => gradH (UI L) (kernelsI J K)
local notation "Φ'" => flowH (UI L) (kernelsI J K) M A hA (hKJ J K M A hK) (hsJ J K hs)
local notation "u'" => profH (UI L) (kernelsI J K) M A hA (hKJ J K M A hK) (hsJ J K hs) (J u₀)
  (hJu J u₀ hu₀)
local notation "S'" => SH (UI L) (kernelsI J K) M A hA (hKJ J K M A hK) (hsJ J K hs) (J u₀)
  (hJu J u₀ hu₀)
local notation "hess'" => hessH (UI L) (kernelsI J K)

/-- `∇F_J(v) = J* ∇F'(J v)`. -/
def gradJ (v : H) : H := Jadj J (gradH (UI L) (kernelsI J K) (J v))

lemma realDual_comp_Jr (g : L2T L) : (realDual g).comp (Jr J) = realDual (Jadj J g) := by
  ext h
  simp only [ContinuousLinearMap.comp_apply, Jr_apply, realDual_apply, inner_Jadj_left]

lemma realDual_comp_Jar (g : H) : (realDual g).comp (Jar J) = realDual (J g) := by
  ext h
  simp only [ContinuousLinearMap.comp_apply, Jar_apply, realDual_apply, inner_Jadj_right]

theorem gradH_hasFDerivAt' {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
    [CompleteSpace E'] (U : E' ≃ₗᵢ[ℂ] L2T L) (K₀ : Kernels E') (M₀ A₀ : ℝ) (hA₀ : 0 ≤ A₀)
    (hK₀ : KBound K₀ M₀ A₀) (hs₀ : KSelfAdj K₀) (u : E') :
    HasFDerivAt (gradH U K₀) (hessH U K₀ u) u := by
  have h := gradient_hasFDerivAt (BL U K₀) (BL_selfAdj U K₀ hs₀) M₀ A₀ hA₀
    (BL_bound U K₀ M₀ A₀ hK₀) (U u)
  have hc := (URinv U).hasFDerivAt.comp u (h.comp u (UR U).hasFDerivAt)
  have hc' : HasFDerivAt (gradH U K₀) (pull U (gradientDerivative (BL U K₀) (U u))) u := hc
  rw [hessH_eq U K₀ M₀ A₀ hA₀ hK₀ hs₀ u]
  exact hc'

/-- The Hessian of `F_J`. -/
def hessJ (v : H) : H →L[ℝ] H := fderiv ℝ (gradJ J K) v

lemma proj_const (f g : ℝ → L2T L) (hf : ∀ t, HasDerivAt f (g t) t)
    (hg : ∀ t, J (Jadj J (g t)) = g t) (t0 : ℝ) (h0 : J (Jadj J (f t0)) = f t0) (t : ℝ) :
    J (Jadj J (f t)) = f t := by
  have hd : ∀ r, HasDerivAt (fun x => f x - J (Jadj J (f x))) 0 r := by
    intro r
    have h := (hf r).sub (hasDerivAt_J J (hasDerivAt_Jadj J (hf r)))
    rw [hg r, sub_self] at h
    exact h
  have hc := is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt)
    (fun r => (hd r).deriv) t t0
  have hc' : f t - J (Jadj J (f t)) = f t0 - J (Jadj J (f t0)) := hc
  rw [h0, sub_self] at hc'
  exact (sub_eq_zero.mp hc').symm

include M A hA hK hs

/-- **The intrinsic gradient**: `dF(v)[h] = 2 Re ⟪gradJ v, h⟫`. -/
theorem hasFDerivAt_symbol (v : H) : HasFDerivAt (symbolH K) (realDual (gradJ J K v)) v := by
  have h := symbolH_hasFDerivAt (UI L) (kernelsI J K) M A hA (hKJ J K M A hK) (hsJ J K hs) (J v)
  have hc := h.comp v (Jr J).hasFDerivAt
  have hf : symbolH K = (symbolH (kernelsI J K)) ∘ (Jr J) := by
    funext x
    change symbolH K x = symbolH (kernelsI J K) (J x)
    rw [symbolH_kernelsI, Jadj_J]
  have hD : realDual (gradJ J K v) = (realDual (gradH (UI L) (kernelsI J K) (J v))).comp (Jr J) :=
    (realDual_comp_Jr J _).symm
  rw [hf, hD]
  exact hc

/-- **Structure of the gradient on `L2T L`**: `∇F'(w) = J ∇F_J(J* w)`. -/
theorem grad_embed (w : L2T L) :
    gradH (UI L) (kernelsI J K) w = J (gradJ J K (Jadj J w)) := by
  have h1 := symbolH_hasFDerivAt (UI L) (kernelsI J K) M A hA (hKJ J K M A hK) (hsJ J K hs) w
  have h2 := (hasFDerivAt_symbol J K M A hA hK hs (Jadj J w)).comp w (Jar J).hasFDerivAt
  have hf : (symbolH K) ∘ (⇑(Jadj J)) = symbolH (kernelsI J K) := by
    funext x
    exact (symbolH_kernelsI J K x).symm
  rw [hf, realDual_comp_Jar] at h2
  exact eq_of_realDual (h1.unique h2)

lemma grad_embed_J (v : H) : gradH (UI L) (kernelsI J K) (J v) = J (gradJ J K v) := by
  rw [grad_embed J K M A hA hK hs, Jadj_J]

lemma grad_range (w : L2T L) :
    J (Jadj J (gradH (UI L) (kernelsI J K) w)) = gradH (UI L) (kernelsI J K) w := by
  rw [grad_embed J K M A hA hK hs w, Jadj_J]

/-! ### Differentiability of the gradient field and the Hessian -/

theorem hasFDerivAt_gradJ (v : H) :
    HasFDerivAt (gradJ J K)
      ((Jar J).comp ((hessH (UI L) (kernelsI J K) (J v)).comp (Jr J))) v := by
  have h := gradH_hasFDerivAt' (UI L) (kernelsI J K) M A hA (hKJ J K M A hK) (hsJ J K hs) (J v)
  exact (Jar J).hasFDerivAt.comp v (h.comp v (Jr J).hasFDerivAt)

theorem hessJ_eq (v : H) :
    hessJ J K v = (Jar J).comp ((hessH (UI L) (kernelsI J K) (J v)).comp (Jr J)) :=
  (hasFDerivAt_gradJ J K M A hA hK hs v).fderiv

/-- **Structure of the Hessian on `L2T L`**. -/
theorem hess_embed (w : L2T L) :
    hessH (UI L) (kernelsI J K) w = (Jr J).comp ((hessJ J K (Jadj J w)).comp (Jar J)) := by
  have h1 := gradH_hasFDerivAt' (UI L) (kernelsI J K) M A hA (hKJ J K M A hK) (hsJ J K hs) w
  have hD : HasFDerivAt (gradJ J K) (hessJ J K (Jadj J w)) (Jadj J w) :=
    (hasFDerivAt_gradJ J K M A hA hK hs (Jadj J w)).differentiableAt.hasFDerivAt
  have h2 := (Jr J).hasFDerivAt.comp w (hD.comp w (Jar J).hasFDerivAt)
  have hf : (⇑(Jr J) ∘ gradJ J K ∘ ⇑(Jadj J)) = gradH (UI L) (kernelsI J K) := by
    funext x
    exact (grad_embed J K M A hA hK hs x).symm
  rw [hf] at h2
  exact h1.unique h2

lemma hess_embed_J (v y : H) :
    hessH (UI L) (kernelsI J K) (J v) (J y) = J (hessJ J K v y) := by
  rw [hess_embed J K M A hA hK hs]
  simp [Jadj_J]

lemma hess_ker (w c : L2T L) (hc : Jadj J c = 0) :
    hessH (UI L) (kernelsI J K) w c = 0 := by
  rw [hess_embed J K M A hA hK hs]
  simp [hc]

lemma hess_range (w y : L2T L) :
    J (Jadj J (hessH (UI L) (kernelsI J K) w y)) = hessH (UI L) (kernelsI J K) w y := by
  rw [hess_embed J K M A hA hK hs]
  simp [Jadj_J]

lemma hessJ_compress (v : H) (y : H) :
    hessJ J K v y = Jadj J (hessH (UI L) (kernelsI J K) (J v) (J y)) := by
  rw [hessJ_eq J K M A hA hK hs]
  simp

/-! ### Invariance of `range J` -/

theorem flow_inv (x : H) (t : ℝ) : J (Jadj J (Φ' t (J x))) = Φ' t (J x) := by
  obtain ⟨h0, hd⟩ := flowH_spec (UI L) (kernelsI J K) M A hA (hKJ J K M A hK) (hsJ J K hs) (J x)
  refine proj_const J (fun r => Φ' r (J x)) (fun r => (-Complex.I) • G' (Φ' r (J x)))
    (fun r => (hd r).1) (fun r => ?_) 0 ?_ t
  · rw [map_smul, map_smul, grad_range J K M A hA hK hs]
  · rw [h0, Jadj_J]

theorem prof_inv (t : ℝ) : J (Jadj J (u' t)) = u' t := by
  obtain ⟨h0, hd⟩ := profH_spec (UI L) (kernelsI J K) M A hA (hKJ J K M A hK) (hsJ J K hs)
    (J u₀) (hJu J u₀ hu₀)
  refine proj_const J (u' ) (fun r => (-Complex.I) • G' (u' r))
    (fun r => (hd r).2) (fun r => ?_) 0 ?_ t
  · rw [map_smul, map_smul, grad_range J K M A hA hK hs]
  · rw [h0, Jadj_J]

/-- The flow on `H`. -/
def flowJ (t : ℝ) (x : H) : H := Jadj J (Φ' t (J x))

/-- The trajectory on `H`. -/
def profJ (t : ℝ) : H := Jadj J (u' t)

lemma J_flowJ (t : ℝ) (x : H) : J (flowJ J K M A hA hK hs t x) = Φ' t (J x) :=
  flow_inv J K M A hA hK hs x t

lemma J_profJ (t : ℝ) : J (profJ J K M A hA hK hs u₀ hu₀ t) = u' t :=
  prof_inv J K M A hA hK hs u₀ hu₀ t

/-! ### The variational flow -/

theorem flowH_hasFDerivAt' (s t : ℝ) : HasFDerivAt (Φ' (t - s)) (S' t s) (u' s) := by
  have h := classicalFlow_hasFDerivAt (BL (UI L) (kernelsI J K)) M A hA
    (BL_bound (UI L) (kernelsI J K) M A (hKJ J K M A hK))
    (BL_selfAdj (UI L) (kernelsI J K) (hsJ J K hs))
    (sphL (UI L) (J u₀) (hJu J u₀ hu₀)) s t
  rw [← U_profH (UI L) (kernelsI J K) M A hA (hKJ J K M A hK) (hsJ J K hs) (J u₀)
    (hJu J u₀ hu₀) s] at h
  have hc := (URinv (UI L)).hasFDerivAt.comp (profH (UI L) (kernelsI J K) M A hA
      (hKJ J K M A hK) (hsJ J K hs) (J u₀) (hJu J u₀ hu₀) s)
    (h.comp (profH (UI L) (kernelsI J K) M A hA
      (hKJ J K M A hK) (hsJ J K hs) (J u₀) (hJu J u₀ hu₀) s) (UR (UI L)).hasFDerivAt)
  have hc' : HasFDerivAt (flowH (UI L) (kernelsI J K) M A hA (hKJ J K M A hK) (hsJ J K hs) (t - s))
      (pull (UI L) (flow (BL (UI L) (kernelsI J K)) M A hA
        (BL_bound (UI L) (kernelsI J K) M A (hKJ J K M A hK))
        (BL_selfAdj (UI L) (kernelsI J K) (hsJ J K hs))
        (sphL (UI L) (J u₀) (hJu J u₀ hu₀)) t s).toContinuousLinearMap)
      (profH (UI L) (kernelsI J K) M A hA (hKJ J K M A hK) (hsJ J K hs) (J u₀)
        (hJu J u₀ hu₀) s) := hc
  rw [SH_eq]
  exact hc'

/-- `S_J(t,s) = DΦ_J(t-s)(u_J(s))`, as in the frozen definition of `SH`. -/
def SJ (t s : ℝ) : H →L[ℝ] H := fderiv ℝ (flowJ J K M A hA hK hs (t - s)) (profJ J K M A hA hK hs u₀ hu₀ s)

theorem SJ_eq (t s : ℝ) :
    SJ J K M A hA hK hs u₀ hu₀ t s = (Jar J).comp ((S' t s).comp (Jr J)) := by
  have hΦ := flowH_hasFDerivAt' J K M A hA hK hs u₀ hu₀ s t
  rw [← J_profJ J K M A hA hK hs u₀ hu₀ s] at hΦ
  have h := (Jar J).hasFDerivAt.comp (profJ J K M A hA hK hs u₀ hu₀ s)
    (hΦ.comp (profJ J K M A hA hK hs u₀ hu₀ s) (Jr J).hasFDerivAt)
  exact h.fderiv

lemma SJ_apply (t s : ℝ) (x : H) :
    SJ J K M A hA hK hs u₀ hu₀ t s x = Jadj J (S' t s (J x)) := by
  rw [SJ_eq]; rfl

theorem S'_ker (t s : ℝ) (c : L2T L) (hc : Jadj J c = 0) : S' t s c = c := by
  have h := SH_unique (UI L) (kernelsI J K) M A hA (hKJ J K M A hK) (hsJ J K hs) (J u₀)
    (hJu J u₀ hu₀) s c (fun _ => c)
    (fun t' => by
      have h0 : (-Complex.I) • hessH (UI L) (kernelsI J K) (u' t') c = 0 := by
        rw [hess_ker J K M A hA hK hs _ c hc, smul_zero]
      rw [h0]
      exact hasDerivAt_const t' c) rfl t
  exact h.symm

theorem S'_range (t s : ℝ) (x : H) : J (Jadj J (S' t s (J x))) = S' t s (J x) := by
  refine proj_const J (fun r => S' r s (J x))
    (fun r => (-Complex.I) • hessH (UI L) (kernelsI J K) (u' r) (S' r s (J x)))
    (fun r => SH_variational (UI L) (kernelsI J K) M A hA (hKJ J K M A hK) (hsJ J K hs) (J u₀)
      (hJu J u₀ hu₀) s r (J x)) (fun r => ?_) s ?_ t
  · rw [map_smul, map_smul, hess_range J K M A hA hK hs]
  · rw [SH_self, Jadj_J]

theorem S_embed (t s : ℝ) (x : H) :
    S' t s (J x) = J (SJ J K M A hA hK hs u₀ hu₀ t s x) := by
  rw [SJ_apply]
  exact (S'_range J K M A hA hK hs u₀ hu₀ t s x).symm

theorem S_decomp (t s : ℝ) (w : L2T L) :
    S' t s w = J (SJ J K M A hA hK hs u₀ hu₀ t s (Jadj J w)) + (w - J (Jadj J w)) := by
  have hw : w = J (Jadj J w) + (w - J (Jadj J w)) := by abel
  have hc : Jadj J (w - J (Jadj J w)) = 0 := by rw [map_sub, Jadj_J, sub_self]
  conv_lhs => rw [hw]
  rw [map_add, S'_ker J K M A hA hK hs u₀ hu₀ t s _ hc, ← S_embed J K M A hA hK hs u₀ hu₀]

/-- The variational equation for `S_J`. -/
theorem SJ_variational (s t : ℝ) (x : H) :
    HasDerivAt (fun r => SJ J K M A hA hK hs u₀ hu₀ r s x)
      ((-Complex.I) • hessJ J K (profJ J K M A hA hK hs u₀ hu₀ t)
        (SJ J K M A hA hK hs u₀ hu₀ t s x)) t := by
  have h := hasDerivAt_Jadj J (SH_variational (UI L) (kernelsI J K) M A hA (hKJ J K M A hK)
    (hsJ J K hs) (J u₀) (hJu J u₀ hu₀) s t (J x))
  have hfun : (fun r => SJ J K M A hA hK hs u₀ hu₀ r s x) =
      fun r => Jadj J (S' r s (J x)) := funext (fun r => SJ_apply J K M A hA hK hs u₀ hu₀ r s x)
  rw [hfun]
  refine h.congr_deriv ?_
  rw [map_smul, hessJ_compress J K M A hA hK hs, J_profJ J K M A hA hK hs u₀ hu₀,
    S_embed J K M A hA hK hs u₀ hu₀ t s x]

/-- The uniqueness of the variational flow, transported: any solution of the intrinsic variational equation
for `hessJ` along `profJ` with value `x` at `s` is `S_J(·, s) x`. -/
theorem SJ_unique (s : ℝ) (x : H) (v : ℝ → H)
    (hv : ∀ t, HasDerivAt v ((-Complex.I) • hessJ J K (profJ J K M A hA hK hs u₀ hu₀ t) (v t)) t)
    (hi : v s = x) : ∀ t, v t = SJ J K M A hA hK hs u₀ hu₀ t s x := by
  have hw : ∀ t, HasDerivAt (fun r => J (v r))
      ((-Complex.I) • hessH (UI L) (kernelsI J K) (u' t) (J (v t))) t := by
    intro t
    have h := hasDerivAt_J J (hv t)
    rw [map_smul, ← hess_embed_J J K M A hA hK hs (profJ J K M A hA hK hs u₀ hu₀ t) (v t),
      J_profJ J K M A hA hK hs u₀ hu₀ t] at h
    exact h
  have hu := SH_unique (UI L) (kernelsI J K) M A hA (hKJ J K M A hK) (hsJ J K hs) (J u₀)
    (hJu J u₀ hu₀) s (J x) (fun r => J (v r)) hw (by simp only [hi])
  intro t
  apply J.injective
  rw [hu t, S_embed J K M A hA hK hs u₀ hu₀]

end Setup

end QuantumNLS.Prop022BClass1
