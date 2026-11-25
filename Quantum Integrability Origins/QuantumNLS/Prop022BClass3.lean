import Mathlib
import QuantumNLS.Prop022BClass2

/-! PROP-022 route A, finite-dimensional case, stage B3c: the classical conclusions 1-3 of Q7B:lem:pair
for a complex Hilbert space `H` embedded isometrically in `L2T L` (no finiteness of `H` is used), and the
independence of the embedding `J` (intrinsic: the gradient is the Riesz gradient of the symbol on `H`, the
trajectory is the unique unit solution, and `S_J` the unique solution of the variational equation). -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop022BClass3
open TensorCarrier PhysicalTensor Prop022GTensor Prop022AIsoTensor Prop022GAntiHS
open Prop022GClassical Prop022GLinear Prop022BIso Prop022BClass1 Prop022BClass2
open Prop022FactorialMajorantR115

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

section Indep
variable (J J' : H →ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hA : 0 ≤ A) (hK : KBound K M A)
  (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1)
include M A hA hK hs

theorem gradJ_indep : gradJ J' K = gradJ J K :=
  funext (fun v => eq_of_realDual
    ((hasFDerivAt_symbol J' K M A hA hK hs v).unique (hasFDerivAt_symbol J K M A hA hK hs v)))

theorem hessJ_indep : hessJ J' K = hessJ J K := by
  funext v
  unfold hessJ
  rw [gradJ_indep J J' K M A hA hK hs]

include u₀ hu₀

theorem profJ_indep :
    profJ J' K M A hA hK hs u₀ hu₀ = profJ J K M A hA hK hs u₀ hu₀ := by
  obtain ⟨h0, hd⟩ := profJ_spec J' K M A hA hK hs u₀ hu₀
  exact profJ_unique J K M A hA hK hs u₀ hu₀ _ h0 (fun t => by
    have h := hd t
    rw [gradJ_indep J J' K M A hA hK hs] at h
    exact h)

theorem SJ_indep (t s : ℝ) :
    SJ J' K M A hA hK hs u₀ hu₀ t s = SJ J K M A hA hK hs u₀ hu₀ t s := by
  ext x
  exact SJ_unique J K M A hA hK hs u₀ hu₀ s x (fun r => SJ J' K M A hA hK hs u₀ hu₀ r s x)
    (fun r => by
      have h := SJ_variational J' K M A hA hK hs u₀ hu₀ s r x
      rw [hessJ_indep J J' K M A hA hK hs, profJ_indep J J' K M A hA hK hs u₀ hu₀] at h
      exact h) (SJ_self J' K M A hA hK hs u₀ hu₀ s x) t

end Indep

section Main
variable (J : H →ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A)
  (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1)

include hM in
/-- **PROP-022 (Q7B:lem:pair), printed conclusions 1-3, through an isometric embedding `J : H → L2T L`.** -/
theorem PROP022_J_classical (T P : ℝ) (hP : 1 ≤ P) {ι : Type*} (e : HilbertBasis ι ℂ H) :
    let F := symbolH K
    let grad := gradJ J K
    let Φ := flowJ J K M A hA.le hK hs
    let u := profJ J K M A hA.le hK hs u₀ hu₀
    let S := SJ J K M A hA.le hK hs u₀ hu₀
    let a := aJ J K M A hA.le hK hs u₀ hu₀
    let b := bJ J K M A hA.le hK hs u₀ hu₀
    let α := alphaJ J K M A hA.le hK hs u₀ hu₀
    let β := betaJ J K M A hA.le hK hs u₀ hu₀
    (∀ v, HasFDerivAt F (realDual (grad v)) v) ∧
    (∀ v, F v = Prop022ClassicalTimeR116.classicalSeries (BL (UI L) (kernelsI J K)) (J v)) ∧
    (∀ x, Φ 0 x = x ∧ ∀ t, HasDerivAt (fun r => Φ r x) ((-Complex.I) • grad (Φ t x)) t ∧
      ‖Φ t x‖ = ‖x‖) ∧
    (u 0 = u₀ ∧ ∀ t, ‖u t‖ = 1 ∧ HasDerivAt u ((-Complex.I) • grad (u t)) t) ∧
    (∀ γ : ℝ → H, γ 0 = u₀ → (∀ t, ‖γ t‖ = 1 ∧ HasDerivAt γ ((-Complex.I) • grad (γ t)) t) →
      γ = u) ∧
    (∀ s t, Φ (t - s) (u s) = u t) ∧
    (∀ t s, S t s = fderiv ℝ (Φ (t - s)) (u s)) ∧
    (∀ t, CLinear (a t) ∧ (∀ x y, ⟪x, a t y⟫_ℂ = ⟪a t x, y⟫_ℂ) ∧
      Antilinear (b t) ∧ (∀ x y, ⟪x, b t y⟫_ℂ = ⟪y, b t x⟫_ℂ) ∧
      antiHS e (b t) ≠ ⊤ ∧ Real.sqrt ((antiHS e (b t)).toReal) ≤ pairMajorant A * M ∧
      ‖a t‖ ≤ M * ∑' r : ℕ,
        (((r+1 : ℕ) : ℝ)^2 * A^(r+1) / Real.sqrt ((2*(r+1)).factorial : ℝ))) ∧
    (∀ s t x, Complex.I • deriv (fun r => S r s x) t = a t (S t s x) + b t (S t s x)) ∧
    (∀ t s, S t s = α t s + β t s ∧ CLinear (α t s) ∧ Antilinear (β t s)) ∧
    ((∀ r q : ℝ, |r| ≤ T → |q| ≤ T → ‖S r q‖ ≤ P) → ∀ t, |t| ≤ T →
      antiHS e (β t 0) ≠ ⊤ ∧
        Real.sqrt ((antiHS e (β t 0)).toReal) ≤ |t| * pairMajorant A * M * P) ∧
    (∀ J' : H →ₗᵢ[ℂ] L2T L, gradJ J' K = grad ∧
      profJ J' K M A hA.le hK hs u₀ hu₀ = u ∧
      SJ J' K M A hA.le hK hs u₀ hu₀ = S ∧ aJ J' K M A hA.le hK hs u₀ hu₀ = a ∧
      bJ J' K M A hA.le hK hs u₀ hu₀ = b ∧ alphaJ J' K M A hA.le hK hs u₀ hu₀ = α ∧
      betaJ J' K M A hA.le hK hs u₀ hu₀ = β) := by
  intro F grad Φ u S a b α β
  obtain ⟨wb, c, -⟩ := exists_hilbertBasis ℂ (L2T L)
  have hHS : ∀ t, antiHS e (bJ J K M A hA.le hK hs u₀ hu₀ t) =
      antiHS c (bH (UI L) (kernelsI J K) M A hA.le (hKJ J K M A hK) (hsJ J K hs) (J u₀)
        (hJu J u₀ hu₀) t) := by
    intro t
    rw [bH'_eq J K M A hA.le hK hs u₀ hu₀ t]
    exact antiHS_embed J e c _ (antilinearPart_antilinear _)
  have hHSb : ∀ t, antiHS e (betaJ J K M A hA.le hK hs u₀ hu₀ t 0) =
      antiHS c (betaH (UI L) (kernelsI J K) M A hA.le (hKJ J K M A hK) (hsJ J K hs) (J u₀)
        (hJu J u₀ hu₀) t 0) := by
    intro t
    rw [betaH'_eq J K M A hA.le hK hs u₀ hu₀ t 0]
    exact antiHS_embed J e c _ (antilinearPart_antilinear _)
  refine ⟨fun v => hasFDerivAt_symbol J K M A hA.le hK hs v, fun v => ?_,
    fun x => flowJ_spec J K M A hA.le hK hs x, profJ_spec J K M A hA.le hK hs u₀ hu₀,
    fun γ h0 hγ => profJ_unique J K M A hA.le hK hs u₀ hu₀ γ h0 hγ,
    fun s t => flowJ_profJ J K M A hA.le hK hs u₀ hu₀ s t, fun t s => rfl, fun t => ?_,
    fun s t x => ?_, fun t s => ?_, fun hS t ht => ?_, fun J' => ?_⟩
  · have h := symbolH_eq (UI L) (kernelsI J K) (J v)
    rw [symbolH_kernelsI, Jadj_J] at h
    exact h
  · obtain ⟨h1, h2, h3⟩ := bH_bounds (UI L) (kernelsI J K) M A hA.le (hKJ J K M A hK)
      (hsJ J K hs) (J u₀) (hJu J u₀ hu₀) c t
    refine ⟨complexPart_clinear _, fun x y => ?_, antilinearPart_antilinear _, fun x y => ?_, ?_, ?_, ?_⟩
    · change ⟪x, aJ J K M A hA.le hK hs u₀ hu₀ t y⟫_ℂ = ⟪aJ J K M A hA.le hK hs u₀ hu₀ t x, y⟫_ℂ
      rw [aJ_eq J K M A hA.le hK hs u₀ hu₀ t]
      simp only [ContinuousLinearMap.comp_apply, Jr_apply, Jar_apply]
      rw [inner_Jadj_right, aH_hermitian (UI L) (kernelsI J K) M A hA.le (hKJ J K M A hK)
        (hsJ J K hs) (J u₀) (hJu J u₀ hu₀) t (J x) (J y), inner_Jadj_left]
    · change ⟪x, bJ J K M A hA.le hK hs u₀ hu₀ t y⟫_ℂ = ⟪y, bJ J K M A hA.le hK hs u₀ hu₀ t x⟫_ℂ
      rw [bJ_eq J K M A hA.le hK hs u₀ hu₀ t]
      simp only [ContinuousLinearMap.comp_apply, Jr_apply, Jar_apply]
      rw [inner_Jadj_right, bH_symmetric (UI L) (kernelsI J K) M A hA.le (hKJ J K M A hK)
        (hsJ J K hs) (J u₀) (hJu J u₀ hu₀) t (J x) (J y), inner_Jadj_right]
    · rw [hHS t]; exact h1
    · rw [hHS t]; exact h2
    · change ‖aJ J K M A hA.le hK hs u₀ hu₀ t‖ ≤ _
      rw [aJ_eq J K M A hA.le hK hs u₀ hu₀ t]
      exact (norm_compress_le J _).trans h3
  · have h := SJ_variational J K M A hA.le hK hs u₀ hu₀ s t x
    rw [h.deriv, smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
    have hp := congrArg (fun T : H →L[ℝ] H => T (SJ J K M A hA.le hK hs u₀ hu₀ t s x))
      (Ext006Blocks.parts_sum (hessJ J K (profJ J K M A hA.le hK hs u₀ hu₀ t)))
    simp only [ContinuousLinearMap.add_apply] at hp
    exact hp.symm
  · exact ⟨(Ext006Blocks.parts_sum _).symm, complexPart_clinear _, antilinearPart_antilinear _⟩
  · have hS' : ∀ r q : ℝ, |r| ≤ T → |q| ≤ T →
        ‖SH (UI L) (kernelsI J K) M A hA.le (hKJ J K M A hK) (hsJ J K hs) (J u₀)
          (hJu J u₀ hu₀) r q‖ ≤ P := fun r q hr hq =>
      norm_S'_le J K M A hA.le hK hs u₀ hu₀ T P hP r q (hS r q hr hq)
    obtain ⟨h1, h2⟩ := beta_estimate (UI L) (kernelsI J K) M A hA.le (hKJ J K M A hK)
      (hsJ J K hs) (J u₀) (hJu J u₀ hu₀) hM c T P hP hS' t ht
    rw [hHSb t]
    exact ⟨h1, h2⟩
  · refine ⟨gradJ_indep J J' K M A hA.le hK hs, profJ_indep J J' K M A hA.le hK hs u₀ hu₀,
      funext (fun t => funext (fun s => SJ_indep J J' K M A hA.le hK hs u₀ hu₀ t s)),
      funext (fun t => ?_), funext (fun t => ?_), funext (fun t => funext (fun s => ?_)),
      funext (fun t => funext (fun s => ?_))⟩
    · unfold aJ
      rw [hessJ_indep J J' K M A hA.le hK hs, profJ_indep J J' K M A hA.le hK hs u₀ hu₀]
      rfl
    · unfold bJ
      rw [hessJ_indep J J' K M A hA.le hK hs, profJ_indep J J' K M A hA.le hK hs u₀ hu₀]
      rfl
    · unfold alphaJ
      rw [SJ_indep J J' K M A hA.le hK hs u₀ hu₀]
      rfl
    · unfold betaJ
      rw [SJ_indep J J' K M A hA.le hK hs u₀ hu₀]
      rfl

end Main

end QuantumNLS.Prop022BClass3

#print axioms QuantumNLS.Prop022BClass3.PROP022_J_classical
