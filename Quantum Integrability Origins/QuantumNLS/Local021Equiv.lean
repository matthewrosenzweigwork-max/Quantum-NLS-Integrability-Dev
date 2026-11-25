import Mathlib
import QuantumNLS.ResetMoserProcedure
import QuantumNLS.Local021Mono
import QuantumNLS.Local021Haar

/-!
# LOCAL-021, stage 3: the radial-primitive / Haar / Moser procedure is equivariant

Source: `local_covariance.tex:152-185`.  For a monomial operator `U` (stage 1) with `U^*Ω = εΩ` on `B_R` for the form `Ω` of the
LOCAL-017 procedure (`PrintedHyp P`, bounds `B`):

* `beta_cov`  : the radial primitive `β = betaR (toHyp P)` satisfies `β_{Uz}(Uh) = ε β_z(h)`;
* `f_cov`     : the Haar primitive `f = LOCAL017Haar.primitive β` satisfies `f(Uz) = ε f(z)` (stage 2);
* `beta0_cov` : `β⁰ = β - df` satisfies `β⁰_{Uz}(Uh) = ε β⁰_z(h)`;
* `moserY_cov`: the Moser field `Y_t = P.moserY t` (the unique solution of `ι_{Y_t}[ω + t(Ω-ω)] = -β⁰`) satisfies `Y_t(Uz) = U Y_t(z)`;
* `Sm_cov`, `Si_cov` : the time-one flow `S = MD.Sfl 1` and its inverse `S⁻¹ = MD.Tinv` of the LOCAL-017 procedure commute with `U`
  (ODE uniqueness, `MoserData.flow_unique`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric

namespace QuantumNLS.Local021

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.ResetMoser QuantumNLS.ResetMoserClamp

/-- precomposition with `U` as a continuous linear equivalence of covectors. -/
def Ucov (U : Mono) : Cov ≃L[ℝ] Cov := U.cle.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)

theorem Ucov_apply (U : Mono) (φ : Cov) (h : K) : Ucov U φ h = φ (U.act h) := rfl

theorem cle_intervalIntegral {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : E ≃L[ℝ] F) (f : ℝ → E) (a b : ℝ) :
    ∫ t in a..b, L (f t) = L (∫ t in a..b, f t) := by
  simp only [intervalIntegral, ContinuousLinearEquiv.integral_comp_comm, map_sub]

/-- `U^*Ω = εΩ` on `B_R`. -/
def CovΩ (P : PrintedHyp) (U : Mono) : Prop :=
  ∀ y ∈ ball (0 : K) P.R, ∀ v w : K, P.Ω (U.act y) (U.act v) (U.act w) = U.eps * P.Ω y v w

theorem fderiv_eps_mul (U : Mono) (g : K → ℝ) (x : K) :
    fderiv ℝ (fun y => U.eps * g y) x = U.eps • fderiv ℝ g x := by
  unfold Mono.eps
  split_ifs
  · have : (fun y => (-1 : ℝ) * g y) = fun y => -g y := by funext y; ring
    rw [this, fderiv_fun_neg]; exact (neg_one_smul ℝ _).symm
  · simp

variable (P : PrintedHyp)

theorem beta_cov (U : Mono) (hU : CovΩ P U) {z : K} (hz : z ∈ ball (0 : K) P.R) (h : K) :
    betaR P.toHyp (U.act z) (U.act h) = U.eps * betaR P.toHyp z h := by
  rw [P.betaR_toHyp (U.mem_ball hz), P.betaR_toHyp hz]
  unfold PrintedHyp.betaP
  have key : ∫ t in (0 : ℝ)..1, Ucov U (t • ((P.Ω (t • U.act z) - omegaF) (U.act z))) =
      ∫ t in (0 : ℝ)..1, U.eps • (t • ((P.Ω (t • z) - omegaF) z)) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    have htz : t • z ∈ ball (0 : K) P.R := scale_mem' hz ht
    ext h'
    simp only [Ucov_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.sub_apply]
    have e1 : t • U.act z = U.act (t • z) := by
      have := U.act_smul_real t z
      exact this.symm
    rw [e1, hU _ htz, omegaF_apply, omegaF_apply, Mono.omega_act]
    ring
  have h1 := cle_intervalIntegral (Ucov U) (fun t => t • ((P.Ω (t • U.act z) - omegaF) (U.act z))) 0 1
  rw [key, intervalIntegral.integral_smul] at h1
  have h2 := congrArg (fun φ : Cov => φ h) h1
  simp only [Ucov_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at h2
  exact h2.symm

variable {P}

theorem f_cov (B : PrintedBounds P) (U : Mono) (hU : CovΩ P U) {z : K} (hz : z ∈ ball (0 : K) B.radius) :
    QuantumNLS.LOCAL017Haar.primitive (betaR P.toHyp) (U.act z) =
      U.eps * QuantumNLS.LOCAL017Haar.primitive (betaR P.toHyp) z := by
  refine primitive_equivariant U (betaR P.toHyp) (R := B.radius) ?_ ?_ hz
  · intro y hy
    exact (betaR_hasFDerivAt P.toHyp B.toNative.loc hy).continuousAt.continuousWithinAt
  · intro y hy h
    exact beta_cov P U hU (ball_subset_ball B.ρR hy) h

theorem beta0_cov (B : PrintedBounds P) (U : Mono) (hU : CovΩ P U) {z : K} (hz : z ∈ ball (0 : K) B.radius)
    (h : K) :
    QuantumNLS.LOCAL017Haar.beta0 (betaR P.toHyp) (U.act z) (U.act h) =
      U.eps * QuantumNLS.LOCAL017Haar.beta0 (betaR P.toHyp) z h := by
  unfold QuantumNLS.LOCAL017Haar.beta0
  simp only [ContinuousLinearMap.sub_apply]
  rw [beta_cov P U hU (ball_subset_ball B.ρR hz) h]
  set f := QuantumNLS.LOCAL017Haar.primitive (betaR P.toHyp) with hf
  have hev : (f ∘ U.cle) =ᶠ[𝓝 z] fun x => U.eps * f x := by
    filter_upwards [isOpen_ball.mem_nhds hz] with x hx
    exact f_cov B U hU hx
  have h1 : fderiv ℝ (f ∘ U.cle) z = fderiv ℝ (fun x => U.eps * f x) z := hev.fderiv_eq
  rw [U.cle.comp_right_fderiv, fderiv_eps_mul] at h1
  have h2 := congrArg (fun φ : K →L[ℝ] ℝ => φ h) h1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at h2
  have : (↑U.cle : K →L[ℝ] K) h = U.act h := rfl
  rw [show (U.cle z : K) = U.act z from rfl, this] at h2
  rw [h2]; ring

theorem norm_D_lt (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) {z : K} (hz : z ∈ ball (0 : K) P.R) :
    ‖t • (P.Ω z - omegaF)‖ < 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  have := P.Ω_lt z hz
  nlinarith [ht.2, norm_nonneg (P.Ω z - omegaF)]

theorem moserY_cov (B : PrintedBounds P) (U : Mono) (hU : CovΩ P U) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {z : K}
    (hz : z ∈ ball (0 : K) B.radius) : P.moserY t (U.act z) = U.act (P.moserY t z) := by
  have hzP : z ∈ ball (0 : K) P.R := ball_subset_ball B.ρR hz
  have hUzB : U.act z ∈ ball (0 : K) B.radius := U.mem_ball hz
  have hUzP : U.act z ∈ ball (0 : K) P.R := ball_subset_ball B.ρR hUzB
  have hiota : ∀ (w : K) (hw : w ∈ ball (0 : K) P.R) (h : K),
      omega (P.moserY t w) h + (t • (P.Ω w - omegaF)) (P.moserY t w) h =
        -(QuantumNLS.LOCAL017Haar.beta0 (betaR P.toHyp) w h) := fun w hw h =>
    iota_Ycov (norm_D_lt t ht hw) _ h
  set Y := P.moserY t z with hY
  set Y' := P.moserY t (U.act z) with hY'
  have hpair : ∀ k : K, omega (Y' - U.act Y) k + (t • (P.Ω (U.act z) - omegaF)) (Y' - U.act Y) k = 0 := by
    intro k
    set h' := U.inv.act k with hh'
    have hk : k = U.act h' := (U.act_inv_act k).symm
    have a1 := hiota (U.act z) hUzP k
    have a2 := hiota z hzP h'
    have b := beta0_cov B U hU hz h'
    rw [← hk] at b
    have e1 : omega (U.act Y) k + (t • (P.Ω (U.act z) - omegaF)) (U.act Y) k =
        U.eps * (omega Y h' + (t • (P.Ω z - omegaF)) Y h') := by
      rw [hk, Mono.omega_act]
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, smul_eq_mul]
      rw [hU z hzP, omegaF_apply, omegaF_apply, Mono.omega_act]
      ring
    have lin : omega (Y' - U.act Y) k + (t • (P.Ω (U.act z) - omegaF)) (Y' - U.act Y) k =
        (omega Y' k + (t • (P.Ω (U.act z) - omegaF)) Y' k) -
          (omega (U.act Y) k + (t • (P.Ω (U.act z) - omegaF)) (U.act Y) k) := by
      rw [omega_sub_left, map_sub, ContinuousLinearMap.sub_apply]; ring
    rw [lin, e1, a1, a2, b]; ring
  have hD : ‖(omegaF + t • (P.Ω (U.act z) - omegaF)) - omegaF‖ < 1 := by
    rw [add_sub_cancel_left]; exact norm_D_lt t ht hUzP
  have h0 : Y' - U.act Y = 0 := by
    refine PrintedHyp.eq_zero_of_pairing hD fun k => ?_
    simp only [ContinuousLinearMap.add_apply, omegaF_apply]
    exact hpair k
  exact sub_eq_zero.1 h0

theorem Yf_cov (B : PrintedBounds P) (U : Mono) (hU : CovΩ P U) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {z : K}
    (hz : z ∈ ball (0 : K) (moserR0 B.radius B.realConstant)) :
    (moserDataN P.toHyp B.toNative).Yf t (U.act z) = U.act ((moserDataN P.toHyp B.toNative).Yf t z) := by
  have hR : moserR0 B.radius B.realConstant ≤ B.radius := moserR0_le_R P.toHyp B.toNative
  have hzB : z ∈ ball (0 : K) B.radius := ball_subset_ball hR hz
  have hzP : z ∈ ball (0 : K) P.R := ball_subset_ball B.ρR hzB
  rw [← P.moserY_eq_Yf B t (U.mem_ball hzP), ← P.moserY_eq_Yf B t hzP]
  exact moserY_cov B U hU ht hzB

/-- `S(Uz) = U S(z)` on `B_r`. -/
theorem Sm_cov (B : PrintedBounds P) (U : Mono) (hU : CovΩ P U) {z : K}
    (hz : ‖z‖ < (moserDataN P.toHyp B.toNative).R0 / 4) :
    (moserDataN P.toHyp B.toNative).Sfl 1 (U.act z) = U.act ((moserDataN P.toHyp B.toNative).Sfl 1 z) := by
  set MD := moserDataN P.toHyp B.toNative with hMD
  have hR0 : MD.R0 = moserR0 B.radius B.realConstant := rfl
  have hpos : 0 < MD.R0 := MD.R0_pos
  have hder : ∀ t, HasDerivAt (fun s => U.act (MD.Sfl s z)) (U.act (MD.Yf (sig t) (MD.Sfl t z))) t := fun t =>
    (U.cle.toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt t (MD.Sfl_deriv hz.le t)
  have hU' : ‖U.act z‖ < MD.R0 / 4 := by rwa [U.norm_act]
  have := MD.flow_unique hU' (γ := fun s => U.act (MD.Sfl s z)) (by simp [MD.Sfl_zero])
    (fun t _ => (hder t).continuousAt.continuousWithinAt)
    (fun t ht => by
      have h1 := (hder t).hasDerivWithinAt (s := Ici t)
      rw [sig_eq (s := t) ⟨by linarith [ht.1], by linarith [ht.2]⟩] at h1
      have hmem : MD.Sfl t z ∈ ball (0 : K) MD.R0 := by
        rw [mem_ball_zero_iff, MD.norm_Sfl]; linarith
      rw [Yf_cov B U hU ⟨ht.1, ht.2.le⟩ (by rw [← hR0]; exact hmem)]
      exact h1)
    (fun t _ => by
      rw [mem_ball_zero_iff, U.norm_act, MD.norm_Sfl]; linarith) 1 ⟨zero_le_one, le_rfl⟩
  exact this.symm

/-- `S⁻¹(Uw) = U S⁻¹(w)` on `B_r`. -/
theorem Si_cov (B : PrintedBounds P) (U : Mono) (hU : CovΩ P U) {w : K}
    (hw : ‖w‖ < (moserDataN P.toHyp B.toNative).R0 / 4) :
    (moserDataN P.toHyp B.toNative).Tinv (U.act w) = U.act ((moserDataN P.toHyp B.toNative).Tinv w) := by
  set MD := moserDataN P.toHyp B.toNative with hMD
  have h1 : ‖MD.Tinv w‖ < MD.R0 / 4 := by rwa [MD.norm_Tinv]
  have h2 := Sm_cov B U hU h1
  have e : w = MD.Sfl 1 (MD.Tinv w) := (MD.Sfl_one_Tinv w).symm
  calc MD.Tinv (U.act w) = MD.Tinv (U.act (MD.Sfl 1 (MD.Tinv w))) := by rw [← e]
    _ = MD.Tinv (MD.Sfl 1 (U.act (MD.Tinv w))) := by rw [h2]
    _ = U.act (MD.Tinv w) := MD.Tinv_Sfl_one _

end QuantumNLS.Local021

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.Local021.beta_cov
#print axioms QuantumNLS.Local021.f_cov
#print axioms QuantumNLS.Local021.beta0_cov
#print axioms QuantumNLS.Local021.moserY_cov
#print axioms QuantumNLS.Local021.Sm_cov
#print axioms QuantumNLS.Local021.Si_cov
