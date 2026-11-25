import QuantumNLS.D01ReconCore
import QuantumNLS.TerraMultiRound19D01Full

/-!
# `thm:global-D01-reconstruction` (R-701613DA), part 2: analyticity, symplecticity, `Φ^*ᾱ = ᾱ`, bounded inverse differential

Source: `liouville_reconstruction.tex`, proof of Theorem `thm:global-D01-reconstruction` (lines 296-382): "For each fixed `u`, choose `t` with the strict inequality ... The same `t` works throughout an open neighborhood of `u`, because the norm is continuous.  On that neighborhood `Φ` is a finite composition of real-analytic maps ... `Φ^*ω_K = e^t F_{-t}^*(φ^*ω_K) = e^t F_{-t}^*ω_H = ω_H`, `Φ^*α_K = e^t F_{-t}^*(φ^*α_K) = e^t F_{-t}^* ᾱ = ᾱ` ... the chain rule in the full Hilbert spaces shows `DΨ(Φ(u))DΦ(u) = Id_H`, `DΦ(u)DΨ(Φ(u)) = Id_K`."

Carried hypothesis (named, open): `GP04CompactLocalAnalyticity S` (terra_multi's `TerraMultiRound18AnalyticFlow.GP04CompactLocalAnalyticity`, the GP-04 analytic-initial-dependence remainder being proved by Sol r92). It is exactly the open premise of R-B390B5E9 as packaged in `TerraMultiRound19D01Full.global_D01_completeness`; through it
`analytic_initial_dependence` (`F_t` real analytic), `conformal_symplectic` (`F_t^*ω_H = e^t ω_H`) and `one_form_pullback` (`F_t^*ᾱ = e^t ᾱ`) are used, read-only.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology
open Filter Set

namespace QuantumNLS.D01Reconstruction

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.StrongSymplectic
open QuantumNLS.TerraMultiRound18Flow QuantumNLS.TerraMultiRound18AnalyticFlow
open QuantumNLS.TerraMultiRound18Pullbacks QuantumNLS.RealAnalyticDef

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Hyp H)

theorem omega_rsmul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (a : ℝ) (x y : E) :
    omega (a • x) (a • y) = a ^ 2 * omega x y := by
  unfold omega
  rw [← Complex.coe_smul, ← Complex.coe_smul, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  ring

theorem alphaF_rsmul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (a : ℝ) (x y : E) :
    alphaF (a • x) (a • y) = a ^ 2 * alphaF x y := by
  unfold alphaF
  rw [← Complex.coe_smul, ← Complex.coe_smul, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  ring

theorem exp_sq_mul (t : ℝ) : Real.exp (t / 2) ^ 2 * Real.exp (-t) = 1 := by
  have h0 : t / 2 + t / 2 + -t = 0 := by ring
  rw [pow_two, ← Real.exp_add, ← Real.exp_add, h0, Real.exp_zero]

/-! ## 1. Local structure of `Φ` and `Ψ` -/

theorem Phi_local (u0 : H) :
    ∃ t0 : ℝ, Adm S t0 ‖u0‖ ∧
      ∀ᶠ u in 𝓝 u0, Phi S u = Real.exp (t0 / 2) • S.phi (flow S (-t0) u) := by
  have hadm := tOf_adm S (norm_nonneg u0)
  refine ⟨tOf S ‖u0‖, hadm, ?_⟩
  have ho : IsOpen {u : H | Real.exp (-tOf S ‖u0‖ / 2) * ‖u‖ < S.ε} :=
    isOpen_lt (continuous_const.mul continuous_norm) continuous_const
  filter_upwards [ho.mem_nhds hadm.2] with u hu
  exact Phi_eq S ⟨hadm.1, hu⟩

variable {S}

theorem Phi_hasFDerivAt (ha : GP04CompactLocalAnalyticity S) (u0 : H) :
    ∃ t0 : ℝ, Adm S t0 ‖u0‖ ∧
      HasFDerivAt (Phi S) (Real.exp (t0 / 2) •
        (fderiv ℝ S.phi (flow S (-t0) u0)).comp (fderiv ℝ (flow S (-t0)) u0)) u0 := by
  obtain ⟨t0, ht0, hev⟩ := Phi_local S u0
  refine ⟨t0, ht0, ?_⟩
  have hv : flow S (-t0) u0 ∈ S.B := flow_mem S (by simpa [neg_div] using ht0.2)
  have h1 : HasFDerivAt S.phi (fderiv ℝ S.phi (flow S (-t0) u0)) (flow S (-t0) u0) :=
    (S.diff_phi hv).hasFDerivAt
  have h2 : HasFDerivAt (flow S (-t0)) (fderiv ℝ (flow S (-t0)) u0) u0 :=
    ((analytic_initial_dependence S ha (-t0) u0).differentiableAt).hasFDerivAt
  have h3 := (h1.comp u0 h2).const_smul (Real.exp (t0 / 2))
  exact h3.congr_of_eventuallyEq hev

theorem Phi_analyticAt (ha : GP04CompactLocalAnalyticity S) (u0 : H) : AnalyticAt ℝ (Phi S) u0 := by
  obtain ⟨t0, ht0, hev⟩ := Phi_local S u0
  have hv : flow S (-t0) u0 ∈ S.B := flow_mem S (by simpa [neg_div] using ht0.2)
  have h1 : AnalyticAt ℝ S.phi (flow S (-t0) u0) :=
    analyticAt_of_isRealAnalyticPoly (S.phi_analytic _ hv)
  have h2 : AnalyticAt ℝ (flow S (-t0)) u0 := analytic_initial_dependence S ha (-t0) u0
  have h3 : AnalyticAt ℝ (fun u => Real.exp (t0 / 2) • S.phi (flow S (-t0) u)) u0 := by
    have := (analyticAt_const (v := Real.exp (t0 / 2))).smul (h1.comp h2)
    exact this
  have hev' : Phi S =ᶠ[𝓝 u0] fun u => Real.exp (t0 / 2) • S.phi (flow S (-t0) u) := hev
  exact h3.congr hev'.symm

theorem Psi_analyticAt (ha : GP04CompactLocalAnalyticity S) (z0 : K) : AnalyticAt ℝ (Psi S) z0 := by
  have hadm := tOf_adm S (norm_nonneg z0)
  set t0 := tOf S ‖z0‖ with ht0
  have ho : IsOpen {z : K | Real.exp (-t0 / 2) * ‖z‖ < S.ε} :=
    isOpen_lt (continuous_const.mul continuous_norm) continuous_const
  have hev : ∀ᶠ z in 𝓝 z0, Psi S z = flow S t0 (S.psi (Real.exp (-t0 / 2) • z)) := by
    filter_upwards [ho.mem_nhds hadm.2] with z hz
    exact Psi_eq S ⟨hadm.1, hz⟩
  have hw : Real.exp (-t0 / 2) • z0 ∈ S.BK := smul_mem_BK S hadm.2
  have h1 : AnalyticAt ℝ S.psi (Real.exp (-t0 / 2) • z0) :=
    analyticAt_of_isRealAnalyticPoly (S.psi_analytic _ hw)
  have h2 : AnalyticAt ℝ (fun z : K => Real.exp (-t0 / 2) • z) z0 := by
    have := (analyticAt_const (v := Real.exp (-t0 / 2))).smul (analyticAt_id (𝕜 := ℝ) (E := K) (z := z0))
    exact this
  have h3 : AnalyticAt ℝ (flow S t0) (S.psi (Real.exp (-t0 / 2) • z0)) :=
    analytic_initial_dependence S ha t0 _
  have h5 : AnalyticAt ℝ (fun z : K => S.psi (Real.exp (-t0 / 2) • z)) z0 := h1.comp h2
  have h4 : AnalyticAt ℝ (fun z : K => flow S t0 (S.psi (Real.exp (-t0 / 2) • z))) z0 :=
    AnalyticAt.comp (f := fun z : K => S.psi (Real.exp (-t0 / 2) • z)) h3 h5
  have hev' : Psi S =ᶠ[𝓝 z0] fun z : K => flow S t0 (S.psi (Real.exp (-t0 / 2) • z)) := hev
  exact h4.congr hev'.symm

/-! ## 2. The pullback identities -/

theorem Phi_symp (ha : GP04CompactLocalAnalyticity S) (u h k : H) :
    omega (fderiv ℝ (Phi S) u h) (fderiv ℝ (Phi S) u k) = omega h k := by
  obtain ⟨t0, ht0, hD⟩ := Phi_hasFDerivAt ha u
  have hv : flow S (-t0) u ∈ S.B := flow_mem S (by simpa [neg_div] using ht0.2)
  rw [hD.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  refine (omega_rsmul _ _ _).trans ?_
  rw [S.phi_symp _ hv, conformal_symplectic S ha (-t0) u h k, ← mul_assoc, exp_sq_mul, one_mul]

theorem Phi_alpha (ha : GP04CompactLocalAnalyticity S) (u h : H) :
    alphaF (Phi S u) (fderiv ℝ (Phi S) u h) = S.abar u h := by
  obtain ⟨t0, ht0, hD⟩ := Phi_hasFDerivAt ha u
  have hv : flow S (-t0) u ∈ S.B := flow_mem S (by simpa [neg_div] using ht0.2)
  rw [hD.fderiv, Phi_eq S ht0]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  refine (alphaF_rsmul _ _ _).trans ?_
  rw [S.local_primitive hv, one_form_pullback S ha (-t0) u h, ← mul_assoc, exp_sq_mul, one_mul]

/-! ## 3. Strong symplecticity and the bounded inverse differential -/

theorem Psi_Phi_funext : (Psi S) ∘ (Phi S) = id := funext (Psi_Phi S)

theorem Phi_Psi_funext : (Phi S) ∘ (Psi S) = id := funext (Phi_Psi S)

theorem dPsi_dPhi (ha : GP04CompactLocalAnalyticity S) (u : H) :
    (fderiv ℝ (Psi S) (Phi S u)).comp (fderiv ℝ (Phi S) u) = ContinuousLinearMap.id ℝ H := by
  have h := fderiv_comp u ((Psi_analyticAt ha (Phi S u)).differentiableAt)
    ((Phi_analyticAt ha u).differentiableAt)
  rw [Psi_Phi_funext, fderiv_id] at h
  exact h.symm

theorem dPhi_dPsi (ha : GP04CompactLocalAnalyticity S) (u : H) :
    (fderiv ℝ (Phi S) u).comp (fderiv ℝ (Psi S) (Phi S u)) = ContinuousLinearMap.id ℝ K := by
  have h := fderiv_comp (Phi S u) (g := Phi S) (f := Psi S)
    (by rw [Psi_Phi]; exact (Phi_analyticAt ha u).differentiableAt)
    ((Psi_analyticAt ha (Phi S u)).differentiableAt)
  rw [Phi_Psi_funext, fderiv_id, Psi_Phi] at h
  exact h.symm

theorem Phi_stronglySymplectic (ha : GP04CompactLocalAnalyticity S) :
    IsStronglySymplectic (Phi S) where
  exists_inverse := ⟨Psi S, Psi_Phi S, Phi_Psi S, fun z => (Psi_analyticAt ha z).differentiableAt⟩
  differentiable := fun u => (Phi_analyticAt ha u).differentiableAt
  deriv_iso := fun u => ⟨ContinuousLinearEquiv.equivOfInverse (fderiv ℝ (Phi S) u)
    (fderiv ℝ (Psi S) (Phi S u))
    (fun h => by
      have := congrArg (fun T => T h) (dPsi_dPhi ha u)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
      exact this)
    (fun k => by
      have := congrArg (fun T => T k) (dPhi_dPsi ha u)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
      exact this), rfl⟩
  symplectic := Phi_symp ha

end QuantumNLS.D01Reconstruction

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.D01Reconstruction.Phi_analyticAt
#print axioms QuantumNLS.D01Reconstruction.Psi_analyticAt
#print axioms QuantumNLS.D01Reconstruction.Phi_symp
#print axioms QuantumNLS.D01Reconstruction.Phi_alpha
#print axioms QuantumNLS.D01Reconstruction.dPsi_dPhi
#print axioms QuantumNLS.D01Reconstruction.dPhi_dPsi
#print axioms QuantumNLS.D01Reconstruction.Phi_stronglySymplectic
