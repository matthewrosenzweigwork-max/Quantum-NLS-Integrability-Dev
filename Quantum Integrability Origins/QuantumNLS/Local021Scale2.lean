import Mathlib
import QuantumNLS.ResetMoserProcedure
import QuantumNLS.Local021Mono
import QuantumNLS.Local021Haar
import QuantumNLS.Local021Equiv
import QuantumNLS.Local021Scale
import QuantumNLS.Local021ScaleAux

/-!
# LOCAL-021, stage 4a: coupling scaling of `β⁰` and `Y_t`

Source: `local_covariance.tex:193-215`: "As bilinear forms, `Ω_{κ,z} = Ω_{1,√κ z}`.  The radial primitive has the corresponding homogeneity, its
scalar Haar integral has `f_κ(z) = κ^{-1} f_1(√κ z)`, and the defining linear equation gives `Y_{κ,t}(z) = κ^{-1/2} Y_{1,t}(√κ z)`.
Consequently `S_κ` and `Φ_κ` have the same scaling relation."

Here two instances `(PA, BA)` (coupling `κ`) and `(PB, BB)` (coupling `κ s²`) of the LOCAL-017 procedure are compared, given
`ScaleΩ PA PB s` (`Ω^A_{s y} = Ω^B_y` as bilinear forms on the common domain):

* `beta_scale`  : `β^A_{s z} = s β^B_z`;   `f_scale` : `f^A(s z) = s² f^B(z)`;   `beta0_scale` : `β⁰^A_{s z} = s β⁰^B_z`;
* `moserY_scale`: `Y^A_t(s z) = s Y^B_t(z)`;
* `Sm_scale`, `Si_scale` : `S^A(s z) = s S^B(z)`, `(S^A)⁻¹(s w) = s (S^B)⁻¹(w)`.
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
open QuantumNLS.Ext025B7LocalPath QuantumNLS.LOCAL017Haar

variable {PA PB : PrintedHyp}

theorem beta0_scale {s : ℝ} (hs : 0 < s) (h : ScaleΩ PA PB s) {z : K} (hz : z ∈ ball (0 : K) PB.R)
    (hsz : s • z ∈ ball (0 : K) PA.R) :
    beta0 (betaR PA.toHyp) (s • z) = s • beta0 (betaR PB.toHyp) z := by
  unfold beta0
  rw [beta_scale hs h hz hsz, smul_sub, sub_right_inj]
  have hm1 : ∀ᶠ x in 𝓝 z, x ∈ ball (0 : K) PB.R := isOpen_ball.mem_nhds hz
  have hcont : ContinuousAt (fun x : K => s • x) z := (continuous_id.const_smul s).continuousAt
  have hm2 : ∀ᶠ x in 𝓝 z, s • x ∈ ball (0 : K) PA.R := hcont.preimage_mem_nhds (isOpen_ball.mem_nhds hsz)
  have hev : (fun x => primitive (betaR PA.toHyp) (s • x)) =ᶠ[𝓝 z]
      fun x => s ^ 2 • primitive (betaR PB.toHyp) x := by
    filter_upwards [hm1, hm2] with x hx1 hx2
    have := f_scale hs h hx1 hx2
    rw [smul_eq_mul]
    exact this
  have h1 := fderiv_smul_scale (f := primitive (betaR PA.toHyp)) (g := primitive (betaR PB.toHyp)) (z := z) hs.ne'
    (pow_ne_zero 2 hs.ne') hev
  have e : s⁻¹ * s ^ 2 = s := by field_simp
  rw [e] at h1
  exact h1


theorem moserY_scale (BA : PrintedBounds PA) (BB : PrintedBounds PB) {s : ℝ} (hs : 0 < s) (h : ScaleΩ PA PB s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {z : K} (hz : z ∈ ball (0 : K) PB.R) (hsz : s • z ∈ ball (0 : K) PA.R) :
    PA.moserY t (s • z) = s • PB.moserY t z := by
  have hiota : ∀ (P : PrintedHyp) (w : K) (hw : w ∈ ball (0 : K) P.R) (k : K),
      omega (P.moserY t w) k + (t • (P.Ω w - omegaF)) (P.moserY t w) k =
        -(beta0 (betaR P.toHyp) w k) := fun P w hw k =>
    iota_Ycov (norm_D_lt t ht hw) _ k
  set Y := PB.moserY t z with hY
  set Y' := PA.moserY t (s • z) with hY'
  have hpair : ∀ k : K, omega (Y' - s • Y) k + (t • (PA.Ω (s • z) - omegaF)) (Y' - s • Y) k = 0 := by
    intro k
    have a1 := hiota PA (s • z) hsz k
    have a2 := hiota PB z hz k
    have b := beta0_scale hs h hz hsz
    have b' := congrArg (fun φ : ResetMoser.Cov => φ k) b
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul] at b'
    have hΩ := h z hz hsz
    have e1 : omega (s • Y) k + (t • (PA.Ω (s • z) - omegaF)) (s • Y) k =
        s * (omega Y k + (t • (PB.Ω z - omegaF)) Y k) := by
      rw [hΩ]
      have : omega (s • Y) k = s * omega Y k := by
        rw [← Jw_apply, ← Jw_apply, ContinuousLinearEquiv.map_smul]; simp
      have h2 : (t • (PB.Ω z - omegaF)) (s • Y) k = s * (t • (PB.Ω z - omegaF)) Y k := by
        rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [this, h2]; ring
    have lin : omega (Y' - s • Y) k + (t • (PA.Ω (s • z) - omegaF)) (Y' - s • Y) k =
        (omega Y' k + (t • (PA.Ω (s • z) - omegaF)) Y' k) -
          (omega (s • Y) k + (t • (PA.Ω (s • z) - omegaF)) (s • Y) k) := by
      rw [omega_sub_left, map_sub, ContinuousLinearMap.sub_apply]; ring
    rw [lin, e1, a1, a2, b']; ring
  have hD : ‖(omegaF + t • (PA.Ω (s • z) - omegaF)) - omegaF‖ < 1 := by
    rw [add_sub_cancel_left]; exact norm_D_lt t ht hsz
  have h0 : Y' - s • Y = 0 := by
    refine PrintedHyp.eq_zero_of_pairing hD fun k => ?_
    simp only [ContinuousLinearMap.add_apply, omegaF_apply]
    exact hpair k
  exact sub_eq_zero.1 h0

end QuantumNLS.Local021

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.Local021.beta0_scale
#print axioms QuantumNLS.Local021.moserY_scale
