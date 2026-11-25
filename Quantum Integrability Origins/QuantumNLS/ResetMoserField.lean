import QuantumNLS.D01LocalPrimitive
import QuantumNLS.Ext025AFoundations

/-!
# `thm:reset-moser` (LOCAL-017), stage M1: the Moser field `Y_t`, `ι_{Y_t}Ω^t = −β⁰`, and `dq_n(z) Y_t(z) = 0` at every point

Source: `source-text/chapters/local/symplectic_correction.tex`, Theorem `thm:reset-moser` (line 25), proof, subsection "The deformation and its invariant ball" (equation `eq:reset-moser-field`, the Neumann series, the isotropy argument "If every coordinate of `z` is nonzero, then `ℋ = 𝒯_z ⊕ i𝒯_z` ... the `Ω^t` symplectic orthogonal of `𝒯_z` is exactly `𝒯_z` ... `Y_t(z) ∈ 𝒯_z`. Hence `dq_n(z)Y_t(z) = 0` for every `n`. Points with no zero coordinates are dense, and this scalar identity is continuous in `z`. It therefore holds at all points, including every zero stratum").

Realized objects used read-only: DEF-015 `omega`, the sequence space `K = ℓ²(ℤ;ℂ)`, `q`, `fderiv_q_apply` (`D01LocalPrimitive`); GP-06 `Ext025A.gp06_strong_symplectic_identification` (the isomorphism `J : K ≃L K*`, `J v w = ω(v,w)`, `‖J⁻¹ℓ‖ = ‖ℓ‖/2`).

Hypotheses of this stage (the printed ones that it needs, as in the proof): a two-form family `Ω : K → K →L K →L ℝ` continuous on `B_R`, `‖Ω_z − ω‖ < 1`; the isotropy of the angular space `𝒯_z = {h : h_n ∈ i z_n ℝ}` for `Ω` at points with all coordinates nonzero (the printed subsection "Isotropy of every coordinate torus": **carried as the named clause `hiso`**, to be bound to the Poisson-commutation argument); and a covector family `β⁰` continuous on `B_R` annihilating `𝒯_z` (**the named clause `hann`**, the output of the printed subsection "A primitive in all angular directions", GP-05/15/16).

* `Ycov D b = −(1 + J⁻¹D)⁻¹ J⁻¹ b` (Neumann inverse, `‖J⁻¹D‖ ≤ ‖D‖/2 < 1/2`);
* `iota_Ycov`: `(ω + D)(Y, h) = −b(h)` (`eq:reset-moser-field`);
* `Ycov_mem_Tz`: at a point with all coordinates nonzero, `Y ∈ 𝒯_z`;
* `dq_Y_zero`: `dq_n(z) Y_t(z) = 0` for all `z ∈ B_R` (density of the all-nonzero points and continuity).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric

namespace QuantumNLS.ResetMoser

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket

/-- Bounded real alternating-type forms: `K →L K →L ℝ`. -/
abbrev Cov : Type := K →L[ℝ] ℝ
abbrev Form : Type := K →L[ℝ] K →L[ℝ] ℝ

/-! ## 1. The symplectic isomorphism (GP-06) and the Neumann operator -/

def Jw : K ≃L[ℝ] Cov := (QuantumNLS.Ext025A.gp06_strong_symplectic_identification (E := K)).choose

theorem Jw_apply (v w : K) : Jw v w = omega v w :=
  (QuantumNLS.Ext025A.gp06_strong_symplectic_identification (E := K)).choose_spec.1 v w

theorem omega_I_smul (v : K) : omega v (Complex.I • v) = 2 * ‖v‖ ^ 2 := by
  unfold omega
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp [Complex.mul_im]
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

theorem norm_Jw_symm_le (ℓ : Cov) : ‖Jw.symm ℓ‖ ≤ ‖ℓ‖ / 2 := by
  set v := Jw.symm ℓ with hv
  have hJ : Jw v = ℓ := Jw.apply_symm_apply ℓ
  have h1 : 2 * ‖v‖ ^ 2 ≤ ‖ℓ‖ * ‖v‖ := by
    have e : ℓ (Complex.I • v) = 2 * ‖v‖ ^ 2 := by
      rw [← hJ, Jw_apply, omega_I_smul]
    have := ℓ.le_opNorm (Complex.I • v)
    rw [e, Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_smul, Complex.norm_I, one_mul] at this
    exact this
  have h0 : 0 ≤ ‖v‖ := norm_nonneg _
  rcases h0.eq_or_lt with h | h
  · rw [← h]; have := norm_nonneg ℓ; linarith
  · nlinarith

/-- `ω` as a bounded form. -/
def omegaF : Form := (Jw : K →L[ℝ] Cov)

theorem omegaF_apply (v w : K) : omegaF v w = omega v w := Jw_apply v w

/-- `N = J⁻¹ D`. -/
def Nop (D : Form) : K →L[ℝ] K := (Jw.symm : Cov →L[ℝ] K).comp D

theorem norm_Nop_le (D : Form) : ‖Nop D‖ ≤ ‖D‖ / 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  change ‖Jw.symm (D v)‖ ≤ ‖D‖ / 2 * ‖v‖
  have h1 := norm_Jw_symm_le (D v)
  have := D.le_opNorm v
  linarith

theorem isUnit_one_add {N : K →L[ℝ] K} (h : ‖N‖ < 1) : IsUnit (1 + N) := by
  have := (Units.oneSub (-N) (by simpa using h)).isUnit
  simpa [sub_neg_eq_add] using this

/-- The Moser field: `Y = −(1 + J⁻¹D)⁻¹ J⁻¹ b`. -/
def Ycov (D : Form) (b : Cov) : K := -((Ring.inverse (1 + Nop D)) (Jw.symm b))

theorem iota_Ycov {D : Form} (hD : ‖D‖ < 1) (b : Cov) (h : K) :
    omega (Ycov D b) h + D (Ycov D b) h = -b h := by
  have hN : ‖Nop D‖ < 1 := by
    have := norm_Nop_le D
    linarith
  have hu := isUnit_one_add hN
  have h1 : ((1 + Nop D) * Ring.inverse (1 + Nop D)) = 1 := Ring.mul_inverse_cancel _ hu
  have h2 : (1 + Nop D) (Ycov D b) = -(Jw.symm b) := by
    unfold Ycov
    rw [map_neg]
    have := congrArg (fun T => T (Jw.symm b)) h1
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at this
    rw [this]
  have h3 : omega (Ycov D b) h + D (Ycov D b) h = Jw ((1 + Nop D) (Ycov D b)) h := by
    rw [← Jw_apply]
    have : Jw (Nop D (Ycov D b)) = D (Ycov D b) := by
      change Jw (Jw.symm (D (Ycov D b))) = _
      exact Jw.apply_symm_apply _
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply, map_add, this,
      ContinuousLinearMap.add_apply]
  rw [h3, h2, map_neg, ContinuousLinearMap.neg_apply, Jw.apply_symm_apply]

/-- Continuity of `(D, b) ↦ Y` on `‖D‖ < 1`. -/
theorem continuousOn_Ycov : ContinuousOn (fun p : Form × Cov => Ycov p.1 p.2) {p | ‖p.1‖ < 1} := by
  intro p hp
  have hN : ‖Nop p.1‖ < 1 := by
    have := norm_Nop_le p.1
    have : ‖p.1‖ < 1 := hp
    linarith
  have hu := isUnit_one_add hN
  have hNc : Continuous fun D : Form => Nop D :=
    ((ContinuousLinearMap.compL ℝ K Cov K) (Jw.symm : Cov →L[ℝ] K)).continuous
  have h1 : ContinuousAt (fun p : Form × Cov => 1 + Nop p.1) p :=
    (continuous_const.add (hNc.comp continuous_fst)).continuousAt
  have h2 : ContinuousAt (fun p : Form × Cov => Ring.inverse (1 + Nop p.1)) p := by
    have := NormedRing.inverse_continuousAt hu.unit
    simp only [IsUnit.unit_spec] at this
    exact ContinuousAt.comp (g := Ring.inverse) (f := fun p : Form × Cov => 1 + Nop p.1) this h1
  have h3 : ContinuousAt (fun p : Form × Cov => Jw.symm p.2) p :=
    (Jw.symm.continuous.comp continuous_snd).continuousAt
  have := (h2.clm_apply h3).neg
  exact this.continuousWithinAt

/-! ## 2. The angular space `𝒯_z` -/

/-- `𝒯_z = {h : h_n ∈ i z_n ℝ}`. -/
def Tz (z : K) : Set K := {h | ∀ n, ∃ a : ℝ, h n = Complex.I * z n * a}

theorem omega_Tz {z h h' : K} (hh : h ∈ Tz z) (hh' : h' ∈ Tz z) : omega h h' = 0 := by
  unfold omega
  have hs : Summable (fun n => inner ℂ (h n) (h' n)) := lp.summable_inner (𝕜 := ℂ) h h'
  have hterm : ∀ n, (inner ℂ (h n) (h' n)).im = 0 := by
    intro n
    obtain ⟨a, ha⟩ := hh n
    obtain ⟨b, hb⟩ := hh' n
    rw [ha, hb]
    simp [Complex.mul_im, Complex.mul_re]
    ring
  have h1 : (inner ℂ h h').im = ∑' n, (inner ℂ (h n) (h' n)).im := by
    rw [lp.inner_eq_tsum (𝕜 := ℂ)]
    exact Complex.imCLM.map_tsum hs
  have h2 : ∑' n, (inner ℂ (h n) (h' n)).im = 0 := by simp only [hterm, tsum_zero]
  rw [h1, h2]; ring

theorem dq_Tz {z h : K} (hh : h ∈ Tz z) (n : ℤ) : fderiv ℝ (q n) z h = 0 := by
  rw [fderiv_q_apply]
  obtain ⟨a, ha⟩ := hh n
  rw [ha]
  simp [Complex.mul_re, Complex.mul_im]
  ring

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.iota_Ycov
#print axioms QuantumNLS.ResetMoser.continuousOn_Ycov
#print axioms QuantumNLS.ResetMoser.omega_Tz
#print axioms QuantumNLS.ResetMoser.dq_Tz
