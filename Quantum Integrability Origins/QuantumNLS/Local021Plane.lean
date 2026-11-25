import Mathlib
import QuantumNLS.ResetMoserProcedure
import QuantumNLS.Local021Mono
import QuantumNLS.Local021Haar
import QuantumNLS.Local021Equiv

/-!
# LOCAL-021, stage 5: the correction fixes every Fourier plane pointwise

Source: `local_covariance.tex:174-191`: "On a single coordinate plane, `ζ` and its inverse restrict to the identity.  Thus the restriction of `Ω` to
that plane is `ω`.  The radial difference primitive vanishes on its tangent vectors, and the scalar Haar integral is zero on that plane.  Its derivative
in every plane-tangent direction is zero there.  The Moser field preserves each coordinate modulus, so a solution starting on this plane remains on it.
Its vector at that point is therefore a tangent vector in the plane.  Its defining equation, tested against every plane-tangent vector, has zero right
side; nondegeneracy of the restricted form forces the field to be zero.  Thus `S` fixes the plane pointwise."

`Plane k` is the plane `{c e_k}`; `PlaneOmega P B k` states that `Ω = ω` on plane tangents at plane points of `B_{ρ}` (`ρ = B.radius`).
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

/-- the coordinate plane `{c e_k}`. -/
def Plane (k : ℤ) : Set K := {y | ∀ n, n ≠ k → y n = 0}

theorem Plane.smul_real {k : ℤ} {y : K} (hy : y ∈ Plane k) (t : ℝ) : t • y ∈ Plane k := by
  intro n hn; simp [hy n hn]

theorem Plane.smul_I {k : ℤ} {y : K} (hy : y ∈ Plane k) : Complex.I • y ∈ Plane k := by
  intro n hn; simp [hy n hn]

theorem Plane.add {k : ℤ} {y v : K} (hy : y ∈ Plane k) (hv : v ∈ Plane k) : y + v ∈ Plane k := by
  intro n hn; simp [hy n hn, hv n hn]

/-- `Ω = ω` on plane tangents, at plane points of `B_{B.radius}`. -/
def PlaneOmega (P : PrintedHyp) (B : PrintedBounds P) (k : ℤ) : Prop :=
  ∀ y ∈ Plane k, y ∈ ball (0 : K) B.radius → ∀ v ∈ Plane k, ∀ w ∈ Plane k, P.Ω y v w = omegaF v w

variable {P : PrintedHyp} (B : PrintedBounds P) {k : ℤ}

theorem beta_plane (hpl : PlaneOmega P B k) {y : K} (hyP : y ∈ Plane k) (hyB : y ∈ ball (0 : K) B.radius)
    {h : K} (hh : h ∈ Plane k) : betaR P.toHyp y h = 0 := by
  unfold betaR
  have hint : IntervalIntegrable (fun t : ℝ => t • (Dl P.toHyp (t • y) y)) MeasureTheory.volume 0 1 :=
    ContinuousOn.intervalIntegrable (by
      simpa only [uIcc_of_le zero_le_one] using radial_cont P.toHyp B.toNative.loc hyB)
  have := ContinuousLinearMap.intervalIntegral_comp_comm (ContinuousLinearMap.apply ℝ ℝ h) hint
  simp only [ContinuousLinearMap.apply_apply] at this
  rw [← this]
  have : ∀ t ∈ uIcc (0 : ℝ) 1, (t • (Dl P.toHyp (t • y) y)) h = 0 := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have htB : t • y ∈ ball (0 : K) B.radius := scale_mem' hyB ht
    have htP : t • y ∈ ball (0 : K) P.R := ball_subset_ball B.ρR htB
    simp only [ContinuousLinearMap.smul_apply, Dl, ContinuousLinearMap.sub_apply, smul_eq_mul]
    rw [P.toHyp_Ω htP, hpl _ (Plane.smul_real hyP t) htB y hyP h hh, sub_self, mul_zero]
  rw [intervalIntegral.integral_congr this]; simp

theorem f_plane (hpl : PlaneOmega P B k) {y : K} (hyP : y ∈ Plane k) (hyB : y ∈ ball (0 : K) B.radius) :
    primitive (betaR P.toHyp) y = 0 := by
  unfold primitive
  have : ∀ p, pathIntegrand (betaR P.toHyp) y p = 0 := by
    intro p
    unfold pathIntegrand
    have h1 : rotation p y ∈ Plane k := by
      intro n hn
      show (rotationAngles p n : ℂ) * y n = 0
      rw [hyP n hn, mul_zero]
    have h2 : velocity p.1 (rotation p y) ∈ Plane k := by
      intro n hn
      rw [velocity_apply, h1 n hn, mul_zero]
    have h3 : rotation p y ∈ ball (0 : K) B.radius := by
      rw [mem_ball_zero_iff, rotation_norm]; exact mem_ball_zero_iff.1 hyB
    exact beta_plane B hpl h1 h3 h2
  simp [this]

theorem df_plane (hpl : PlaneOmega P B k) {y : K} (hyP : y ∈ Plane k) (hyB : y ∈ ball (0 : K) B.radius)
    {h : K} (hh : h ∈ Plane k) : fderiv ℝ (primitive (betaR P.toHyp)) y h = 0 := by
  set f := primitive (betaR P.toHyp)
  by_cases hd : DifferentiableAt ℝ f y
  · have hline : HasDerivAt (fun s : ℝ => y + s • h) h 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add y
    have hd' : HasFDerivAt f (fderiv ℝ f y) (y + (0 : ℝ) • h) := by simpa using hd.hasFDerivAt
    have h1 := hd'.comp_hasDerivAt (0 : ℝ) hline
    have hev : (fun s : ℝ => f (y + s • h)) =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
      have hc : ContinuousAt (fun s : ℝ => y + s • h) 0 := by fun_prop
      have hopen := hc.preimage_mem_nhds (isOpen_ball.mem_nhds (by simpa using hyB : y + (0 : ℝ) • h ∈ ball (0 : K) B.radius))
      filter_upwards [hopen] with s hs
      exact f_plane B hpl (Plane.add hyP (Plane.smul_real hh s)) hs
    have h2 : HasDerivAt (fun s : ℝ => f (y + s • h)) 0 0 := (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hev
    have h3 : (fderiv ℝ f y) h = 0 := h1.unique h2
    exact h3
  · rw [fderiv_zero_of_not_differentiableAt hd]; simp

theorem beta0_plane (hpl : PlaneOmega P B k) {y : K} (hyP : y ∈ Plane k) (hyB : y ∈ ball (0 : K) B.radius)
    {h : K} (hh : h ∈ Plane k) : beta0 (betaR P.toHyp) y h = 0 := by
  unfold beta0
  simp only [ContinuousLinearMap.sub_apply]
  rw [beta_plane B hpl hyP hyB hh, df_plane B hpl hyP hyB hh, sub_self]

/-- the Moser vector at a plane point vanishes as soon as it is tangent to the plane. -/
theorem moserY_plane_zero (hpl : PlaneOmega P B k) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {y : K}
    (hyP : y ∈ Plane k) (hyB : y ∈ ball (0 : K) B.radius) (hY : P.moserY t y ∈ Plane k) : P.moserY t y = 0 := by
  set Y := P.moserY t y with hYdef
  have hyR : y ∈ ball (0 : K) P.R := ball_subset_ball B.ρR hyB
  have h1 : omega Y (Complex.I • Y) + (t • (P.Ω y - omegaF)) Y (Complex.I • Y) =
      -(beta0 (betaR P.toHyp) y (Complex.I • Y)) := iota_Ycov (norm_D_lt t ht hyR) _ _
  have hIY : Complex.I • Y ∈ Plane k := Plane.smul_I hY
  rw [beta0_plane B hpl hyP hyB hIY] at h1
  have h2 : (t • (P.Ω y - omegaF)) Y (Complex.I • Y) = 0 := by
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, smul_eq_mul]
    rw [hpl y hyP hyB Y hY _ hIY, sub_self, mul_zero]
  have h3 : omega Y (Complex.I • Y) = 2 * ‖Y‖ ^ 2 := omega_I_smul Y
  rw [h2, add_zero, h3] at h1
  have : ‖Y‖ ^ 2 = 0 := by linarith
  exact norm_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)

/-- `S` fixes the plane pointwise. -/
theorem Sm_plane (hpl : PlaneOmega P B k) {z : K} (hz : z ∈ Plane k)
    (hzr : ‖z‖ < (moserDataN P.toHyp B.toNative).R0 / 4) :
    (moserDataN P.toHyp B.toNative).Sfl 1 z = z := by
  set MD := moserDataN P.toHyp B.toNative with hMD
  have hR0 : MD.R0 = moserR0 B.radius B.realConstant := rfl
  have hR : MD.R0 ≤ B.radius := by rw [hR0]; exact moserR0_le_R P.toHyp B.toNative
  have hpos : 0 < MD.R0 := MD.R0_pos
  have hcoord : ∀ t, MD.Sfl t z ∈ Plane k := by
    intro t n hn
    have h := MD.q_Sfl n t z
    unfold q at h
    rw [hz n hn, norm_zero] at h
    have : ‖MD.Sfl t z n‖ ^ 2 = 0 := by simpa using h
    exact norm_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)
  have hnorm : ∀ t, MD.Sfl t z ∈ ball (0 : K) B.radius := fun t => by
    rw [mem_ball_zero_iff, MD.norm_Sfl]; linarith [mem_ball_zero_iff.1 (mem_ball_zero_iff.2 hzr : z ∈ ball (0 : K) (MD.R0 / 4))]
  have hder : ∀ t, HasDerivAt (fun s => MD.Sfl s z) (MD.Yf (sig t) (MD.Sfl t z)) t := MD.Sfl_deriv hzr.le
  have hzero : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt (fun s => MD.Sfl s z) (0 : K) (Ici t) t := by
    intro t ht
    have h1 := hder t
    rw [sig_eq (s := t) ⟨by linarith [ht.1], by linarith [ht.2]⟩] at h1
    have hmP : MD.Sfl t z ∈ ball (0 : K) P.R := ball_subset_ball B.ρR (hnorm t)
    rw [← P.moserY_eq_Yf B t hmP] at h1
    have hYpl : P.moserY t (MD.Sfl t z) ∈ Plane k := by
      intro n hn
      have hc : ∀ s, (MD.Sfl s z) n = 0 := fun s => hcoord s n hn
      have hd := (evalR n).hasFDerivAt.comp_hasDerivAt t (hder t)
      rw [sig_eq (s := t) ⟨by linarith [ht.1], by linarith [ht.2]⟩, ← P.moserY_eq_Yf B t hmP] at hd
      have hconst : HasDerivAt (fun s : ℝ => (evalR n) (MD.Sfl s z)) 0 t := by
        have : (fun s : ℝ => (evalR n) (MD.Sfl s z)) = fun _ => (0 : ℂ) := funext hc
        rw [this]; exact hasDerivAt_const _ _
      simpa using hd.unique hconst
    have h0 := moserY_plane_zero B hpl ⟨ht.1, ht.2.le⟩ (hcoord t) (hnorm t) hYpl
    rw [h0] at h1
    exact h1.hasDerivWithinAt
  have hcont : ContinuousOn (fun s => MD.Sfl s z) (Icc (0 : ℝ) 1) := fun s _ => (hder s).continuousAt.continuousWithinAt
  have := constant_of_has_deriv_right_zero hcont hzero 1 ⟨zero_le_one, le_rfl⟩
  rw [this, MD.Sfl_zero]

theorem Si_plane (hpl : PlaneOmega P B k) {z : K} (hz : z ∈ Plane k)
    (hzr : ‖z‖ < (moserDataN P.toHyp B.toNative).R0 / 4) :
    (moserDataN P.toHyp B.toNative).Tinv z = z := by
  have h := Sm_plane B hpl hz hzr
  have := (moserDataN P.toHyp B.toNative).Tinv_Sfl_one z
  rwa [h] at this

end QuantumNLS.Local021

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.Local021.beta0_plane
#print axioms QuantumNLS.Local021.Sm_plane
#print axioms QuantumNLS.Local021.Si_plane
