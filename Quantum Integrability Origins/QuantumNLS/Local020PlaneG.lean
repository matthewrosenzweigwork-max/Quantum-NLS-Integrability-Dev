import Mathlib
import QuantumNLS.Local007Statement
import QuantumNLS.Local020Plane
import QuantumNLS.Local020Cov
import QuantumNLS.Local020Rr
import QuantumNLS.Local020Rep

/-! LOCAL-020 stage S7b: `g_k(a e_k) = a` on every single Fourier plane (for small `a`). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric Filter Topology ComplexConjugate
open QuantumNLS.LocalSpectral
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Local007Final (Pkg gcoef)
open QuantumNLS.Fourier (modeLp)

namespace QuantumNLS.Local020PlaneG

variable {L κ r ρ C : ℝ} [Fact (0 < L)]

theorem fourier_neg_arg (k : ℤ) (x : AddCircle L) : fourier k (-x) = conj (fourier k x) := by
  rw [fourier_apply (n := k) (x := -x), smul_neg, fourier_neg']

theorem star_refl_mode (t : ℝ) (k : ℤ) :
    star (QuantumNLS.ResetNormalizationUniqueness.reflectR L ((t : ℂ) • modeLp L k)) =
      (t : ℂ) • modeLp L k := by
  apply Lp.ext
  have hmp := (QuantumNLS.ResetNormalizationUniqueness.negMP L).quasiMeasurePreserving
  filter_upwards [QuantumNLS.ResetNormalizationUniqueness.coeFn_cj L
      (QuantumNLS.ResetNormalizationUniqueness.reflectR L ((t : ℂ) • modeLp L k)),
    QuantumNLS.ResetNormalizationUniqueness.coeFn_reflectR L ((t : ℂ) • modeLp L k),
    Lp.coeFn_smul (t : ℂ) (modeLp L k), QuantumNLS.Fourier.coeFn_modeLp L k,
    hmp.ae_eq_comp (Lp.coeFn_smul (t : ℂ) (modeLp L k)),
    hmp.ae_eq_comp (QuantumNLS.Fourier.coeFn_modeLp L k)] with x h1 h2 h3 h4 h5 h6
  rw [h1, h2, h3]
  simp only [Function.comp] at h5 h6
  rw [Pi.smul_apply, h4]
  simp only [Pi.smul_apply] at h5
  rw [h5, h6]
  unfold QuantumNLS.Fourier.mode
  rw [fourier_neg_arg]
  simp [Complex.conj_ofReal]

theorem circleRep_mode (a : ℂ) (k : ℤ) :
    circleRep (a • modeLp L k) =ᵐ[μI L] QuantumNLS.Local020Plane.pw L a k := by
  have h := QuantumNLS.Local020Rep.circleRep_ae_fun (v := a • modeLp L k)
    (f := fun y => a * QuantumNLS.Fourier.mode L k y) (by
      filter_upwards [Lp.coeFn_smul a (modeLp L k), QuantumNLS.Fourier.coeFn_modeLp L k] with y h1 h2
      rw [h1, Pi.smul_apply, h2]; rfl)
  refine h.trans (Eventually.of_forall fun x => ?_)
  have e : 2 * (Real.pi : ℂ) * Complex.I * k * x / L = Complex.I * (pm L k : ℂ) * x := by
    have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : 0 < L).ne'
    unfold pm
    push_cast
    field_simp
  simp only [QuantumNLS.Fourier.mode_coe, QuantumNLS.Local020Plane.pw]
  rw [e]
  ring

theorem norm_cc (hκ : 0 < κ) (t : ℝ) (ht : 0 ≤ t) :
    ‖QuantumNLS.Local020Plane.cc L κ (t : ℂ)‖ ^ 2 = 4 * κ * t ^ 2 / L := by
  have hL : 0 < L := Fact.out
  unfold QuantumNLS.Local020Plane.cc QuantumNLS.Local020Plane.cc'
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
    Complex.norm_real, Complex.norm_two, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)), Real.norm_of_nonneg ht]
  have h1 : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  have h2 : (Real.sqrt L)⁻¹ ^ 2 = L⁻¹ := by rw [inv_pow, Real.sq_sqrt hL.le]
  have : (2 * 1 * Real.sqrt κ * (Real.sqrt L)⁻¹ * t) ^ 2 = 4 * (Real.sqrt κ ^ 2) * ((Real.sqrt L)⁻¹ ^ 2) * t ^ 2 := by ring
  rw [this, h1, h2]; field_simp

theorem conj_gcoef : conj (gcoef L κ) = -gcoef L κ := by
  unfold gcoef
  have h2c : (starRingEnd ℂ) 2 = 2 := map_ofNat _ 2
  simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, h2c]
  have : (2 : ℂ) * -Complex.I * (Real.sqrt κ : ℂ) = -(2 * Complex.I * (Real.sqrt κ : ℂ)) := by ring
  rw [this, div_neg]

/-- **S7b.**  On every single Fourier plane `g_k(c e_k) = c` (small `c`). -/
theorem plane_g (hκ : 0 < κ) {a : ℤ → L2T L → ℝ} {b : ℤ → L2T L → ℂ}
    (hP : ∀ n, Pkg L κ r ρ C n (a n) (b n)) (hC0 : 0 ≤ C) (hρ : 0 < ρ) (hCρ : C * ρ ^ 2 < 2)
    (hρr : 2 * Real.sqrt κ * (Real.sqrt L)⁻¹ * ρ < r) (k : ℤ) (c : ℂ) (hc : ‖c‖ < ρ) :
    gcoef L κ * b k (c • modeLp L k) = c := by
  have hL : 0 < L := Fact.out
  by_cases hc0 : c = 0
  · subst hc0
    rw [zero_smul, QuantumNLS.Local007Statement.pkg_b_zero hκ hρ (hP k), mul_zero]
  set t : ℝ := ‖c‖ with ht
  have htp : 0 < t := norm_pos_iff.2 hc0
  set u0 : L2T L := (t : ℂ) • modeLp L k with hu0def
  have hnu0 : ‖u0‖ = t := by
    rw [hu0def, norm_smul, QuantumNLS.Local020Rr.norm_modeLp, mul_one, Complex.norm_real,
      Real.norm_of_nonneg htp.le]
  have hu0 : u0 ∈ ball (0 : L2T L) ρ := by rw [mem_ball_zero_iff, hnu0]; exact hc
  -- the key claim at the positive amplitude
  have key : gcoef L κ * b k u0 = (t : ℂ) := by
    have pk := (hP k).2.2.2.2.1 u0 hu0
    have hccn : ‖QuantumNLS.Local020Plane.cc L κ (t : ℂ)‖ ^ 2 = 4 * κ * t ^ 2 / L :=
      QuantumNLS.Local020PlaneG.norm_cc hκ t htp.le
    have hccne : QuantumNLS.Local020Plane.cc L κ (t : ℂ) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hccn
      have : 0 < 4 * κ * t ^ 2 / L := by positivity
      linarith
    have hcclt : ‖QuantumNLS.Local020Plane.cc L κ (t : ℂ)‖ < r := by
      have h1 : ‖QuantumNLS.Local020Plane.cc L κ (t : ℂ)‖ = 2 * Real.sqrt κ * (Real.sqrt L)⁻¹ * t := by
        unfold QuantumNLS.Local020Plane.cc QuantumNLS.Local020Plane.cc'
        rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
          Complex.norm_real, Complex.norm_two, Real.norm_of_nonneg (Real.sqrt_nonneg _),
          Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)), Real.norm_of_nonneg htp.le]
        ring
      rw [h1]
      calc 2 * Real.sqrt κ * (Real.sqrt L)⁻¹ * t ≤ 2 * Real.sqrt κ * (Real.sqrt L)⁻¹ * ρ := by
            gcongr
        _ < r := hρr
    obtain ⟨-, hbn⟩ := QuantumNLS.Local020Plane.plane_modulus (κ := κ) hL (t : ℂ) k hccne hcclt
      (QuantumNLS.Local020PlaneG.circleRep_mode (t : ℂ) k) pk.2.2.2.1
    -- reality: u0 = star (R u0), hence b = - conj b
    have hRu : QuantumNLS.ResetNormalizationUniqueness.reflectR L u0 ∈ ball (0 : L2T L) ρ := by
      rw [mem_ball_zero_iff, LinearIsometry.norm_map]; exact mem_ball_zero_iff.1 hu0
    obtain ⟨hb1, -⟩ := QuantumNLS.Local020Cov.cov_refl hP hu0 k
    obtain ⟨hb2, -⟩ := QuantumNLS.Local020Cov.cov_conj hP hRu (-k)
    rw [neg_neg, QuantumNLS.Local020PlaneG.star_refl_mode, hb1] at hb2
    -- hb2 : b k u0 = - conj (b k u0)
    have hb2' : b k u0 = -conj (b k u0) := hb2
    have hG : conj (gcoef L κ * b k u0) = gcoef L κ * b k u0 := by
      calc conj (gcoef L κ * b k u0) = (-gcoef L κ) * conj (b k u0) := by rw [map_mul, conj_gcoef]
        _ = gcoef L κ * (-conj (b k u0)) := by ring
        _ = gcoef L κ * b k u0 := by rw [← hb2']
    have him : (gcoef L κ * b k u0).im = 0 := Complex.conj_eq_iff_im.1 hG
    have hnorm : ‖gcoef L κ * b k u0‖ = t := by
      rw [norm_mul, hbn]
      have h1 := QuantumNLS.Local007Final.norm_gcoef_sq (L := L) hκ
      have h2 : (‖gcoef L κ‖ * ‖QuantumNLS.Local020Plane.cc L κ (t : ℂ)‖) ^ 2 = t ^ 2 := by
        rw [mul_pow, h1, hccn]; field_simp
      exact (sq_eq_sq₀ (by positivity) htp.le).1 h2
    have hcub := (hP k).2.2.2.2.2.2.1 u0 hu0
    rw [hnu0, QuantumNLS.Local020Rr.coeff_smul_mode] at hcub
    set G := gcoef L κ * b k u0 with hGdef
    have hGre : G = (G.re : ℂ) := Complex.ext (by simp) (by simpa using him)
    have habs : |G.re| = t := by
      have : ‖G‖ = |G.re| := by rw [hGre]; simp [Complex.norm_real]
      rw [← this]; exact hnorm
    rcases abs_eq htp.le |>.1 habs with h1 | h1
    · rw [hGre, h1]
    · exfalso
      rw [hGre, h1] at hcub
      have h2 : ‖((-t : ℝ) : ℂ) - (t : ℂ)‖ = 2 * t := by
        rw [show ((-t : ℝ) : ℂ) - (t : ℂ) = ((-2 * t : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_of_neg (by linarith)]
        ring
      rw [h2] at hcub
      have h3 : C * t ^ 2 < 2 := by
        have : t ^ 2 < ρ ^ 2 := by nlinarith
        nlinarith
      have h4 : 2 * t ≤ C * t ^ 3 := hcub
      nlinarith [mul_pos htp htp, mul_pos (mul_pos htp htp) htp]
  -- phase
  have hcarg : (t : ℂ) * Complex.exp (((Complex.arg c : ℝ) : ℂ) * Complex.I) = c := by
    have := Complex.norm_mul_exp_arg_mul_I c
    simpa [ht] using this
  have hcu : c • modeLp L k = Complex.exp (((Complex.arg c : ℝ) : ℂ) * Complex.I) • u0 := by
    rw [hu0def, smul_smul, mul_comm, hcarg]
  rw [hcu, QuantumNLS.Local020Cov.cov_phase hP (Complex.arg c) hu0 k, ← mul_assoc, mul_comm (gcoef L κ), mul_assoc,
    key, mul_comm, hcarg]

end QuantumNLS.Local020PlaneG

#print axioms QuantumNLS.Local020PlaneG.plane_g
