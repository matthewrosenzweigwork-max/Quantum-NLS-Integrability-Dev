import NlsGge.GK38.ContourAction
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Complex.Trigonometric

set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations
namespace NlsGge.GK38.ActionBranch
noncomputable section

def rho (u : PhysicalL2) (z : ℂ) : ℂ :=
  (discrim (realSlice u) z - canonRoot38 (realSlice u) z) / 2

def expRoot (u : PhysicalL2) (z : ℂ) : ℂ :=
  Complex.exp (actualQuasimomentumE02_38 u z * Complex.I)

theorem quadratic_roots (D x w : ℂ)
    (hx : x ^ 2 - D * x + 1 = 0) (hw : w ^ 2 - D * w + 1 = 0) :
    x = w ∨ x * w = 1 := by
  have he : (x - w) * (x * w - 1) = 0 := by
    linear_combination w * hx - x * hw
  rcases mul_eq_zero.mp he with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

theorem quadratic_root_norm_ne_one (D x w : ℂ)
    (hx : x ^ 2 - D * x + 1 = 0) (hw : w ^ 2 - D * w + 1 = 0)
    (hwlt : ‖w‖ < 1) : ‖x‖ ≠ 1 := by
  intro hn
  rcases quadratic_roots D x w hx hw with he | he
  · rw [he] at hn
    linarith
  · have hh := congrArg norm he
    rw [norm_mul, norm_one, hn, one_mul] at hh
    linarith

theorem quadratic_unit_disc_unique (D x w : ℂ)
    (hx : x ^ 2 - D * x + 1 = 0) (hw : w ^ 2 - D * w + 1 = 0)
    (hxlt : ‖x‖ < 1) (hwlt : ‖w‖ < 1) : x = w := by
  rcases quadratic_roots D x w hx hw with he | he
  · exact he
  · have hh := congrArg norm he
    rw [norm_mul, norm_one] at hh
    nlinarith [norm_nonneg x, norm_nonneg w]

theorem exp_trig_quadratic (v : ℂ) :
    Complex.exp (v * Complex.I) ^ 2 -
      (2 * Complex.cos v) * Complex.exp (v * Complex.I) + 1 = 0 := by
  rw [Complex.exp_mul_I]
  calc
    _ = -(Complex.cos v ^ 2 + Complex.sin v ^ 2 - 1) +
        Complex.sin v ^ 2 * (Complex.I ^ 2 + 1) := by ring
    _ = 0 := by rw [Complex.cos_sq_add_sin_sq, Complex.I_sq]; ring

theorem exp_norm_lt_one (v : ℂ) (hv : 0 < v.im) :
    ‖Complex.exp (v * Complex.I)‖ < 1 := by
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub]
  exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hv)

theorem root_domain (u : PhysicalL2) (z : ℂ) (hz : 0 < z.im) :
    (realSlice u, z) ∈ rootDomain38 :=
  rootDomain_realSlice_nonreal38 u z (ne_of_gt hz)

theorem rho_quadratic (u : PhysicalL2) (z : ℂ) (hz : 0 < z.im) :
    rho u z ^ 2 - discrim (realSlice u) z * rho u z + 1 = 0 := by
  have hr := canonRoot_sq38 (realSlice u) (realSlice_mem_gkW u) z (root_domain u z hz).2
  rw [perChar_eq] at hr
  unfold rho
  linear_combination (1 / 4 : ℂ) * hr

theorem expRoot_quadratic (u : PhysicalL2) (z : ℂ) (hz : 0 < z.im) :
    expRoot u z ^ 2 - discrim (realSlice u) z * expRoot u z + 1 = 0 := by
  have hk := isActualQuasimomentumBranch_actualQuasimomentumE02_38 u
  rw [discrim_realSlice, ← hk.2.1 z hz]
  exact exp_trig_quadratic _

theorem expRoot_norm_lt_one (u : PhysicalL2) (z : ℂ) (hz : 0 < z.im) :
    ‖expRoot u z‖ < 1 :=
  exp_norm_lt_one _ ((isActualQuasimomentumBranch_actualQuasimomentumE02_38 u).2.2.1 z hz)

theorem rho_norm_ne_one (u : PhysicalL2) (z : ℂ) (hz : 0 < z.im) :
    ‖rho u z‖ ≠ 1 :=
  quadratic_root_norm_ne_one _ _ _ (rho_quadratic u z hz)
    (expRoot_quadratic u z hz) (expRoot_norm_lt_one u z hz)

theorem rho_free (z : ℂ) (hz : 0 < z.im) :
    rho (0 : PhysicalL2) z = Complex.exp (z * Complex.I) := by
  have hp := root_domain (0 : PhysicalL2) z hz
  rw [realSlice_zero] at hp
  unfold rho
  rw [realSlice_zero, discrim_zero, canonRoot_free38 z hp.2, Complex.exp_mul_I]
  ring

end
end NlsGge.GK38.ActionBranch
