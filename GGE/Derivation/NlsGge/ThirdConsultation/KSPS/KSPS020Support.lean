import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS020Host
import NlsGge.ThirdConsultation.KSPS.KSPS019Support
import NlsGge.Atomic.KSPS.KSPS018
import NlsGge.Atomic.G1.G1049
import NlsGge.Atomic.G1.G1050
import NlsGge.Atomic.G1.G1051
import NlsGge.GK38.PeriodicLabellingCanonical

/- KSPS-020 SUPPORT01 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS020Support.lean.
   Part A: abstract endpoint localisation (pure complex analysis, no spectral objects).
   Part B: bridges to the monodromy: trace estimates, the identity Delta^2 - 4 = (m1-m4)^2 + 4 m2 m3 bound, ball facts.
   Part C: uniform (on Cset B) periodic counting with ONE cutoff; labelled periodic endpoints lie in the quarter discs. -/
set_option autoImplicit false
noncomputable section

open Filter Topology Set Metric
open scoped Matrix.Norms.L2Operator

namespace NlsGge.ThirdConsultation.KSPS020Support

/-! ### Part A -/


theorem norm_cos_sub_one_le {t : ℂ} (ht : ‖t‖ ≤ 1) : ‖Complex.cos t - 1‖ ≤ ‖t‖ ^ 2 := by
  have h1 : ‖Complex.exp (-t * Complex.I) - 1 - (-t * Complex.I)‖ ≤ ‖t‖ ^ 2 := by
    have := Complex.norm_exp_sub_one_sub_id_le (x := -t * Complex.I) (by simpa using ht)
    simpa using this
  have h2 : ‖Complex.exp (t * Complex.I) - 1 - (t * Complex.I)‖ ≤ ‖t‖ ^ 2 := by
    have := Complex.norm_exp_sub_one_sub_id_le (x := t * Complex.I) (by simpa using ht)
    simpa using this
  have key : Complex.cos t - 1 =
      ((Complex.exp (-t * Complex.I) - 1 - (-t * Complex.I)) +
        (Complex.exp (t * Complex.I) - 1 - (t * Complex.I))) / 2 := by
    rw [Complex.cos]; ring
  rw [key, norm_div, Complex.norm_ofNat]
  have := norm_add_le (Complex.exp (-t * Complex.I) - 1 - (-t * Complex.I))
    (Complex.exp (t * Complex.I) - 1 - (t * Complex.I))
  linarith

/-- `‖2 + x‖ ≥ 2 - ‖x‖`. -/
theorem norm_two_add_ge (x : ℂ) : 2 - ‖x‖ ≤ ‖(2 : ℂ) + x‖ := by
  have := norm_sub_norm_le (2 : ℂ) (-x)
  rw [norm_neg, sub_neg_eq_add, Complex.norm_ofNat] at this
  exact this

/-- Abstract endpoint localisation: if the discriminant-like function `d` has a root of `d² = 4`
near `c = nπ` (with the cosine behaviour `cos (c + t) = s cos t`, `s² = 1`), is `K/ν`-close to
`2 cos` with a `K/ν`-close derivative on the quarter disc, and `l'` is a point of the quarter disc
within `K/ν` of `c` at which `d² - 4` is `O(1/ν²)`, then the root is within `(39 K + 1)/ν` of `c`. -/
theorem endpoint_close {d : ℂ → ℂ} {c s : ℂ} {ν K : ℝ}
    (hs : s * s = 1) (hcos : ∀ t : ℂ, Complex.cos (c + t) = s * Complex.cos t)
    (hK : 0 ≤ K) (hν : 1 ≤ ν) (hKν : K / ν ≤ 7 / 10)
    (h0 : ∀ z ∈ ball c (Real.pi / 4), ‖d z - 2 * Complex.cos z‖ ≤ K / ν)
    (h1 : ∀ z ∈ ball c (Real.pi / 4), DifferentiableAt ℂ d z ∧
      ‖deriv d z + 2 * Complex.sin z‖ ≤ K / ν)
    {l l' : ℂ} (hl : l ∈ ball c (Real.pi / 4)) (hl' : l' ∈ ball c (Real.pi / 4))
    (hroot : d l ^ 2 = 4) (hid : ‖d l' ^ 2 - 4‖ ≤ K / ν ^ 2) (hu : ‖l' - c‖ ≤ K / ν) :
    ‖l - c‖ ≤ (39 * K + 1) / ν := by
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hνpos : 0 < ν := lt_of_lt_of_le one_pos hν
  have hns : ‖s‖ = 1 := by
    have h : ‖s‖ * ‖s‖ = 1 := by rw [← norm_mul, hs, norm_one]
    rcases mul_self_eq_one_iff.mp h with h | h
    · exact h
    · linarith [norm_nonneg s]
  have hball : ∀ z ∈ ball c (Real.pi / 4), ‖z - c‖ < Real.pi / 4 := fun z hz => by
    rwa [mem_ball, dist_eq_norm] at hz
  have hcosz : ∀ z : ℂ, Complex.cos z = s * Complex.cos (z - c) := fun z => by
    have := hcos (z - c)
    rwa [add_sub_cancel] at this
  -- lower bound for `d z + 2 s`
  have hlow : ∀ z ∈ ball c (Real.pi / 4), 2 ≤ ‖d z + 2 * s‖ := by
    intro z hz
    have ht := hball z hz
    have ht1 : ‖z - c‖ ≤ 1 := by linarith
    have hc1 := norm_cos_sub_one_le ht1
    have hsq : ‖z - c‖ ^ 2 ≤ 0.63 := by nlinarith [norm_nonneg (z - c)]
    have hb := norm_two_add_ge (Complex.cos (z - c) - 1)
    have e1 : (2 : ℂ) + (Complex.cos (z - c) - 1) = 1 + Complex.cos (z - c) := by ring
    rw [e1] at hb
    have e2 : d z + 2 * s = (d z - 2 * Complex.cos z) + (2 * s) * (1 + Complex.cos (z - c)) := by
      rw [hcosz z]; ring
    have h3 : ‖(2 * s) * (1 + Complex.cos (z - c))‖ = 2 * ‖1 + Complex.cos (z - c)‖ := by
      rw [norm_mul, norm_mul, hns, Complex.norm_ofNat, mul_one]
    have h4 : ‖(2 * s) * (1 + Complex.cos (z - c))‖ - ‖d z - 2 * Complex.cos z‖ ≤
        ‖(d z - 2 * Complex.cos z) + (2 * s) * (1 + Complex.cos (z - c))‖ := by
      have := norm_sub_norm_le ((2 * s) * (1 + Complex.cos (z - c))) (-(d z - 2 * Complex.cos z))
      rw [norm_neg, sub_neg_eq_add] at this
      rw [add_comm (d z - 2 * Complex.cos z)]
      exact this
    rw [← e2, h3] at h4
    have := h0 z hz
    linarith
  have hdl : d l = 2 * s := by
    have hfac : (d l - 2 * s) * (d l + 2 * s) = 0 := by
      linear_combination hroot - 4 * hs
    rcases mul_eq_zero.mp hfac with h | h
    · exact sub_eq_zero.mp h
    · have := hlow l hl
      rw [h, norm_zero] at this
      linarith
  have he : ‖d l' - 2 * s‖ ≤ K / (2 * ν ^ 2) := by
    have hfac : d l' ^ 2 - 4 = (d l' - 2 * s) * (d l' + 2 * s) := by
      linear_combination (4 : ℂ) * hs
    have h2 := hlow l' hl'
    have h5 : ‖d l' - 2 * s‖ * 2 ≤ ‖d l' ^ 2 - 4‖ := by
      rw [hfac, norm_mul]
      exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    have : K / (2 * ν ^ 2) = (K / ν ^ 2) / 2 := by field_simp
    rw [this]
    linarith
  -- mean value inequality for `g = d - 2 cos` on the quarter disc
  have hMV : ‖(d l - 2 * Complex.cos l) - (d l' - 2 * Complex.cos l')‖ ≤ K / ν * ‖l - l'‖ := by
    have hderiv : ∀ z ∈ ball c (Real.pi / 4),
        HasDerivWithinAt (fun w : ℂ => d w - 2 * Complex.cos w)
          (deriv d z + 2 * Complex.sin z) (ball c (Real.pi / 4)) z := by
      intro z hz
      have hd := (h1 z hz).1.hasDerivAt
      have hc := (Complex.hasDerivAt_cos z).const_mul (2 : ℂ)
      have := (hd.sub hc).hasDerivWithinAt (s := ball c (Real.pi / 4))
      convert this using 1
      ring
    exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv (fun z hz => (h1 z hz).2)
      (convex_ball c (Real.pi / 4)) hl' hl
  -- cos l - cos l'
  set w := l - c with hw
  set u := l' - c with hu'
  have hwlt := hball l hl
  have hult := hball l' hl'
  have hcc : ‖Complex.cos l - Complex.cos l'‖ = ‖Complex.cos w - Complex.cos u‖ := by
    rw [hcosz l, hcosz l', ← mul_sub, norm_mul, hns, one_mul]
  have hsum : Complex.cos w - Complex.cos u =
      -2 * Complex.sin ((w + u) / 2) * Complex.sin ((w - u) / 2) := Complex.cos_sub_cos w u
  have hQ : ‖(w + u) / 2‖ < Real.pi / 4 := by
    rw [norm_div, Complex.norm_ofNat]
    have := norm_add_le w u
    linarith
  have hP : ‖(w - u) / 2‖ < Real.pi / 4 := by
    rw [norm_div, Complex.norm_ofNat]
    have := norm_sub_le w u
    linarith
  have h5Q := NlsGge.ThirdConsultation.KSPS019Support.norm_le_five_mul_norm_sin hQ
  have h5P := NlsGge.ThirdConsultation.KSPS019Support.norm_le_five_mul_norm_sin hP
  set P := ‖w - u‖ with hPdef
  set Q := ‖w + u‖ with hQdef
  have hPu : ‖l - l'‖ = P := by
    rw [hPdef, hw, hu']; congr 1; ring
  have hcosnorm : ‖Complex.cos w - Complex.cos u‖ =
      2 * (‖Complex.sin ((w + u) / 2)‖ * ‖Complex.sin ((w - u) / 2)‖) := by
    rw [hsum, norm_mul, norm_mul, norm_neg, Complex.norm_ofNat]
    ring
  have hQ2 : ‖(w + u) / 2‖ = Q / 2 := by rw [norm_div, Complex.norm_ofNat]
  have hP2 : ‖(w - u) / 2‖ = P / 2 := by rw [norm_div, Complex.norm_ofNat]
  rw [hQ2] at h5Q
  rw [hP2] at h5P
  have hPQ : P * Q ≤ 50 * ‖Complex.cos w - Complex.cos u‖ := by
    rw [hcosnorm]
    have hsQ : Q / 10 ≤ ‖Complex.sin ((w + u) / 2)‖ := by linarith
    have hsP : P / 10 ≤ ‖Complex.sin ((w - u) / 2)‖ := by linarith
    have hP0 : 0 ≤ P := norm_nonneg _
    have hQ0 : 0 ≤ Q := norm_nonneg _
    nlinarith [mul_le_mul hsQ hsP (by positivity) (norm_nonneg _)]
  -- the exact relation
  have hrel : 2 * (Complex.cos l - Complex.cos l') =
      -(d l' - 2 * s) - ((d l - 2 * Complex.cos l) - (d l' - 2 * Complex.cos l')) := by
    rw [hdl]; ring
  have hrelnorm : 2 * ‖Complex.cos w - Complex.cos u‖ ≤ K / (2 * ν ^ 2) + K / ν * P := by
    rw [← hcc]
    have : ‖2 * (Complex.cos l - Complex.cos l')‖ = 2 * ‖Complex.cos l - Complex.cos l'‖ := by
      rw [norm_mul, Complex.norm_ofNat]
    rw [← this, hrel]
    calc _ ≤ ‖-(d l' - 2 * s)‖ + ‖(d l - 2 * Complex.cos l) - (d l' - 2 * Complex.cos l')‖ :=
          norm_sub_le _ _
      _ ≤ K / (2 * ν ^ 2) + K / ν * P := by
          rw [norm_neg, ← hPu]
          exact add_le_add he hMV
  have hPQ2 : P * Q ≤ 25 * (K / (2 * ν ^ 2) + K / ν * P) := by linarith
  have hu_ : ‖u‖ ≤ K / ν := hu
  have hwu : ‖w‖ ≤ ‖u‖ + P := by
    have := norm_le_norm_add_norm_sub' w u
    linarith [norm_sub_rev w u]
  have hκ : 0 ≤ K / ν := div_nonneg hK hνpos.le
  have hfin : (39 * K + 1) / ν = 39 * (K / ν) + 1 / ν := by field_simp
  have hone : 0 ≤ 1 / ν := by positivity
  rw [hfin]
  by_cases hPle : P ≤ 1 / ν
  · linarith
  · push_neg at hPle
    have hPpos : 0 < P := lt_trans (by positivity) hPle
    have e : K / (2 * ν ^ 2) = (K / ν) * (1 / ν) / 2 := by field_simp
    have h1P : (K / ν) * (1 / ν) ≤ (K / ν) * P := mul_le_mul_of_nonneg_left hPle.le hκ
    have hQle : Q ≤ 75 / 2 * (K / ν) := by
      have : P * Q ≤ P * (75 / 2 * (K / ν)) := by
        rw [e] at hPQ2
        nlinarith
      exact le_of_mul_le_mul_left this hPpos
    have hwQ : ‖w‖ ≤ Q + ‖u‖ := by
      have := norm_sub_le (w + u) u
      rw [add_sub_cancel_right] at this
      exact this
    linarith

/-! ### Part B -/

section PartB

open NlsGge.GK38 NlsGge.ThirdConsultation.KSPS
open NlsGge.ThirdConsultation.KSPSVolterra (fundamental)

theorem norm_trace_le_two (A : Matrix (Fin 2) (Fin 2) ℂ) : ‖Matrix.trace A‖ ≤ 2 * ‖A‖ := by
  rw [Matrix.trace_fin_two]
  have h0 := NlsGge.ThirdConsultation.KSPS006Support.norm_entry_le_l2 A 0 0
  have h1 := NlsGge.ThirdConsultation.KSPS006Support.norm_entry_le_l2 A 1 1
  have := norm_add_le (A 0 0) (A 1 1)
  linarith

theorem trace_freePropagator_one (z : ℂ) :
    Matrix.trace (freePropagator 1 z) = 2 * Complex.cos z := by
  rw [Matrix.trace_fin_two, Complex.two_cos]
  simp only [freePropagator, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Complex.ofReal_one, mul_one]
  rw [mul_comm Complex.I z, neg_mul, add_comm]

theorem discrim_eq_trace (φ : SobolevC 1) (z : ℂ) :
    discrim (toPotPair φ) z = Matrix.trace (fundamental φ 1 z) := by
  rw [← NlsGge.ThirdConsultation.KSPS019Support.monodromy_eq]
  rfl

theorem disc_sub_two_cos_le (φ : SobolevC 1) (z : ℂ) :
    ‖discrim (toPotPair φ) z - 2 * Complex.cos z‖ ≤ 2 * ‖fundamental φ 1 z - freePropagator 1 z‖ := by
  rw [discrim_eq_trace, ← trace_freePropagator_one, ← Matrix.trace_sub]
  exact norm_trace_le_two _

theorem differentiableAt_discrim (φ : SobolevC 1) (z : ℂ) :
    DifferentiableAt ℂ (discrim (toPotPair φ)) z := by
  have hfun : discrim (toPotPair φ) = fun w : ℂ => Matrix.trace (fundamental φ 1 w) :=
    funext (discrim_eq_trace φ)
  rw [hfun]
  have hd := ((NlsGge.ThirdConsultation.KSPS018Support.analyticOnNhd_fundamental φ zero_le_one)
    z (Set.mem_univ _)).differentiableAt.hasDerivAt
  exact (NlsGge.Atomic.G1050S2.K47.hasDerivAt_trace hd).differentiableAt

theorem deriv_disc_add_two_sin_le (φ : SobolevC 1) (z : ℂ) :
    ‖deriv (discrim (toPotPair φ)) z + 2 * Complex.sin z‖ ≤
      2 * ‖deriv (fun l : ℂ => fundamental φ 1 l) z - deriv (fun l : ℂ => freePropagator 1 l) z‖ := by
  have hfun : (fun w : ℂ => ∑' m : ℕ, NlsGge.Atomic.Volterra.potentialVolterraTerm38
      (toPotPair φ) w m 1) = fun w : ℂ => fundamental φ 1 w :=
    funext fun w => (NlsGge.ThirdConsultation.KSPS018Support.fundamental_eq_tsum φ zero_le_one w).symm
  have hfree : (fun w : ℂ => NlsGge.SpectralFoundations.freeZsFundamentalComplex w 1) =
      fun w : ℂ => freePropagator 1 w :=
    funext fun w => by
      rw [← NlsGge.ThirdConsultation.KSPS018Support.E_eq_freeZs]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [NlsGge.ThirdConsultation.KSPSVolterra.E, freePropagator]
  have hd : DifferentiableAt ℂ (fun w : ℂ => ∑' m : ℕ, NlsGge.Atomic.Volterra.potentialVolterraTerm38
      (toPotPair φ) w m 1) z := by
    rw [hfun]
    exact ((NlsGge.ThirdConsultation.KSPS018Support.analyticOnNhd_fundamental φ zero_le_one)
      z (Set.mem_univ _)).differentiableAt
  have key := NlsGge.Atomic.G1050S2.deriv_discrim_add_two_sin (toPotPair φ) z hd
  rw [hfun, hfree] at key
  rw [key]
  exact norm_trace_le_two _

/-- `Delta^2 - 4 = (m1 - m4)^2 + 4 m2 m3` bounded through `D = M - E` and `|sin|`. -/
theorem sq_sub_four_le (φ : SobolevC 1) (z : ℂ) :
    ‖discrim (toPotPair φ) z ^ 2 - 4‖ ≤
      (2 * ‖fundamental φ 1 z - freePropagator 1 z‖ + 2 * ‖Complex.sin z‖) ^ 2 +
        4 * ‖fundamental φ 1 z - freePropagator 1 z‖ ^ 2 := by
  obtain ⟨e1, -, hdet⟩ := NlsGge.Atomic.G1051S3.entries (toPotPair φ) z
  have hM := NlsGge.ThirdConsultation.KSPS019Support.monodromy_eq φ z
  set M := monodromyPair (toPotPair φ) z with hMdef
  set D := fundamental φ 1 z - freePropagator 1 z with hD
  have hMD : M = D + freePropagator 1 z := by rw [hD, ← hM]; abel
  have hP01 : freePropagator 1 z 0 1 = 0 := by simp [freePropagator]
  have hP10 : freePropagator 1 z 1 0 = 0 := by simp [freePropagator]
  have hP : (freePropagator 1 z 0 0 - freePropagator 1 z 1 1) * Complex.I = 2 * Complex.sin z := by
    rw [Complex.two_sin]
    simp only [freePropagator, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Complex.ofReal_one, mul_one]
    rw [mul_comm Complex.I z, neg_mul]
  have hPn : ‖freePropagator 1 z 0 0 - freePropagator 1 z 1 1‖ = 2 * ‖Complex.sin z‖ := by
    have := congrArg norm hP
    rw [norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_ofNat] at this
    exact this
  have hid : discrim (toPotPair φ) z ^ 2 - 4 = (M 0 0 - M 1 1) ^ 2 + 4 * (M 0 1 * M 1 0) := by
    rw [e1]; linear_combination 4 * hdet
  have hm01 : M 0 1 = D 0 1 := by rw [hMD]; simp [hP01]
  have hm10 : M 1 0 = D 1 0 := by rw [hMD]; simp [hP10]
  have hm00 : M 0 0 - M 1 1 = (D 0 0 - D 1 1) + (freePropagator 1 z 0 0 - freePropagator 1 z 1 1) := by
    rw [hMD]; simp; ring
  have d00 := NlsGge.ThirdConsultation.KSPS006Support.norm_entry_le_l2 D 0 0
  have d11 := NlsGge.ThirdConsultation.KSPS006Support.norm_entry_le_l2 D 1 1
  have d01 := NlsGge.ThirdConsultation.KSPS006Support.norm_entry_le_l2 D 0 1
  have d10 := NlsGge.ThirdConsultation.KSPS006Support.norm_entry_le_l2 D 1 0
  have hdiag : ‖M 0 0 - M 1 1‖ ≤ 2 * ‖D‖ + 2 * ‖Complex.sin z‖ := by
    rw [hm00]
    have := norm_add_le (D 0 0 - D 1 1) (freePropagator 1 z 0 0 - freePropagator 1 z 1 1)
    have := norm_sub_le (D 0 0) (D 1 1)
    linarith
  have hoff : ‖M 0 1 * M 1 0‖ ≤ ‖D‖ ^ 2 := by
    rw [hm01, hm10, norm_mul, sq]
    exact mul_le_mul d01 d10 (norm_nonneg _) (norm_nonneg _)
  rw [hid]
  calc _ ≤ ‖(M 0 0 - M 1 1) ^ 2‖ + ‖4 * (M 0 1 * M 1 0)‖ := norm_add_le _ _
    _ ≤ (2 * ‖D‖ + 2 * ‖Complex.sin z‖) ^ 2 + 4 * ‖D‖ ^ 2 := by
        rw [norm_pow, norm_mul, Complex.norm_ofNat]
        have h1 : ‖M 0 0 - M 1 1‖ ^ 2 ≤ (2 * ‖D‖ + 2 * ‖Complex.sin z‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hdiag 2
        nlinarith

theorem ball_facts {z : ℂ} {n : ℤ} (hz : ‖z - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 4)
    (hn : 1 ≤ n.natAbs) : (2 : ℝ) * n.natAbs ≤ ‖z‖ ∧ |z.im| ≤ 1 := by
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi' : 3.14 < Real.pi := Real.pi_gt_d2
  have hm : ‖(n : ℂ)‖ = (n.natAbs : ℝ) := by
    rw [Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs]
  have hn1 : (1 : ℝ) ≤ n.natAbs := by exact_mod_cast hn
  have hnz : ‖(n : ℂ) * (Real.pi : ℂ)‖ = (n.natAbs : ℝ) * Real.pi := by
    rw [norm_mul, hm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  constructor
  · have h1 := norm_sub_norm_le ((n : ℂ) * (Real.pi : ℂ)) z
    rw [norm_sub_rev, hnz] at h1
    have hmpi : 3.14 * (n.natAbs : ℝ) ≤ (n.natAbs : ℝ) * Real.pi := by nlinarith
    linarith
  · have him : z.im = (z - (n : ℂ) * (Real.pi : ℂ)).im := by simp
    rw [him]
    calc |(z - (n : ℂ) * (Real.pi : ℂ)).im| ≤ ‖z - (n : ℂ) * (Real.pi : ℂ)‖ :=
          Complex.abs_im_le_norm _
      _ ≤ 1 := by linarith

theorem cos_int_mul_pi_add (n : ℤ) (t : ℂ) :
    Complex.cos ((n : ℂ) * (Real.pi : ℂ) + t) = (-1 : ℂ) ^ n * Complex.cos t := by
  have hc : Complex.cos ((n : ℂ) * (Real.pi : ℂ)) = (-1 : ℂ) ^ n := by
    have h := Complex.ofReal_cos ((n : ℝ) * Real.pi)
    rw [Real.cos_int_mul_pi] at h
    push_cast at h
    exact h.symm
  rw [Complex.cos_add, Complex.sin_int_mul_pi, zero_mul, sub_zero, hc]

end PartB

/-! ### Part C -/

section PartC

open NlsGge.GK38 NlsGge.ThirdConsultation.KSPS
open NlsGge.Atomic.G1049S1

theorem unif_periodic_counting {B : ℝ} (hB : 0 ≤ B) :
    ∃ N : ℕ, ∀ φ ∈ Cset B, RootCountingAt38 (perChar φ) 2 N := by
  obtain ⟨R, hR⟩ := uniform_cmp (Cset B) (isCompact_Cset hB)
  obtain ⟨K, hK⟩ := exists_nat_gt (R / Real.pi)
  let N : ℕ := K + 1
  have hN : 0 < N := Nat.succ_pos K
  have hRN : R ≤ countingRadius38 N := by
    have h := (div_lt_iff₀ Real.pi_pos).mp hK
    unfold countingRadius38 N
    push_cast
    linarith [Real.pi_pos]
  refine ⟨N, fun φ hφ => ?_⟩
  have hcmp : ∀ z : ℂ, countingRadius38 N ≤ ‖z‖ →
      (∀ n : ℤ, Real.pi / 4 ≤ ‖z - countingCenter38 n‖) →
      ‖perChar φ z - perChar 0 z‖ < ‖perChar 0 z‖ :=
    fun z hz hsep => hR φ hφ z (hRN.trans hz) hsep
  have hsphere := counting_radius_mem_sphere38 N
  have hnorm : countingRadius38 N ≤ ‖(countingRadius38 N : ℂ)‖ := by
    simp [Complex.norm_real, abs_of_pos (countingRadius_pos38 N)]
  have hsep := counting_central_sphere_separated38 N hsphere
  obtain ⟨hs₁, hc₁, he₁⟩ := periodic_counting_at38 φ N hcmp
  refine ⟨hN, analyticOnNhd_perChar_z φ,
    ⟨_, counting_ne_zero_of_comparison38 (hcmp _ hnorm hsep)⟩,
    counting_zeroMult_support_finite38 φ, hs₁, ?_, he₁⟩
  omega

theorem labels_mem_ball {ψ : PotPair} {N : ℕ} (hp : RootCountingAt38 (perChar ψ) 2 N) {n : ℤ}
    (hn : (N : ℤ) < |n|) :
    ‖lamMinus ψ n - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 4 ∧
    ‖lamPlus ψ n - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 4 := by
  have hm := periodicCandidate_small_multiset38 hp hn
  have hS := lamSeq_eq_candidate38 ψ hp
  have h1 : lamMinus ψ n ∈ Lib.zeroMultiset (perChar ψ) (ball (countingCenter38 n) (Real.pi / 4)) := by
    rw [← hm]
    simp only [lamMinus, hS]
    exact Multiset.mem_cons_self _ _
  have h2 : lamPlus ψ n ∈ Lib.zeroMultiset (perChar ψ) (ball (countingCenter38 n) (Real.pi / 4)) := by
    rw [← hm]
    simp only [lamPlus, hS]
    exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)
  have g1 := ((Lib.mem_zeroMultiset_ball (hp.2.1.mono (subset_univ _))).1 h1).1
  have g2 := ((Lib.mem_zeroMultiset_ball (hp.2.1.mono (subset_univ _))).1 h2).1
  rw [Metric.mem_ball, dist_eq_norm] at g1 g2
  exact ⟨g1, g2⟩

end PartC

end NlsGge.ThirdConsultation.KSPS020Support
end
