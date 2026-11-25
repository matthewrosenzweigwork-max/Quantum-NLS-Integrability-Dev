import Mathlib
import NlsGge.Atomic.G4.G4036H3
import NlsGge.Atomic.G4.G4036H2
import NlsGge.Atomic.G4.G4036Host
import NlsGge.Atomic.G4.G4036Cauchy
import NlsGge.Atomic.G4.G4027
import NlsGge.Atomic.G4.G4017
import NlsGge.GK38.TauGamma
import NlsGge.GK38.IsolatingDefs

/- G4-046 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G4/G4046.lean,
   namespace NlsGge.GKDefinitionDesign as the landed G4 packets.
   Head: design STATEMENTS/G4.md G4-046 (identical in followup1..9; no Pro round states it), verbatim except the lexical
   rename `lam` for the keyword `λ` in hderiv.
   Route: see G4046_ROUTE.md. With T = cauchyOwnCorr (the landed G4036 coefficient) and z(u) = tau - (gamma/2) cosh u, the
   function Psi(u) = (gamma/2) sinh u * T(z(u)) + (K(tau)-1) u satisfies Psi' = -(K(z(u)) - K(tau)) by the landed ODE
   (G4036H2). With u* = slitPrimitive(2(mu-tau)/gamma) one has cosh u* = -rho, sinh u* = -slitRoot rho, z(u*) = mu and
   regularEtaIntegral = -Psi(u*). Psi(0) = 0 and the vertical-then-horizontal path in the u-plane stays in the convex hull of
   {lamMinus, lamPlus, mu} (explicit convex combination), giving |Psi(u*)| <= (pi/2) L (|gamma| + |mu - tau|).
   The collapsed case lamPlus = lamMinus is a separate Lipschitz argument for h(z) = (z-tau) T(z). -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory Metric
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.Atomic.G4036Cauchy

namespace NlsGge.GKDefinitionDesign
noncomputable section

namespace G4046Core

def zOf (τ γ : ℂ) (u : ℂ) : ℂ := τ - γ / 2 * Complex.cosh u

def Psi (T : ℂ → ℂ) (τ γ c₀ : ℂ) (u : ℂ) : ℂ :=
  γ / 2 * Complex.sinh u * T (zOf τ γ u) + c₀ * u

theorem norm_cosh_le (u : ℂ) : ‖Complex.cosh u‖ ≤ Real.cosh u.re := by
  have h : Complex.cosh u = (Complex.exp u + Complex.exp (-u)) / 2 := rfl
  rw [h, norm_div, Real.cosh_eq]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  gcongr
  calc ‖Complex.exp u + Complex.exp (-u)‖ ≤ ‖Complex.exp u‖ + ‖Complex.exp (-u)‖ := norm_add_le _ _
    _ = Real.exp u.re + Real.exp (-u.re) := by
      rw [Complex.norm_exp, Complex.norm_exp]; simp

theorem abs_sinh_le_norm_cosh (u : ℂ) : |Real.sinh u.re| ≤ ‖Complex.cosh u‖ := by
  have h : Complex.cosh u = (Complex.exp u + Complex.exp (-u)) / 2 := rfl
  have h1 := abs_norm_sub_norm_le (Complex.exp u) (-Complex.exp (-u))
  rw [sub_neg_eq_add, norm_neg, Complex.norm_exp, Complex.norm_exp] at h1
  simp only [Complex.neg_re] at h1
  rw [h, norm_div, Real.sinh_eq]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  gcongr

theorem hasDerivAt_zOf (τ γ u : ℂ) : HasDerivAt (zOf τ γ) (-(γ / 2 * Complex.sinh u)) u :=
  ((Complex.hasDerivAt_cosh u).const_mul (γ / 2)).const_sub τ

theorem hasDerivAt_Psi {T K : ℂ → ℂ} {c : ℂ} {r : ℝ} {τ γ : ℂ}
    (hT : AnalyticOnNhd ℂ T (ball c r))
    (hode : ∀ z ∈ ball c r,
      ((z - τ) ^ 2 - γ ^ 2 / 4) * deriv T z + (z - τ) * T z = K z - 1)
    (u : ℂ) (hu : zOf τ γ u ∈ ball c r) :
    HasDerivAt (Psi T τ γ (K τ - 1)) (-(K (zOf τ γ u) - K τ)) u := by
  have hz := hasDerivAt_zOf τ γ u
  have hTd : HasDerivAt T (deriv T (zOf τ γ u)) (zOf τ γ u) :=
    ((hT _ hu).differentiableAt).hasDerivAt
  have hc := hTd.comp u hz
  have hs := (Complex.hasDerivAt_sinh u).const_mul (γ / 2)
  have hp := hs.mul hc
  have hl := (hasDerivAt_id u).const_mul (K τ - 1)
  have hsum := hp.add hl
  have hode' := hode _ hu
  have hcs := Complex.cosh_sq u
  refine HasDerivAt.congr_deriv (f := Psi T τ γ (K τ - 1)) hsum ?_
  have e : zOf τ γ u - τ = -(γ / 2 * Complex.cosh u) := by unfold zOf; ring
  rw [e] at hode'
  simp only [Function.comp_apply]
  set d : ℂ := deriv T (zOf τ γ u) with hd
  linear_combination (-1 : ℂ) * hode' + (γ ^ 2 / 4 * d) * hcs

theorem norm_deriv_Psi_le {K : ℂ → ℂ} {c : ℂ} {r : ℝ} {τ γ : ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hKL : ∀ z ∈ ball c r, ‖K z - K τ‖ ≤ L * ‖z - τ‖)
    (u : ℂ) (hu : zOf τ γ u ∈ ball c r) :
    ‖-(K (zOf τ γ u) - K τ)‖ ≤ L * (‖γ‖ / 2 * Real.cosh u.re) := by
  rw [norm_neg]
  refine (hKL _ hu).trans ?_
  have e : zOf τ γ u - τ = -(γ / 2 * Complex.cosh u) := by unfold zOf; ring
  rw [e, norm_neg, norm_mul]
  have h2 : ‖γ / 2‖ = ‖γ‖ / 2 := by simp
  rw [h2]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_cosh_le u) (by positivity)) hL

theorem zOf_vertical_mem {c : ℂ} {r : ℝ} {τ γ : ℂ}
    (hm : τ - γ / 2 ∈ ball c r) (hp : τ + γ / 2 ∈ ball c r) (s : ℝ) :
    zOf τ γ ((s : ℂ) * Complex.I) ∈ ball c r := by
  have hcos : Complex.cosh ((s : ℂ) * Complex.I) = ((Real.cos s : ℝ) : ℂ) := by
    rw [Complex.cosh_mul_I, Complex.ofReal_cos]
  have hc1 := Real.neg_one_le_cos s
  have hc2 := Real.cos_le_one s
  have h := (convex_ball c r) hm hp (show (0 : ℝ) ≤ (1 + Real.cos s) / 2 by linarith)
    (show (0 : ℝ) ≤ (1 - Real.cos s) / 2 by linarith) (by ring)
  convert h using 1
  rw [Complex.real_smul, Complex.real_smul]
  unfold zOf
  rw [hcos]
  push_cast
  ring

theorem psi_vertical {T K : ℂ → ℂ} {c : ℂ} {r : ℝ} {τ γ : ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hT : AnalyticOnNhd ℂ T (ball c r))
    (hode : ∀ z ∈ ball c r,
      ((z - τ) ^ 2 - γ ^ 2 / 4) * deriv T z + (z - τ) * T z = K z - 1)
    (hKL : ∀ z ∈ ball c r, ‖K z - K τ‖ ≤ L * ‖z - τ‖)
    (hm : τ - γ / 2 ∈ ball c r) (hp : τ + γ / 2 ∈ ball c r) (b : ℝ) :
    ‖Psi T τ γ (K τ - 1) ((b : ℂ) * Complex.I)‖ ≤ L * (‖γ‖ / 2) * |b| := by
  have mem : ∀ t : ℝ, zOf τ γ ((t : ℂ) * ((b : ℂ) * Complex.I)) ∈ ball c r := by
    intro t
    have := zOf_vertical_mem hm hp (t * b)
    convert this using 2
    push_cast; ring
  let f : ℝ → ℂ := fun t => Psi T τ γ (K τ - 1) ((t : ℂ) * ((b : ℂ) * Complex.I))
  have h1 : ∀ t : ℝ, HasDerivAt f
      (-(K (zOf τ γ ((t : ℂ) * ((b : ℂ) * Complex.I))) - K τ) * ((b : ℂ) * Complex.I)) t := by
    intro t
    have e1 : HasDerivAt (fun s : ℂ => s * ((b : ℂ) * Complex.I)) ((b : ℂ) * Complex.I) (t : ℂ) := by
      simpa using (hasDerivAt_id (t : ℂ)).mul_const ((b : ℂ) * Complex.I)
    have e2 := (hasDerivAt_Psi hT hode ((t : ℂ) * ((b : ℂ) * Complex.I)) (mem t)).comp (t : ℂ) e1
    exact e2.comp_ofReal
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (a := 0) (b := 1)
    (C := L * (‖γ‖ / 2) * |b|) (fun x _ => (h1 x).hasDerivWithinAt) (fun x _ => by
      rw [norm_mul]
      have hb : ‖(b : ℂ) * Complex.I‖ = |b| := by simp
      rw [hb]
      have := norm_deriv_Psi_le hL hKL ((x : ℂ) * ((b : ℂ) * Complex.I)) (mem x)
      have hre : (((x : ℂ) * ((b : ℂ) * Complex.I))).re = 0 := by simp
      rw [hre, Real.cosh_zero, mul_one] at this
      calc ‖-(K (zOf τ γ ((x : ℂ) * ((b : ℂ) * Complex.I))) - K τ)‖ * |b|
          ≤ (L * (‖γ‖ / 2)) * |b| := mul_le_mul_of_nonneg_right this (abs_nonneg b)) 1
    (right_mem_Icc.2 zero_le_one)
  have h0 : f 0 = 0 := by simp [f, Psi]
  have h1' : f 1 = Psi T τ γ (K τ - 1) ((b : ℂ) * Complex.I) := by simp [f]
  rw [h0, h1'] at hmv
  simpa using hmv

theorem convex_three {s : Set ℂ} (hs : Convex ℝ s) {x y z : ℂ} (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c = 1) :
    (a : ℂ) * x + (b : ℂ) * y + (c : ℂ) * z ∈ s := by
  by_cases hbc : b + c = 0
  · have hb0 : b = 0 := by linarith
    have hc0 : c = 0 := by linarith
    have ha1 : a = 1 := by linarith
    subst hb0 hc0 ha1
    simpa using hx
  · have hbcp : 0 < b + c := lt_of_le_of_ne (add_nonneg hb hc) (Ne.symm hbc)
    have hw := hs hy hz (div_nonneg hb hbcp.le) (div_nonneg hc hbcp.le)
      (by field_simp)
    have := hs hx hw ha (add_nonneg hb hc) (by linarith)
    convert this using 1
    simp only [Complex.real_smul]
    push_cast
    have hbc' : (b : ℂ) + (c : ℂ) ≠ 0 := by exact_mod_cast hbc
    field_simp
    ring

theorem zOf_horizontal_mem {c : ℂ} {r : ℝ} {τ γ : ℂ}
    (hm : τ - γ / 2 ∈ ball c r) (hp : τ + γ / 2 ∈ ball c r) (a b : ℝ) (ha : 0 < a)
    (hμ : zOf τ γ ((a : ℂ) + (b : ℂ) * Complex.I) ∈ ball c r)
    (x : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    zOf τ γ ((x : ℂ) + (b : ℂ) * Complex.I) ∈ ball c r := by
  have hsa : 0 < Real.sinh a := Real.sinh_pos_iff.2 ha
  have hsx : 0 ≤ Real.sinh x := Real.sinh_nonneg_iff.2 hx0
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = Real.sinh x / Real.sinh a := ⟨_, rfl⟩
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = Real.cosh x - θ * Real.cosh a := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := by rw [hθ]; exact div_nonneg hsx hsa.le
  have hθ1 : θ ≤ 1 := by
    rw [hθ]; exact (div_le_one hsa).2 (Real.sinh_le_sinh.2 hxa)
  have hθs : θ * Real.sinh a = Real.sinh x := by rw [hθ]; field_simp
  have hsub : Real.sinh (a - x) = Real.sinh a * Real.cosh x - Real.cosh a * Real.sinh x := Real.sinh_sub a x
  have hmsa : m * Real.sinh a = Real.sinh (a - x) := by
    rw [hsub, hmdef]
    have : (Real.cosh x - θ * Real.cosh a) * Real.sinh a
        = Real.cosh x * Real.sinh a - (θ * Real.sinh a) * Real.cosh a := by ring
    rw [this, hθs]; ring
  have hsax : 0 ≤ Real.sinh (a - x) := Real.sinh_nonneg_iff.2 (by linarith)
  have hm0 : 0 ≤ m := by
    by_contra h
    push_neg at h
    nlinarith
  have hkey : Real.sinh x + Real.sinh (a - x) ≤ Real.sinh a := by
    have e : Real.sinh a = Real.sinh x * Real.cosh (a - x) + Real.cosh x * Real.sinh (a - x) := by
      have := Real.sinh_add x (a - x)
      rw [show x + (a - x) = a by ring] at this
      exact this
    nlinarith [Real.one_le_cosh x, Real.one_le_cosh (a - x), hsx, hsax]
  have hm1 : m ≤ 1 - θ := by
    by_contra h
    push_neg at h
    nlinarith
  have hC1 := Real.neg_one_le_cos b
  have hC2 := Real.cos_le_one b
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = Real.cos b * m := ⟨_, rfl⟩
  have he1 : e ≤ 1 - θ := by
    rw [hedef]; nlinarith
  have he2 : -(1 - θ) ≤ e := by
    rw [hedef]; nlinarith
  have hcx : Complex.cosh ((x : ℂ) + (b : ℂ) * Complex.I) =
      (Real.cosh x : ℂ) * (Real.cos b : ℂ) + (Real.sinh x : ℂ) * ((Real.sin b : ℂ) * Complex.I) := by
    rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cosh,
      ← Complex.ofReal_sinh, Complex.ofReal_cos, Complex.ofReal_sin]
  have hca : Complex.cosh ((a : ℂ) + (b : ℂ) * Complex.I) =
      (Real.cosh a : ℂ) * (Real.cos b : ℂ) + (Real.sinh a : ℂ) * ((Real.sin b : ℂ) * Complex.I) := by
    rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cosh,
      ← Complex.ofReal_sinh, Complex.ofReal_cos, Complex.ofReal_sin]
  have hθc : (θ : ℂ) * (Real.sinh a : ℂ) = (Real.sinh x : ℂ) := by exact_mod_cast hθs
  have hmc : (m : ℂ) = (Real.cosh x : ℂ) - (θ : ℂ) * (Real.cosh a : ℂ) := by
    rw [hmdef]; push_cast; ring
  have hsum := convex_three (convex_ball c r) hμ hm hp (a := θ) (b := (1 - θ + e) / 2)
    (c := (1 - θ - e) / 2) hθ0 (by linarith) (by linarith) (by ring)
  convert hsum using 1
  unfold zOf
  rw [hcx, hca]
  have hec' : (e : ℂ) = Complex.cos (b : ℂ) *
      (Complex.cosh (x : ℂ) - (θ : ℂ) * Complex.cosh (a : ℂ)) := by
    rw [hedef, hmdef]; push_cast; ring
  have hθc' : (θ : ℂ) * Complex.sinh (a : ℂ) = Complex.sinh (x : ℂ) := by
    have := hθc; push_cast at this; exact this
  push_cast
  rw [hec']
  linear_combination (γ / 2 * (Complex.sin (b : ℂ) * Complex.I)) * hθc'

theorem psi_horizontal {T K : ℂ → ℂ} {c : ℂ} {r : ℝ} {τ γ : ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hT : AnalyticOnNhd ℂ T (ball c r))
    (hode : ∀ z ∈ ball c r,
      ((z - τ) ^ 2 - γ ^ 2 / 4) * deriv T z + (z - τ) * T z = K z - 1)
    (hKL : ∀ z ∈ ball c r, ‖K z - K τ‖ ≤ L * ‖z - τ‖)
    (a b : ℝ) (ha : 0 < a)
    (hmem : ∀ t ∈ Icc (0 : ℝ) 1, zOf τ γ ((t : ℂ) * (a : ℂ) + (b : ℂ) * Complex.I) ∈ ball c r) :
    ‖Psi T τ γ (K τ - 1) ((a : ℂ) + (b : ℂ) * Complex.I) -
      Psi T τ γ (K τ - 1) ((b : ℂ) * Complex.I)‖ ≤ L * (‖γ‖ / 2) * Real.sinh a := by
  let f : ℝ → ℂ := fun t => Psi T τ γ (K τ - 1) ((t : ℂ) * (a : ℂ) + (b : ℂ) * Complex.I) -
    Psi T τ γ (K τ - 1) ((b : ℂ) * Complex.I)
  have h1 : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f
      (-(K (zOf τ γ ((t : ℂ) * (a : ℂ) + (b : ℂ) * Complex.I)) - K τ) * (a : ℂ)) t := by
    intro t ht
    have e1 : HasDerivAt (fun s : ℂ => s * (a : ℂ) + (b : ℂ) * Complex.I) (a : ℂ) (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const (a : ℂ)).add_const ((b : ℂ) * Complex.I)
    have e2 := (hasDerivAt_Psi hT hode ((t : ℂ) * (a : ℂ) + (b : ℂ) * Complex.I) (hmem t ht)).comp
      (t : ℂ) e1
    exact (e2.comp_ofReal).sub_const _
  have hB : ∀ t : ℝ, HasDerivAt (fun t : ℝ => L * (‖γ‖ / 2) * Real.sinh (a * t))
      (L * (‖γ‖ / 2) * (a * Real.cosh (a * t))) t := by
    intro t
    have := ((Real.hasDerivAt_sinh (a * t)).comp t ((hasDerivAt_id t).const_mul a)).const_mul
      (L * (‖γ‖ / 2))
    convert this using 1
    simp
    ring
  have hcont : ContinuousOn f (Icc (0 : ℝ) 1) := fun t ht => (h1 t ht).continuousAt.continuousWithinAt
  have hbd := image_norm_le_of_norm_deriv_right_le_deriv_boundary hcont
    (f' := fun t => -(K (zOf τ γ ((t : ℂ) * (a : ℂ) + (b : ℂ) * Complex.I)) - K τ) * (a : ℂ))
    (fun x hx => (h1 x (Ico_subset_Icc_self hx)).hasDerivWithinAt)
    (B := fun t : ℝ => L * (‖γ‖ / 2) * Real.sinh (a * t))
    (B' := fun t => L * (‖γ‖ / 2) * (a * Real.cosh (a * t)))
    (by simp [f]) hB (fun x hx => by
      rw [norm_mul]
      have ha' : ‖(a : ℂ)‖ = a := by simp [abs_of_pos ha]
      rw [ha']
      have := norm_deriv_Psi_le hL hKL ((x : ℂ) * (a : ℂ) + (b : ℂ) * Complex.I)
        (hmem x (Ico_subset_Icc_self hx))
      have hre : (((x : ℂ) * (a : ℂ) + (b : ℂ) * Complex.I)).re = x * a := by simp
      rw [hre] at this
      have hc : Real.cosh (x * a) = Real.cosh (a * x) := by rw [mul_comm]
      rw [hc] at this
      calc ‖-(K (zOf τ γ ((x : ℂ) * (a : ℂ) + (b : ℂ) * Complex.I)) - K τ)‖ * a
          ≤ (L * (‖γ‖ / 2 * Real.cosh (a * x))) * a := mul_le_mul_of_nonneg_right this ha.le
        _ = L * (‖γ‖ / 2) * (a * Real.cosh (a * x)) := by ring) (x := 1) ⟨zero_le_one, le_rfl⟩
  have hf1 : f 1 = Psi T τ γ (K τ - 1) ((a : ℂ) + (b : ℂ) * Complex.I) -
      Psi T τ γ (K τ - 1) ((b : ℂ) * Complex.I) := by simp [f]
  rw [hf1] at hbd
  simpa using hbd


theorem Psi_odd (T : ℂ → ℂ) (τ γ c₀ u : ℂ) :
    Psi T τ γ c₀ (-u) = -Psi T τ γ c₀ u := by
  unfold Psi zOf
  rw [Complex.sinh_neg, Complex.cosh_neg]
  ring

theorem psi_bound_nonneg {T K : ℂ → ℂ} {c : ℂ} {r : ℝ} {τ γ : ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hT : AnalyticOnNhd ℂ T (ball c r))
    (hode : ∀ z ∈ ball c r,
      ((z - τ) ^ 2 - γ ^ 2 / 4) * deriv T z + (z - τ) * T z = K z - 1)
    (hKL : ∀ z ∈ ball c r, ‖K z - K τ‖ ≤ L * ‖z - τ‖)
    (hm : τ - γ / 2 ∈ ball c r) (hp : τ + γ / 2 ∈ ball c r)
    (u : ℂ) (hre : 0 ≤ u.re) (hu : zOf τ γ u ∈ ball c r) :
    ‖Psi T τ γ (K τ - 1) u‖ ≤ L * (‖γ‖ / 2) * (|u.im| + Real.sinh u.re) := by
  have hu' : u = (u.re : ℂ) + (u.im : ℂ) * Complex.I := (Complex.re_add_im u).symm
  have hv := psi_vertical hL hT hode hKL hm hp u.im
  rcases hre.eq_or_lt with h0 | hpos
  · have hu0 : u = (u.im : ℂ) * Complex.I := by
      rw [hu']; rw [← h0]; simp
    rw [hu0] at *
    have : Real.sinh (((u.im : ℂ) * Complex.I).re) = 0 := by simp
    rw [this]
    simpa using hv
  · rw [hu'] at hu
    have hmem : ∀ t ∈ Icc (0 : ℝ) 1,
        zOf τ γ ((t : ℂ) * (u.re : ℂ) + (u.im : ℂ) * Complex.I) ∈ ball c r := by
      intro t ht
      have := zOf_horizontal_mem hm hp u.re u.im hpos hu (t * u.re)
        (mul_nonneg ht.1 hre) (by nlinarith [ht.2])
      convert this using 2
      push_cast; ring
    have hh := psi_horizontal hL hT hode hKL u.re u.im hpos hmem
    rw [← hu'] at hh
    calc ‖Psi T τ γ (K τ - 1) u‖
        = ‖(Psi T τ γ (K τ - 1) u - Psi T τ γ (K τ - 1) ((u.im : ℂ) * Complex.I)) +
            Psi T τ γ (K τ - 1) ((u.im : ℂ) * Complex.I)‖ := by rw [sub_add_cancel]
      _ ≤ ‖Psi T τ γ (K τ - 1) u - Psi T τ γ (K τ - 1) ((u.im : ℂ) * Complex.I)‖ +
            ‖Psi T τ γ (K τ - 1) ((u.im : ℂ) * Complex.I)‖ := norm_add_le _ _
      _ ≤ L * (‖γ‖ / 2) * Real.sinh u.re + L * (‖γ‖ / 2) * |u.im| := add_le_add hh hv
      _ = L * (‖γ‖ / 2) * (|u.im| + Real.sinh u.re) := by ring

theorem psi_bound {T K : ℂ → ℂ} {c : ℂ} {r : ℝ} {τ γ : ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hT : AnalyticOnNhd ℂ T (ball c r))
    (hode : ∀ z ∈ ball c r,
      ((z - τ) ^ 2 - γ ^ 2 / 4) * deriv T z + (z - τ) * T z = K z - 1)
    (hKL : ∀ z ∈ ball c r, ‖K z - K τ‖ ≤ L * ‖z - τ‖)
    (hm : τ - γ / 2 ∈ ball c r) (hp : τ + γ / 2 ∈ ball c r)
    (u : ℂ) (hu : zOf τ γ u ∈ ball c r) :
    ‖Psi T τ γ (K τ - 1) u‖ ≤ L * (‖γ‖ / 2) * (|u.im| + Real.sinh |u.re|) := by
  rcases le_or_gt 0 u.re with h | h
  · rw [abs_of_nonneg h]
    exact psi_bound_nonneg hL hT hode hKL hm hp u h hu
  · have hz : zOf τ γ (-u) = zOf τ γ u := by unfold zOf; rw [Complex.cosh_neg]
    have hre : 0 ≤ (-u).re := by simp; linarith
    have := psi_bound_nonneg hL hT hode hKL hm hp (-u) hre (by rw [hz]; exact hu)
    rw [Psi_odd, norm_neg] at this
    have e1 : (-u).im = -u.im := by simp
    have e2 : (-u).re = -u.re := by simp
    rw [e1, e2, abs_neg] at this
    rw [abs_of_neg h]
    exact this

theorem psi_final {T K : ℂ → ℂ} {c : ℂ} {r : ℝ} {τ γ : ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hT : AnalyticOnNhd ℂ T (ball c r))
    (hode : ∀ z ∈ ball c r,
      ((z - τ) ^ 2 - γ ^ 2 / 4) * deriv T z + (z - τ) * T z = K z - 1)
    (hKL : ∀ z ∈ ball c r, ‖K z - K τ‖ ≤ L * ‖z - τ‖)
    (hm : τ - γ / 2 ∈ ball c r) (hp : τ + γ / 2 ∈ ball c r)
    (u : ℂ) (hu : zOf τ γ u ∈ ball c r) (him : |u.im| ≤ Real.pi) :
    ‖Psi T τ γ (K τ - 1) u‖ ≤ (Real.pi / 2) * L * (‖γ‖ + ‖zOf τ γ u - τ‖) := by
  have h1 := psi_bound hL hT hode hKL hm hp u hu
  have hs : Real.sinh |u.re| ≤ ‖Complex.cosh u‖ := by
    have := abs_sinh_le_norm_cosh u
    rcases le_or_gt 0 u.re with h | h
    · rw [abs_of_nonneg h] at *
      exact (le_abs_self _).trans this
    · rw [abs_of_neg h, Real.sinh_neg]
      rw [abs_of_neg h] at *
      exact (neg_le_abs _).trans (by simpa [Real.sinh_neg] using this)
  have e : ‖zOf τ γ u - τ‖ = ‖γ‖ / 2 * ‖Complex.cosh u‖ := by
    have : zOf τ γ u - τ = -(γ / 2 * Complex.cosh u) := by unfold zOf; ring
    rw [this, norm_neg, norm_mul]
    have h2 : ‖γ / 2‖ = ‖γ‖ / 2 := by simp
    rw [h2]
  have hpi := Real.pi_gt_three
  have hg : 0 ≤ ‖γ‖ := norm_nonneg _
  have hn : 0 ≤ ‖Complex.cosh u‖ := norm_nonneg _
  calc ‖Psi T τ γ (K τ - 1) u‖ ≤ L * (‖γ‖ / 2) * (|u.im| + Real.sinh |u.re|) := h1
    _ ≤ L * (‖γ‖ / 2) * (Real.pi + ‖Complex.cosh u‖) := by
        gcongr
    _ = (Real.pi / 2) * L * ‖γ‖ + L * ‖zOf τ γ u - τ‖ := by rw [e]; ring
    _ ≤ (Real.pi / 2) * L * (‖γ‖ + ‖zOf τ γ u - τ‖) := by
        have : L * ‖zOf τ γ u - τ‖ ≤ (Real.pi / 2) * L * ‖zOf τ γ u - τ‖ := by
          have h3 : 0 ≤ L * ‖zOf τ γ u - τ‖ := by positivity
          nlinarith
        nlinarith

theorem degenerate_bound {T K : ℂ → ℂ} {c : ℂ} {r : ℝ} {τ : ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hT : AnalyticOnNhd ℂ T (ball c r))
    (hode0 : ∀ z ∈ ball c r, (z - τ) ^ 2 * deriv T z + (z - τ) * T z = K z - 1)
    (hKL : ∀ z ∈ ball c r, ‖K z - K τ‖ ≤ L * ‖z - τ‖)
    (hτ : τ ∈ ball c r) (μ : ℂ) (hμ : μ ∈ ball c r) :
    ‖(τ - μ) * T μ‖ ≤ L * ‖μ - τ‖ := by
  have hKτ : K τ = 1 := by
    have := hode0 τ hτ
    simp at this
    linear_combination -this
  let h : ℂ → ℂ := fun z => (z - τ) * T z
  let h' : ℂ → ℂ := fun z => T z + (z - τ) * deriv T z
  have hd : ∀ z ∈ ball c r, HasDerivAt h (h' z) z := by
    intro z hz
    have := ((hasDerivAt_id z).sub_const τ).mul ((hT z hz).differentiableAt.hasDerivAt)
    have hfun : h = (fun x => id x - τ) * T := by funext x; simp [h]
    rw [hfun]
    exact this.congr_deriv (by simp [h'])
  have hb0 : ∀ z ∈ ball c r, z ≠ τ → ‖h' z‖ ≤ L := by
    intro z hz hne
    have e : (z - τ) * h' z = K z - K τ := by
      simp only [h']
      rw [hKτ]
      have := hode0 z hz
      linear_combination this
    have hpos : 0 < ‖z - τ‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    have h2 : ‖z - τ‖ * ‖h' z‖ ≤ ‖z - τ‖ * L := by
      rw [← norm_mul, e]
      have := hKL z hz
      linarith
    exact le_of_mul_le_mul_left h2 hpos
  have hbτ : ‖h' τ‖ ≤ L := by
    have a1 : AnalyticAt ℂ T τ := hT τ hτ
    have a2 : AnalyticAt ℂ (deriv T) τ := a1.deriv
    have hcont : ContinuousAt h' τ :=
      a1.continuousAt.add ((continuousAt_id.sub continuousAt_const).mul a2.continuousAt)
    have ht : Tendsto (fun z => ‖h' z‖) (𝓝[≠] τ) (𝓝 ‖h' τ‖) :=
      hcont.norm.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto ht ?_
    have h1 : ball c r ∈ 𝓝[≠] τ := mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hτ)
    filter_upwards [h1, self_mem_nhdsWithin] with z hz hne using hb0 z hz hne
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := h) (f' := h') (C := L)
    (fun x hx => (hd x hx).hasDerivWithinAt)
    (fun x hx => by
      by_cases hxτ : x = τ
      · rw [hxτ]; exact hbτ
      · exact hb0 x hx hxτ)
    (convex_ball c r) hτ hμ
  have hh0 : h τ = 0 := by simp [h]
  rw [hh0, sub_zero] at hmv
  have e : (τ - μ) * T μ = -h μ := by simp only [h]; ring
  rw [e, norm_neg]
  exact hmv

end G4046Core

open G4046Core in
theorem G4046 (V : Set PotPair) (hV : V ⊆ sourceBetaW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (ε L : ℝ)
    (hε : 0 < ε) (hL : 0 ≤ L)
    (hR : ∀ n : ℤ, ε < R n)
    (hfamily : ∀ φ ∈ V, IsolatingFamily38 φ C R)
    (hcollar : ∀ φ ∈ V, ∀ n : ℤ,
      gapSegment φ n ⊆ Metric.closedBall (C n) (R n - ε) ∧
      muSeq φ n ∈ Metric.closedBall (C n) (R n - ε))
    (hderiv : ∀ φ ∈ V, ∀ n : ℤ, ∀ lam ∈ Metric.ball (C n) (R n),
      DifferentiableAt ℂ (normalizedZeta n φ) lam ∧
      ‖deriv (normalizedZeta n φ) lam‖ ≤ L) :
  ∃ A : ℝ, 0 < A ∧ ∀ φ ∈ V, ∀ n : ℤ,
    ‖regularEtaIntegral n φ‖ ≤ A * L *
      (‖lamPlus φ n - lamMinus φ n‖ + ‖muSeq φ n - tauN φ n‖) := by
  refine ⟨Real.pi / 2, by positivity, fun φ hφ n => ?_⟩
  have hφS : φ ∈ sourceBetaW := hV hφ
  have hgk : φ ∈ gkW := G4017Aux.sourceBetaW_gkW hφS
  obtain ⟨c, N, hg, hs⟩ := hfamily φ hφ
  obtain ⟨hTan, hode⟩ := g4036_family_ode φ hgk C R c N hg hs n
    (g4036_zero_period_family n φ hφS C R c N hg hs)
  have hid := g4036_identify n φ hφS C R c N hg hs
  have hεR : Metric.closedBall (C n) (R n - ε) ⊆ Metric.ball (C n) (R n) :=
    Metric.closedBall_subset_ball (by linarith)
  have hballgap : ∀ z ∈ gapSegment φ n, z ∈ Metric.ball (C n) (R n) :=
    fun z hz => hεR ((hcollar φ hφ n).1 hz)
  have hlm : lamMinus φ n ∈ Metric.ball (C n) (R n) :=
    hballgap _ (left_mem_segment ℝ _ _)
  have hlp : lamPlus φ n ∈ Metric.ball (C n) (R n) :=
    hballgap _ (right_mem_segment ℝ _ _)
  have hτ : tauN φ n ∈ Metric.ball (C n) (R n) :=
    hballgap _ (g4036_tau_mem φ hgk n)
  have hμ : muSeq φ n ∈ Metric.ball (C n) (R n) := hεR (hcollar φ hφ n).2
  have hKL : ∀ z ∈ Metric.ball (C n) (R n),
      ‖normalizedZeta n φ z - normalizedZeta n φ (tauN φ n)‖ ≤ L * ‖z - tauN φ n‖ := by
    intro z hz
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := normalizedZeta n φ)
      (f' := deriv (normalizedZeta n φ)) (C := L)
      (fun x hx => ((hderiv φ hφ n x hx).1.hasDerivAt).hasDerivWithinAt)
      (fun x hx => (hderiv φ hφ n x hx).2) (convex_ball (C n) (R n)) hτ hz
    exact this
  have hγ2 : gamma2 φ n = (lamPlus φ n - lamMinus φ n) ^ 2 := gamma2_value38 φ hgk n
  have hτv : tauN φ n = (lamPlus φ n + lamMinus φ n) / 2 := tauN_value38 φ hgk n
  have hodeC : ∀ z ∈ Metric.ball (C n) (R n),
      ((z - tauN φ n) ^ 2 - (lamPlus φ n - lamMinus φ n) ^ 2 / 4) *
          deriv (cauchyOwnCorr (C n) (R n) (normalizedZeta n φ) (standardRoot φ n)) z +
        (z - tauN φ n) * cauchyOwnCorr (C n) (R n) (normalizedZeta n φ) (standardRoot φ n) z =
          normalizedZeta n φ z - 1 := by
    intro z hz
    have := hode z hz
    rwa [hγ2] at this
  by_cases hne : lamPlus φ n = lamMinus φ n
  · -- collapsed gap: lamPlus = lamMinus
    have hreg : regularEtaIntegral n φ =
        (tauN φ n - muSeq φ n) *
          cauchyOwnCorr (C n) (R n) (normalizedZeta n φ) (standardRoot φ n) (muSeq φ n) := by
      unfold regularEtaIntegral localRootAtDirichlet constantEtaCorrection elementaryEtaIntegral
      rw [dif_pos hne, if_pos hne, hid]
      simp
    have hode0 : ∀ z ∈ Metric.ball (C n) (R n),
        (z - tauN φ n) ^ 2 *
            deriv (cauchyOwnCorr (C n) (R n) (normalizedZeta n φ) (standardRoot φ n)) z +
          (z - tauN φ n) *
            cauchyOwnCorr (C n) (R n) (normalizedZeta n φ) (standardRoot φ n) z =
          normalizedZeta n φ z - 1 := by
      intro z hz
      have := hodeC z hz
      rw [hne, sub_self] at this
      simpa using this
    have hdeg := degenerate_bound hL hTan hode0 hKL hτ (muSeq φ n) hμ
    rw [hreg]
    have hg0 : ‖lamPlus φ n - lamMinus φ n‖ = 0 := by rw [hne, sub_self, norm_zero]
    rw [hg0, zero_add]
    refine hdeg.trans ?_
    have hn : 0 ≤ L * ‖muSeq φ n - tauN φ n‖ := by positivity
    have hpi := Real.pi_gt_three
    nlinarith
  · -- genuine gap
    have hγ : lamPlus φ n - lamMinus φ n ≠ 0 := sub_ne_zero.mpr hne
    set γ : ℂ := lamPlus φ n - lamMinus φ n with hγdef
    set ρ : ℂ := 2 * (muSeq φ n - tauN φ n) / γ with hρ
    set u : ℂ := slitPrimitive ρ with hu
    have hexp : Complex.exp u = -ρ - slitRoot ρ := G4027Aux.exp_slit ρ
    have hexpn : Complex.exp (-u) = -ρ + slitRoot ρ := G4027Aux.exp_slit_neg ρ
    have hcosh : Complex.cosh u = -ρ := by
      show (Complex.exp u + Complex.exp (-u)) / 2 = -ρ
      rw [hexp, hexpn]; ring
    have hsinh : Complex.sinh u = -slitRoot ρ := by
      rw [Complex.sinh, show (Complex.exp u - Complex.exp (-u)) / 2 = -slitRoot ρ by
        rw [hexp, hexpn]; ring]
    have hz : zOf (tauN φ n) γ u = muSeq φ n := by
      unfold zOf
      rw [hcosh, hρ]
      field_simp
      ring
    have him : |u.im| ≤ Real.pi := by
      rw [hu]
      unfold slitPrimitive
      rw [Complex.log_im]
      exact Complex.abs_arg_le_pi _
    have hm : tauN φ n - γ / 2 ∈ Metric.ball (C n) (R n) := by
      have : tauN φ n - γ / 2 = lamMinus φ n := by rw [hτv, hγdef]; ring
      rw [this]; exact hlm
    have hp : tauN φ n + γ / 2 ∈ Metric.ball (C n) (R n) := by
      have : tauN φ n + γ / 2 = lamPlus φ n := by rw [hτv, hγdef]; ring
      rw [this]; exact hlp
    have hodeC' : ∀ z ∈ Metric.ball (C n) (R n),
        ((z - tauN φ n) ^ 2 - γ ^ 2 / 4) *
            deriv (cauchyOwnCorr (C n) (R n) (normalizedZeta n φ) (standardRoot φ n)) z +
          (z - tauN φ n) *
            cauchyOwnCorr (C n) (R n) (normalizedZeta n φ) (standardRoot φ n) z =
          normalizedZeta n φ z - 1 := hodeC
    have hfin := psi_final hL hTan hodeC' hKL hm hp u (by rw [hz]; exact hμ) him
    rw [hz] at hfin
    have hreg : regularEtaIntegral n φ =
        -Psi (cauchyOwnCorr (C n) (R n) (normalizedZeta n φ) (standardRoot φ n))
          (tauN φ n) γ (normalizedZeta n φ (tauN φ n) - 1) u := by
      unfold regularEtaIntegral localRootAtDirichlet constantEtaCorrection elementaryEtaIntegral
      rw [dif_neg hne, if_neg hne, hid]
      unfold Psi
      rw [hz, hsinh]
      change γ / 2 * slitRoot ρ * _ - _ * u = _
      ring
    rw [hreg, norm_neg]
    exact hfin


end
end NlsGge.GKDefinitionDesign
