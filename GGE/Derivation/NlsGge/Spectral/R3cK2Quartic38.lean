import NlsGge.Spectral.R3cK2ResolventSplit38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.HierarchyRiccati.Core

theorem quartic_alg38 (r U U1 Ub Ub1 T Q ρ G : ℂ) (hρ : ρ = r * U + r ^ 2 * U1 + r ^ 2 * T)
    (hG : G = r * Ub - r ^ 2 * Ub1 + r ^ 2 * Q) :
    ρ * (U * G ^ 2) =
      r ^ 3 * (U * Ub) ^ 2 + r ^ 4 * (U1 * U * Ub ^ 2) - 2 * r ^ 4 * (U ^ 2 * Ub * Ub1)
      + r ^ 5 * (U ^ 2 * Ub1 ^ 2) - 2 * r ^ 5 * ((U * Ub) * (U1 * Ub1))
      + r ^ 4 * (T * (U * Ub ^ 2)) + 2 * r ^ 4 * ((U * Ub * U) * Q)
      + r ^ 2 * U1 * U * (r ^ 2 * Ub1) ^ 2
      + r ^ 2 * ((U * (-(r ^ 2 * Ub1)) * (r * Ub + (r * Ub - r ^ 2 * Ub1))) * T)
      + 2 * r ^ 2 * ((U * (r * U * (-(r ^ 2 * Ub1)) + r ^ 2 * U1 * (r * Ub - r ^ 2 * Ub1))) * Q)
      + 2 * r ^ 4 * (T * ((U * (r * Ub - r ^ 2 * Ub1)) * Q))
      + r ^ 4 * (Q * ((ρ * U) * Q)) := by
  subst hG
  rw [hρ]
  ring


theorem nr38 {r : ℝ} (hr : 0 ≤ r) : ‖(r : ℂ)‖ = r := by
  rw [Complex.norm_real, Real.norm_of_nonneg hr]

theorem sqrt_l2sq_le38 {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) {T : ℝ → ℂ}
    (hTb : l2sq38 T ≤ (s * r) ^ 2) : Real.sqrt (l2sq38 T) ≤ s * r := by
  calc Real.sqrt (l2sq38 T) ≤ Real.sqrt ((s * r) ^ 2) := Real.sqrt_le_sqrt hTb
    _ = s * r := Real.sqrt_sq (by positivity)

theorem piece_sup38 {s r M : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) {f T : ℝ → ℂ} (hf : Continuous f)
    (hT : Continuous T) (hM : ∀ x, ‖f x‖ ≤ M) (hTb : l2sq38 T ≤ (s * r) ^ 2) (c : ℂ) :
    ‖∫ x in (0:ℝ)..1, c * (f x * T x)‖ ≤ ‖c‖ * (M * (s * r)) := by
  rw [intervalIntegral.integral_const_mul, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h := norm_pair38_le_sup hf hT hM
  exact h.trans (mul_le_mul_of_nonneg_left (sqrt_l2sq_le38 hs hr hTb)
    ((norm_nonneg _).trans (hM 0)))

theorem piece_l2_38 {s r M : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) {T Q h : ℝ → ℂ} (hT : Continuous T)
    (hQ : Continuous Q) (hh : Continuous h) (hM : ∀ x, ‖h x‖ ≤ M)
    (hTb : l2sq38 T ≤ (s * r) ^ 2) (hQb : l2sq38 Q ≤ (s * r) ^ 2) (c : ℂ) :
    ‖∫ x in (0:ℝ)..1, c * (T x * (h x * Q x))‖ ≤ ‖c‖ * ((s * r) * (M * (s * r))) := by
  rw [intervalIntegral.integral_const_mul, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h1 := norm_pair38_le_l2 hT (hh.mul hQ)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have h2 : l2sq38 (fun x => h x * Q x) ≤ (M * (s * r)) ^ 2 :=
    (l2sq38_mul_le hh hQ hM).trans (by rw [mul_pow]; gcongr)
  have h3 : Real.sqrt (l2sq38 (fun x => h x * Q x)) ≤ M * (s * r) := by
    calc _ ≤ Real.sqrt ((M * (s * r)) ^ 2) := Real.sqrt_le_sqrt h2
      _ = M * (s * r) := Real.sqrt_sq (by positivity)
  exact h1.trans (mul_le_mul (sqrt_l2sq_le38 hs hr hTb) h3 (Real.sqrt_nonneg _) (by positivity))


theorem quartic_abs38 {r A0 A1 s C1 C2 : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hA0 : 0 ≤ A0)
    (hA1 : 0 ≤ A1) (hs : 0 ≤ s) {U U1 U2 T Q ρ G : ℝ → ℂ}
    (hU : PerC1_38 U U1) (hU1 : PerC1_38 U1 U2) (hTc : Continuous T) (hQc : Continuous Q)
    (hρ : ∀ x, ρ x = (r : ℂ) * U x + (r : ℂ) ^ 2 * U1 x + (r : ℂ) ^ 2 * T x)
    (hG : ∀ x, G x = (r : ℂ) * star (U x) - (r : ℂ) ^ 2 * star (U1 x) + (r : ℂ) ^ 2 * Q x)
    (hUb : ∀ x, ‖U x‖ ≤ A0) (hU1b : ∀ x, ‖U1 x‖ ≤ A1) (hρb : ∀ x, ‖ρ x‖ ≤ r * A0)
    (hTb : l2sq38 T ≤ (s * r) ^ 2) (hQb : l2sq38 Q ≤ (s * r) ^ 2)
    (hK1 : ‖pair38 T (fun x => U x * star (U x) ^ 2) -
      (r : ℂ) * (∫ x in (0:ℝ)..1, U2 x * U x * star (U x) ^ 2)‖ ≤ C1 * r ^ 2)
    (hK2 : ‖pair38 (fun x => U x * star (U x) * U x) Q -
      (r : ℂ) * (∫ x in (0:ℝ)..1, U x * star (U x) * U x * star (U2 x))‖ ≤ C2 * r ^ 2) :
    ‖pair38 ρ (fun x => U x * G x ^ 2) -
      ((r : ℂ) ^ 3 * (∫ x in (0:ℝ)..1, (U x * star (U x)) ^ 2)
      + (r : ℂ) ^ 4 * (∫ x in (0:ℝ)..1, U1 x * U x * star (U x) ^ 2)
      - 2 * (r : ℂ) ^ 4 * (∫ x in (0:ℝ)..1, U x ^ 2 * star (U x) * star (U1 x))
      + (r : ℂ) ^ 5 * ((∫ x in (0:ℝ)..1, U2 x * U x * star (U x) ^ 2)
          + (∫ x in (0:ℝ)..1, U x ^ 2 * star (U1 x) ^ 2)
          + 2 * (∫ x in (0:ℝ)..1, U x * star (U x) * U x * star (U2 x)))
      - 2 * (r : ℂ) ^ 5 * (∫ x in (0:ℝ)..1, (U x * star (U x)) * (U1 x * star (U1 x))))‖ ≤
    (A0 * A1 ^ 3 + 3 * A0 * A1 * (2 * A0 + A1) * s + 2 * s ^ 2 * A0 * (A0 + A1)
      + A0 ^ 2 * s ^ 2 + C1 + 2 * C2) * r ^ 6 := by
  have hUc : Continuous U := hU.cont
  have hU1c : Continuous U1 := hU.cont'
  have hU2c : Continuous U2 := hU1.cont'
  have hρc : Continuous ρ := by
    rw [show ρ = fun x => (r : ℂ) * U x + (r : ℂ) ^ 2 * U1 x + (r : ℂ) ^ 2 * T x from funext hρ]
    fun_prop
  -- sup bounds for the small factors
  have hnr : ‖(r : ℂ)‖ = r := nr38 hr0.le
  have ha : ∀ x, ‖(r : ℂ) * star (U x)‖ ≤ r * A0 := fun x => by
    rw [norm_mul, hnr, norm_star]; gcongr; exact hUb x
  have ha1 : ∀ x, ‖(r : ℂ) ^ 2 * star (U1 x)‖ ≤ r ^ 2 * A1 := fun x => by
    rw [norm_mul, norm_pow, hnr, norm_star]; gcongr; exact hU1b x
  have hα : ∀ x, ‖(r : ℂ) * star (U x) - (r : ℂ) ^ 2 * star (U1 x)‖ ≤ r * A0 + r ^ 2 * A1 :=
    fun x => (norm_sub_le _ _).trans (add_le_add (ha x) (ha1 x))
  have hr2 : r ^ 2 ≤ r := by nlinarith
  have hr3 : r ^ 6 * r ≤ r ^ 6 := by
    have : 0 ≤ r ^ 6 := by positivity
    nlinarith
  -- named pieces
  obtain ⟨f1, hf1⟩ : ∃ f : ℝ → ℂ, f = fun x => U x * (-((r : ℂ) ^ 2 * star (U1 x))) *
      ((r : ℂ) * star (U x) + ((r : ℂ) * star (U x) - (r : ℂ) ^ 2 * star (U1 x))) := ⟨_, rfl⟩
  obtain ⟨f2, hf2⟩ : ∃ f : ℝ → ℂ, f = fun x => U x * ((r : ℂ) * U x * (-((r : ℂ) ^ 2 * star (U1 x)))
      + (r : ℂ) ^ 2 * U1 x * ((r : ℂ) * star (U x) - (r : ℂ) ^ 2 * star (U1 x))) := ⟨_, rfl⟩
  obtain ⟨h3, hh3⟩ : ∃ f : ℝ → ℂ, f = fun x => U x *
      ((r : ℂ) * star (U x) - (r : ℂ) ^ 2 * star (U1 x)) := ⟨_, rfl⟩
  obtain ⟨h4, hh4⟩ : ∃ f : ℝ → ℂ, f = fun x => ρ x * U x := ⟨_, rfl⟩
  have hf1c : Continuous f1 := by rw [hf1]; fun_prop
  have hf2c : Continuous f2 := by rw [hf2]; fun_prop
  have hh3c : Continuous h3 := by rw [hh3]; fun_prop
  have hh4c : Continuous h4 := by rw [hh4]; fun_prop
  have hM1 : ∀ x, ‖f1 x‖ ≤ r ^ 3 * (A0 * A1 * (2 * A0 + A1)) := fun x => by
    rw [hf1]
    simp only []
    have e1 : ‖U x * (-((r : ℂ) ^ 2 * star (U1 x))) *
        ((r : ℂ) * star (U x) + ((r : ℂ) * star (U x) - (r : ℂ) ^ 2 * star (U1 x)))‖ =
        ‖U x‖ * ‖(r : ℂ) ^ 2 * star (U1 x)‖ * ‖(r : ℂ) * star (U x) +
          ((r : ℂ) * star (U x) - (r : ℂ) ^ 2 * star (U1 x))‖ := by
      rw [norm_mul, norm_mul, norm_neg]
    rw [e1]
    have h5 : ‖(r : ℂ) * star (U x) + ((r : ℂ) * star (U x) - (r : ℂ) ^ 2 * star (U1 x))‖ ≤
        r * A0 + (r * A0 + r ^ 2 * A1) := (norm_add_le _ _).trans (add_le_add (ha x) (hα x))
    calc _ ≤ A0 * (r ^ 2 * A1) * (r * A0 + (r * A0 + r ^ 2 * A1)) := by
          gcongr
          · exact hUb x
          · exact ha1 x
      _ ≤ r ^ 3 * (A0 * A1 * (2 * A0 + A1)) := by
          have : 0 ≤ r ^ 3 * A0 * A1 * (A1 - r * A1) :=
            mul_nonneg (by positivity) (by nlinarith)
          nlinarith
  have hM2 : ∀ x, ‖f2 x‖ ≤ r ^ 3 * (A0 * A1 * (2 * A0 + A1)) := fun x => by
    rw [hf2]
    simp only []
    have e2 : ‖(r : ℂ) * U x * (-((r : ℂ) ^ 2 * star (U1 x))) +
        (r : ℂ) ^ 2 * U1 x * ((r : ℂ) * star (U x) - (r : ℂ) ^ 2 * star (U1 x))‖ ≤
        r * A0 * (r ^ 2 * A1) + r ^ 2 * A1 * (r * A0 + r ^ 2 * A1) := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, norm_neg, norm_mul, hnr]
        gcongr; exact hUb x; exact ha1 x
      · rw [norm_mul, norm_mul, norm_pow, hnr]
        gcongr; exact hU1b x; exact hα x
    rw [norm_mul]
    calc _ ≤ A0 * (r * A0 * (r ^ 2 * A1) + r ^ 2 * A1 * (r * A0 + r ^ 2 * A1)) := by
          gcongr; exact hUb x
      _ ≤ r ^ 3 * (A0 * A1 * (2 * A0 + A1)) := by
          have : 0 ≤ r ^ 3 * A0 * A1 * (A1 - r * A1) :=
            mul_nonneg (by positivity) (by nlinarith)
          nlinarith
  have hM3 : ∀ x, ‖h3 x‖ ≤ r * (A0 * (A0 + A1)) := fun x => by
    rw [hh3]
    simp only []
    rw [norm_mul]
    calc _ ≤ A0 * (r * A0 + r ^ 2 * A1) := by gcongr; exact hUb x; exact hα x
      _ ≤ r * (A0 * (A0 + A1)) := by
          have : 0 ≤ r * A0 * A1 * (1 - r) := mul_nonneg (by positivity) (by linarith)
          nlinarith
  have hM4 : ∀ x, ‖h4 x‖ ≤ r * A0 * A0 := fun x => by
    rw [hh4]
    simp only []
    rw [norm_mul]
    gcongr; exact hρb x; exact hUb x
  -- the twelve summands
  obtain ⟨p1, hp1⟩ : ∃ p : ℝ → ℂ, p = fun x => (r : ℂ) ^ 3 * (U x * star (U x)) ^ 2 := ⟨_, rfl⟩
  obtain ⟨p2, hp2⟩ : ∃ p : ℝ → ℂ, p = fun x =>
    (r : ℂ) ^ 4 * (U1 x * U x * star (U x) ^ 2) := ⟨_, rfl⟩
  obtain ⟨p3, hp3⟩ : ∃ p : ℝ → ℂ, p = fun x =>
    (-2 * (r : ℂ) ^ 4) * (U x ^ 2 * star (U x) * star (U1 x)) := ⟨_, rfl⟩
  obtain ⟨p4, hp4⟩ : ∃ p : ℝ → ℂ, p = fun x =>
    (r : ℂ) ^ 5 * (U x ^ 2 * star (U1 x) ^ 2) := ⟨_, rfl⟩
  obtain ⟨p5, hp5⟩ : ∃ p : ℝ → ℂ, p = fun x =>
    (-2 * (r : ℂ) ^ 5) * ((U x * star (U x)) * (U1 x * star (U1 x))) := ⟨_, rfl⟩
  obtain ⟨p6, hp6⟩ : ∃ p : ℝ → ℂ, p = fun x =>
    (r : ℂ) ^ 4 * (T x * (U x * star (U x) ^ 2)) := ⟨_, rfl⟩
  obtain ⟨p7, hp7⟩ : ∃ p : ℝ → ℂ, p = fun x =>
    (2 * (r : ℂ) ^ 4) * (U x * star (U x) * U x * Q x) := ⟨_, rfl⟩
  obtain ⟨p8, hp8⟩ : ∃ p : ℝ → ℂ, p = fun x =>
    (r : ℂ) ^ 6 * (U1 x * U x * star (U1 x) ^ 2) := ⟨_, rfl⟩
  obtain ⟨p9, hp9⟩ : ∃ p : ℝ → ℂ, p = fun x => (r : ℂ) ^ 2 * (f1 x * T x) := ⟨_, rfl⟩
  obtain ⟨p10, hp10⟩ : ∃ p : ℝ → ℂ, p = fun x => (2 * (r : ℂ) ^ 2) * (f2 x * Q x) := ⟨_, rfl⟩
  obtain ⟨p11, hp11⟩ : ∃ p : ℝ → ℂ, p = fun x =>
    (2 * (r : ℂ) ^ 4) * (T x * (h3 x * Q x)) := ⟨_, rfl⟩
  obtain ⟨p12, hp12⟩ : ∃ p : ℝ → ℂ, p = fun x =>
    (r : ℂ) ^ 4 * (Q x * (h4 x * Q x)) := ⟨_, rfl⟩
  have hp1c : Continuous p1 := by rw [hp1]; fun_prop
  have hp2c : Continuous p2 := by rw [hp2]; fun_prop
  have hp3c : Continuous p3 := by rw [hp3]; fun_prop
  have hp4c : Continuous p4 := by rw [hp4]; fun_prop
  have hp5c : Continuous p5 := by rw [hp5]; fun_prop
  have hp6c : Continuous p6 := by rw [hp6]; fun_prop
  have hp7c : Continuous p7 := by rw [hp7]; fun_prop
  have hp8c : Continuous p8 := by rw [hp8]; fun_prop
  have hp9c : Continuous p9 := by rw [hp9]; fun_prop
  have hp10c : Continuous p10 := by rw [hp10]; fun_prop
  have hp11c : Continuous p11 := by rw [hp11]; fun_prop
  have hp12c : Continuous p12 := by rw [hp12]; fun_prop
  have key : ∀ x, ρ x * (U x * G x ^ 2) = p1 x + p2 x + p3 x + p4 x + p5 x + p6 x + p7 x + p8 x
      + p9 x + p10 x + p11 x + p12 x := fun x => by
    simp only [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hf1, hf2, hh3, hh4]
    have := quartic_alg38 (r : ℂ) (U x) (U1 x) (star (U x)) (star (U1 x)) (T x) (Q x) (ρ x) (G x)
      (hρ x) (hG x)
    linear_combination this
  have hF : pair38 ρ (fun x => U x * G x ^ 2) = ∫ x in (0:ℝ)..1, (p1 x + p2 x + p3 x + p4 x + p5 x
      + p6 x + p7 x + p8 x + p9 x + p10 x + p11 x + p12 x) := by
    unfold pair38
    exact intervalIntegral.integral_congr (fun x _ => key x)
  have hsum : ∫ x in (0:ℝ)..1, (p1 x + p2 x + p3 x + p4 x + p5 x
      + p6 x + p7 x + p8 x + p9 x + p10 x + p11 x + p12 x) =
      (∫ x in (0:ℝ)..1, p1 x) + (∫ x in (0:ℝ)..1, p2 x) + (∫ x in (0:ℝ)..1, p3 x)
      + (∫ x in (0:ℝ)..1, p4 x) + (∫ x in (0:ℝ)..1, p5 x) + (∫ x in (0:ℝ)..1, p6 x)
      + (∫ x in (0:ℝ)..1, p7 x) + (∫ x in (0:ℝ)..1, p8 x) + (∫ x in (0:ℝ)..1, p9 x)
      + (∫ x in (0:ℝ)..1, p10 x) + (∫ x in (0:ℝ)..1, p11 x) + (∫ x in (0:ℝ)..1, p12 x) := by
    repeat rw [intervalIntegral.integral_add]
    all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
  have i1 : ∫ x in (0:ℝ)..1, p1 x = (r : ℂ) ^ 3 * ∫ x in (0:ℝ)..1, (U x * star (U x)) ^ 2 := by
    rw [hp1]; exact intervalIntegral.integral_const_mul _ _
  have i2 : ∫ x in (0:ℝ)..1, p2 x =
      (r : ℂ) ^ 4 * ∫ x in (0:ℝ)..1, U1 x * U x * star (U x) ^ 2 := by
    rw [hp2]; exact intervalIntegral.integral_const_mul _ _
  have i3 : ∫ x in (0:ℝ)..1, p3 x =
      (-2 * (r : ℂ) ^ 4) * ∫ x in (0:ℝ)..1, U x ^ 2 * star (U x) * star (U1 x) := by
    rw [hp3]; exact intervalIntegral.integral_const_mul _ _
  have i4 : ∫ x in (0:ℝ)..1, p4 x =
      (r : ℂ) ^ 5 * ∫ x in (0:ℝ)..1, U x ^ 2 * star (U1 x) ^ 2 := by
    rw [hp4]; exact intervalIntegral.integral_const_mul _ _
  have i5 : ∫ x in (0:ℝ)..1, p5 x = (-2 * (r : ℂ) ^ 5) *
      ∫ x in (0:ℝ)..1, (U x * star (U x)) * (U1 x * star (U1 x)) := by
    rw [hp5]; exact intervalIntegral.integral_const_mul _ _
  have i6 : ∫ x in (0:ℝ)..1, p6 x =
      (r : ℂ) ^ 4 * ∫ x in (0:ℝ)..1, T x * (U x * star (U x) ^ 2) := by
    rw [hp6]; exact intervalIntegral.integral_const_mul _ _
  have i7 : ∫ x in (0:ℝ)..1, p7 x =
      (2 * (r : ℂ) ^ 4) * ∫ x in (0:ℝ)..1, U x * star (U x) * U x * Q x := by
    rw [hp7]; exact intervalIntegral.integral_const_mul _ _
  simp only [pair38] at hK1 hK2
  have hD : pair38 ρ (fun x => U x * G x ^ 2) -
      ((r : ℂ) ^ 3 * (∫ x in (0:ℝ)..1, (U x * star (U x)) ^ 2)
      + (r : ℂ) ^ 4 * (∫ x in (0:ℝ)..1, U1 x * U x * star (U x) ^ 2)
      - 2 * (r : ℂ) ^ 4 * (∫ x in (0:ℝ)..1, U x ^ 2 * star (U x) * star (U1 x))
      + (r : ℂ) ^ 5 * ((∫ x in (0:ℝ)..1, U2 x * U x * star (U x) ^ 2)
          + (∫ x in (0:ℝ)..1, U x ^ 2 * star (U1 x) ^ 2)
          + 2 * (∫ x in (0:ℝ)..1, U x * star (U x) * U x * star (U2 x)))
      - 2 * (r : ℂ) ^ 5 * (∫ x in (0:ℝ)..1, (U x * star (U x)) * (U1 x * star (U1 x)))) =
      (∫ x in (0:ℝ)..1, p8 x) + (∫ x in (0:ℝ)..1, p9 x) + (∫ x in (0:ℝ)..1, p10 x)
      + (∫ x in (0:ℝ)..1, p11 x) + (∫ x in (0:ℝ)..1, p12 x)
      + (r : ℂ) ^ 4 * ((∫ x in (0:ℝ)..1, T x * (U x * star (U x) ^ 2)) -
          (r : ℂ) * ∫ x in (0:ℝ)..1, U2 x * U x * star (U x) ^ 2)
      + (2 * (r : ℂ) ^ 4) * ((∫ x in (0:ℝ)..1, U x * star (U x) * U x * Q x) -
          (r : ℂ) * ∫ x in (0:ℝ)..1, U x * star (U x) * U x * star (U2 x)) := by
    rw [hF, hsum, i1, i2, i3, i4, i5, i6, i7]
    ring
  rw [hD]
  -- norm bounds of the error pieces
  have hn2 : ‖(2 : ℂ)‖ = 2 := by simp
  have b8 : ‖∫ x in (0:ℝ)..1, p8 x‖ ≤ (A0 * A1 ^ 3) * r ^ 6 := by
    rw [hp8, intervalIntegral.integral_const_mul, norm_mul, norm_pow, hnr]
    have h : ‖∫ x in (0:ℝ)..1, U1 x * U x * star (U1 x) ^ 2‖ ≤ A1 * A0 * A1 ^ 2 * |(1:ℝ) - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const (fun x _ => ?_)
      rw [norm_mul, norm_mul, norm_pow, norm_star]
      gcongr
      · exact hU1b x
      · exact hUb x
      · exact hU1b x
    rw [show |(1:ℝ) - 0| = 1 by simp, mul_one] at h
    calc _ ≤ r ^ 6 * (A1 * A0 * A1 ^ 2) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by ring
  have b9 : ‖∫ x in (0:ℝ)..1, p9 x‖ ≤ (A0 * A1 * (2 * A0 + A1) * s) * r ^ 6 := by
    rw [hp9]
    refine (piece_sup38 hs hr0.le hf1c hTc hM1 hTb _).trans ?_
    rw [norm_pow, hnr]
    apply le_of_eq; ring
  have b10 : ‖∫ x in (0:ℝ)..1, p10 x‖ ≤ (2 * (A0 * A1 * (2 * A0 + A1) * s)) * r ^ 6 := by
    rw [hp10]
    refine (piece_sup38 hs hr0.le hf2c hQc hM2 hQb _).trans ?_
    rw [norm_mul, norm_pow, hnr, hn2]
    apply le_of_eq; ring
  have b11 : ‖∫ x in (0:ℝ)..1, p11 x‖ ≤ (2 * (s ^ 2 * A0 * (A0 + A1))) * r ^ 6 := by
    rw [hp11]
    refine (piece_l2_38 hs hr0.le hTc hQc hh3c hM3 hTb hQb _).trans ?_
    rw [norm_mul, norm_pow, hnr, hn2]
    have hK : 0 ≤ 2 * (s ^ 2 * A0 * (A0 + A1)) := by positivity
    calc _ = (2 * (s ^ 2 * A0 * (A0 + A1))) * (r ^ 6 * r) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hr3 hK
  have b12 : ‖∫ x in (0:ℝ)..1, p12 x‖ ≤ (A0 ^ 2 * s ^ 2) * r ^ 6 := by
    rw [hp12]
    refine (piece_l2_38 hs hr0.le hQc hQc hh4c hM4 hQb hQb _).trans ?_
    rw [norm_pow, hnr]
    have hK : 0 ≤ A0 ^ 2 * s ^ 2 := by positivity
    calc _ = (A0 ^ 2 * s ^ 2) * (r ^ 6 * r) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hr3 hK
  have b6 : ‖(r : ℂ) ^ 4 * ((∫ x in (0:ℝ)..1, T x * (U x * star (U x) ^ 2)) -
          (r : ℂ) * ∫ x in (0:ℝ)..1, U2 x * U x * star (U x) ^ 2)‖ ≤ C1 * r ^ 6 := by
    rw [norm_mul, norm_pow, hnr]
    calc _ ≤ r ^ 4 * (C1 * r ^ 2) := mul_le_mul_of_nonneg_left hK1 (by positivity)
      _ = _ := by ring
  have b7 : ‖(2 * (r : ℂ) ^ 4) * ((∫ x in (0:ℝ)..1, U x * star (U x) * U x * Q x) -
          (r : ℂ) * ∫ x in (0:ℝ)..1, U x * star (U x) * U x * star (U2 x))‖ ≤ 2 * C2 * r ^ 6 := by
    rw [norm_mul, norm_mul, norm_pow, hnr, hn2]
    calc _ ≤ 2 * r ^ 4 * (C2 * r ^ 2) := mul_le_mul_of_nonneg_left hK2 (by positivity)
      _ = _ := by ring
  have e7 : ∀ a b c d e f g : ℂ,
      ‖a + b + c + d + e + f + g‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ + ‖g‖ := by
    intro a b c d e f g
    have h1 := norm_add_le (a + b + c + d + e + f) g
    have h2 := norm_add_le (a + b + c + d + e) f
    have h3 := norm_add_le (a + b + c + d) e
    have h4 := norm_add_le (a + b + c) d
    have h5 := norm_add_le (a + b) c
    have h6 := norm_add_le a b
    linarith
  refine (e7 _ _ _ _ _ _ _).trans ?_
  nlinarith [b6, b7, b8, b9, b10, b11, b12]

end NlsGge.SpectralFoundations
