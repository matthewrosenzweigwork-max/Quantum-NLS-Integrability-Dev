import QuantumNLS.ResetMoserTorusPrim

/-!
# `thm:reset-moser` (LOCAL-017), stage 3d-4 (item 2(c)): the cone primitive on the angle space is `2π`-periodic in each coordinate of the support

Source: `symplectic_correction.tex`, "The periods of a radial primitive": the periods of `β` along the coordinate circles vanish ("all of its periods are zero. Lifting again
to `ℝ^{|F|}` gives a periodic primitive of this restricted one-form").

* Step 1 (the flow loop): the angle lift `θ_k(s) = ∫_0^s ang_k(φ_j^u z) du` of the loop `φ_j^s z` (`Hyp.gamma_coord`) satisfies `R_{θ(s)} z = φ_j^s z`,
  `i θ'(s) R_{θ(s)} z = X_j(φ_j^s z)`, so by `Hyp.Gint_hasDerivAt`, `d/ds G(θ(s)) = β_{γ}(X_j(γ))`; integrating over `[0,2π]` with `Hyp.loop_beta_zero`
  and the winding `Hyp.winding` gives `G(−2π e_j) = G(0)`.
* Step 2 (translation): `s ↦ G(θ₀ + sθ¹ + 2πe_j) − G(θ₀ + sθ¹)` has zero derivative (the rotated points and tangent vectors coincide), so
  `G(θ + 2πe_j) − G(θ) = G(0) − G(−2πe_j) = 0`: **`Hyp.Gint_shift`**.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric MeasureTheory
open scoped Interval

namespace QuantumNLS.ResetMoser

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.RealAnalyticDef
open QuantumNLS.ResetMoserFlow QuantumNLS.ResetMoserSurface

theorem Emb_congr (T : Finset ℤ) {c c' : ℤ → ℂ} (h : ∀ k ∈ T, c k = c' k) : Emb T c = Emb T c' := by
  unfold Emb
  exact Finset.sum_congr rfl fun k hk => by rw [h k hk]

theorem Gint_congr (S : Hyp) (T : Finset ℤ) (z : K) {θ θ' : ℤ → ℝ} (h : ∀ k ∈ T, θ k = θ' k) :
    Gint S T z θ = Gint S T z θ' := by
  unfold Gint
  refine intervalIntegral.integral_congr fun r _ => ?_
  have e1 : Emb T (sg z θ r) = Emb T (sg z θ' r) :=
    Emb_congr T fun k hk => by simp only [sg, h k hk]
  have e2 : Emb T (uu z θ r) = Emb T (uu z θ' r) :=
    Emb_congr T fun k hk => by simp only [uu, sg, h k hk]
  simp only [e1, e2]

/-- The unit shift of a base angle. -/
def shiftJ (j : ℤ) (c : ℝ) (θ : ℤ → ℝ) : ℤ → ℝ := fun k => θ k + if k = j then c else 0

theorem exp_shift (x : ℝ) :
    Complex.exp (Complex.I * ((x + 2 * Real.pi : ℝ) : ℂ)) = Complex.exp (Complex.I * (x : ℂ)) := by
  have : Complex.I * ((x + 2 * Real.pi : ℝ) : ℂ) = Complex.I * (x : ℂ) + 2 * Real.pi * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem sg_shift (z : K) (j : ℤ) (θ : ℤ → ℝ) (k : ℤ) :
    sg z (shiftJ j (2 * Real.pi) θ) 1 k = sg z θ 1 k := by
  unfold sg shiftJ
  by_cases h : k = j
  · simp only [h, if_true, one_mul, exp_shift]
  · simp [h]

theorem vv_shift (z : K) (j : ℤ) (θ θ' : ℤ → ℝ) (k : ℤ) :
    vv z (shiftJ j (2 * Real.pi) θ) θ' 1 k = vv z θ θ' 1 k := by
  unfold vv
  rw [sg_shift]

theorem Hyp.beta_loop_continuous (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) (j : ℤ) {z : K}
    (hz : z ∈ ball (0 : K) ρ) :
    Continuous (fun s => betaR S (S.φ j s z) (Xn S.Ω j (S.φ j s z))) := by
  have h1 := S.cont_gamma hL j hz (g := betaR S)
    (fun w hw => (betaR_hasFDerivAt S hL hw).continuousAt)
  have h2 := S.cont_gamma hL j hz (g := Xn S.Ω j)
    (fun w hw => (S.Xn_contDiffAt (ball_mono_R hL hw) j).continuousAt)
  exact h1.clm_apply h2

/-- The angle lift of the flow loop. -/
def thLoop (S : Hyp) (T : Finset ℤ) (z : K) (j : ℤ) (s : ℝ) : ℤ → ℝ :=
  fun k => if k ∈ T then ∫ u in (0 : ℝ)..s, ang S j k (S.φ j u z) else 0

def thLoop' (S : Hyp) (T : Finset ℤ) (z : K) (j : ℤ) (s : ℝ) : ℤ → ℝ :=
  fun k => if k ∈ T then ang S j k (S.φ j s z) else 0

/-- Step 1: `G(−2π e_j) = G(0)`. -/
theorem Hyp.Gint_loop (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {z : K} (hz : z ∈ ball (0 : K) ρ)
    {T : Finset ℤ} (hT : ∀ n, z n ≠ 0 ↔ n ∈ T) {j : ℤ} (hj : j ∈ T) :
    Gint S T z (fun k => -(2 * Real.pi) * (if k = j then 1 else 0)) = Gint S T z (fun _ => 0) := by
  have hzR : z ∈ ball (0 : K) S.R := ball_mono_R hL hz
  have hθ : ∀ k ∈ T, ∀ s, HasDerivAt (fun s => thLoop S T z j s k) (thLoop' S T z j s k) s := by
    intro k hk s
    have hkz := (hT k).2 hk
    simp only [thLoop, thLoop', hk, if_true]
    exact ((S.ang_gamma_continuous hzR j k hkz).integral_hasStrictDerivAt 0 s).hasDerivAt
  have hθ'c : ∀ k ∈ T, Continuous fun s => thLoop' S T z j s k := by
    intro k hk
    have := S.ang_gamma_continuous hzR j k ((hT k).2 hk)
    simpa only [thLoop', hk, if_true] using this
  have hγc : ∀ s, ∀ n ∈ T, sg z (thLoop S T z j s) 1 n = S.φ j s z n := by
    intro s n hn
    have hnz := (hT n).2 hn
    unfold sg
    rw [S.gamma_coord hzR j n hnz s]
    simp only [thLoop, hn, if_true, one_mul]
    ring
  have hγ : ∀ s, Emb T (sg z (thLoop S T z j s) 1) = S.φ j s z := by
    intro s
    ext n
    rw [Emb_apply]
    by_cases hn : n ∈ T
    · simp only [hn, if_true]; exact hγc s n hn
    · have : z n = 0 := by
        by_contra h; exact hn ((hT n).1 h)
      simp only [hn, if_false]
      exact (S.gamma_coord_zero hzR j this s).symm
  have hX : ∀ s, Emb T (vv z (thLoop S T z j s) (thLoop' S T z j s) 1) = Xn S.Ω j (S.φ j s z) := by
    intro s
    ext n
    rw [Emb_apply]
    by_cases hn : n ∈ T
    · have hnz := (hT n).2 hn
      have hne := S.gamma_coord_ne hzR j n hnz s
      rw [S.Xn_coord_eq (S.φ_mem j z hzR s) j n hne]
      simp only [hn, if_true]
      unfold vv
      rw [hγc s n hn]
      simp only [thLoop', hn, if_true, one_mul]
    · have : z n = 0 := by
        by_contra h; exact hn ((hT n).1 h)
      simp only [hn, if_false]
      exact (S.Xn_coord_zero (S.φ_mem j z hzR s) (S.gamma_coord_zero hzR j this s) j).symm
  have hderiv : ∀ s, HasDerivAt (fun s => Gint S T z (thLoop S T z j s))
      (betaR S (S.φ j s z) (Xn S.Ω j (S.φ j s z))) s := by
    intro s
    have := S.Gint_hasDerivAt hL hz (fun n hn => (hT n).1 hn) hθ hθ'c s
    rwa [hγ, hX] at this
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 2 * Real.pi) (fun s _ => hderiv s)
    ((S.beta_loop_continuous hL j hz).intervalIntegrable _ _)
  rw [S.loop_beta_zero hL j hz T hT ((hT j).2 hj)] at hftc
  have e1 : Gint S T z (thLoop S T z j (2 * Real.pi)) =
      Gint S T z (fun k => -(2 * Real.pi) * (if k = j then 1 else 0)) :=
    Gint_congr S T z fun k hk => by
      simp only [thLoop, hk, if_true]
      exact S.winding hL hz j k ((hT k).2 hk)
  have e0 : Gint S T z (thLoop S T z j 0) = Gint S T z (fun _ => 0) :=
    Gint_congr S T z fun k hk => by simp [thLoop, hk]
  rw [e1, e0] at hftc
  linarith

/-- **Step 2**: `G` is `2π`-periodic in each support coordinate. -/
theorem Hyp.Gint_shift (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {z : K} (hz : z ∈ ball (0 : K) ρ)
    {T : Finset ℤ} (hT : ∀ n, z n ≠ 0 ↔ n ∈ T) {j : ℤ} (hj : j ∈ T) (θ : ℤ → ℝ) :
    Gint S T z (shiftJ j (2 * Real.pi) θ) = Gint S T z θ := by
  set θ₀ : ℤ → ℝ := fun k => -(2 * Real.pi) * (if k = j then 1 else 0) with hθ₀
  set θ1 : ℤ → ℝ := fun k => θ k + (if k = j then 2 * Real.pi else 0) with hθ1
  set a : ℝ → ℤ → ℝ := fun s k => θ₀ k + s * θ1 k with ha
  set b : ℝ → ℤ → ℝ := fun s => shiftJ j (2 * Real.pi) (a s) with hb
  have hda : ∀ k ∈ T, ∀ s, HasDerivAt (fun s => a s k) (θ1 k) s := by
    intro k _ s
    have := ((hasDerivAt_id s).mul_const (θ1 k)).const_add (θ₀ k)
    exact this.congr_deriv (one_mul _)
  have hdb : ∀ k ∈ T, ∀ s, HasDerivAt (fun s => b s k) (θ1 k) s := by
    intro k hk s
    have := (hda k hk s).add_const (if k = j then 2 * Real.pi else 0)
    simpa [hb, shiftJ] using this
  have hc : ∀ k ∈ T, Continuous fun _ : ℝ => θ1 k := fun _ _ => continuous_const
  have hA := fun s => S.Gint_hasDerivAt hL hz (fun n hn => (hT n).1 hn) (θ := a) (θ' := fun _ => θ1) hda hc s
  have hB := fun s => S.Gint_hasDerivAt hL hz (fun n hn => (hT n).1 hn) (θ := b) (θ' := fun _ => θ1) hdb hc s
  have hD : ∀ s, HasDerivAt (fun s => Gint S T z (b s) - Gint S T z (a s)) 0 s := by
    intro s
    have h1 := (hB s).sub (hA s)
    have e1 : Emb T (sg z (b s) 1) = Emb T (sg z (a s) 1) := by
      congr 1; funext k; exact sg_shift z j (a s) k
    have e2 : Emb T (vv z (b s) θ1 1) = Emb T (vv z (a s) θ1 1) := by
      congr 1; funext k; exact vv_shift z j (a s) θ1 k
    rw [e1, e2, sub_self] at h1
    exact h1
  have hconst := is_const_of_deriv_eq_zero (f := fun s => Gint S T z (b s) - Gint S T z (a s))
    (fun s => (hD s).differentiableAt) (fun s => (hD s).deriv) 1 0
  have h1 : Gint S T z (b 1) = Gint S T z (shiftJ j (2 * Real.pi) θ) := by
    refine Gint_congr S T z fun k _ => ?_
    simp only [hb, ha, shiftJ, hθ₀, hθ1]
    split_ifs <;> ring
  have h2 : Gint S T z (a 1) = Gint S T z θ := by
    refine Gint_congr S T z fun k _ => ?_
    simp only [ha, hθ₀, hθ1]
    split_ifs <;> ring
  have h3 : Gint S T z (b 0) = Gint S T z (fun _ => 0) := by
    refine Gint_congr S T z fun k _ => ?_
    simp only [hb, ha, shiftJ, hθ₀]
    split_ifs <;> ring
  have h4 : Gint S T z (a 0) = Gint S T z θ₀ := by
    refine Gint_congr S T z fun k _ => ?_
    simp [ha]
  have hloop := S.Gint_loop hL hz hT hj
  simp only [h1, h2, h3, h4] at hconst
  rw [← hθ₀] at hloop
  linarith

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.Hyp.Gint_loop
#print axioms QuantumNLS.ResetMoser.Hyp.Gint_shift
