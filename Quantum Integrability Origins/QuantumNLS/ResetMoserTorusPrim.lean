import QuantumNLS.ResetMoserLoop
import QuantumNLS.ResetMoserEmb
import QuantumNLS.ResetMoserSurface
import QuantumNLS.ResetMoserDt

/-!
# `thm:reset-moser` (LOCAL-017), stage 3d-3 (item 2(c)): the cone primitive `G` on the angle space of a finitely supported torus and its derivative along curves

Source: `symplectic_correction.tex`, "The periods of a radial primitive": "The restriction of `α` to the torus is closed by isotropy [...] lifting to `ℝ^{|F|}` and
integrating the closed form along rectangle boundaries". For `z` with finite support `T`, the angle `θ ∈ ℝ^T` corresponds to the torus point `R_θ z`
(`(R_θ z)_k = e^{iθ_k} z_k`) with tangent vectors `i θ_k (R_θ z)_k`; `G(θ) = ∫_0^1 β_{R_{rθ}z}(i θ R_{rθ}z) dr` (the cone/Poincaré primitive of the pulled-back
`β`, which is closed because `Ω − ω` vanishes on `𝒯 × 𝒯`).

* `Gint S T z θ`; `Hyp.Gint_hasDerivAt`: along every `C¹` curve of base angles, `d/ds G(θ(s)) = β_{R_{θ(s)}z}(i θ'(s) R_{θ(s)}z)`
  (the abstract `surface_deriv` applied to the surface `σ(r,s) = R_{rθ(s)}z`; `dβ(v,u) = 0` by `betaR_antisym` and `Ω_sub_omega_Tz`).
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

/-- Coordinates of `R_{rθ} z`. -/
def sg (z : K) (θ : ℤ → ℝ) (r : ℝ) : ℤ → ℂ := fun k => Complex.exp (Complex.I * ((r * θ k : ℝ) : ℂ)) * z k
/-- `∂_r σ`. -/
def uu (z : K) (θ : ℤ → ℝ) (r : ℝ) : ℤ → ℂ := fun k => Complex.I * (θ k : ℂ) * sg z θ r k
/-- `∂_s σ`. -/
def vv (z : K) (θ θ' : ℤ → ℝ) (r : ℝ) : ℤ → ℂ := fun k => Complex.I * ((r * θ' k : ℝ) : ℂ) * sg z θ r k
/-- `∂_s ∂_r σ = ∂_r ∂_s σ`. -/
def ww (z : K) (θ θ' : ℤ → ℝ) (r : ℝ) : ℤ → ℂ := fun k =>
  Complex.I * (θ' k : ℂ) * sg z θ r k + Complex.I * (θ k : ℂ) * vv z θ θ' r k

/-- The cone primitive of the pulled-back form on the angle space. -/
def Gint (S : Hyp) (T : Finset ℤ) (z : K) (θ : ℤ → ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..1, betaR S (Emb T (sg z θ r)) (Emb T (uu z θ r))

theorem norm_sg (z : K) (θ : ℤ → ℝ) (r : ℝ) (k : ℤ) : ‖sg z θ r k‖ = ‖z k‖ := by
  unfold sg
  rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]

theorem norm_Emb_sg {T : Finset ℤ} {z : K} (hT : ∀ n, z n ≠ 0 → n ∈ T) (θ : ℤ → ℝ) (r : ℝ) :
    ‖Emb T (sg z θ r)‖ = ‖z‖ := by
  rw [← Emb_self hT]
  exact norm_Emb_eq T _ _ fun k _ => by rw [norm_sg, Emb_self hT]

theorem sg_zero (z : K) (θ : ℤ → ℝ) : sg z θ 0 = fun k => z k := by
  funext k; simp [sg]

theorem vv_zero (z : K) (θ θ' : ℤ → ℝ) : vv z θ θ' 0 = fun _ => 0 := by
  funext k; simp [vv]

theorem Emb_zero (T : Finset ℤ) : Emb T (fun _ => 0) = 0 := by
  ext n; rw [Emb_apply]; split_ifs <;> simp

theorem hasDerivAt_sg_s {z : K} {θ θ' : ℝ → ℤ → ℝ} {k : ℤ} {s : ℝ} (h : HasDerivAt (fun s => θ s k) (θ' s k) s)
    (r : ℝ) : HasDerivAt (fun s => sg z (θ s) r k) (vv z (θ s) (θ' s) r k) s := by
  have h1 : HasDerivAt (fun s => ((r * θ s k : ℝ) : ℂ)) ((r * θ' s k : ℝ) : ℂ) s :=
    (h.const_mul r).ofReal_comp
  have h2 := ((h1.const_mul Complex.I).cexp).mul_const (z k)
  refine h2.congr_deriv ?_
  simp only [vv, sg]
  ring

theorem hasDerivAt_sg_r {z : K} {θ : ℤ → ℝ} {k : ℤ} (r : ℝ) :
    HasDerivAt (fun r => sg z θ r k) (uu z θ r k) r := by
  have h1 : HasDerivAt (fun r : ℝ => ((r * θ k : ℝ) : ℂ)) ((θ k : ℝ) : ℂ) r := by
    have := ((hasDerivAt_id r).mul_const (θ k)).ofReal_comp
    simpa using this
  have h2 := ((h1.const_mul Complex.I).cexp).mul_const (z k)
  refine h2.congr_deriv ?_
  simp only [uu, sg]
  ring

theorem hasDerivAt_uu_s {z : K} {θ θ' : ℝ → ℤ → ℝ} {k : ℤ} {s : ℝ} (h : HasDerivAt (fun s => θ s k) (θ' s k) s)
    (r : ℝ) : HasDerivAt (fun s => uu z (θ s) r k) (ww z (θ s) (θ' s) r k) s := by
  have h1 : HasDerivAt (fun s => ((θ s k : ℝ) : ℂ)) ((θ' s k : ℝ) : ℂ) s := h.ofReal_comp
  have h2 := (h1.const_mul Complex.I).mul (hasDerivAt_sg_s (z := z) h r)
  refine h2.congr_deriv ?_
  simp only [ww, uu]

theorem hasDerivAt_vv_r {z : K} {θ θ' : ℤ → ℝ} {k : ℤ} (r : ℝ) :
    HasDerivAt (fun r => vv z θ θ' r k) (ww z θ θ' r k) r := by
  have h1 : HasDerivAt (fun r : ℝ => ((r * θ' k : ℝ) : ℂ)) ((θ' k : ℝ) : ℂ) r := by
    have := ((hasDerivAt_id r).mul_const (θ' k)).ofReal_comp
    simpa using this
  have h2 := (h1.const_mul Complex.I).mul (hasDerivAt_sg_r (z := z) (θ := θ) (k := k) r)
  refine h2.congr_deriv ?_
  simp only [ww, vv, uu, sg]
  ring

theorem Hyp.closed_Tz (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {x : K} (hx : x ∈ ball (0 : K) ρ) {a b : K}
    (ha : a ∈ Tz x) (hb : b ∈ Tz x) :
    (∫ t in (0 : ℝ)..1, Lval S x t) a b = (∫ t in (0 : ℝ)..1, Lval S x t) b a := by
  have h := betaR_antisym S hL hx a b
  have h0 : Dl S x a b = 0 := Ω_sub_omega_Tz S (ball_mono_R hL hx) a ha b hb
  linarith

/-- The derivative of `G` along a `C¹` curve of base angles. -/
theorem Hyp.Gint_hasDerivAt (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {z : K} (hz : z ∈ ball (0 : K) ρ)
    {T : Finset ℤ} (hT : ∀ n, z n ≠ 0 → n ∈ T) {θ θ' : ℝ → ℤ → ℝ}
    (hθ : ∀ k ∈ T, ∀ s, HasDerivAt (fun s => θ s k) (θ' s k) s)
    (hθ'c : ∀ k ∈ T, Continuous fun s => θ' s k) (s₀ : ℝ) :
    HasDerivAt (fun s => Gint S T z (θ s))
      (betaR S (Emb T (sg z (θ s₀) 1)) (Emb T (vv z (θ s₀) (θ' s₀) 1))) s₀ := by
  have hθc : ∀ k ∈ T, Continuous fun s => θ s k := fun k hk =>
    continuous_iff_continuousAt.2 fun s => (hθ k hk s).continuousAt
  have hzn : ‖z‖ < ρ := mem_ball_zero_iff.1 hz
  have hβ'c : ContinuousOn (fun x => ∫ t in (0 : ℝ)..1, Lval S x t) (ball (0 : K) ρ) := by
    intro x hx
    have h := (alphaD_continuousAt S hL hx).sub (continuousAt_const (y := (1 / 2 : ℝ) • (omegaF : K →L[ℝ] Cov)))
    have e : (fun x => ∫ t in (0 : ℝ)..1, Lval S x t) =
        fun x => alphaD S x - (1 / 2 : ℝ) • (omegaF : K →L[ℝ] Cov) := by
      funext x; simp [alphaD]
    rw [e]
    exact h.continuousWithinAt
  have hσU : ∀ r s, Emb T (sg z (θ s) r) ∈ ball (0 : K) ρ := fun r s => by
    rw [mem_ball_zero_iff, norm_Emb_sg hT]; exact hzn
  have hmain := surface_deriv (U := ball (0 : K) ρ) isOpen_ball (β := betaR S)
    (β' := fun x => ∫ t in (0 : ℝ)..1, Lval S x t) (fun x hx => betaR_hasFDerivAt S hL hx) hβ'c
    (σ := fun r s => Emb T (sg z (θ s) r)) (u := fun r s => Emb T (uu z (θ s) r))
    (v := fun r s => Emb T (vv z (θ s) (θ' s) r)) (w := fun r s => Emb T (ww z (θ s) (θ' s) r))
    hσU ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ s₀
  · rw [sg_zero, vv_zero, Emb_zero, Emb_self hT] at hmain
    simpa [Gint] using hmain
  · intro r s
    exact Emb_hasDerivAt T (f := fun s k => sg z (θ s) r k) (f' := fun s k => vv z (θ s) (θ' s) r k)
      (s := s) fun k hk => hasDerivAt_sg_s (z := z) (hθ k hk s) r
  · intro r s
    exact Emb_hasDerivAt T (f := fun r k => sg z (θ s) r k) (f' := fun r k => uu z (θ s) r k)
      (s := r) fun k hk => hasDerivAt_sg_r (z := z) r
  · intro r s
    exact Emb_hasDerivAt T (f := fun s k => uu z (θ s) r k) (f' := fun s k => ww z (θ s) (θ' s) r k)
      (s := s) fun k hk => hasDerivAt_uu_s (z := z) (hθ k hk s) r
  · intro r s
    exact Emb_hasDerivAt T (f := fun r k => vv z (θ s) (θ' s) r k) (f' := fun r k => ww z (θ s) (θ' s) r k)
      (s := r) fun k hk => hasDerivAt_vv_r (z := z) r
  · refine Emb_continuous T fun k hk => ?_
    have h1 := hθc k hk
    unfold sg
    fun_prop
  · refine Emb_continuous T fun k hk => ?_
    have h1 := hθc k hk
    unfold uu sg
    fun_prop
  · refine Emb_continuous T fun k hk => ?_
    have h1 := hθc k hk
    have h2 := hθ'c k hk
    unfold vv sg
    fun_prop
  · refine Emb_continuous T fun k hk => ?_
    have h1 := hθc k hk
    have h2 := hθ'c k hk
    unfold ww vv sg
    fun_prop
  · intro r s
    have hσ := hσU r s
    have hu : Emb T (uu z (θ s) r) ∈ Tz (Emb T (sg z (θ s) r)) :=
      Emb_mem_Tz T _ _ fun k _ => ⟨θ s k, by simp [uu]; ring⟩
    have hv : Emb T (vv z (θ s) (θ' s) r) ∈ Tz (Emb T (sg z (θ s) r)) :=
      Emb_mem_Tz T _ _ fun k _ => ⟨r * θ' s k, by simp [vv]; ring⟩
    exact S.closed_Tz hL hσ hv hu

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.Hyp.Gint_hasDerivAt
