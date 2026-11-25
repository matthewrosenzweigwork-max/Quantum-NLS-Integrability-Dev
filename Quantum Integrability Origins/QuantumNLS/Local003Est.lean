import Mathlib
import QuantumNLS.Local003Taylor

/-! LOCAL-003 `thm:reset-uniform-reduction` (spectral_reduction.tex:87-110), stage H2d: the uniform cubic and quadratic
estimates from a complexified, bounded, analytic extension.

Abstract statement (no operator theory): let `G : U →L[ℝ] X` be a bounded real-linear map into a complex Banach space,
`𝔟 : X → ℂ` complex analytic on `‖Y‖ < q0` with `‖𝔟‖ ≤ M` there, and `b : U → ℂ` with `b u = 𝔟 (G u)` and `b (-u) = - b u`
on `‖u‖ < ρ`, where `K ρ ≤ q0/8`, `‖G u‖ ≤ K ‖u‖`.  Then, with `ℓ(u) = d/dζ 𝔟(ζ G u)|₀`,
* `‖b u - ℓ(u)‖ ≤ 32 M K³ ‖u‖³ / q0³`   (Taylor series of an odd function, Cauchy bounds; `Local003Taylor.cubic_line`);
* `b` is `ℝ`-differentiable and `‖Db(u) v - Db(0) v‖ ≤ 128 M K³ ‖u‖² ‖v‖ / q0³` (`Local003Taylor.even_deriv`).
All constants depend only on `(q0, M, K)`, not on `u`, `v`, or the index `n` of the later application. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Metric Filter Topology Set
namespace QuantumNLS.Local003Est
open QuantumNLS.Local003Taylor

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

section
variable (G : U →L[ℝ] X) (𝔟 : X → ℂ) (b : U → ℂ) {q0 M K ρ : ℝ}

lemma small_comb {u v : U} {ρ : ℝ} (hρ : 0 < ρ) (hu : ‖u‖ < ρ) {t s : ℝ}
    (ht : |t| < ρ / (‖u‖ + ‖v‖ + 1)) (hs : |s| < ρ / (‖u‖ + ‖v‖ + 1)) :
    ‖t • u + s • v‖ < ρ := by
  have hd : 0 < ‖u‖ + ‖v‖ + 1 := by positivity
  have h1 : |t| * (‖u‖ + ‖v‖ + 1) < ρ := by rwa [lt_div_iff₀ hd] at ht
  have h2 : |s| * (‖u‖ + ‖v‖ + 1) < ρ := by rwa [lt_div_iff₀ hd] at hs
  calc ‖t • u + s • v‖ ≤ ‖t • u‖ + ‖s • v‖ := norm_add_le _ _
    _ = |t| * ‖u‖ + |s| * ‖v‖ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ < ρ := by nlinarith [abs_nonneg t, abs_nonneg s, norm_nonneg u, norm_nonneg v]

theorem est_cubic (hq0 : 0 < q0)
    (hana : AnalyticOnNhd ℂ 𝔟 (ball 0 q0)) (hM : ∀ Y ∈ ball (0 : X) q0, ‖𝔟 Y‖ ≤ M)
    (hK : 0 ≤ K) (hGn : ∀ u, ‖G u‖ ≤ K * ‖u‖) (hρ : 0 < ρ) (hρK : K * ρ ≤ q0 / 8)
    (hb : ∀ u, ‖u‖ < ρ → b u = 𝔟 (G u)) (hodd : ∀ u, ‖u‖ < ρ → b (-u) = - b u)
    {u : U} (hu : ‖u‖ < ρ) :
    ‖b u - deriv (fun ζ : ℂ => 𝔟 (ζ • G u)) 0‖ ≤ 32 * M * (K * ‖u‖) ^ 3 / q0 ^ 3 := by
  have h0 : (0 : X) ∈ ball (0 : X) q0 := mem_ball_self hq0
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 h0)
  have hKu : K * ‖u‖ ≤ q0 / 8 := le_trans (mul_le_mul_of_nonneg_left hu.le hK) hρK
  have hY : ‖G u‖ ≤ q0 / 4 := by linarith [hGn u]
  have hε : 0 < ρ / (‖u‖ + 1) := by positivity
  have hoddl : ∀ t : ℝ, |t| < ρ / (‖u‖ + 1) → 𝔟 ((-t : ℝ) • G u) = - 𝔟 (t • G u) := by
    intro t ht
    have hnt : ‖t • u‖ < ρ := by
      have hd : 0 < ‖u‖ + 1 := by positivity
      have h1 : |t| * (‖u‖ + 1) < ρ := by rwa [lt_div_iff₀ hd] at ht
      rw [norm_smul, Real.norm_eq_abs]; nlinarith [abs_nonneg t, norm_nonneg u]
    have hnt' : ‖(-t) • u‖ < ρ := by
      rw [norm_smul, Real.norm_eq_abs, abs_neg]; rwa [norm_smul, Real.norm_eq_abs] at hnt
    have e1 : (-t : ℝ) • G u = G ((-t) • u) := (map_smul G (-t) u).symm
    have e2 : t • G u = G (t • u) := (map_smul G t u).symm
    rw [e1, e2, ← hb _ hnt', ← hb _ hnt, neg_smul, hodd _ hnt]
  have := cubic_line 𝔟 hq0 hana hM hY hε hoddl
  rw [hb u hu]
  refine this.trans ?_
  have hnn : 0 ≤ ‖G u‖ := norm_nonneg _
  have h3 : ‖G u‖ ^ 3 ≤ (K * ‖u‖) ^ 3 := pow_le_pow_left₀ hnn (hGn u) 3
  have : 32 * M * ‖G u‖ ^ 3 / q0 ^ 3 ≤ 32 * M * (K * ‖u‖) ^ 3 / q0 ^ 3 := by
    gcongr
  exact this

theorem est_deriv (hq0 : 0 < q0)
    (hana : AnalyticOnNhd ℂ 𝔟 (ball 0 q0)) (hM : ∀ Y ∈ ball (0 : X) q0, ‖𝔟 Y‖ ≤ M)
    (hK : 0 ≤ K) (hGn : ∀ u, ‖G u‖ ≤ K * ‖u‖) (hρ : 0 < ρ) (hρK : K * ρ ≤ q0 / 8)
    (hb : ∀ u, ‖u‖ < ρ → b u = 𝔟 (G u)) (hodd : ∀ u, ‖u‖ < ρ → b (-u) = - b u)
    {u : U} (hu : ‖u‖ < ρ) (v : U) :
    DifferentiableAt ℝ b u ∧
      ‖fderiv ℝ b u v - fderiv ℝ b 0 v‖ ≤ 128 * M * (K * ‖u‖) ^ 2 * (K * ‖v‖) / q0 ^ 3 := by
  have h0 : (0 : X) ∈ ball (0 : X) q0 := mem_ball_self hq0
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 h0)
  have hGbig : ∀ w : U, ‖w‖ < ρ → ‖G w‖ < q0 := fun w hw => by
    have := mul_le_mul_of_nonneg_left hw.le hK
    have h2 := hGn w
    nlinarith
  have hmemG : ∀ w : U, ‖w‖ < ρ → G w ∈ ball (0 : X) q0 := fun w hw => by
    rw [mem_ball_zero_iff]; exact hGbig w hw
  -- differentiability
  have hdiff : ∀ w : U, ‖w‖ < ρ → DifferentiableAt ℝ b w := by
    intro w hw
    have h𝔟 : DifferentiableAt ℂ 𝔟 (G w) := (hana _ (hmemG w hw)).differentiableAt
    have h1 : DifferentiableAt ℝ (fun w => 𝔟 (G w)) w :=
      (h𝔟.restrictScalars ℝ).comp w G.differentiableAt
    have hev : b =ᶠ[𝓝 w] fun w => 𝔟 (G w) := by
      filter_upwards [(isOpen_ball (x := (0 : U)) (ε := ρ)).mem_nhds (by simpa using hw)] with w' hw'
      exact hb w' (by simpa using hw')
    exact h1.congr_of_eventuallyEq hev
  -- the derivative is the complex derivative of the line
  have hline : ∀ w : U, ‖w‖ < ρ → fderiv ℝ b w v =
      deriv (fun ξ : ℂ => 𝔟 (G w + ξ • G v)) 0 := by
    intro w hw
    have hd := (hdiff w hw).hasFDerivAt
    have hl : HasDerivAt (fun s : ℝ => w + s • v) v 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add w
      simpa using this
    have h1 : HasDerivAt (fun s : ℝ => b (w + s • v)) (fderiv ℝ b w v) 0 :=
      HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (by simpa using hd) hl (by simp)
    have h𝔟 : DifferentiableAt ℂ 𝔟 (G w) := (hana _ (hmemG w hw)).differentiableAt
    have h2c : HasDerivAt (fun ξ : ℂ => 𝔟 (G w + ξ • G v)) (deriv (fun ξ : ℂ => 𝔟 (G w + ξ • G v)) 0) 0 := by
      have hl2 : HasDerivAt (fun ξ : ℂ => G w + ξ • G v) ((1 : ℂ) • G v) 0 :=
        ((hasDerivAt_id (0 : ℂ)).smul_const (G v)).const_add (G w)
      have := h𝔟.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hl2 (by simp)
      exact (this.differentiableAt).hasDerivAt
    have h2 : HasDerivAt (fun s : ℝ => 𝔟 (G w + (s : ℂ) • G v))
        (deriv (fun ξ : ℂ => 𝔟 (G w + ξ • G v)) 0) 0 :=
      HasDerivAt.comp_ofReal (e := fun ξ : ℂ => 𝔟 (G w + ξ • G v)) (z := 0)
        (by rw [Complex.ofReal_zero]; exact h2c)
    have hev : (fun s : ℝ => b (w + s • v)) =ᶠ[𝓝 0] fun s : ℝ => 𝔟 (G w + (s : ℂ) • G v) := by
      have hc : Continuous (fun s : ℝ => w + s • v) := by fun_prop
      have hnb : ∀ᶠ s : ℝ in 𝓝 0, ‖w + s • v‖ < ρ := by
        have : Tendsto (fun s : ℝ => w + s • v) (𝓝 0) (𝓝 w) := by
          simpa using hc.tendsto 0
        exact this.eventually (isOpen_ball (x := (0 : U)) (ε := ρ) |>.mem_nhds (by simpa using hw)) |>.mono
          (fun s hs => by simpa using hs)
      filter_upwards [hnb] with s hs
      rw [hb _ hs, map_add, map_smul, Complex.coe_smul]
    exact h1.unique (h2.congr_of_eventuallyEq hev)
  refine ⟨hdiff u hu, ?_⟩
  have hu0 : ‖(0 : U)‖ < ρ := by simpa using hρ
  rw [hline u hu, hline 0 hu0]
  simp only [map_zero, zero_add]
  have hY : ‖G u‖ ≤ q0 / 8 := le_trans (hGn u) (le_trans (mul_le_mul_of_nonneg_left hu.le hK) hρK)
  have hoddl : ∀ t s : ℝ, |t| < ρ / (‖u‖ + ‖v‖ + 1) → |s| < ρ / (‖u‖ + ‖v‖ + 1) →
      𝔟 ((-t : ℝ) • G u + (-s : ℝ) • G v) = - 𝔟 (t • G u + s • G v) := by
    intro t s ht hs
    have hn := small_comb (v := v) hρ hu ht hs
    have e1 : (-t : ℝ) • G u + (-s : ℝ) • G v = G (-(t • u + s • v)) := by
      rw [map_neg, map_add, map_smul, map_smul, neg_add, neg_smul, neg_smul]
    have e2 : t • G u + s • G v = G (t • u + s • v) := by rw [map_add, map_smul, map_smul]
    rw [e1, e2, ← hb _ (by rw [norm_neg]; exact hn), ← hb _ hn, hodd _ hn]
  have hε : 0 < ρ / (‖u‖ + ‖v‖ + 1) := by positivity
  have := even_deriv 𝔟 hq0 hana hM hY hε hoddl (Z := G v)
  refine this.trans ?_
  have hnn1 : 0 ≤ ‖G u‖ := norm_nonneg _
  have hnn2 : 0 ≤ ‖G v‖ := norm_nonneg _
  have h3 : ‖G u‖ ^ 2 * ‖G v‖ ≤ (K * ‖u‖) ^ 2 * (K * ‖v‖) :=
    mul_le_mul (pow_le_pow_left₀ hnn1 (hGn u) 2) (hGn v) hnn2 (by positivity)
  have : 128 * M * ‖G u‖ ^ 2 * ‖G v‖ / q0 ^ 3 ≤ 128 * M * (K * ‖u‖) ^ 2 * (K * ‖v‖) / q0 ^ 3 := by
    have e : 128 * M * ‖G u‖ ^ 2 * ‖G v‖ = 128 * M * (‖G u‖ ^ 2 * ‖G v‖) := by ring
    have e' : 128 * M * (K * ‖u‖) ^ 2 * (K * ‖v‖) = 128 * M * ((K * ‖u‖) ^ 2 * (K * ‖v‖)) := by ring
    rw [e, e']
    gcongr
  exact this

end

end QuantumNLS.Local003Est
#print axioms QuantumNLS.Local003Est.est_cubic
#print axioms QuantumNLS.Local003Est.est_deriv
