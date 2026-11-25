import Mathlib
import QuantumNLS.MixedQuadratures
import QuantumNLS.MPChartDeriv
import QuantumNLS.MPContour

/-!
# PROP-026 `lem:MP-linearization`: the actual family `F_θ`, `g_θ = f_{z_θ}`: smoothness, derivative bounds, measurability

New module.  Over the parameter space `Θ = Fin m × [0,1]` of `MPContour` (pieces `P`, contour points `z_θ`, complex weights `u_θ`),
and a background family `c₀, D, s, A : ℂ → ℂ` satisfying the uniform bounds of the source's contour setup on the contour set
(`d₀ ≤ ‖D‖`, `‖s‖ ≤ s₁`, `a₀ ≤ ‖A‖`, `A = (s+D)/2`, `‖c₀‖ ≤ c₁`, continuity off the real axis):

* `gθ θ = gfun r c₀(z_θ) D(z_θ) s(z_θ) A(z_θ)` (the bounded smooth extension `f_{z_θ}` of the chart) at good parameters
  (`Im z_θ ≠ 0`; the finitely many parameters on the real axis form a `ν`-null set) and `0` otherwise;
  `Fθ θ = quadF (u_θ) (gθ θ)`  (`F_θ(x) = Re(u_θ g_θ(x₀+ix₁))`);
* `contDiff_Fθ`: `F_θ ∈ C^∞`; `norm_iteratedFDeriv_Fθ_le`: `‖D^i F_θ(x)‖ ≤ w_θ · Bder(Cψ, r, c₁, i)` for `i ≤ m`
  (so `hFb` of PROP-014 with `w = ‖u‖` and `M0 = ∑_{i ≤ m} Bder`);
* `continuousAt_gθ`: `(θ, w) ↦ gθ θ w` is continuous at every good `θ`;
* `aesm_resKd`: `θ ↦ F_θ|_K ∈ C(K,ℂ)` is a.e. strongly measurable (**`hFm`**);
* `hasDerivAt_gθ`, `aesm_fderiv`: `∂_wg_θ(s_θ) = D(z_θ)⁻¹` (good) and strong measurability of the directional derivatives (**`hdF`**).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ContDiff

namespace QuantumNLS.MPFamily

open QuantumNLS.MPContour QuantumNLS.MPChartBounds QuantumNLS.MPChartSmooth QuantumNLS.MPChartDeriv
open QuantumNLS.MixedQuadratures (quadF isoR2 Kdisc fderiv_quadF continuous_quadF)
open QuantumNLS.FunctionalLinearization (resKd resKd_apply)
open QuantumNLS.MixedTraceNorm (chartLambda hasDerivAt_chartLambda)

/-- The background data on the contour set `Z` (the uniform bounds stated in the source's contour setup). -/
structure BgFam (Z : Set ℂ) (d₀ s₁ a₀ c₁ : ℝ) where
  c0 : ℂ → ℂ
  D : ℂ → ℂ
  s : ℂ → ℂ
  A : ℂ → ℂ
  hc0 : ContinuousOn c0 (Z ∩ {z | z.im ≠ 0})
  hD : ContinuousOn D (Z ∩ {z | z.im ≠ 0})
  hs : ContinuousOn s (Z ∩ {z | z.im ≠ 0})
  hA : ContinuousOn A (Z ∩ {z | z.im ≠ 0})
  bg : ∀ z ∈ Z, z.im ≠ 0 → Bg d₀ s₁ a₀ (D z) (s z) (A z)
  c0le : ∀ z ∈ Z, z.im ≠ 0 → ‖c0 z‖ ≤ c₁
  s_le : ∀ z ∈ Z, ‖s z‖ ≤ s₁

variable {m : ℕ} {Z : Set ℂ} {d₀ s₁ a₀ c₁ : ℝ}

/-- Good parameters: the contour point is off the real axis. -/
def good (P : Fin m → Piece) (θ : ThetaSpace m) : Prop := (zθ P θ).im ≠ 0

theorem isOpen_good (P : Fin m → Piece) : IsOpen {θ : ThetaSpace m | good P θ} :=
  isOpen_ne_fun (Complex.continuous_im.comp (continuous_zθ P)) continuous_const

open Classical in
/-- The bounded smooth extension `f_{z_θ}` of the chart. -/
def gθ (P : Fin m → Piece) (B : BgFam Z d₀ s₁ a₀ c₁) (θ : ThetaSpace m) : ℂ → ℂ :=
  if good P θ then gfun (rad d₀ s₁ a₀) (B.c0 (zθ P θ)) (B.D (zθ P θ)) (B.s (zθ P θ)) (B.A (zθ P θ))
  else fun _ => 0

/-- `F_θ(x) = Re(u_θ g_θ(x₀ + i x₁))`. -/
def Fθ (κ : ℝ) (P : Fin m → Piece) (B : BgFam Z d₀ s₁ a₀ c₁) (θ : ThetaSpace m) :
    EuclideanSpace ℝ (Fin 2) → ℝ := quadF (uθ κ P θ) (gθ P B θ)

open Classical in
/-- The derivative `∂_w g_θ(s_θ)`: `D(z_θ)⁻¹` at good parameters. -/
def dθ (P : Fin m → Piece) (B : BgFam Z d₀ s₁ a₀ c₁) (θ : ThetaSpace m) : ℂ :=
  if good P θ then (B.D (zθ P θ))⁻¹ else 0

section Smooth

variable (κ : ℝ) (P : Fin m → Piece) (B : BgFam Z d₀ s₁ a₀ c₁) (hZ : ∀ i, ∀ τ ∈ Icc (0 : ℝ) 1, (P i).γ τ ∈ Z)
include hZ

theorem contDiff_gθ (θ : ThetaSpace m) : ContDiff ℝ ∞ (gθ P B θ) := by
  unfold gθ
  split_ifs with h
  · exact contDiff_gfun (B.bg _ (hZ θ.1 θ.2 θ.2.2) h) _
  · exact contDiff_const

theorem contDiff_Fθ (θ : ThetaSpace m) : ContDiff ℝ ∞ (Fθ κ P B θ) := by
  unfold Fθ quadF
  exact Complex.reCLM.contDiff.comp (contDiff_const.mul ((contDiff_gθ P B hZ θ).comp
    isoR2.symm.contDiff))

omit hZ in
theorem Bder_mono {Cψ r c c' : ℝ} (hC : 0 ≤ Cψ) (hr : 0 < r) (hcc : c ≤ c') (i : ℕ) :
    Bder Cψ r c i ≤ Bder Cψ r c' i := by
  unfold Bder
  refine Finset.sum_le_sum (fun j _ => ?_)
  have h1 : 0 ≤ (i.choose j : ℝ) * Cψ := mul_nonneg (Nat.cast_nonneg _) hC
  refine mul_le_mul_of_nonneg_left ?_ h1
  have h2 : (0 : ℝ) < r ^ (i - j) := pow_pos hr _
  rw [div_le_div_iff_of_pos_right h2]
  exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)

omit hZ in
theorem norm_iteratedFDeriv_quadF_le (u : ℂ) {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g) (i : ℕ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ‖iteratedFDeriv ℝ i (quadF u g) x‖ ≤ ‖u‖ * ‖iteratedFDeriv ℝ i g (isoR2.symm x)‖ := by
  set L : ℂ →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.mul ℝ ℂ u) with hL
  have e : quadF u g = L ∘ (g ∘ isoR2.symm) := by
    funext y; simp [quadF, hL]
  rw [e]
  have h1 : ContDiffAt ℝ ∞ (g ∘ isoR2.symm) x := (hg.comp isoR2.symm.contDiff).contDiffAt
  have hLn : ‖L‖ ≤ ‖u‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg u) (fun y => ?_)
    simp only [hL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', Complex.reCLM_apply]
    calc ‖(u * y).re‖ ≤ ‖u * y‖ := by rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
      _ = ‖u‖ * ‖y‖ := norm_mul _ _
  calc ‖iteratedFDeriv ℝ i (L ∘ (g ∘ isoR2.symm)) x‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ i (g ∘ isoR2.symm) x‖ :=
        L.norm_iteratedFDeriv_comp_left h1 (by exact_mod_cast le_top)
    _ ≤ ‖u‖ * ‖iteratedFDeriv ℝ i (g ∘ isoR2.symm) x‖ :=
        mul_le_mul_of_nonneg_right hLn (norm_nonneg _)
    _ = ‖u‖ * ‖iteratedFDeriv ℝ i g (isoR2.symm x)‖ := by
        rw [isoR2.symm.norm_iteratedFDeriv_comp_right]

omit hZ in
theorem Fθ_bad {θ : ThetaSpace m} (h : ¬ good P θ) : Fθ κ P B θ = fun _ => 0 := by
  unfold Fθ gθ
  rw [if_neg h]
  funext x; simp [quadF]

/-- **`hFb` of PROP-014**: the uniform derivative bound, with `w = ‖u‖`. -/
theorem norm_iteratedFDeriv_Fθ_le (hc1 : 0 ≤ c₁) {mm : ℕ} {Cψ : ℝ}
    (hCψ : ∀ i ≤ mm, ∀ v, ‖iteratedFDeriv ℝ i (cutoff (rad d₀ s₁ a₀)) v‖ ≤ Cψ) (hC0 : 0 ≤ Cψ)
    (hr : 0 < rad d₀ s₁ a₀) {i : ℕ} (hi : i ≤ mm) (θ : ThetaSpace m) (x : EuclideanSpace ℝ (Fin 2)) :
    ‖iteratedFDeriv ℝ i (Fθ κ P B θ) x‖ ≤ wθ κ P θ * Bder Cψ (rad d₀ s₁ a₀) c₁ i := by
  by_cases h : good P θ
  · have hbg := B.bg _ (hZ θ.1 θ.2 θ.2.2) h
    have hq := norm_iteratedFDeriv_quadF_le (uθ κ P θ) (contDiff_gθ P B hZ θ) i x
    have hg : gθ P B θ = gfun (rad d₀ s₁ a₀) (B.c0 (zθ P θ)) (B.D (zθ P θ)) (B.s (zθ P θ)) (B.A (zθ P θ)) := by
      unfold gθ; rw [if_pos h]
    have hd := norm_iteratedFDeriv_gfun_le hbg (B.c0 (zθ P θ)) hCψ hC0 hi (isoR2.symm x)
    have hm := Bder_mono hC0 hr (B.c0le _ (hZ θ.1 θ.2 θ.2.2) h) i
    unfold Fθ
    calc ‖iteratedFDeriv ℝ i (quadF (uθ κ P θ) (gθ P B θ)) x‖
        ≤ ‖uθ κ P θ‖ * ‖iteratedFDeriv ℝ i (gθ P B θ) (isoR2.symm x)‖ := hq
      _ ≤ ‖uθ κ P θ‖ * Bder Cψ (rad d₀ s₁ a₀) c₁ i := by
          rw [hg]
          exact mul_le_mul_of_nonneg_left (hd.trans hm) (norm_nonneg _)
  · rw [Fθ_bad κ P B h]
    have : iteratedFDeriv ℝ i (fun _ : EuclideanSpace ℝ (Fin 2) => (0 : ℝ)) x = 0 := by
      have := iteratedFDeriv_fun_zero (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 2)) (F := ℝ) (n := i)
      simpa using congrFun this x
    rw [this, norm_zero]
    exact mul_nonneg (norm_nonneg _) (Bder_nonneg hC0 hr hc1 i)

end Smooth

end QuantumNLS.MPFamily

#print axioms QuantumNLS.MPFamily.contDiff_Fθ
#print axioms QuantumNLS.MPFamily.norm_iteratedFDeriv_Fθ_le
#print axioms QuantumNLS.MPFamily.norm_iteratedFDeriv_quadF_le
