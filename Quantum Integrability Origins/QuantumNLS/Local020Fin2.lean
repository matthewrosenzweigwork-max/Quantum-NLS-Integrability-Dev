import Mathlib
import QuantumNLS.Local020Fin1
import QuantumNLS.RootMassPlane
import QuantumNLS.RootMassScaling

/-! LOCAL-020: plane waves and scaling for a LOCAL-007 family. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric Filter Topology ComplexConjugate BoundedContinuousFunction
open QuantumNLS.LocalSpectral
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Local007Final (Pkg gcoef)
open QuantumNLS.Fourier (modeLp)
open QuantumNLS.RootIndexedMasses (masses)
open QuantumNLS.Local020Fin1 (Dat)

namespace QuantumNLS.Local020Fin2

variable {L κ r : ℝ} [Fact (0 < L)]
variable {hκ : 0 < κ} {ρ C : ℝ} {a : ℤ → L2T L → ℝ} {b : ℤ → L2T L → ℂ} {rr : L2T L → (ℤ →ᵇ ℝ)}

theorem coeff_c_mode (c : ℂ) (k n : ℤ) :
    QuantumNLS.Fourier.coeff L (((c • modeLp L k : L2T L)) : AddCircle L → ℂ) n = if n = k then c else 0 := by
  rw [← QuantumNLS.Fourier.fourierL2_apply, map_smul, QuantumNLS.Fourier.fourierL2_modeLp]
  simp [lp.single_apply, Pi.single_apply]

/-- **(c4)** `ζ(u) = 𝓕u` on every single Fourier plane. -/
theorem plane_zeta (D : Dat L κ r ρ C hκ a b rr) (hρr : 2 * Real.sqrt κ * (Real.sqrt L)⁻¹ * ρ < r)
    (k : ℤ) (c : ℂ) (hc : ‖c‖ < ρ) (n : ℤ) :
    gcoef L κ * b n (c • modeLp L k) * ((Real.sqrt (rr (c • modeLp L k) n) : ℝ) : ℂ) =
      QuantumNLS.Fourier.coeff L (((c • modeLp L k : L2T L)) : AddCircle L → ℂ) n := by
  have hL : 0 < L := Fact.out
  have hCρ : C * ρ ^ 2 < 2 := by linarith [D.small]
  set u : L2T L := c • modeLp L k with hu
  have hub : u ∈ ball (0 : L2T L) ρ := by
    rw [mem_ball_zero_iff, hu, norm_smul, QuantumNLS.Local020Rr.norm_modeLp L k, mul_one]; exact hc
  have hmass := D.mass u hub n
  have hpm : (masses hκ u).1 n = if n = k then ‖c‖ ^ 2 else 0 := by
    have hs : (Real.sqrt L : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hL).ne'
    have := QuantumNLS.RootMassPlane.masses_plane_amplitude (L := L) hκ (c / (Real.sqrt L : ℂ)) k n
    rw [show ((Real.sqrt L : ℂ) * (c / (Real.sqrt L : ℂ))) = c from by field_simp] at this
    rw [hu, this]
    split_ifs
    · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt hL.le]
      field_simp
    · rfl
  rw [coeff_c_mode]
  by_cases hnk : n = k
  · subst hnk
    simp only [if_true]
    have hg := QuantumNLS.Local020PlaneG.plane_g hκ D.pkg D.hC0 D.hρ hCρ hρr n c hc
    rw [hg]
    by_cases hc0 : c = 0
    · subst hc0; simp
    · have h1 : ‖c‖ ^ 2 = ‖gcoef L κ * b n u‖ ^ 2 * rr u n := by rw [← hmass, hpm]; simp
      rw [hg] at h1
      have hrr : rr u n = 1 := by
        have : 0 < ‖c‖ ^ 2 := by positivity
        have h2 : ‖c‖ ^ 2 * (rr u n - 1) = 0 := by linarith
        rcases mul_eq_zero.1 h2 with h | h
        · exact absurd h this.ne'
        · linarith
      simp [hrr]
  · simp only [hnk, if_false]
    have h1 : ‖gcoef L κ * b n u‖ ^ 2 * rr u n = 0 := by rw [← hmass, hpm]; simp [hnk]
    have hpos := D.pos u hub n
    have h2 : ‖gcoef L κ * b n u‖ ^ 2 = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact h
      · exact absurd h hpos.ne'
    have h3 : gcoef L κ * b n u = 0 := norm_eq_zero.1 (by simpa using h2)
    rw [h3, zero_mul]

/-- Identity theorem: an analytic function vanishing near `0` vanishes on the whole ball. -/
theorem eq_ball_extend {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ρ ρ₃ : ℝ} (hρ₃ : 0 < ρ₃)
    {f : E → ℝ} (hf : AnalyticOnNhd ℝ f (ball (0 : E) ρ)) (h0 : ∀ w ∈ ball (0 : E) ρ₃, f w = 0) :
    ∀ w ∈ ball (0 : E) ρ, f w = 0 := by
  by_cases hρ : 0 < ρ
  · have h0mem : (0 : E) ∈ ball (0 : E) ρ := mem_ball_self hρ
    have hev : f =ᶠ[𝓝 (0 : E)] 0 := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hρ₃)] with w hw using h0 w hw
    exact hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball (0 : E) ρ).isPreconnected h0mem hev
  · intro w hw
    exact absurd hw (by rw [ball_eq_empty.2 (not_lt.1 hρ)]; exact Set.notMem_empty w)

theorem gcoef_scale (hκ : 0 < κ) {s : ℝ} (hs : 0 < s) : gcoef L κ = (s : ℂ) * gcoef L (κ * s ^ 2) := by
  unfold gcoef
  have h1 : Real.sqrt (κ * s ^ 2) = Real.sqrt κ * s := by
    rw [Real.sqrt_mul' _ (sq_nonneg s), Real.sqrt_sq hs.le]
  rw [h1]
  have hk : (Real.sqrt κ : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hκ).ne'
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  push_cast
  field_simp

theorem masses_scale (hκ : 0 < κ) {s : ℝ} (hs : 0 < s) (hκ₂ : 0 < κ * s ^ 2) (w : L2T L) (n : ℤ) :
    (masses hκ ((s : ℂ) • w)).1 n = s ^ 2 * (masses hκ₂ w).1 n := by
  have hc : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hn : ‖(s : ℂ)‖ = s := by rw [Complex.norm_real, Real.norm_of_nonneg hs.le]
  have key : ∀ κ'' (h : κ'' = κ * ‖(s : ℂ)‖ ^ 2) (hκ'' : 0 < κ''),
      (masses hκ ((s : ℂ) • w)).1 n = ‖(s : ℂ)‖ ^ 2 * (masses hκ'' w).1 n := by
    intro κ'' h hκ''
    subst h
    exact QuantumNLS.RootMassScaling.masses_smul hκ (s : ℂ) hc w n
  have := key (κ * s ^ 2) (by rw [hn]) hκ₂
  rwa [hn] at this

/-- **(c5)** scaling: `g_κ(s u) = s g_{κ s²}(u)` and `rr_κ(s u) = rr_{κ s²}(u)`, for every other family. -/
theorem scale_clause (D : Dat L κ r ρ C hκ a b rr) {s : ℝ} (hs : 0 < s) (hκ₂ : 0 < κ * s ^ 2)
    {ρ₂ C₂ : ℝ} {a₂ : ℤ → L2T L → ℝ} {b₂ : ℤ → L2T L → ℂ} {rr₂ : L2T L → (ℤ →ᵇ ℝ)}
    (hρ₂ : 0 < ρ₂) (hC₂ : 0 ≤ C₂) (hP₂ : ∀ n, Pkg L (κ * s ^ 2) r ρ₂ C₂ n (a₂ n) (b₂ n))
    (hana₂ : AnalyticOnNhd ℝ rr₂ (ball (0 : L2T L) ρ₂))
    (hmass₂ : ∀ u ∈ ball (0 : L2T L) ρ₂, ∀ n : ℤ,
      (masses hκ₂ u).1 n = ‖gcoef L (κ * s ^ 2) * b₂ n u‖ ^ 2 * rr₂ u n)
    {u : L2T L} (hu₂ : ‖u‖ < ρ₂) (hsu : s * ‖u‖ < ρ) (n : ℤ) :
    gcoef L κ * b n ((s : ℂ) • u) = (s : ℂ) * (gcoef L (κ * s ^ 2) * b₂ n u) ∧
      rr ((s : ℂ) • u) n = rr₂ u n := by
  have hn : ∀ w : L2T L, ‖(s : ℂ) • w‖ = s * ‖w‖ := fun w => by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hs.le]
  have hsb : ∀ w : L2T L, ‖w‖ < ρ₂ → s * ‖w‖ < ρ → ∀ m : ℤ, b m ((s : ℂ) • w) = b₂ m w := fun w hw1 hw2 m =>
    QuantumNLS.Local020Cov.cov_scale hs rfl D.pkg hP₂ (mem_ball_zero_iff.2 hw1)
      (mem_ball_zero_iff.2 (by rw [hn]; exact hw2)) m
  have hg : ∀ w : L2T L, ‖w‖ < ρ₂ → s * ‖w‖ < ρ → ∀ m : ℤ,
      gcoef L κ * b m ((s : ℂ) • w) = (s : ℂ) * (gcoef L (κ * s ^ 2) * b₂ m w) := fun w hw1 hw2 m => by
    rw [hsb w hw1 hw2 m, gcoef_scale hκ hs]; ring
  refine ⟨hg u hu₂ hsu n, ?_⟩
  -- rr by uniqueness
  set ρ'' : ℝ := min ρ₂ (ρ / s) with hρ''
  have hρ''pos : 0 < ρ'' := lt_min hρ₂ (div_pos D.hρ hs)
  have hmem : ∀ w, w ∈ ball (0 : L2T L) ρ'' → ‖w‖ < ρ₂ ∧ s * ‖w‖ < ρ := fun w hw => by
    rw [mem_ball_zero_iff] at hw
    refine ⟨lt_of_lt_of_le hw (min_le_left _ _), ?_⟩
    have := lt_of_lt_of_le hw (min_le_right _ _)
    rw [lt_div_iff₀ hs] at this; linarith
  let Ts : L2T L →L[ℝ] L2T L := (s : ℝ) • ContinuousLinearMap.id ℝ (L2T L)
  have hTs : ∀ w, Ts w = (s : ℂ) • w := fun w => by
    show (s : ℝ) • w = _
    exact (Complex.coe_smul s w).symm
  have hf1 : AnalyticOnNhd ℝ (fun w : L2T L => (rr (Ts w)) n) (ball (0 : L2T L) ρ'') := fun w hw => by
    have hb : Ts w ∈ ball (0 : L2T L) ρ := by
      rw [mem_ball_zero_iff, hTs, hn]; exact (hmem w hw).2
    exact (((BoundedContinuousFunction.evalCLM ℝ n).analyticAt (rr (Ts w))).comp (D.ana _ hb)).comp (Ts.analyticAt w)
  have hf2 : AnalyticOnNhd ℝ (fun w : L2T L => (rr₂ w) n) (ball (0 : L2T L) ρ'') := fun w hw => by
    exact ((BoundedContinuousFunction.evalCLM ℝ n).analyticAt (rr₂ w)).comp
      (hana₂ w (mem_ball_zero_iff.2 (hmem w hw).1))
  set ρ₃ : ℝ := min ρ'' (1 / (C₂ + 1)) with hρ₃
  have hρ₃pos : 0 < ρ₃ := lt_min hρ''pos (by positivity)
  have hρ₃C : C₂ * ρ₃ ^ 2 < 1 := by
    have h1 : ρ₃ ≤ 1 / (C₂ + 1) := min_le_right _ _
    have h2 : 0 ≤ ρ₃ := hρ₃pos.le
    have h3 : ρ₃ * (C₂ + 1) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at h1
    nlinarith [sq_nonneg ρ₃, mul_nonneg h2 hC₂]
  have hsub : ball (0 : L2T L) ρ₃ ⊆ ball (0 : L2T L) ρ'' := ball_subset_ball (min_le_left _ _)
  have hg₂ : AnalyticOnNhd ℝ (fun w : L2T L => gcoef L (κ * s ^ 2) * b₂ n w) (ball (0 : L2T L) ρ₃) :=
    (hP₂ n).2.2.2.2.2.1.mono (ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)))
  obtain ⟨w0, hw0, hg0⟩ := QuantumNLS.Local020Rr.g_ne_zero (hP₂ n) hC₂ hρ₃pos
    ((min_le_left _ _).trans (min_le_left _ _)) hρ₃C
  have hunique := QuantumNLS.Local020Rr.eq_of_mul_eq hg₂ ⟨w0, hw0, hg0⟩ (hf1.mono hsub) (hf2.mono hsub)
    (fun w hw => by
      have hw'' := hsub hw
      obtain ⟨h1, h2⟩ := hmem w hw''
      have hwb : Ts w ∈ ball (0 : L2T L) ρ := by
        rw [mem_ball_zero_iff, hTs, hn]; exact h2
      have e1 := D.mass (Ts w) hwb n
      rw [hTs, masses_scale hκ hs hκ₂, hmass₂ w (mem_ball_zero_iff.2 h1) n] at e1
      rw [hg w h1 h2 n, norm_mul (s : ℂ) (gcoef L (κ * s ^ 2) * b₂ n w), Complex.norm_real,
        Real.norm_of_nonneg hs.le] at e1
      show ‖gcoef L (κ * s ^ 2) * b₂ n w‖ ^ 2 * (rr (Ts w)) n = ‖gcoef L (κ * s ^ 2) * b₂ n w‖ ^ 2 * (rr₂ w) n
      rw [hTs]
      have hs2 : 0 < s ^ 2 := by positivity
      have : s ^ 2 * (‖gcoef L (κ * s ^ 2) * b₂ n w‖ ^ 2 * (rr₂ w) n) =
          s ^ 2 * (‖gcoef L (κ * s ^ 2) * b₂ n w‖ ^ 2 * (rr ((s : ℂ) • w)) n) := by
        rw [e1]; ring
      exact (mul_left_cancel₀ hs2.ne' this).symm)
  have hext := eq_ball_extend hρ₃pos (hf1.sub hf2) (fun w hw => by
    simp only [Pi.sub_apply]; rw [hunique w hw]; ring)
  have := hext u (mem_ball_zero_iff.2 (lt_min hu₂ (by rw [lt_div_iff₀ hs]; linarith)))
  simp only [Pi.sub_apply, hTs] at this
  linarith

end QuantumNLS.Local020Fin2

#print axioms QuantumNLS.Local020Fin2.scale_clause
#print axioms QuantumNLS.Local020Fin2.plane_zeta
