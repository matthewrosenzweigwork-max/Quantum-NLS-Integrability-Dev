import Mathlib
import QuantumNLS.RB01Head

/-! R-EC25334D (`thm:global-B01-actions`), stage RB01Tail: the exact tail form (source `collective_actions.tex:56-58`,
"for a field-dependent integer `N`, the tail has the exact form `I_n(u) = |g_n(u)|² r_n(u)`, `|n| > N`"; proof
:375-386 and eq. `GB01-mass-factor`).

With contour radius `r = d = dd L` and one common `N`, `ρ` for the frozen inputs
`RB01Bridge.tail_entries_profile` (the entry `b_n = (B_n − p_n)_{10}` as one real-analytic `ℓ²`-valued map, together
with `SqSmall` and `‖S − 1‖ ≤ 1/2`), `RB01RootCount.root_count` and `RB01RootPrep.root_prep` (at `t = 1`),
`RB01Density.density` (at `t = 1`) and `RB01Head.r_ext` (the map `G` of `RB01CxDensity.r_linf`):
* `RB01SpecEig.ident` gives `B_n − p_n = [[α_n, b̄_n],[b_n, α_n]]` with `τ_n = |b_n|²`;
* RB01Density (e): `I_n = (L/(4κ)) τ_n r_n`, `Im r_n = 0`, `1/2 < Re r_n < 3/2`.
* **`tail_form`**: `I_n(u) = (L/(4κ)) |b_n(u)|² Re r_n(u) = |g_n(u)|² Re r_n(u)` with `g_n = √(L/(4κ)) b_n`, for all
  `‖u − u₀‖ < ρ`, `|n| > N`, where `r_n(u) = G(u, ū)_n`; also returned: real analyticity of `b` and of
  `u ↦ G(u, ū)`, and the `RB01Head.r_ext` complexification of `G`. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace QuantumNLS.RB01Tail

open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002SA QuantumNLS.Local002Circle
  QuantumNLS.Local003InvSqrt QuantumNLS.LocalSpectral.Round23
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.ProductTorusComplexification (Cx)
open QuantumNLS.TerraMultiRound30HessianBridge (Actions)
open QuantumNLS.RB01SpecForm (Kmat Bmat)
open QuantumNLS.RB01RootPrep (dd dd_pos)
open QuantumNLS.RB01Head (trunc)

variable {L κ : ℝ} [Fact (0 < L)]

/-- **Exact tail form** `I_n = |g_n|² r_n`, `g_n = √(L/(4κ)) b_n`, `|n| > N`, on `‖u − u₀‖ < ρ`. -/
theorem tail_form (hκ : 0 < κ) (u₀ : L2T L) :
    ∃ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ∃ b : L2T L → lp (fun _ : ℤ => ℂ) 2,
      ∃ G : L2T L × L2T L → QuantumNLS.RB01LinfLift.Linf ℤ,
      AnalyticOnNhd ℝ b (ball u₀ ρ) ∧
      (∀ u : L2T L, ‖u - u₀‖ < ρ → AnalyticAt ℝ (fun u' : L2T L => G (u', star u')) u) ∧
      (∀ S : Finset ℤ, ∃ R > (0 : ℝ), R ≤ ρ ∧ ∃ M : ℝ, ∃ rc : Cx (L2T L) → QuantumNLS.RB01LinfLift.Linf ℤ,
        AnalyticOnNhd ℂ rc (ball (Cx.ι u₀) R) ∧ (∀ z ∈ ball (Cx.ι u₀) R, ‖rc z‖ ≤ M) ∧
        ∀ x ∈ ball u₀ R, rc (Cx.ι x) = trunc ∞ S (G (x, star x))) ∧
      ∀ u : L2T L, ‖u - u₀‖ < ρ → ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| →
        Actions hκ u n = ‖((√(L / (4 * κ)) : ℝ) : ℂ) * b u n‖ ^ 2 * (G (u, star u) n).re ∧
        Actions hκ u n = L / (4 * κ) * ‖b u n‖ ^ 2 * (G (u, star u) n).re ∧
        (G (u, star u) n).im = 0 ∧ 1 / 2 < (G (u, star u) n).re ∧ (G (u, star u) n).re < 3 / 2 := by
  have hL : 0 < L := Fact.out
  obtain ⟨N₁, ρ₁, hρ₁, bf, hba, hbf⟩ :=
    QuantumNLS.RB01Bridge.tail_entries_profile (κ := κ) hL (dd_pos (L := L)) (QuantumNLS.RB01SpecEig.dd_lt (L := L)) u₀
  obtain ⟨N₂, ρ₂, hρ₂, h2⟩ := QuantumNLS.RB01RootCount.root_count hκ u₀
  obtain ⟨N₃, ρ₃, hρ₃, h3⟩ := QuantumNLS.RB01RootPrep.root_prep κ u₀
  obtain ⟨N₄, ρ₄, hρ₄, h4⟩ := QuantumNLS.RB01Density.density hκ u₀
  obtain ⟨N₅, ρ₅, hρ₅, G, -, hGr, hGs, hGe⟩ := QuantumNLS.RB01Head.r_ext hκ u₀
  set N : ℕ := max (max N₁ N₂) (max (max N₃ N₄) N₅) with hNdef
  set ρ : ℝ := min (min ρ₁ ρ₂) (min (min ρ₃ ρ₄) ρ₅) with hρdef
  have hρ : 0 < ρ := lt_min (lt_min hρ₁ hρ₂) (lt_min (lt_min hρ₃ hρ₄) hρ₅)
  have hρ1 : ρ ≤ ρ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hρ2 : ρ ≤ ρ₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hρ3 : ρ ≤ ρ₃ := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hρ4 : ρ ≤ ρ₄ := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hρ5 : ρ ≤ ρ₅ := (min_le_right _ _).trans (min_le_right _ _)
  have hN : ∀ k : ℕ, k ≤ N → ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| → (k : ℝ) < |(n : ℝ)| := fun k hk n hn =>
    lt_of_le_of_lt (by exact_mod_cast hk) hn
  have hk1 : N₁ ≤ N := (le_max_left _ _).trans (le_max_left _ _)
  have hk2 : N₂ ≤ N := (le_max_right _ _).trans (le_max_left _ _)
  have hk3 : N₃ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hk4 : N₄ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hk5 : N₅ ≤ N := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨N, ρ, hρ, fun v => bf (vec2 1 0) 1 v, G, fun v hv => hba _ _ v (ball_subset_ball hρ1 hv),
    fun u hu => hGr u (lt_of_lt_of_le hu hρ5),
    fun S => ?_, fun u hu n hn => ?_⟩
  · obtain ⟨R, hR, hRρ, M, rc, h1, h2, h3⟩ := hGe S
    refine ⟨min R ρ, lt_min hR hρ, min_le_right _ _, M, rc, fun z hz => h1 z (ball_subset_ball (min_le_left _ _) hz),
      fun z hz => h2 z (ball_subset_ball (min_le_left _ _) hz),
      fun x hx => h3 x (ball_subset_ball (min_le_left _ _) hx)⟩
  -- the pointwise identity
  have hub : u ∈ ball u₀ ρ₁ := by rw [mem_ball, dist_eq_norm]; exact lt_of_lt_of_le hu hρ1
  obtain ⟨hSq, hS, hbeq⟩ := (hbf u hub n (vec2 1 0) 1).1 (hN N₁ hk1 n hn)
  have ht : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hc := h2 n (hN N₂ hk2 n hn) u (lt_of_lt_of_le hu hρ2) 1 ht
  have hp := h3 n (hN N₃ hk3 n hn) u (lt_of_lt_of_le hu hρ3) 1 ht
  have hd := h4 n (hN N₄ hk4 n hn) u (lt_of_lt_of_le hu hρ4) 1 ht
  simp only [one_smul] at hc hp hd
  obtain ⟨-, -, -, -, hb1, hb2, hz, -⟩ := hc
  obtain ⟨-, -, hΔ, -⟩ := hp
  obtain ⟨-, -, -, -, ⟨hI, -, -, -⟩, -⟩ := hd
  obtain ⟨a, b, hab, -, htau⟩ := QuantumNLS.RB01SpecEig.ident hκ u n hSq (lt_of_le_of_lt hS (by norm_num))
    hz hb1 hb2 hΔ
  have hB : (Bmat L κ (circleRep u) n (dd L) (vec2 1 0)) 1 = b := by
    rw [hab]; simp
  have hbb : bf (vec2 1 0) 1 u n = b := by
    rw [← hB]; exact hbeq
  obtain ⟨hGn, him, hlo, hhi⟩ := hGs u (lt_of_lt_of_le hu hρ5) n (hN N₅ hk5 n hn)
  rw [hGn]
  have hr : QuantumNLS.RB01Density.rn hκ u n = (((QuantumNLS.RB01Density.rn hκ u n).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [hr] at hI
  have hI' : Actions hκ u n = L / (4 * κ) * QuantumNLS.RB01RootCount.tau hκ u n *
      (QuantumNLS.RB01Density.rn hκ u n).re := by
    have : (((Actions hκ u n : ℝ)) : ℂ) = ((L / (4 * κ) * QuantumNLS.RB01RootCount.tau hκ u n *
        (QuantumNLS.RB01Density.rn hκ u n).re : ℝ) : ℂ) := by
      rw [show ((Actions hκ u n : ℝ) : ℂ) = (((QuantumNLS.RootIndexedMasses.masses hκ u).1 n : ℝ) : ℂ) from rfl, hI]
      push_cast; ring
    exact_mod_cast this
  have hq : 0 ≤ L / (4 * κ) := by positivity
  refine ⟨?_, ?_, him, hlo, hhi⟩
  · rw [hI', htau, hbb, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, Real.sq_sqrt hq]
  · rw [hI', htau, hbb]

end QuantumNLS.RB01Tail

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.RB01Tail.tail_form
