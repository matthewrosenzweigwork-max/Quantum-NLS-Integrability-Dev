import Mathlib
import NlsGge.Atomic.G2.G2030
import NlsGge.Atomic.G2.G2033
import NlsGge.Atomic.G2.G2035
import NlsGge.GK38.TauGamma
import NlsGge.GK38.IsolatingFamily
import NlsGge.Sobolev.SourceEmbeddings
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38
-- MODULE: NlsGge.Atomic.G6.G6022

/- G6-022 PRODUCTION (proof development, AUTHOR; not self-reviewed). Weighted actions and weighted gaps have the same finiteness.
   Head verbatim from followup4 STATEMENTS/G6.md lines 493-498 (theorem G6022); no Pro round-5 entry exists for G6-022.
   Proof route: for every n, 4 I_n = (upper_n - lower_n)^2 * Re(xiSq38 n (realSlice u)) (G2_033, G2_030, tauGamma_real38);
   G2_035 at realSlice u gives delta <= Re(xiSq38 n (realSlice u)) <= 2 + 2C; then two-sided comparison and
   Summable.of_nonneg_of_le in both directions. No hypothesis is added; hm is unused. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- If ‖z - 1‖² ≤ C then Re(z²) ≤ 2 + 2C. -/
theorem g6022_re_sq_le (z : ℂ) (C : ℝ) (h : ‖z - 1‖ ^ 2 ≤ C) :
    (z ^ 2).re ≤ 2 + 2 * C := by
  have h1 : ‖z‖ ≤ ‖z - 1‖ + 1 := by
    have := norm_sub_norm_le z 1
    rw [norm_one] at this
    linarith
  have h2 : ‖z‖ * ‖z‖ ≤ (‖z - 1‖ + 1) * (‖z - 1‖ + 1) :=
    mul_le_mul h1 h1 (norm_nonneg _) (by positivity)
  have h3 : (z ^ 2).re ≤ ‖z ^ 2‖ := Complex.re_le_norm _
  rw [norm_pow] at h3
  nlinarith [sq_nonneg (‖z - 1‖ - 1)]

/-- Exact identity on one labelled gap: γ_n² · Re(ξ_n²) = 4 I_n on the real slice. -/
theorem g6022_identity (u : PhysicalL2) (n : ℤ) :
    (actualGapUpperAllE02_38 u n - actualGapLowerAllE02_38 u n) ^ 2 *
        (NlsGge.GK38.xiSq38 n (NlsGge.GK38.realSlice u)).re =
      4 * actualGapActionAllE02_38 u n := by
  have h33 : NlsGge.GK38.gamma2 (NlsGge.GK38.realSlice u) n *
        NlsGge.GK38.xiSq38 n (NlsGge.GK38.realSlice u) =
      4 * NlsGge.GK38.gkActionC38 (NlsGge.GK38.realSlice u) n :=
    ((G2_033 n).2 (NlsGge.GK38.realSlice u) (NlsGge.GK38.realSlice_mem_gkW u)).1
  rw [(NlsGge.GK38.tauGamma_real38 u n).2, (G2_030 u n).1] at h33
  have h4 : ((4 * actualGapActionAllE02_38 u n : ℝ) : ℂ) =
      4 * (actualGapActionAllE02_38 u n : ℂ) := by
    simp
  rw [← h4] at h33
  have h := congrArg Complex.re h33
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  linarith

/-- Uniform real bounds on Re(ξ_n²) along the real slice, from G2_035 at realSlice u. -/
theorem g6022_bounds (u : PhysicalL2) :
    ∃ δ C : ℝ, 0 < δ ∧ ∀ n : ℤ,
      δ ≤ (NlsGge.GK38.xiSq38 n (NlsGge.GK38.realSlice u)).re ∧
      (NlsGge.GK38.xiSq38 n (NlsGge.GK38.realSlice u)).re ≤ 2 + 2 * C := by
  have hmem : NlsGge.GK38.realSlice u ∈ NlsGge.GKDefinitionDesign.actionPositiveDomain :=
    G2_035.2.1 (⟨u, rfl⟩ : NlsGge.GK38.realSlice u ∈
      Set.range (fun v : PhysicalL2 => NlsGge.GK38.realSlice v))
  obtain ⟨U, hU, -, δ, C, hδ, -, hb⟩ := G2_035.2.2.2.2 _ hmem
  obtain ⟨hlow, hsum, htsum⟩ := hb _ (mem_of_mem_nhds hU)
  refine ⟨δ, C, hδ, fun n => ⟨(hlow n).1, ?_⟩⟩
  have hle : ‖NlsGge.GK38.xiN38 n (NlsGge.GK38.realSlice u) - 1‖ ^ 2 ≤ C :=
    (hsum.le_tsum n (fun j _ => sq_nonneg _)).trans htsum
  have hsq := g6022_re_sq_le (NlsGge.GK38.xiN38 n (NlsGge.GK38.realSlice u)) C hle
  rw [← (hlow n).2.2]
  exact hsq

theorem G6022 (u : PhysicalL2) (m : ℕ) (hm : 1 ≤ m) :
  Summable (fun n : ℤ => sobolevModeWeight (m : ℝ) n *
    actualGapActionAllE02_38 u n) ↔
  Summable (fun n : ℤ => sobolevModeWeight (m : ℝ) n *
    (actualGapUpperAllE02_38 u n - actualGapLowerAllE02_38 u n)^2) := by
  obtain ⟨δ, C, hδ, hb⟩ := g6022_bounds u
  have hw : ∀ n : ℤ, 0 ≤ sobolevModeWeight (m : ℝ) n :=
    fun n => ((sobolevModeWeightPositive (m : ℝ)).out n).le
  have hγ : ∀ n : ℤ, 0 ≤ (actualGapUpperAllE02_38 u n - actualGapLowerAllE02_38 u n) ^ 2 :=
    fun n => sq_nonneg _
  have hlo : ∀ n : ℤ, δ * (actualGapUpperAllE02_38 u n - actualGapLowerAllE02_38 u n) ^ 2 ≤
      4 * actualGapActionAllE02_38 u n := by
    intro n
    have h1 := g6022_identity u n
    have h2 := mul_le_mul_of_nonneg_left (hb n).1 (hγ n)
    nlinarith
  have hhi : ∀ n : ℤ, 4 * actualGapActionAllE02_38 u n ≤
      (2 + 2 * C) * (actualGapUpperAllE02_38 u n - actualGapLowerAllE02_38 u n) ^ 2 := by
    intro n
    have h1 := g6022_identity u n
    have h2 := mul_le_mul_of_nonneg_left (hb n).2 (hγ n)
    nlinarith
  have hI0 : ∀ n : ℤ, 0 ≤ actualGapActionAllE02_38 u n := by
    intro n
    have h1 := mul_nonneg hδ.le (hγ n)
    have h2 := hlo n
    linarith
  constructor
  · intro hI
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hw n) (hγ n)) (fun n => ?_)
      (hI.mul_left (4 / δ))
    show sobolevModeWeight (m : ℝ) n *
        (actualGapUpperAllE02_38 u n - actualGapLowerAllE02_38 u n) ^ 2 ≤
      4 / δ * (sobolevModeWeight (m : ℝ) n * actualGapActionAllE02_38 u n)
    have e : 4 / δ * (sobolevModeWeight (m : ℝ) n * actualGapActionAllE02_38 u n) =
        sobolevModeWeight (m : ℝ) n * (4 * actualGapActionAllE02_38 u n) / δ := by
      ring
    rw [e, le_div_iff₀ hδ]
    nlinarith [mul_le_mul_of_nonneg_left (hlo n) (hw n)]
  · intro hG
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hw n) (hI0 n)) (fun n => ?_)
      (hG.mul_left ((2 + 2 * C) / 4))
    show sobolevModeWeight (m : ℝ) n * actualGapActionAllE02_38 u n ≤
      (2 + 2 * C) / 4 * (sobolevModeWeight (m : ℝ) n *
        (actualGapUpperAllE02_38 u n - actualGapLowerAllE02_38 u n) ^ 2)
    have e : (2 + 2 * C) / 4 * (sobolevModeWeight (m : ℝ) n *
        (actualGapUpperAllE02_38 u n - actualGapLowerAllE02_38 u n) ^ 2) =
        sobolevModeWeight (m : ℝ) n *
          ((2 + 2 * C) * (actualGapUpperAllE02_38 u n - actualGapLowerAllE02_38 u n) ^ 2) / 4 := by
      ring
    rw [e, le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    nlinarith [mul_le_mul_of_nonneg_left (hhi n) (hw n)]

end
end NlsGge.GKDefinitionDesign
