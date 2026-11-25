import NlsGge.Birkhoff.W07Probability38
import NlsGge.Ramer.CylindricalDensityConvergence

/-! # W07, part b: the exact decomposition of `f_N` (v2 `D:eq:fdecomposition`), conditional on `B`, `O`

Source: `paper/v2.tex` l.1565-1573. For `x ∈ E_s`, `x_N = P_N x`, `y_N = K(x_N) ∈ H` (`H = ActualCM c`,
the Cameron-Martin space) and `v_N = P_N x ∈ P_N H` (the head point of the Ramer density):

`f_N(x) = e^{-R_W(𝓕⁻¹ x_N)} · e^{-A((1-P_N) y_N)} · e^{-(‖v_N + P_N y_N‖² - ‖v_N‖²)/2}`,

where `A(h) = ½‖h‖²_H = ∑ a_n |h_n|²`. The first two factors are `e^{-R_W}` and
`exp[-A((Id-P_N)K(x_N))]` of v2 and the third is `exp[-A(P_N T x_N) + A(x_N)]`. The proof uses
the complete trace identity `E_W = ∑ a_n|Φ_n|² + R_W` (W05, `W05_chargeSeries_38`, item 4/6).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.HierarchyRiccati.Core NlsGge.Ramer Filter Topology
open scoped ENNReal Real

section Decomp

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) {s : ℝ}

theorem cmModeWeight_eq_two_fullWeightRate_W07 (n : ℤ) :
    cmModeWeight c n = 2 * fullWeightRate c.val n := rfl

theorem cmCoord_sub_W07 (a b : ActualCM c) (n : ℤ) :
    cmCoord (a - b) n = cmCoord a n - cmCoord b n := rfl

/-- `‖v‖² = 2 A(v)` for a head point. -/
theorem norm_sq_headPt_W07 (N : ℕ) (x : ℤ → ℂ) :
    ‖(headPt c N x : ActualCM c)‖ ^ 2 = 2 * Afin38 c N x := by
  rw [actualCM_norm_sq, tsum_eq_sum (s := symmetricModes N)]
  · unfold Afin38
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [cmCoord_headPt, cmModeWeight_eq_two_fullWeightRate_W07]
    simp only [hn, ↓reduceIte]
    ring
  · intro n hn
    rw [cmCoord_headPt]; simp [hn]

theorem headToE_headPt_projE38_W07 (N : ℕ) (x : FullWeightedHilbert c s) :
    headToE c s N (headPt c N (coordE c s x)) = projE38 c s N x := by
  apply fullWeighted_ext
  intro n
  rw [headToE_coord, cmCoord_headPt]
  exact (eCoe38_projE38 c s N x n).symm

/-- The tail `y - P_N y` and the head `v + P_N y`: coordinates. -/
theorem cmCoord_tail_W07 (N : ℕ) (y : ActualCM c) (n : ℤ) :
    cmCoord (y - ((cmTrunc c N y : actualCMHead c N) : ActualCM c)) n =
      if n ∈ symmetricModes N then 0 else cmCoord y n := by
  rw [cmCoord_sub_W07, cmCoord_cmTrunc]
  split_ifs <;> simp

theorem cmCoord_head_W07 (N : ℕ) (x : ℤ → ℂ) (y : ActualCM c) (n : ℤ) :
    cmCoord ((headPt c N x : ActualCM c) + ((cmTrunc c N y : actualCMHead c N) : ActualCM c)) n =
      if n ∈ symmetricModes N then x n + cmCoord y n else 0 := by
  rw [cmCoord_add, cmCoord_headPt, cmCoord_cmTrunc]
  split_ifs <;> simp

/-- Every finite section has finite spectral energy `E_W(𝓕⁻¹ x_N) < ∞` (so that `.toReal` in `f_N` is
the genuine energy). -/
theorem spectralEnergy_projE38_ne_top_W07 (N : ℕ) (x : FullWeightedHilbert c s) :
    spectralEnergyW38 c.val (physOfE38 c s (projE38 c s N x)) ≠ ⊤ := by
  rw [physOfE38_projE38_W07]; exact spectralEnergy_planeL2_ne_top_W07 c N _

end Decomp

section DecompB

namespace BirkhoffInput38

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {lower upper : ℝ}
  (c : BoundedCoefficients lower upper) {s : ℝ}

/-- `y_N = K(P_N x) ∈ H`. -/
def yN38 (hs1 : s ≤ 1) (N : ℕ) (x : FullWeightedHilbert c s) : ActualCM c :=
  B.KW06_38 O c hs1 (projE38 c s N x)

/-- Splitting of the coordinates of `T(P_N x)`: head `v + P_N y` plus tail `y - P_N y`. -/
theorem T_projE38_coord_W07 (hs1 : s ≤ 1) (N : ℕ) (x : FullWeightedHilbert c s) (n : ℤ) :
    B.T (eCoe38 c s (projE38 c s N x)) n =
      cmCoord ((headPt c N (coordE c s x) : ActualCM c) +
          ((cmTrunc c N (B.yN38 O c hs1 N x) : actualCMHead c N) : ActualCM c)) n +
        cmCoord ((B.yN38 O c hs1 N x) -
          ((cmTrunc c N (B.yN38 O c hs1 N x) : actualCMHead c N) : ActualCM c)) n := by
  rw [cmCoord_head_W07, cmCoord_tail_W07]
  have hy : cmCoord (B.yN38 O c hs1 N x) n =
      B.T (eCoe38 c s (projE38 c s N x)) n - eCoe38 c s (projE38 c s N x) n :=
    B.cmCoord_KW06_38 O c hs1 (projE38 c s N x) n
  rw [hy]
  by_cases hn : n ∈ symmetricModes N
  · have e := eCoe38_projE38 c s N x n
    simp only [hn, ↓reduceIte] at e ⊢
    rw [e, coordE_eq_eCoe38]; ring
  · have e := eCoe38_projE38 c s N x n
    simp only [hn, ↓reduceIte] at e ⊢
    rw [e]; ring

/-- The complete trace identity for the finite section (v2 `D:eq:energyidentity` at `u = 𝓕⁻¹ x_N`):
`E_W(𝓕⁻¹ x_N) = ½‖v + P_N y‖² + ½‖y - P_N y‖² + R_W(𝓕⁻¹ x_N)`, every quantity finite. -/
theorem energy_identity_W07 (hs' : s < 3 / 4) (hs1 : s ≤ 1) (N : ℕ) (x : FullWeightedHilbert c s) :
    (spectralEnergyW38 c.val (physOfE38 c s (projE38 c s N x))).toReal =
      ‖(headPt c N (coordE c s x) : ActualCM c) +
          ((cmTrunc c N (B.yN38 O c hs1 N x) : actualCMHead c N) : ActualCM c)‖ ^ 2 / 2 +
        ‖B.yN38 O c hs1 N x -
          ((cmTrunc c N (B.yN38 O c hs1 N x) : actualCMHead c N) : ActualCM c)‖ ^ 2 / 2 +
        remainder38 c.val (physOfE38 c s (projE38 c s N x)) := by
  set u := physOfE38 c s (projE38 c s N x) with hu
  have hE : spectralEnergyW38 c.val u ≠ ⊤ := by
    rw [hu, physOfE38_projE38_W07]; exact spectralEnergy_planeL2_ne_top_W07 c N _
  have hmem : fourierSeq38 u ∈ seqE38 c s := by
    rw [hu, fourierSeq38_physOfE38]; exact eCoe38_mem c s _
  obtain ⟨-, -, -, hex, hid, hspec⟩ := B.W05_chargeSeries_38 O (c := c) (s := s) hs'
  set u' : FinvE38 c s := ⟨u, hmem⟩ with hu'
  obtain ⟨U, hU, hper, hUu⟩ := hex u'
  have h6 : spectralEnergyW38 c.val u = chargeSeriesW38 c.val U := hspec u' U hU hper hUu
  have hfin : chargeSeriesW38 c.val U ≠ ⊤ := h6 ▸ hE
  obtain ⟨hsum, hid'⟩ := hid u' U hU hper hUu hfin
  rw [← h6] at hid'
  have hΦ : ∀ n, B.Φ u n = B.T (eCoe38 c s (projE38 c s N x)) n := by
    intro n
    show B.T (fourierSeq38 u) n = _
    rw [hu, fourierSeq38_physOfE38]
  have hΦ' : ∀ n, fullWeightRate c.val n * ‖B.Φ u'.1 n‖ ^ 2 =
      fullWeightRate c.val n * ‖B.T (eCoe38 c s (projE38 c s N x)) n‖ ^ 2 := fun n =>
    congrArg (fun t : ℂ => fullWeightRate c.val n * ‖t‖ ^ 2) (hΦ n)
  have hsum' : Summable (fun n : ℤ => fullWeightRate c.val n *
      ‖B.T (eCoe38 c s (projE38 c s N x)) n‖ ^ 2) := hsum.congr hΦ'
  set Q : ActualCM c := (headPt c N (coordE c s x) : ActualCM c) +
    ((cmTrunc c N (B.yN38 O c hs1 N x) : actualCMHead c N) : ActualCM c) with hQ
  set Tl : ActualCM c := B.yN38 O c hs1 N x -
    ((cmTrunc c N (B.yN38 O c hs1 N x) : actualCMHead c N) : ActualCM c) with hTl
  have hpt : ∀ n : ℤ, fullWeightRate c.val n * ‖B.T (eCoe38 c s (projE38 c s N x)) n‖ ^ 2 =
      (1 / 2 * (cmModeWeight c n * ‖cmCoord Q n‖ ^ 2)) +
        (1 / 2 * (cmModeWeight c n * ‖cmCoord Tl n‖ ^ 2)) := by
    intro n
    rw [B.T_projE38_coord_W07 O c hs1 N x n, cmModeWeight_eq_two_fullWeightRate_W07]
    rw [hQ, hTl, cmCoord_head_W07, cmCoord_tail_W07]
    by_cases hn : n ∈ symmetricModes N
    · simp only [hn, ↓reduceIte, norm_zero]
      ring_nf
    · simp only [hn, ↓reduceIte, norm_zero]
      ring_nf
  have hnn : ∀ n : ℤ, 0 ≤ 1 / 2 * (cmModeWeight c n * ‖cmCoord Q n‖ ^ 2) := fun n => by
    have : 0 ≤ cmModeWeight c n := by
      rw [cmModeWeight_eq_two_fullWeightRate_W07]
      exact mul_nonneg zero_le_two (fullWeightRate_pos38 c n).le
    positivity
  have hnn' : ∀ n : ℤ, 0 ≤ 1 / 2 * (cmModeWeight c n * ‖cmCoord Tl n‖ ^ 2) := fun n => by
    have : 0 ≤ cmModeWeight c n := by
      rw [cmModeWeight_eq_two_fullWeightRate_W07]
      exact mul_nonneg zero_le_two (fullWeightRate_pos38 c n).le
    positivity
  have hs1' : Summable (fun n : ℤ => 1 / 2 * (cmModeWeight c n * ‖cmCoord Q n‖ ^ 2)) :=
    Summable.of_nonneg_of_le hnn (fun n => by have := hpt n; linarith [hnn' n]) hsum'
  have hs2' : Summable (fun n : ℤ => 1 / 2 * (cmModeWeight c n * ‖cmCoord Tl n‖ ^ 2)) :=
    Summable.of_nonneg_of_le hnn' (fun n => by have := hpt n; linarith [hnn n]) hsum'
  have htsum : ∑' n : ℤ, fullWeightRate c.val n *
      ‖B.T (eCoe38 c s (projE38 c s N x)) n‖ ^ 2 = ‖Q‖ ^ 2 / 2 + ‖Tl‖ ^ 2 / 2 := by
    rw [tsum_congr hpt, hs1'.tsum_add hs2', tsum_mul_left, tsum_mul_left, ← actualCM_norm_sq,
      ← actualCM_norm_sq]
    ring
  rw [hid', tsum_congr hΦ', htsum]

/-- **The decomposition `D:eq:fdecomposition`.** For `x ∈ E_s`, `x_N = P_N x`, `y = K(x_N)`,
`v = P_N x` (head point):
`f_N(x) = e^{-R_W(𝓕⁻¹ x_N)} · e^{-A((Id-P_N) y)} · e^{-A(P_N T x_N) + A(x_N)}`, with
`A(h) = ½‖h‖²_H`, `P_N T x_N = v + P_N y`, `A(x_N) = ½‖v‖²`. -/
theorem fN38_decomp (hs' : s < 3 / 4) (hs1 : s ≤ 1) (N : ℕ) (x : FullWeightedHilbert c s) :
    fN38 c s N x =
      Real.exp (-(remainder38 c.val (physOfE38 c s (projE38 c s N x)))) *
        Real.exp (-(‖B.yN38 O c hs1 N x -
          ((cmTrunc c N (B.yN38 O c hs1 N x) : actualCMHead c N) : ActualCM c)‖ ^ 2 / 2)) *
        Real.exp (-(‖(headPt c N (coordE c s x) : ActualCM c) +
          ((cmTrunc c N (B.yN38 O c hs1 N x) : actualCMHead c N) : ActualCM c)‖ ^ 2 -
            ‖(headPt c N (coordE c s x) : ActualCM c)‖ ^ 2) / 2) := by
  unfold fN38
  rw [B.energy_identity_W07 O c hs' hs1 N x, ← Real.exp_add, ← Real.exp_add]
  congr 1
  have := norm_sq_headPt_W07 c N (coordE c s x)
  linarith

/-- `K(P_N x) → K(x)` in `H`. -/
theorem tendsto_yN_W07 (hs1 : s ≤ 1) (x : FullWeightedHilbert c s) :
    Tendsto (fun N : ℕ => B.yN38 O c hs1 N x) atTop (𝓝 (B.KW06_38 O c hs1 x)) := by
  have hK : Continuous (B.KW06_38 O c hs1) :=
    continuousOn_univ.1 (B.analytic_KW06_38 O c hs1).continuousOn
  exact (hK.tendsto x).comp (tendsto_projE38 c s x)

/-- `A((Id - P_N) K(x_N)) → 0`: the omitted high Cameron-Martin energy vanishes
(v2: "the second tends to one because `K(x_N) → K(x)` in `H`"). -/
theorem tendsto_tailEnergy_W07 (hs1 : s ≤ 1) (x : FullWeightedHilbert c s) :
    Tendsto (fun N : ℕ => ‖B.yN38 O c hs1 N x -
      ((cmTrunc c N (B.yN38 O c hs1 N x) : actualCMHead c N) : ActualCM c)‖ ^ 2 / 2)
      atTop (𝓝 0) := by
  set Kinf := B.KW06_38 O c hs1 x with hKinf
  have h1 := B.tendsto_yN_W07 O c hs1 x
  have h2 : Tendsto (fun N : ℕ => ((cmTrunc c N Kinf : actualCMHead c N) : ActualCM c)) atTop
      (𝓝 Kinf) := by
    have := tendsto_starProjection_actualCMHead c Kinf
    refine this.congr (fun N => ?_)
    exact starProjection_actualCMHead c N Kinf
  have h3 : Tendsto (fun N : ℕ => ‖Kinf - ((cmTrunc c N Kinf : actualCMHead c N) : ActualCM c)‖) atTop
      (𝓝 0) := by
    have := (tendsto_const_nhds (x := Kinf)).sub h2
    rw [sub_self] at this
    simpa using this.norm
  have h4 : Tendsto (fun N : ℕ => ‖B.yN38 O c hs1 N x - Kinf‖) atTop (𝓝 0) := by
    have := h1.sub (tendsto_const_nhds (x := Kinf))
    rw [sub_self] at this
    simpa using this.norm
  have hbound : ∀ N : ℕ, ‖B.yN38 O c hs1 N x -
      ((cmTrunc c N (B.yN38 O c hs1 N x) : actualCMHead c N) : ActualCM c)‖ ≤
      2 * ‖B.yN38 O c hs1 N x - Kinf‖ + ‖Kinf - ((cmTrunc c N Kinf : actualCMHead c N) : ActualCM c)‖ := by
    intro N
    set y := B.yN38 O c hs1 N x
    have e : y - ((cmTrunc c N y : actualCMHead c N) : ActualCM c) =
        (y - Kinf) - ((cmTrunc c N (y - Kinf) : actualCMHead c N) : ActualCM c) +
          (Kinf - ((cmTrunc c N Kinf : actualCMHead c N) : ActualCM c)) := by
      rw [map_sub]
      simp only [Submodule.coe_sub]
      abel
    have hn : ‖((cmTrunc c N (y - Kinf) : actualCMHead c N) : ActualCM c)‖ ≤ ‖y - Kinf‖ :=
      norm_cmTrunc_le c N _
    calc _ = ‖(y - Kinf) - ((cmTrunc c N (y - Kinf) : actualCMHead c N) : ActualCM c) +
          (Kinf - ((cmTrunc c N Kinf : actualCMHead c N) : ActualCM c))‖ := by rw [e]
      _ ≤ ‖(y - Kinf) - ((cmTrunc c N (y - Kinf) : actualCMHead c N) : ActualCM c)‖ +
          ‖Kinf - ((cmTrunc c N Kinf : actualCMHead c N) : ActualCM c)‖ := norm_add_le _ _
      _ ≤ (‖y - Kinf‖ + ‖((cmTrunc c N (y - Kinf) : actualCMHead c N) : ActualCM c)‖) +
          ‖Kinf - ((cmTrunc c N Kinf : actualCMHead c N) : ActualCM c)‖ :=
        add_le_add_left (norm_sub_le _ _) _
      _ ≤ _ := by linarith
  have h5 : Tendsto (fun N : ℕ => 2 * ‖B.yN38 O c hs1 N x - Kinf‖ +
      ‖Kinf - ((cmTrunc c N Kinf : actualCMHead c N) : ActualCM c)‖) atTop (𝓝 0) := by
    have := (h4.const_mul 2).add h3
    simpa using this
  have h6 : Tendsto (fun N : ℕ => ‖B.yN38 O c hs1 N x -
      ((cmTrunc c N (B.yN38 O c hs1 N x) : actualCMHead c N) : ActualCM c)‖) atTop (𝓝 0) :=
    squeeze_zero (fun N => norm_nonneg _) hbound h5
  have := (h6.pow 2).div_const 2
  simpa using this

end BirkhoffInput38

end DecompB

end NlsGge.Birkhoff
