import NlsGge.Birkhoff.W07Probability38c

/-! # W07, part d: convergence of the weights in probability (v2 `D:prop:probability`, first claim)

Source: `paper/v2.tex` l.1561-1573. Conditional on `B : BirkhoffInput38`, `O : OneSmoothingInput38 B`,
for `1/2 < s < 3/4` and `c : BoundedCoefficients`.

With `x_N = P_N x`, `y_N = K(x_N)`, `A = ½‖·‖²_H`, the decomposition (part b) reads
`f_N = e^{-R_W(𝓕⁻¹x_N)} · e^{-A((1-P_N)y_N)} · e^{-A(P_N T x_N)+A(x_N)}`, and
`|det L_N| · e^{-A(P_N T x_N)+A(x_N)} = finiteRamerDensity(T_N)(P_N x) → J_T` in probability
(E05, `eq:cylindricalcommon`, i.e. F02's cylindrical convergence). Hence
`f_N · |det L_N| = e^{-R_W(𝓕⁻¹x_N)} · e^{-A((1-P_N)y_N)} · J_N` with
`e^{-R_W(𝓕⁻¹x_N)} → e^{-R_W(𝓕⁻¹x)}` (W05 continuity of `R_W`), `e^{-A((1-P_N)y_N)} → 1`,
`|det L_N| → 1` (F01) and `J_N → J_T` in probability, so `f_N → f_W` in probability
(subsequence-to-almost-sure criterion for a probability measure).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.HierarchyRiccati.Core NlsGge.Ramer NlsGge.Analysis.RegularizedDeterminant
  Filter Topology
open scoped ENNReal Real

namespace BirkhoffInput38

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {lower upper : ℝ}
  (c : BoundedCoefficients lower upper) {s : ℝ}

/-- **F01 for the finite Ramer map:** `|det D T_N(P_N x)| → 1` (v2 `eq:ordinarydet`). -/
theorem tendsto_absDet_W07 (hs1 : s ≤ 1) (x : FullWeightedHilbert c s) :
    Tendsto (fun N : ℕ =>
      |(fderiv ℝ (B.TNfin38 O c hs1 N) (headPt c N (coordE c s x))).det|) atTop (𝓝 1) := by
  have h := B.tendsto_sq_detLN O (eToSob38 c s ((1 : ℕ) : ℝ) x)
  have h2 := (Real.continuous_sqrt.tendsto 1).comp h
  rw [Real.sqrt_one] at h2
  refine h2.congr (fun N => ?_)
  rw [Function.comp_apply, B.det_TNfin_eq_detLN_W07 O c hs1 N x]
  exact Real.sqrt_sq (abs_nonneg _)

include B O in
/-- **W05:** the remainder factor converges pointwise (`R_W` is continuous on `𝓕⁻¹ E_s`,
and `P_N x → x` in `E_s`). -/
theorem tendsto_remainder_W07 (hs' : s < 3 / 4) (x : FullWeightedHilbert c s) :
    Tendsto (fun N : ℕ => remainder38 c.val (physOfE38 c s (projE38 c s N x))) atTop
      (𝓝 (remainder38 c.val (physOfE38 c s x))) :=
  ((B.continuous_remainder_physOfE38 c s O hs').tendsto x).comp (tendsto_projE38 c s x)

/-- W06 with the cylindrical convergence retained (the 7th conjunct of E05's Ramer theorem). -/
theorem ramer_W06_cyl_38 (hs : (1 : ℝ) / 2 < s) (hs1 : s ≤ 1) :
    ∃ δK : (ℤ → ℂ) → ℝ, RamerDivergence38 c s (B.KW06_38 O c hs1) δK ∧
      (fullWeightedSequenceGaussian c s).map (TW06_38 B O c s).symm =
        (fullWeightedSequenceGaussian c s).withDensity
          (fun x => ENNReal.ofReal (JW06_38 c s hs (B.KW06_38 O c hs1) δK x)) ∧
      (∀ x, 0 < JW06_38 c s hs (B.KW06_38 O c hs1) δK x) ∧
      Integrable (JW06_38 c s hs (B.KW06_38 O c hs1) δK) (fullWeightedSequenceGaussian c s) ∧
      ∫ x, JW06_38 c s hs (B.KW06_38 O c hs1) δK x ∂(fullWeightedSequenceGaussian c s) = 1 ∧
      TendstoInMeasure (fullWeightSequenceGaussian c.val)
        (fun N z => finiteRamerDensity (fun v => v + truncField c s (B.KW06_38 O c hs1) N v)
          (headPt c N z))
        atTop (fun z => JW06_38 c s hs (B.KW06_38 O c hs1) δK (fullWeightedSequenceRealization c s z)) := by
  obtain ⟨δK, h2, h3, hmap, hpos, hint, hone, hconv⟩ :=
    NlsGge.Ramer.ramer_eq_Ramercommon c s hs (TW06_38 B O c s) (B.KW06_38 O c hs1)
      (B.KinvW06_38 O c hs1) (fun x => B.hT_W06_38 O c hs hs1 x)
      (fun y => B.hTs_W06_38 O c hs hs1 y) (B.analytic_KW06_38 O c hs1)
      (B.analytic_KinvW06_38 O c hs1)
  exact ⟨δK, ⟨h2, h3⟩, hmap, hpos, hint, hone, hconv⟩

/-- The Ramer density of the finite map, in exponential form. -/
theorem finiteRamerDensity_TNfin_W07 (hs1 : s ≤ 1) (N : ℕ) (x : FullWeightedHilbert c s) :
    finiteRamerDensity (fun v => v + truncField c s (B.KW06_38 O c hs1) N v)
        (headPt c N (coordE c s x)) =
      |(fderiv ℝ (B.TNfin38 O c hs1 N) (headPt c N (coordE c s x))).det| *
        Real.exp (-(‖(headPt c N (coordE c s x) : ActualCM c) +
          ((cmTrunc c N (B.yN38 O c hs1 N x) : actualCMHead c N) : ActualCM c)‖ ^ 2 -
            ‖(headPt c N (coordE c s x) : ActualCM c)‖ ^ 2) / 2) := by
  have e : truncField c s (B.KW06_38 O c hs1) N (headPt c N (coordE c s x)) =
      cmTrunc c N (B.yN38 O c hs1 N x) := by
    unfold truncField yN38
    rw [headToE_headPt_projE38_W07]
  have hnorm : ‖(headPt c N (coordE c s x) +
      truncField c s (B.KW06_38 O c hs1) N (headPt c N (coordE c s x)) : actualCMHead c N)‖ =
      ‖(headPt c N (coordE c s x) : ActualCM c) +
        ((cmTrunc c N (B.yN38 O c hs1 N x) : actualCMHead c N) : ActualCM c)‖ := by
    rw [e]; rfl
  have hn2 : ‖(headPt c N (coordE c s x) : actualCMHead c N)‖ =
      ‖(headPt c N (coordE c s x) : ActualCM c)‖ := rfl
  unfold finiteRamerDensity
  show |(fderiv ℝ (B.TNfin38 O c hs1 N) (headPt c N (coordE c s x))).det| *
      Real.exp (-(‖(headPt c N (coordE c s x) +
      truncField c s (B.KW06_38 O c hs1) N (headPt c N (coordE c s x)) : actualCMHead c N)‖ ^ 2 -
        ‖(headPt c N (coordE c s x) : actualCMHead c N)‖ ^ 2) / 2) = _
  rw [hnorm, hn2]

/-- **The exact identity** `f_N · |det L_N| = e^{-R_N} · e^{-tail_N} · J_N`. -/
theorem fN38_mul_det_W07 (hs' : s < 3 / 4) (hs1 : s ≤ 1) (N : ℕ) (x : FullWeightedHilbert c s) :
    fN38 c s N x *
        |(fderiv ℝ (B.TNfin38 O c hs1 N) (headPt c N (coordE c s x))).det| =
      Real.exp (-(remainder38 c.val (physOfE38 c s (projE38 c s N x)))) *
        Real.exp (-(‖B.yN38 O c hs1 N x -
          ((cmTrunc c N (B.yN38 O c hs1 N x) : actualCMHead c N) : ActualCM c)‖ ^ 2 / 2)) *
        finiteRamerDensity (fun v => v + truncField c s (B.KW06_38 O c hs1) N v)
          (headPt c N (coordE c s x)) := by
  rw [B.finiteRamerDensity_TNfin_W07 O c hs1 N x, B.fN38_decomp O c hs' hs1 N x]
  ring

/-- Pointwise limit along a subsequence: if the finite Ramer densities converge at `x`, so do the
weights `f_N(x)` (to `e^{-R_W(𝓕⁻¹x)} · lim J_N`). -/
theorem tendsto_fN_of_tendsto_J_W07 (hs' : s < 3 / 4) (hs1 : s ≤ 1) (x : FullWeightedHilbert c s)
    (ns : ℕ → ℕ) (hns : StrictMono ns) (Jlim : ℝ)
    (hJ : Tendsto (fun k => finiteRamerDensity
      (fun v => v + truncField c s (B.KW06_38 O c hs1) (ns k) v)
        (headPt c (ns k) (coordE c s x))) atTop (𝓝 Jlim)) :
    Tendsto (fun k => fN38 c s (ns k) x) atTop
      (𝓝 (Real.exp (-(remainder38 c.val (physOfE38 c s x))) * Jlim)) := by
  have hα := ((B.tendsto_remainder_W07 O c hs' x).comp hns.tendsto_atTop)
  have hβ := ((B.tendsto_tailEnergy_W07 O c hs1 x).comp hns.tendsto_atTop)
  have hD := ((B.tendsto_absDet_W07 O c hs1 x).comp hns.tendsto_atTop)
  have hα' : Tendsto (fun k => Real.exp (-(remainder38 c.val
      (physOfE38 c s (projE38 c s (ns k) x))))) atTop
      (𝓝 (Real.exp (-(remainder38 c.val (physOfE38 c s x))))) :=
    (Real.continuous_exp.tendsto _).comp hα.neg
  have hβ' : Tendsto (fun k => Real.exp (-(‖B.yN38 O c hs1 (ns k) x -
      ((cmTrunc c (ns k) (B.yN38 O c hs1 (ns k) x) : actualCMHead c (ns k)) : ActualCM c)‖ ^ 2 /
        2))) atTop (𝓝 1) := by
    have h0 := hβ.neg
    rw [neg_zero] at h0
    have := (Real.continuous_exp.tendsto 0).comp h0
    rw [Real.exp_zero] at this
    exact this
  have hnum := (hα'.mul hβ').mul hJ
  have hq := hnum.div hD one_ne_zero
  simp only [mul_one, div_one] at hq
  refine hq.congr' ?_
  have hev : ∀ᶠ k in atTop, |(fderiv ℝ (B.TNfin38 O c hs1 (ns k))
      (headPt c (ns k) (coordE c s x))).det| ≠ 0 :=
    hD.eventually_ne one_ne_zero
  filter_upwards [hev] with k hk
  have := B.fN38_mul_det_W07 O c hs' hs1 (ns k) x
  simp only [Pi.div_apply, Function.comp_apply]
  rw [← this]
  field_simp

/-- **Convergence of the bare weights in probability** (v2 `eq:probability`, first part), given the
cylindrical convergence of the Ramer densities. -/
theorem tendstoInMeasure_fN_W07 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) (hs1 : s ≤ 1)
    (δK : (ℤ → ℂ) → ℝ)
    (hconv : TendstoInMeasure (fullWeightSequenceGaussian c.val)
      (fun N z => finiteRamerDensity (fun v => v + truncField c s (B.KW06_38 O c hs1) N v)
        (headPt c N z))
      atTop (fun z => JW06_38 c s hs (B.KW06_38 O c hs1) δK
        (fullWeightedSequenceRealization c s z))) :
    TendstoInMeasure (fullWeightedSequenceGaussian c s) (fun N x => fN38 c s N x) atTop
      (fW06_38 c s hs (B.KW06_38 O c hs1) δK) := by
  have hE := tendstoInMeasure_comp_coordE c s hs hconv
  have hR : ∀ x : FullWeightedHilbert c s,
      JW06_38 c s hs (B.KW06_38 O c hs1) δK (fullWeightedSequenceRealization c s (coordE c s x)) =
        JW06_38 c s hs (B.KW06_38 O c hs1) δK x := fun x => by rw [realization_coordE]
  simp only [hR] at hE
  have hmeas : ∀ N, AEStronglyMeasurable (fun x => fN38 c s N x) (fullWeightedSequenceGaussian c s) :=
    fun N => by
      have : (fun x => fN38 c s N x) = fun x => fNseq38 c N (coordE c s x) :=
        funext (fN38_eq_fNseq c s N)
      rw [this]
      exact ((measurable_fNseq38 c N).comp (measurable_coordE c s)).aestronglyMeasurable
  rw [exists_seq_tendstoInMeasure_atTop_iff hmeas]
  intro ns hns
  obtain ⟨ns', hns', hae⟩ := (hE.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ns', hns', ?_⟩
  filter_upwards [hae] with x hx
  have hmono : StrictMono (ns ∘ ns') := hns.comp hns'
  have := B.tendsto_fN_of_tendsto_J_W07 O c hs' hs1 x (ns ∘ ns') hmono _ hx
  exact this

end BirkhoffInput38

end NlsGge.Birkhoff
