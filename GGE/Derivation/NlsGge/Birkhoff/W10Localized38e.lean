import NlsGge.Birkhoff.W10Localized38d

/-! # W10b, file 1 (W10.05): the Galerkin branch identifies the preimage `(φ_N|_{U_N})⁻¹(P_N z)`

Source: `paper/v2.tex` l.1657-1661: "Lemma `D:lem:localinverse` supplies a branch converging in `E_s` to
`x = T⁻¹z`. If any other preimage lies in the support of `χ_R`, it eventually agrees with this branch by
injectivity on a larger fixed ball. When the limiting cutoff is zero, the same argument and continuity show
that the transformed integrand tends to zero." Conditional on `B`, `O` (W08, W09).

* `galerkin_iff_TNfin38`: for `v ∈ V_N`, `v + P_N K(v) = P_N z` iff `v` is a Galerkin solution (W09).
* `unique_preimage_W10`: every `w ∈ U_N(R')` with `φ_N(w) = P_N z` equals the W09 branch `x_N`
  (for `N` large, from the uniqueness part of W09 on a ball of radius `R'' ≥ R'`).
* `tendsto_PsiN38`: for every `z ∈ E_s`, `Ψ_N(P_N z) → F(𝓕⁻¹x) χ_R(𝓕⁻¹x) e^{-R_W(𝓕⁻¹x)}`, `x = T⁻¹z`
  (including the case `‖x‖_{h²} ≥ 2R`, where the limit is `0`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.Ramer Filter Topology
open scoped ENNReal Real

section Tail

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper)

/-- If `y_N → y` in `H`, the omitted high Cameron-Martin energy `‖y_N - P_N y_N‖²/2 → 0`
(v2: "the tail Cameron-Martin energy tends to zero"). -/
theorem tendsto_tail_of_tendsto38 (yN : ℕ → ActualCM c) (Kinf : ActualCM c)
    (h1 : Tendsto yN atTop (𝓝 Kinf)) :
    Tendsto (fun N : ℕ => ‖yN N - ((cmTrunc c N (yN N) : actualCMHead c N) : ActualCM c)‖ ^ 2 / 2)
      atTop (𝓝 0) := by
  have h2 : Tendsto (fun N : ℕ => ((cmTrunc c N Kinf : actualCMHead c N) : ActualCM c)) atTop
      (𝓝 Kinf) := by
    have := tendsto_starProjection_actualCMHead c Kinf
    refine this.congr (fun N => ?_)
    exact starProjection_actualCMHead c N Kinf
  have h3 : Tendsto (fun N : ℕ => ‖Kinf - ((cmTrunc c N Kinf : actualCMHead c N) : ActualCM c)‖)
      atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := Kinf)).sub h2
    rw [sub_self] at this
    simpa using this.norm
  have h4 : Tendsto (fun N : ℕ => ‖yN N - Kinf‖) atTop (𝓝 0) := by
    have := h1.sub (tendsto_const_nhds (x := Kinf))
    rw [sub_self] at this
    simpa using this.norm
  have hbound : ∀ N : ℕ, ‖yN N - ((cmTrunc c N (yN N) : actualCMHead c N) : ActualCM c)‖ ≤
      2 * ‖yN N - Kinf‖ + ‖Kinf - ((cmTrunc c N Kinf : actualCMHead c N) : ActualCM c)‖ := by
    intro N
    set y := yN N
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
  have h5 : Tendsto (fun N : ℕ => 2 * ‖yN N - Kinf‖ +
      ‖Kinf - ((cmTrunc c N Kinf : actualCMHead c N) : ActualCM c)‖) atTop (𝓝 0) := by
    have := (h4.const_mul 2).add h3
    simpa using this
  have h6 : Tendsto (fun N : ℕ => ‖yN N - ((cmTrunc c N (yN N) : actualCMHead c N) : ActualCM c)‖)
      atTop (𝓝 0) :=
    squeeze_zero (fun N => norm_nonneg _) hbound h5
  have := (h6.pow 2).div_const 2
  simpa using this

end Tail

namespace BirkhoffInput38

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {lower upper : ℝ}
  (c : BoundedCoefficients lower upper) {s : ℝ}

theorem headToE_headPt_self38 (N : ℕ) (y : FullWeightedHilbert c s)
    (hy : ∀ n, n ∉ symmetricModes N → eCoe38 c s y n = 0) :
    headToE c s N (headPt c N (coordE c s y)) = y := by
  apply fullWeighted_ext
  intro n
  rw [headToE_coord, cmCoord_headPt]
  by_cases hn : n ∈ symmetricModes N
  · simp only [hn, ↓reduceIte]; rfl
  · simp only [hn, ↓reduceIte]; exact (hy n hn).symm

theorem cmCoord_TNfin38 (hs1 : s ≤ 1) (N : ℕ) (v : actualCMHead c N) (n : ℤ) :
    cmCoord ((B.TNfin38 O c hs1 N v : actualCMHead c N) : ActualCM c) n =
      cmCoord (v : ActualCM c) n +
        (if n ∈ symmetricModes N then
          B.T (eCoe38 c s (headToE c s N v)) n - eCoe38 c s (headToE c s N v) n else 0) := by
  have e1 : cmCoord ((B.TNfin38 O c hs1 N v : actualCMHead c N) : ActualCM c) n =
      cmCoord (v : ActualCM c) n +
        cmCoord ((cmTrunc c N (B.KW06_38 O c hs1 (headToE c s N v)) : actualCMHead c N) :
          ActualCM c) n := rfl
  have hK : cmCoord (B.KW06_38 O c hs1 (headToE c s N v)) n =
      B.T (eCoe38 c s (headToE c s N v)) n - eCoe38 c s (headToE c s N v) n :=
    B.cmCoord_KW06_38 O c hs1 (headToE c s N v) n
  rw [e1, cmCoord_cmTrunc]
  by_cases hn : n ∈ symmetricModes N
  · simp only [hn, ↓reduceIte]
    rw [hK]
  · simp only [hn, ↓reduceIte]

/-- For `v ∈ V_N`: `v` is a Galerkin solution of `P_N T(y) = P_N z` iff `φ_N(v) = P_N z`. -/
theorem galerkin_iff_TNfin38 (hs1 : s ≤ 1) (N : ℕ) (z : FullWeightedHilbert c s)
    (v : actualCMHead c N) :
    B.GalerkinSol38 N (eCoe38 c s z) (eCoe38 c s (headToE c s N v)) ↔
      B.TNfin38 O c hs1 N v = headPt c N (coordE c s z) := by
  have hv : ∀ n, n ∉ symmetricModes N → eCoe38 c s (headToE c s N v) n = 0 :=
    fun n hn => v.2 n hn
  constructor
  · rintro ⟨-, hT⟩
    apply Subtype.ext
    apply cmCoord_ext
    intro n
    rw [B.cmCoord_TNfin38 O c hs1 N v n]
    show _ = cmCoord ((headPt c N (coordE c s z) : actualCMHead c N) : ActualCM c) n
    rw [cmCoord_headPt]
    by_cases hn : n ∈ symmetricModes N
    · simp only [hn, ↓reduceIte]
      have := hT n hn
      have e : cmCoord (v : ActualCM c) n = eCoe38 c s (headToE c s N v) n := rfl
      have e2 : coordE c s z n = eCoe38 c s z n := rfl
      rw [e, this, e2]
      ring
    · simp only [hn, ↓reduceIte]
      rw [v.2 n hn]; simp
  · intro h
    refine ⟨hv, fun n hn => ?_⟩
    have this : cmCoord ((B.TNfin38 O c hs1 N v : actualCMHead c N) : ActualCM c) n =
        cmCoord ((headPt c N (coordE c s z) : actualCMHead c N) : ActualCM c) n :=
      congrArg (fun w : actualCMHead c N => cmCoord (w : ActualCM c) n) h
    rw [B.cmCoord_TNfin38 O c hs1 N v n, cmCoord_headPt] at this
    simp only [hn, ↓reduceIte] at this
    have e : cmCoord (v : ActualCM c) n = eCoe38 c s (headToE c s N v) n := rfl
    rw [e] at this
    have e2 : coordE c s z n = eCoe38 c s z n := rfl
    rw [e2] at this
    linear_combination this

/-- **W10.05 (uniqueness).** If `w ∈ U_N(R')` solves `φ_N(w) = P_N z`, then `w` is the head point of the
W09 branch `x_N`, provided `N` is past the W09 uniqueness threshold for a radius `R'' ≥ R'`. -/
theorem unique_preimage_W10 (hs1 : s ≤ 1) (z : FullWeightedHilbert c s)
    (xN : ℕ → FullWeightedHilbert c s) (R' R'' : ℝ) (hle : R' ≤ R'') (N₀ : ℕ)
    (huniq : ∀ N ≥ N₀, ∀ y : H2_38, ‖y‖ ≤ R'' →
      B.GalerkinSol38 N (eCoe38 c s z) (carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y) →
      carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y = eCoe38 c s (xN N))
    (N : ℕ) (hN : N ≥ N₀) (hsol : B.GalerkinSol38 N (eCoe38 c s z) (eCoe38 c s (xN N)))
    (w : actualCMHead c N) (hw : w ∈ ballU38 c s N R')
    (hφ : B.TNfin38 O c hs1 N w = headPt c N (coordE c s z)) :
    w = headPt c N (coordE c s (xN N)) := by
  have hG := (B.galerkin_iff_TNfin38 O c hs1 N z w).2 hφ
  have hy : ‖eToSob38 c s (((1 + 1 : ℕ)) : ℝ) (headToE c s N w)‖ ≤ R'' :=
    (le_of_lt hw).trans hle
  have hcoe : carrierCoe38 (((1 + 1 : ℕ)) : ℝ) (eToSob38 c s (((1 + 1 : ℕ)) : ℝ) (headToE c s N w)) =
      eCoe38 c s (headToE c s N w) := carrierCoe_eToSob38 c s _ _
  have h1 := huniq N hN _ hy (by rw [hcoe]; exact hG)
  rw [hcoe] at h1
  apply Subtype.ext
  apply cmCoord_ext
  intro n
  show cmCoord (w : ActualCM c) n = cmCoord ((headPt c N (coordE c s (xN N)) : actualCMHead c N) :
    ActualCM c) n
  rw [cmCoord_headPt]
  have e : cmCoord (w : ActualCM c) n = eCoe38 c s (headToE c s N w) n := rfl
  rw [e, h1]
  by_cases hn : n ∈ symmetricModes N
  · simp only [hn, ↓reduceIte]; rfl
  · simp only [hn, ↓reduceIte]; exact hsol.1 n hn

/-- **W10.05 + W10.06 (pointwise convergence of the transformed integrand).** For every `z ∈ E_s`, with
`x = T⁻¹z`: `Ψ_N(P_N z) → F(𝓕⁻¹x) χ_R(𝓕⁻¹x) e^{-R_W(𝓕⁻¹x)}`. -/
theorem tendsto_PsiN38 (hs' : s < 3 / 4) (hs1 : s ≤ 1) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y))) (M : ℝ)
    (hM : ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) (z : ECarrier38 c s) :
    Tendsto (fun N : ℕ => B.PsiN38 O c hs1 χ R F N (headPt c N (coordE c s z))) atTop
      (𝓝 (F (physOfE38 c s ((B.weightedHomeoE38 O c s).symm z)) *
        chiR38 χ R (physOfE38 c s ((B.weightedHomeoE38 O c s).symm z)) *
        Real.exp (-(remainder38 c.val (physOfE38 c s ((B.weightedHomeoE38 O c s).symm z)))))) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  obtain ⟨xN, hlim, hsol, huniq⟩ := B.W09_localGalerkinInverse_ball O c s z
  set x := (B.weightedHomeoE38 O c s).symm z with hx
  set ρ : ℝ := ‖eToSob38 c s (((1 + 1 : ℕ)) : ℝ) x‖ with hρ
  set R'' : ℝ := max (2 * R + 1) (ρ + 1) with hR''
  obtain ⟨N₀, hN₀⟩ := huniq R'' (lt_of_lt_of_le (by linarith) (le_max_right _ _))
  obtain ⟨N₁, hN₁⟩ := B.eventually_injOn_ballU38 O c hs1 (2 * R + 1)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (B.eventually_det_ballU38 O c hs1 (2 * R + 1)).1
  have hbig : ∀ᶠ N : ℕ in atTop, max (max N₀ N₁) N₂ ≤ N := eventually_ge_atTop _
  -- the basic eventual facts
  have hbase : ∀ᶠ N : ℕ in atTop, N₀ ≤ N ∧ B.GalerkinSol38 N (eCoe38 c s z) (eCoe38 c s (xN N)) ∧
      Set.InjOn (B.TNfin38 O c hs1 N) (ballU38 c s N (2 * R + 1)) ∧
      (∀ v ∈ ballU38 c s N (2 * R + 1),
        (fderiv ℝ (B.TNfin38 O c hs1 N) v).det ≠ 0 ∧
          |(fderiv ℝ (B.TNfin38 O c hs1 N) v).det|⁻¹ ≤ 2) := by
    filter_upwards [hbig, hsol] with N hN hs
    exact ⟨le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN, hs,
      hN₁ N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN),
      hN₂ N (le_trans (le_max_right _ _) hN)⟩
  have hvN : ∀ N : ℕ, B.GalerkinSol38 N (eCoe38 c s z) (eCoe38 c s (xN N)) →
      headToE c s N (headPt c N (coordE c s (xN N))) = xN N :=
    fun N hs => headToE_headPt_self38 c N (xN N) hs.1
  have hφv : ∀ N : ℕ, B.GalerkinSol38 N (eCoe38 c s z) (eCoe38 c s (xN N)) →
      B.TNfin38 O c hs1 N (headPt c N (coordE c s (xN N))) = headPt c N (coordE c s z) := by
    intro N hs
    refine (B.galerkin_iff_TNfin38 O c hs1 N z _).1 ?_
    rw [hvN N hs]; exact hs
  have hxNto : Tendsto (fun N => eToSob38 c s (((1 + 1 : ℕ)) : ℝ) (xN N)) atTop
      (𝓝 (eToSob38 c s (((1 + 1 : ℕ)) : ℝ) x)) :=
    ((continuous_eToSob38 c s _).tendsto x).comp hlim
  have hnorm : Tendsto (fun N => ‖eToSob38 c s (((1 + 1 : ℕ)) : ℝ) (xN N)‖) atTop (𝓝 ρ) :=
    hxNto.norm
  have hchi : Tendsto (fun N => chiR38 χ R (physOfE38 c s (xN N))) atTop
      (𝓝 (chiR38 χ R (physOfE38 c s x))) :=
    ((continuous_chiR38_physOfE38 c s hχ hR).tendsto x).comp hlim
  by_cases hρ2 : ρ < 2 * R + 1
  · -- the branch lies in the ball: the transformed integrand is `Hv/|det|` at the branch
    have hin : ∀ᶠ N : ℕ in atTop, ‖eToSob38 c s (((1 + 1 : ℕ)) : ℝ) (xN N)‖ < 2 * R + 1 :=
      hnorm.eventually_lt_const hρ2
    have hU : ∀ᶠ N : ℕ in atTop, headPt c N (coordE c s (xN N)) ∈ ballU38 c s N (2 * R + 1) ∧
        B.GalerkinSol38 N (eCoe38 c s z) (eCoe38 c s (xN N)) ∧
        Set.InjOn (B.TNfin38 O c hs1 N) (ballU38 c s N (2 * R + 1)) := by
      filter_upwards [hin, hbase] with N h1 h2
      refine ⟨?_, h2.2.1, h2.2.2.1⟩
      show hn2V38 c s N _ < _
      unfold hn2V38
      rw [hvN N h2.2.1]; exact h1
    have hval : ∀ᶠ N : ℕ in atTop,
        B.PsiN38 O c hs1 χ R F N (headPt c N (coordE c s z)) =
          B.Hv38 O c hs1 χ R F N (headPt c N (coordE c s (xN N))) /
            |(fderiv ℝ (B.TNfin38 O c hs1 N) (headPt c N (coordE c s (xN N)))).det| := by
      filter_upwards [hU] with N ⟨h1, h2, h3⟩
      unfold PsiN38
      rw [← hφv N h2, localPush38_apply _ _ h3 _ _ h1]
    -- convergence of the numerator
    have hKc : Continuous (B.KW06_38 O c hs1) :=
      continuousOn_univ.1 (B.analytic_KW06_38 O c hs1).continuousOn
    have hKto : Tendsto (fun N => B.KW06_38 O c hs1 (xN N)) atTop (𝓝 (B.KW06_38 O c hs1 x)) :=
      (hKc.tendsto x).comp hlim
    have htail := tendsto_tail_of_tendsto38 c _ _ hKto
    have hFt : Tendsto (fun N => F (physOfE38 c s (xN N))) atTop (𝓝 (F (physOfE38 c s x))) :=
      (hF.tendsto x).comp hlim
    have hrem : Tendsto (fun N => remainder38 c.val (physOfE38 c s (xN N))) atTop
        (𝓝 (remainder38 c.val (physOfE38 c s x))) :=
      ((B.continuous_remainder_physOfE38 c s O hs').tendsto x).comp hlim
    have hnum : Tendsto (fun N => B.Hv38 O c hs1 χ R F N (headPt c N (coordE c s (xN N)))) atTop
        (𝓝 (F (physOfE38 c s x) * chiR38 χ R (physOfE38 c s x) *
          Real.exp (-(remainder38 c.val (physOfE38 c s x))))) := by
      have hlimit : Tendsto (fun N => F (physOfE38 c s (xN N)) * chiR38 χ R (physOfE38 c s (xN N)) *
          Real.exp (-(remainder38 c.val (physOfE38 c s (xN N)))) *
          Real.exp (-(‖B.KW06_38 O c hs1 (xN N) - ((cmTrunc c N (B.KW06_38 O c hs1 (xN N)) :
            actualCMHead c N) : ActualCM c)‖ ^ 2 / 2))) atTop
          (𝓝 (F (physOfE38 c s x) * chiR38 χ R (physOfE38 c s x) *
            Real.exp (-(remainder38 c.val (physOfE38 c s x))) * Real.exp (-0))) :=
        ((hFt.mul hchi).mul (hrem.neg.rexp)).mul (htail.neg.rexp)
      rw [neg_zero, Real.exp_zero, mul_one] at hlimit
      refine hlimit.congr' ?_
      filter_upwards [hsol] with N hs
      unfold Hv38
      rw [hvN N hs]
    -- convergence of the Jacobian
    have hdet : Tendsto (fun N => |(fderiv ℝ (B.TNfin38 O c hs1 N)
        (headPt c N (coordE c s (xN N)))).det|) atTop (𝓝 1) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hd := (B.eventually_det_ballU38 O c hs1 (2 * R + 1)).2 ε hε
      filter_upwards [hd, hU] with N h1 h2
      rw [Real.dist_eq]
      exact h1 _ h2.1
    have hq := hnum.div hdet one_ne_zero
    rw [div_one] at hq
    exact hq.congr' (by filter_upwards [hval] with N h; exact h.symm)
  · -- the branch leaves the support of the cutoff: the transformed integrand tends to zero
    have hρ' : 2 * R ≤ ρ := by linarith [not_lt.1 hρ2]
    have hzero : chiR38 χ R (physOfE38 c s x) = 0 :=
      chiR38_physOfE38_eq_zero c s hχ hR x hρ'
    rw [hzero, mul_zero, zero_mul]
    have hbound : ∀ᶠ N : ℕ in atTop,
        ‖B.PsiN38 O c hs1 χ R F N (headPt c N (coordE c s z))‖ ≤
          2 * M * chiR38 χ R (physOfE38 c s (xN N)) := by
      filter_upwards [hbase] with N ⟨hN0, hs, hinj, hdet⟩
      have hc0 : 0 ≤ chiR38 χ R (physOfE38 c s (xN N)) :=
        (chiR38_mem_Icc hχ hR _).1
      by_cases hz : headPt c N (coordE c s z) ∈
          B.TNfin38 O c hs1 N '' ballU38 c s N (2 * R + 1)
      · obtain ⟨w, hw, hwφ⟩ := hz
        have hwv := B.unique_preimage_W10 O c hs1 z xN (2 * R + 1) R'' (le_max_left _ _) N₀ hN₀
          N hN0 hs w hw hwφ
        unfold PsiN38
        rw [← hwφ, localPush38_apply _ _ hinj _ w hw, Real.norm_eq_abs, abs_div, abs_abs]
        obtain ⟨hd0, hd2⟩ := hdet w hw
        have hpos : 0 < |(fderiv ℝ (B.TNfin38 O c hs1 N) w).det| := abs_pos.2 hd0
        rw [div_le_iff₀ hpos]
        have h1 := B.abs_Hv38_le_chi O c hs' hs1 hχ hR F M hM N w
        have e : headToE c s N w = xN N := by rw [hwv]; exact hvN N hs
        rw [e] at h1
        have h2 : 1 ≤ 2 * |(fderiv ℝ (B.TNfin38 O c hs1 N) w).det| := by
          have := mul_le_mul_of_nonneg_left hd2 hpos.le
          rw [mul_inv_cancel₀ hpos.ne'] at this
          linarith
        have h3 : 0 ≤ M * chiR38 χ R (physOfE38 c s (xN N)) := mul_nonneg hM0 hc0
        nlinarith
      · unfold PsiN38
        rw [localPush38_eq_zero _ _ _ _ hz, norm_zero]
        exact mul_nonneg (mul_nonneg zero_le_two hM0) hc0
    have hlim0 : Tendsto (fun N => 2 * M * chiR38 χ R (physOfE38 c s (xN N))) atTop (𝓝 0) := by
      have := hchi.const_mul (2 * M)
      rw [hzero, mul_zero] at this
      exact this
    exact squeeze_zero_norm' hbound hlim0

end BirkhoffInput38

end NlsGge.Birkhoff
end
