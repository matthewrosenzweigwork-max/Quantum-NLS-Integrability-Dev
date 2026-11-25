import NlsGge.Birkhoff.W09Approx38

/-! # W09 (Birkhoff wave C3), file 2: convergent local Galerkin inverse branches (conditional)

Claim `W09` (`D:lem:localinverse`, v2 l.1616-1633), blueprint `blueprint/claims/W09.md`.
Conditional on `(B : BirkhoffInput38) (O : OneSmoothingInput38 B)`.

Setting: `c : BoundedCoefficients lower upper`, `s : ℝ`, `E_s = ECarrier38 c s`,
`T = weightedHomeoE38 B O c s` (W04), `K = T - Id : E_s → E_{s-1}`.
`GalerkinSol38 B N ζ y` says `y ∈ P_N h⁰` (finite support in `|n| ≤ N`) and `P_N T(y) = P_N ζ`
(coefficientwise for `|n| ≤ N`).

* `exists_galerkin_branch38`: existence of `x_N ∈ P_N E_s` with `P_N T x_N = P_N z` and
  `x_N → T⁻¹ z` in `E_s` (W09.01-W09.05).
* `galerkinSol_unique_W09`: uniqueness in a fixed `h²` ball (W09.06, from W08 `injOn_TN_ballV38`).
* `W09_localGalerkinInverse`: the combined statement of `D:lem:localinverse`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Composition NlsGge.SpectralFoundations
open Filter Topology Metric

/-- The embedding `E_s ↪ h^r` (every `E_s` embeds in every `h^r`, W04.01). -/
def eToSob38 {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s r : ℝ) :
    ECarrier38 c s → SobolevCarrier38 r :=
  fun y => carrierMk38 r (eCoe38 c s y) (seqE38_subset_seqSobolev38 c s r (eCoe38_mem c s y))

theorem carrierCoe_eToSob38 {lower upper : ℝ} (c : BoundedCoefficients lower upper)
    (s r : ℝ) (y : ECarrier38 c s) :
    carrierCoe38 r (eToSob38 c s r y) = eCoe38 c s y :=
  carrierCoe38_mk r _ _

theorem continuous_eToSob38 {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s r : ℝ) :
    Continuous (eToSob38 c s r) :=
  (continuous_toCarrier38 r).comp (fullWeightedToSobolev c s r).continuous

namespace BirkhoffInput38

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {lower upper : ℝ}
  (c : BoundedCoefficients lower upper) (s : ℝ)

/-- `K = T - Id : E_s → E_{s-1}` (W04), as a map of the carrier `E_s`:
`K_E = ι ∘ K'` with `ι : E_{s-1} ↪ E_s`.  This is the factorization through `E_{s-1}` of v2. -/
def KE38 : ECarrier38 c s → ECarrier38 c s :=
  fun y => eInclCLM38 c (by linarith : s - 1 ≤ s)
    (eMap38 c s (s - 1) (fun z => B.T z - z) (B.K_mem_E38 O c s) y)

theorem eCoe_KE38 (y : ECarrier38 c s) (n : ℤ) :
    eCoe38 c s (B.KE38 O c s y) n = B.T (eCoe38 c s y) n - eCoe38 c s y n := by
  unfold KE38
  rw [eCoe38_eInclCLM38, eCoe38_eMap38]
  rfl

theorem analytic_KE38 : AnalyticOnNhd ℝ (B.KE38 O c s) Set.univ :=
  ((eInclCLM38 c (by linarith : s - 1 ≤ s)).analyticOnNhd _).comp (B.analytic_K_E38 O c s)
    (fun _ _ => Set.mem_univ _)

theorem differentiableAt_KE38 (y : ECarrier38 c s) : DifferentiableAt ℝ (B.KE38 O c s) y :=
  (B.analytic_KE38 O c s y trivial).differentiableAt

theorem continuousAt_fderiv_KE38 (y : ECarrier38 c s) :
    ContinuousAt (fun z => fderiv ℝ (B.KE38 O c s) z) y := by
  have hcd : ContDiff ℝ 1 (B.KE38 O c s) :=
    contDiff_iff_contDiffAt.2 (fun x => (B.analytic_KE38 O c s x trivial).contDiffAt)
  exact (hcd.continuous_fderiv one_ne_zero).continuousAt

theorem fderiv_KE38 (y : ECarrier38 c s) :
    fderiv ℝ (B.KE38 O c s) y = (eInclCLM38 c (by linarith : s - 1 ≤ s)).comp
      (fderiv ℝ (eMap38 c s (s - 1) (fun z => B.T z - z) (B.K_mem_E38 O c s)) y) := by
  have hd : DifferentiableAt ℝ (eMap38 c s (s - 1) (fun z => B.T z - z) (B.K_mem_E38 O c s)) y :=
    (B.analytic_K_E38 O c s y trivial).differentiableAt
  exact ((eInclCLM38 c (by linarith : s - 1 ≤ s)).hasFDerivAt.comp y hd.hasFDerivAt).fderiv

/-- **W09.01-W09.02.**  `‖DK(x) - P_N DK(x)‖ → 0` in operator norm on `E_s`: `DK(x)` factors through
`E_{s-1}`, and the inclusion `E_{s-1} ↪ E_s` has tail factor `⟨N⟩⁻¹`. -/
theorem tendsto_tail_DKE38 (x : ECarrier38 c s) :
    Tendsto (fun N : ℕ => ‖fderiv ℝ (B.KE38 O c s) x -
      (projE38 c s N).comp (fderiv ℝ (B.KE38 O c s) x)‖) atTop (𝓝 0) := by
  set D := fderiv ℝ (eMap38 c s (s - 1) (fun z => B.T z - z) (B.K_mem_E38 O c s)) x with hD
  have hlim : Tendsto (fun N : ℕ => tailFactor38 N * ‖D‖) atTop (𝓝 0) := by
    simpa using tendsto_tailFactor38.mul_const ‖D‖
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hlim
  have e : fderiv ℝ (B.KE38 O c s) x - (projE38 c s N).comp (fderiv ℝ (B.KE38 O c s) x) =
      (eInclCLM38 c (by linarith : s - 1 ≤ s) -
        (projE38 c s N).comp (eInclCLM38 c (by linarith : s - 1 ≤ s))).comp D := by
    rw [B.fderiv_KE38 O c s x]
    ext v; simp [hD]
  rw [e]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_tail_eIncl_le38 c s N) (norm_nonneg _))

/-- `T = Id + K_E` on `E_s`. -/
theorem weightedHomeoE38_eq_add_KE (y : ECarrier38 c s) :
    B.weightedHomeoE38 O c s y = y + B.KE38 O c s y := by
  have h := congrFun (B.eMap_T_eq38 O c s) y
  exact h

/-- **W09.02-W09.03 (derivative invertible).**  `DT(x) = Id + DK(x)` is invertible on `E_s`
(`T` is an analytic diffeomorphism of `E_s`, W04). -/
theorem exists_equiv_DT38 (x : ECarrier38 c s) :
    ∃ e : ECarrier38 c s ≃L[ℝ] ECarrier38 c s,
      (e : ECarrier38 c s →L[ℝ] ECarrier38 c s) = 1 + fderiv ℝ (B.KE38 O c s) x := by
  set H := B.weightedHomeoE38 O c s with hH
  have hTfun : (H : ECarrier38 c s → ECarrier38 c s) = fun y => y + B.KE38 O c s y :=
    funext (B.weightedHomeoE38_eq_add_KE O c s)
  have hT : ∀ y, HasFDerivAt (H : ECarrier38 c s → ECarrier38 c s)
      (1 + fderiv ℝ (B.KE38 O c s) y) y := by
    intro y
    rw [hTfun]
    exact (hasFDerivAt_id y).add (B.differentiableAt_KE38 O c s y).hasFDerivAt
  have hS : ∀ y, HasFDerivAt (H.symm : ECarrier38 c s → ECarrier38 c s)
      (fderiv ℝ (H.symm : ECarrier38 c s → ECarrier38 c s) y) y := fun y =>
    ((B.analytic_weightedHomeoE38_symm O c s y trivial).differentiableAt).hasFDerivAt
  set g := fderiv ℝ (H.symm : ECarrier38 c s → ECarrier38 c s) (H x) with hg
  have hSx : H.symm (H x) = x := H.symm_apply_apply x
  have h1 : HasFDerivAt ((H.symm : ECarrier38 c s → ECarrier38 c s) ∘ (H : ECarrier38 c s → ECarrier38 c s))
      (g.comp (1 + fderiv ℝ (B.KE38 O c s) x)) x :=
    (hS (H x)).comp x (hT x)
  have h1' : (H.symm : ECarrier38 c s → ECarrier38 c s) ∘ (H : ECarrier38 c s → ECarrier38 c s) = id :=
    funext H.symm_apply_apply
  rw [h1'] at h1
  have hl : g.comp (1 + fderiv ℝ (B.KE38 O c s) x) = ContinuousLinearMap.id ℝ _ :=
    h1.unique (hasFDerivAt_id x)
  have h2 : HasFDerivAt ((H : ECarrier38 c s → ECarrier38 c s) ∘ (H.symm : ECarrier38 c s → ECarrier38 c s))
      ((1 + fderiv ℝ (B.KE38 O c s) x).comp g) (H x) := by
    have hT' : HasFDerivAt (H : ECarrier38 c s → ECarrier38 c s)
        (1 + fderiv ℝ (B.KE38 O c s) x) (H.symm (H x)) := by rw [hSx]; exact hT x
    exact hT'.comp (H x) (hS (H x))
  have h2' : (H : ECarrier38 c s → ECarrier38 c s) ∘ (H.symm : ECarrier38 c s → ECarrier38 c s) = id :=
    funext H.apply_symm_apply
  rw [h2'] at h2
  have hr : (1 + fderiv ℝ (B.KE38 O c s) x).comp g = ContinuousLinearMap.id ℝ _ :=
    h2.unique (hasFDerivAt_id _)
  exact ⟨ContinuousLinearEquiv.equivOfInverse (1 + fderiv ℝ (B.KE38 O c s) x) g
    (fun v => by simpa using congrArg (fun L => L v) hl)
    (fun v => by simpa using congrArg (fun L => L v) hr), rfl⟩

/-- **W09 (Galerkin solution).**  `y` is a solution in `P_N h⁰` of `P_N T(y) = P_N ζ`: finite
support in `|n| ≤ N` and `T(y)_n = ζ_n` for `|n| ≤ N` (v2 `D:eq:inversefinite`). -/
def GalerkinSol38 (N : ℕ) (ζ y : ℤ → ℂ) : Prop :=
  (∀ n, n ∉ symmetricModes N → y n = 0) ∧ ∀ n ∈ symmetricModes N, B.T y n = ζ n

/-- **W09.01-W09.05 (existence and convergence).** For `z ∈ E_s` and `x = T⁻¹ z`, there are
`x_N ∈ P_N E_s` with `P_N T(x_N) = P_N z` for all large `N`, and `x_N → x` in `E_s`. -/
theorem exists_galerkin_branch38 (z : ECarrier38 c s) :
    ∃ xN : ℕ → ECarrier38 c s,
      Tendsto xN atTop (𝓝 ((B.weightedHomeoE38 O c s).symm z)) ∧
      ∀ᶠ N in atTop, B.GalerkinSol38 N (eCoe38 c s z) (eCoe38 c s (xN N)) := by
  set H := B.weightedHomeoE38 O c s with hH
  set x := H.symm z with hx
  obtain ⟨e, he⟩ := B.exists_equiv_DT38 O c s x
  have hz : x + B.KE38 O c s x = z := by
    rw [← B.weightedHomeoE38_eq_add_KE O c s x]
    exact H.apply_symm_apply z
  obtain ⟨xN, hlim, hsol⟩ := galerkin_newton_W09 (projE38 c s) (norm_projE38_le c s)
    (projE38_idem c s) (B.KE38 O c s) (B.differentiableAt_KE38 O c s) x
    (B.continuousAt_fderiv_KE38 O c s x) e he (tendsto_projE38 c s x)
    (B.tendsto_tail_DKE38 O c s x)
  refine ⟨xN, hlim, ?_⟩
  filter_upwards [hsol] with N ⟨hP, hE⟩
  rw [hz] at hE
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · have := congrArg (fun w => eCoe38 c s w n) hP
    simp only [eCoe38_projE38, hn, ite_false] at this
    exact this.symm
  · have := congrArg (fun w => eCoe38 c s w n) hE
    simp only [eAdd_apply38, eCoe38_projE38, hn, ite_true, eCoe_KE38] at this
    have h2 : eCoe38 c s (xN N) n + (B.T (eCoe38 c s (xN N)) n - eCoe38 c s (xN N) n) =
        eCoe38 c s z n := this
    rw [add_sub_cancel] at h2
    exact h2

include O in
/-- **W09.06 (uniqueness against the `h²` ball, from W08).**  For every `R` and all large `N`,
two solutions in `P_N h⁰` of `P_N T(y) = P_N ζ`, both of `h²`-norm `≤ R`, coincide.
(`ζ` is arbitrary; only `T y_n = ζ_n` for `|n| ≤ N` is used.) -/
theorem galerkinSol_unique_W09 (R : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ ζ : ℤ → ℂ, ∀ y w : H2_38, ‖y‖ ≤ R → ‖w‖ ≤ R →
      B.GalerkinSol38 N ζ (carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y) →
      B.GalerkinSol38 N ζ (carrierCoe38 (((1 + 1 : ℕ)) : ℝ) w) →
      carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y = carrierCoe38 (((1 + 1 : ℕ)) : ℝ) w := by
  classical
  obtain ⟨N₀, hN₀⟩ := B.injOn_TN_ballV38 O R
  refine ⟨N₀, fun N hN ζ y w hy hw hsy hsw => ?_⟩
  -- the elements of `P_N h⁰`
  have hmemV : ∀ y : H2_38, B.GalerkinSol38 N ζ (carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y) →
      projC38 ((0 : ℕ) : ℝ) N (i20_38 y) = i20_38 y := by
    intro y hsy
    apply carrierExt38
    funext n
    rw [carrierCoe38_projC38, carrierCoe38_i20]
    split_ifs with hn
    · rfl
    · exact (hsy.1 n hn).symm
  let u : ∀ y : H2_38, B.GalerkinSol38 N ζ (carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y) → (cp38 N).V :=
    fun y h => ⟨i20_38 y, ((cp38 N).mem_V_iff _).2 (hmemV y h)⟩
  have hball : ∀ (y : H2_38) (h : B.GalerkinSol38 N ζ (carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y)),
      ‖y‖ ≤ R → u y h ∈ ballV38 N R :=
    fun y h hy => ⟨y, hy, rfl⟩
  have hT : ∀ y : H2_38, B.GalerkinSol38 N ζ (carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y) →
      ∀ n, carrierCoe38 ((0 : ℕ) : ℝ) (projC38 ((0 : ℕ) : ℝ) N (B.TC 0 (i20_38 y))) n =
        if n ∈ symmetricModes N then ζ n else 0 := by
    intro y hs n
    rw [carrierCoe38_projC38]
    split_ifs with hn
    · rw [B.TC_coe]
      have e : carrierCoe38 ((0 : ℕ) : ℝ) (i20_38 y) = carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y :=
        carrierCoe38_incl38 _ y
      rw [e]
      exact hs.2 n hn
    · rfl
  have hTN : B.TN N (u y hsy) = B.TN N (u w hsw) := by
    apply Subtype.ext
    rw [B.TN_coe, B.TN_coe]
    show projC38 ((0 : ℕ) : ℝ) N (B.TC 0 (i20_38 y)) = projC38 ((0 : ℕ) : ℝ) N (B.TC 0 (i20_38 w))
    apply carrierExt38
    funext n
    rw [hT y hsy n, hT w hsw n]
  have h2 := congrArg (fun v : (cp38 N).V => (v : H0_38)) (hN₀ N hN (hball y hsy hy) (hball w hsw hw) hTN)
  funext n
  have := congrArg (fun v => carrierCoe38 ((0 : ℕ) : ℝ) v n) h2
  exact (carrierCoe38_i20 y n).symm.trans (this.trans (carrierCoe38_i20 w n))

/-- **W09 (`D:lem:localinverse`), conditional on `B`, `O`.**  For `z ∈ E_s` (`x = T⁻¹ z`):
(1) there are `x_N ∈ P_N E_s` with `P_N T(x_N) = P_N z` for all large `N` and `x_N → x` in `E_s`;
(2) for every `R` there is `N₀` such that for `N ≥ N₀` any solution `y ∈ P_N h⁰` of
`P_N T(y) = P_N z` of `h²`-norm `≤ R` agrees with `x_N`, whenever `x_N` also lies in that `h²`
ball (`x_N = ι w` for some `w ∈ h²`, `‖w‖ ≤ R`). -/
theorem W09_localGalerkinInverse (z : ECarrier38 c s) :
    ∃ xN : ℕ → ECarrier38 c s,
      Tendsto xN atTop (𝓝 ((B.weightedHomeoE38 O c s).symm z)) ∧
      (∀ᶠ N in atTop, B.GalerkinSol38 N (eCoe38 c s z) (eCoe38 c s (xN N))) ∧
      ∀ R : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ y w : H2_38, ‖y‖ ≤ R → ‖w‖ ≤ R →
        B.GalerkinSol38 N (eCoe38 c s z) (carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y) →
        carrierCoe38 (((1 + 1 : ℕ)) : ℝ) w = eCoe38 c s (xN N) →
        B.GalerkinSol38 N (eCoe38 c s z) (eCoe38 c s (xN N)) →
        carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y = eCoe38 c s (xN N) := by
  obtain ⟨xN, hlim, hsol⟩ := B.exists_galerkin_branch38 O c s z
  refine ⟨xN, hlim, hsol, fun R => ?_⟩
  obtain ⟨N₀, hN₀⟩ := B.galerkinSol_unique_W09 O R
  refine ⟨N₀, fun N hN y w hy hw hsy hwe hsx => ?_⟩
  rw [← hwe] at hsx ⊢
  exact hN₀ N hN _ y w hy hw hsy hsx

include O in
/-- **W09 (`D:lem:localinverse`), final form, conditional on `B`, `O`.**  For `z ∈ E_s` and
`x = T⁻¹ z`: there are `x_N ∈ P_N E_s` such that
(1) `P_N T(x_N) = P_N z` for all large `N`;
(2) `x_N → x` in `E_s`;
(3) for every `R` larger than the `h²`-norm of `x`, for all large `N` every solution
`y ∈ P_N h⁰` of `P_N T(y) = P_N z` with `‖y‖_{h²} ≤ R` equals `x_N`.
(`x_N → x` in `E_s` implies `‖x_N‖_{h²} < R` eventually, so the "common ball" of v2 is automatic.) -/
theorem W09_localGalerkinInverse_ball (z : ECarrier38 c s) :
    ∃ xN : ℕ → ECarrier38 c s,
      Tendsto xN atTop (𝓝 ((B.weightedHomeoE38 O c s).symm z)) ∧
      (∀ᶠ N in atTop, B.GalerkinSol38 N (eCoe38 c s z) (eCoe38 c s (xN N))) ∧
      ∀ R : ℝ, ‖eToSob38 c s (((1 + 1 : ℕ)) : ℝ) ((B.weightedHomeoE38 O c s).symm z)‖ < R →
        ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ y : H2_38, ‖y‖ ≤ R →
          B.GalerkinSol38 N (eCoe38 c s z) (carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y) →
          carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y = eCoe38 c s (xN N) := by
  obtain ⟨xN, hlim, hsol, huniq⟩ := B.W09_localGalerkinInverse O c s z
  refine ⟨xN, hlim, hsol, fun R hR => ?_⟩
  have hc : Tendsto (fun N => eToSob38 c s (((1 + 1 : ℕ)) : ℝ) (xN N)) atTop
      (𝓝 (eToSob38 c s (((1 + 1 : ℕ)) : ℝ) ((B.weightedHomeoE38 O c s).symm z))) :=
    ((continuous_eToSob38 c s (((1 + 1 : ℕ)) : ℝ)).tendsto _).comp hlim
  have hnorm : ∀ᶠ N in atTop, ‖eToSob38 c s (((1 + 1 : ℕ)) : ℝ) (xN N)‖ < R :=
    (continuous_norm.tendsto _ |>.comp hc).eventually (gt_mem_nhds hR)
  obtain ⟨N₀, hN₀⟩ := huniq R
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hnorm.and hsol)
  refine ⟨max N₀ N₁, fun N hN y hy hsy => ?_⟩
  obtain ⟨hw, hsx⟩ := hN₁ N (le_trans (le_max_right _ _) hN)
  exact hN₀ N (le_trans (le_max_left _ _) hN) y (eToSob38 c s (((1 + 1 : ℕ)) : ℝ) (xN N)) hy hw.le hsy
    (carrierCoe_eToSob38 c s _ _) hsx

end BirkhoffInput38

end NlsGge.Birkhoff
