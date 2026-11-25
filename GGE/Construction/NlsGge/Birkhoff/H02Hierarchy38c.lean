import NlsGge.Birkhoff.H02Hierarchy38b

/-! # H02, part 3: pathwise convergence on the coupling space (conditional on `B`)

v2 `B:prop:hierarchy`, proof paragraphs 2-4 (l.889-909): for `g ∈ Ω₁` (`Omega1_38`),

* `Φ⁻¹ z^{(m)} → Φ⁻¹ z` in every fixed `H^r` (for the tail `m ≥ r + 2`), by continuity of `T⁻¹` on
  `h^r` (field `analytic_Tinv`) and the weighted-square convergence `z^{(m)} → z` in `h^r`;
* the pathwise `H¹` bound `B_g = sup_m ‖u_m‖_{H¹} + ‖u‖_{H¹} < ∞`;
* the `n`-th summand of `R_m(u_m)` equals `gapIntW_{W_m}(u_m) - a_{m,n}I_n(u_m)`, where
  `a_{m,n} I_n(u_m) = a_{m,n}|z^{(m)}_n|² = |g_n|²` (field `action`), is dominated by
  `C_B |g_n|² ⟨n⟩^{-3/2}` (H01 `uniformSymbolGap38`, v2 `B:eq:coupledbound`, with `C_B` depending on
  the path only through `B_g`, never integrated), and converges to the `n`-th summand of `R_W(u)`;
* `R_m(u_m) → R_W(u)` by dominated convergence for the series.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.SpectralFoundations NlsGge.Weights
  NlsGge.Sobolev38 Filter Topology
open scoped ENNReal

namespace BirkhoffTop38

variable (B : BirkhoffTop38) (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
  (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper)

include hlower hbound hupper

/-- **`Φ⁻¹` is continuous on every `h^r` along the coupling** (v2 l.894-897): for `g ∈ Ω₁` and every
`r`, `T⁻¹ z^{(m)} → T⁻¹ z` in `h^r` as `m → ∞`. -/
theorem tendsto_cleanTinvC_scale38 {g : ℤ → ℂ} (hg : g ∈ Omega1_38 c) (r : ℕ) :
    Tendsto (fun m : ℕ => B.cleanTinvC r (zHier38 c m g)) atTop
      (𝓝 (B.cleanTinvC r (zFull38 c g))) := by
  have hk := ((B.continuous_TinvC r).tendsto _).comp
    (tendsto_carrier_scale38 lower upper c hlower hbound hupper hg r)
  have h2 : Tendsto (fun k : ℕ => B.cleanTinvC r (zHier38 c (k + (r + 2)) g)) atTop
      (𝓝 (B.cleanTinvC r (zFull38 c g))) := by
    rw [B.cleanTinvC_of_mem r (zFull38 c g)
      (zFull38_mem_seqSobolev38_nat lower upper c hlower hbound hupper hg r)]
    refine hk.congr (fun k => ?_)
    rw [B.cleanTinvC_of_mem r _ (zHier38_mem_seqSobolev38_nat lower upper c hlower hbound hupper
      hg (by omega))]
    rfl
  exact (tendsto_add_atTop_iff_nat (f := fun m : ℕ => B.cleanTinvC r (zHier38 c m g))
    (r + 2)).1 h2

omit hlower hbound hupper in
theorem norm_phys_cleanΦinv_eq38 (w : ℤ → ℂ) (hw : w ∈ seqSobolev38 ((1 : ℕ) : ℝ))
    (h : SobolevSquareSummable 1 (physicalFourier (B.cleanΦinv w))) :
    ‖physicalSobolevL2 1 (B.cleanΦinv w) h‖ = ‖B.cleanTinvC 1 w‖ := by
  rw [B.norm_physicalSobolevL2_cleanΦinv38 w hw h, B.cleanTinvC_of_mem 1 w hw]
  rfl

/-- **The pathwise `H¹` bound of v2 (l.899-903)**, `B_g = sup_{m ≥ 3} ‖u_m‖_{H¹} + ‖u‖_{H¹} < ∞`
(the finitely many initial `m` do not matter for any limit). -/
theorem exists_H1_bound_scale38 {g : ℤ → ℂ} (hg : g ∈ Omega1_38 c) :
    ∃ Bd : ℝ, 1 ≤ Bd ∧
      (∀ᶠ m : ℕ in atTop, ∀ h : SobolevSquareSummable 1 (physicalFourier (B.cleanΦinv (zHier38 c m g))),
        ‖physicalSobolevL2 1 (B.cleanΦinv (zHier38 c m g)) h‖ ≤ Bd) ∧
      (∀ h : SobolevSquareSummable 1 (physicalFourier (B.cleanΦinv (zFull38 c g))),
        ‖physicalSobolevL2 1 (B.cleanΦinv (zFull38 c g)) h‖ ≤ Bd) := by
  have ht := (B.tendsto_cleanTinvC_scale38 lower upper c hlower hbound hupper hg 1).norm
  have hz1 : zFull38 c g ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
    zFull38_mem_seqSobolev38_nat lower upper c hlower hbound hupper hg 1
  have hev : ∀ᶠ m : ℕ in atTop, ‖B.cleanTinvC 1 (zHier38 c m g)‖ < ‖B.cleanTinvC 1 (zFull38 c g)‖ + 1 :=
    ht.eventually (gt_mem_nhds (lt_add_one _))
  refine ⟨max 1 (‖B.cleanTinvC 1 (zFull38 c g)‖ + 1), le_max_left _ _, ?_, fun h => ?_⟩
  · filter_upwards [hev, eventually_ge_atTop 3] with m hm hm3 h
    rw [B.norm_phys_cleanΦinv_eq38 _ (zHier38_mem_seqSobolev38_nat lower upper c hlower hbound
      hupper hg (r := 1) (by omega)) h]
    exact hm.le.trans (le_max_right _ _)
  · rw [B.norm_phys_cleanΦinv_eq38 _ hz1 h]
    exact (by linarith : _ ≤ ‖B.cleanTinvC 1 (zFull38 c g)‖ + 1).trans (le_max_right _ _)

/-- **v2 `B:eq:coupledbound`, in the form `a_{m,n}|z^{(m)}_n|² = |g_n|²`.** Via the field `action`:
`I_n(Φ⁻¹ z^{(m)}) = |z^{(m)}_n|²`, hence `a_{m,n} I_n = |g_n|²`. -/
theorem hierRate_mul_action38 {g : ℤ → ℂ} {m : ℕ} (hm : 3 ≤ m) (n : ℤ) (hg : g ∈ Omega1_38 c) :
    hierRate38 c m n * actualGapActionAllE02_38 (B.cleanΦinv (zHier38 c m g)) n = ‖g n‖ ^ 2 := by
  have hz1 : zHier38 c m g ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
    zHier38_mem_seqSobolev38_nat lower upper c hlower hbound hupper hg (r := 1) (by omega)
  rw [B.action_cleanΦinv38 _ hz1, norm_sq_zHier38 lower upper c hlower hbound hupper]
  have := hierRate38_pos lower c hlower hbound m n
  field_simp

theorem fullRate_mul_action38 {g : ℤ → ℂ} (n : ℤ) (hg : g ∈ Omega1_38 c) :
    fullWeightRate c n * actualGapActionAllE02_38 (B.cleanΦinv (zFull38 c g)) n = ‖g n‖ ^ 2 := by
  have hz1 : zFull38 c g ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
    zFull38_mem_seqSobolev38_nat lower upper c hlower hbound hupper hg 1
  rw [B.action_cleanΦinv38 _ hz1, norm_sq_zFull38 lower upper c hlower hbound hupper]
  have := fullWeightRate_pos lower upper c hlower hbound hupper n
  field_simp

/-- Domination (v2 `B:eq:coupledbound`): for the path-dependent `Bd`, eventually in `m`,
`|n`-th summand of `R_m(u_m)| ≤ C_B ⟨n⟩^{-3/2} |g_n|²`, independently of `m`. -/
theorem summand_dominated_scale38 {g : ℤ → ℂ} (hg : g ∈ Omega1_38 c) :
    ∃ CB : ℝ, 0 < CB ∧ ∀ᶠ m : ℕ in atTop, ∀ n : ℤ,
      |gapRemainderTermE02_38 (partialWeight c m) (B.cleanΦinv (zHier38 c m g)) n| ≤
        CB * (japaneseBracket n ^ (-(3 / 2) : ℝ) * ‖g n‖ ^ 2) := by
  obtain ⟨Bd, hBd1, hBdm, -⟩ := B.exists_H1_bound_scale38 lower upper c hlower hbound hupper hg
  have hle : lower ≤ upper := (hbound 0).trans (hupper 0)
  obtain ⟨CB, hCB, hCBP⟩ := NlsGge.Weights.uniformSymbolGap38 lower upper hlower hle Bd hBd1
  refine ⟨CB, hCB, ?_⟩
  filter_upwards [hBdm, eventually_ge_atTop 3] with m hm hm3 n
  have hz1 : zHier38 c m g ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
    zHier38_mem_seqSobolev38_nat lower upper c hlower hbound hupper hg (r := 1) (by omega)
  have hs : SobolevSquareSummable 1 (physicalFourier (B.cleanΦinv (zHier38 c m g))) := by
    simpa using B.sobolev_cleanΦinv38 1 _ hz1
  have h1 := abs_gapRemainderTerm_le38 (partialWeight c m) (continuous_partialWeight38 c m)
    (B.cleanΦinv (zHier38 c m g)) n
    (CB * partialWeight c m (2 * Real.pi * (n : ℝ)) * japaneseBracket n ^ (-(3 / 2) : ℝ))
    (fun l hl => (hCBP c hbound hupper _ hs (hm hs) n l hl).1 m)
  refine h1.trans (le_of_eq ?_)
  have hmul := B.hierRate_mul_action38 lower upper c hlower hbound hupper hm3 n hg
  change CB * hierRate38 c m n * japaneseBracket n ^ (-(3 / 2) : ℝ) *
    actualGapActionAllE02_38 (B.cleanΦinv (zHier38 c m g)) n = _
  calc CB * hierRate38 c m n * japaneseBracket n ^ (-(3 / 2) : ℝ) *
      actualGapActionAllE02_38 (B.cleanΦinv (zHier38 c m g)) n
      = CB * japaneseBracket n ^ (-(3 / 2) : ℝ) *
        (hierRate38 c m n * actualGapActionAllE02_38 (B.cleanΦinv (zHier38 c m g)) n) := by ring
    _ = _ := by rw [hmul]; ring

/-- Fixed-gap convergence (v2 l.905-907): the `n`-th summand of `R_m(u_m)` converges to the `n`-th
summand of `R_W(u)`. -/
theorem tendsto_summand_scale38 {g : ℤ → ℂ} (hg : g ∈ Omega1_38 c) (n : ℤ) :
    Tendsto (fun m : ℕ => gapRemainderTermE02_38 (partialWeight c m)
        (B.cleanΦinv (zHier38 c m g)) n) atTop
      (𝓝 (remainderSummand38 c (B.cleanΦinv (zFull38 c g)) n)) := by
  have hW := weight_continuous38 hlower hbound hupper
  obtain ⟨Bd, hBd1, hBdm, hBdz⟩ := B.exists_H1_bound_scale38 lower upper c hlower hbound hupper hg
  obtain ⟨K, hK, hloc⟩ := actualGapLocalization_allU_E02_38 Bd hBd1
  set L : ℝ := |(n : ℝ)| * Real.pi + K with hL
  have hz1 : zFull38 c g ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
    zFull38_mem_seqSobolev38_nat lower upper c hlower hbound hupper hg 1
  -- the gap integral for the fixed weight `W` converges by continuity
  have hA : Tendsto (fun m : ℕ => gapFnW38 (weight c) n (B.cleanTinvC 1 (zHier38 c m g))) atTop
      (𝓝 (gapFnW38 (weight c) n (B.cleanTinvC 1 (zFull38 c g)))) :=
    ((continuous_gapFnW38 (weight c) hW n).tendsto _).comp
      (B.tendsto_cleanTinvC_scale38 lower upper c hlower hbound hupper hg 1)
  -- the difference `W - W_m` is controlled by the tail of the series
  have hbd : ∀ᶠ m : ℕ in atTop,
      |gapIntW38 (weight c) (B.cleanΦinv (zHier38 c m g)) n -
        gapIntW38 (partialWeight c m) (B.cleanΦinv (zHier38 c m g)) n| ≤
        weightTail38 c m (2 * L) * (‖g n‖ ^ 2 / lower) := by
    filter_upwards [hBdm, eventually_ge_atTop 3] with m hm hm3
    have hzm : zHier38 c m g ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
      zHier38_mem_seqSobolev38_nat lower upper c hlower hbound hupper hg (r := 1) (by omega)
    have hs : SobolevSquareSummable 1 (physicalFourier (B.cleanΦinv (zHier38 c m g))) := by
      simpa using B.sobolev_cleanΦinv38 1 _ hzm
    have h1 := abs_gapIntW_sub_le38 (weight c) (partialWeight c m) hW
      (continuous_partialWeight38 c m) (B.cleanΦinv (zHier38 c m g)) n
      (weightTail38 c m (2 * L)) (fun l hl => by
        have hl' := hloc _ hs (hm hs) n l hl
        have hlL : |l| ≤ L := by
          have h2 : |l - (n : ℝ) * Real.pi| ≤ K := hl'.trans (div_le_self hK.le
            (japaneseBracket_one_le n))
          calc |l| = |(l - (n : ℝ) * Real.pi) + (n : ℝ) * Real.pi| := by ring_nf
            _ ≤ |l - (n : ℝ) * Real.pi| + |(n : ℝ) * Real.pi| := abs_add_le _ _
            _ ≤ K + |(n : ℝ)| * Real.pi := by
              rw [abs_mul, abs_of_pos Real.pi_pos]; linarith
            _ = L := by rw [hL]; ring
        have h22 : |2 * l| ≤ 2 * L := by
          rw [abs_mul, abs_two]; exact mul_le_mul_of_nonneg_left hlL (by norm_num)
        rw [weight_sub_partialWeight38 lower upper c hlower hbound hupper m,
          abs_of_nonneg (weightTail38_nonneg lower upper c hlower hbound hupper m _)]
        exact weightTail38_mono lower upper c hlower hbound hupper m h22)
    refine h1.trans ?_
    rw [B.action_cleanΦinv38 _ hzm, norm_sq_zHier38 lower upper c hlower hbound hupper]
    refine mul_le_mul_of_nonneg_left ?_ (weightTail38_nonneg lower upper c hlower hbound hupper m _)
    have hl := lower_le_hierRate38 lower c hlower hbound m n
    exact div_le_div_of_nonneg_left (sq_nonneg _) hlower hl
  have hD : Tendsto (fun m : ℕ => gapIntW38 (weight c) (B.cleanΦinv (zHier38 c m g)) n -
      gapIntW38 (partialWeight c m) (B.cleanΦinv (zHier38 c m g)) n) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun m : ℕ => weightTail38 c m (2 * L) * (‖g n‖ ^ 2 / lower))
      (hbd.mono (fun m hm => by rwa [Real.norm_eq_abs])) ?_
    simpa using (tendsto_weightTail38 lower upper c hlower hbound hupper (2 * L)).mul_const
      (‖g n‖ ^ 2 / lower)
  have hlim := (hA.sub hD).sub (tendsto_const_nhds (x := ‖g n‖ ^ 2))
  have hrs : remainderSummand38 c (B.cleanΦinv (zFull38 c g)) n =
      gapFnW38 (weight c) n (B.cleanTinvC 1 (zFull38 c g)) - 0 - ‖g n‖ ^ 2 := by
    unfold remainderSummand38
    rw [gapIntegral38_eq_gapIntW38, B.gapIntW38_cleanΦinv38 _ _ hz1 n,
      B.fullRate_mul_action38 lower upper c hlower hbound hupper n hg]
    ring
  rw [hrs]
  refine Tendsto.congr' ?_ hlim
  filter_upwards [eventually_ge_atTop 3] with m hm3
  have hzm : zHier38 c m g ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
    zHier38_mem_seqSobolev38_nat lower upper c hlower hbound hupper hg (r := 1) (by omega)
  rw [gapRemainderTerm_eq_gapIntW38 _ (continuous_partialWeight38 c m),
    B.gapIntW38_cleanΦinv38 (weight c) _ hzm n]
  have hmul := B.hierRate_mul_action38 lower upper c hlower hbound hupper hm3 n hg
  have e : partialWeight c m (2 * Real.pi * (n : ℝ)) = hierRate38 c m n := rfl
  rw [e, hmul]
  ring

/-- **`R_m(u_m) → R_W(u)`** (v2 l.903-908): dominated convergence of the series, with the summable
majorant `C_B ⟨n⟩^{-3/2}|g_n|²` (finite on `Ω₁`; no moment of `C_B` is used). -/
theorem tendsto_remainder_scale38 {g : ℤ → ℂ} (hg : g ∈ Omega1_38 c) :
    Tendsto (fun m : ℕ => hierRemainder38 c m (B.cleanΦinv (zHier38 c m g))) atTop
      (𝓝 (remainder38 c (B.cleanΦinv (zFull38 c g)))) := by
  obtain ⟨CB, hCB, hdom⟩ := B.summand_dominated_scale38 lower upper c hlower hbound hupper hg
  exact tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter ℕ))
    (f := fun (m : ℕ) (n : ℤ) => gapRemainderTermE02_38 (partialWeight c m)
      (B.cleanΦinv (zHier38 c m g)) n)
    (g := fun n : ℤ => remainderSummand38 c (B.cleanΦinv (zFull38 c g)) n)
    (bound := fun n : ℤ => CB * (japaneseBracket n ^ (-(3 / 2) : ℝ) * ‖g n‖ ^ 2))
    (hg.2.mul_left CB)
    (fun n => B.tendsto_summand_scale38 lower upper c hlower hbound hupper hg n)
    (hdom.mono (fun m hm n => by rw [Real.norm_eq_abs]; exact hm n))

/-- **`R̄_m(z^{(m)}) → R̄_W(z)`.** -/
theorem tendsto_hierRbar_scale38 {g : ℤ → ℂ} (hg : g ∈ Omega1_38 c) :
    Tendsto (fun m : ℕ => B.hierRbar38 c m (zHier38 c m g)) atTop
      (𝓝 (B.Rbar38 c (zFull38 c g))) := by
  rw [B.Rbar38_of_mem c (zFull38_mem_Omega038 lower upper c hlower hbound hupper hg)]
  refine (B.tendsto_remainder_scale38 lower upper c hlower hbound hupper hg).congr' ?_
  filter_upwards [eventually_ge_atTop 2] with m hm
  rw [B.hierRbar38_of_mem c m (zHier38_mem_seqSobolev38 lower upper c hlower hbound hupper hg hm)]

end BirkhoffTop38

end NlsGge.Birkhoff
end
