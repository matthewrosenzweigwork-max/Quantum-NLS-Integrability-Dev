import NlsGge.Birkhoff.S03Measure38b

/-! # S03, part 3: projections, continuity of `Φ⁻¹`, pathwise convergence (conditional on
`B : BirkhoffTop38`)

S03.03 (projection convergence in every `h^m`), S03.04 (continuity of `Φ⁻¹` in `H^m`, a pathwise
`H¹` bound), S03.05 (fixed-gap convergence), S03.06 (domination), S03.07 (limit nonnegativity).
Every declaration with `B` is conditional on the E01 input `BirkhoffTop38`.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.SpectralFoundations NlsGge.Weights
  NlsGge.Sobolev38 Filter Topology
open scoped ENNReal

/-! ### Finite coordinate projections and exhaustions -/

/-- Coordinate projection `P_Λ z` onto a finite index set (v2 `sec:finitegap`). -/
def projFin38 (Λ : Finset ℤ) (z : ℤ → ℂ) : ℤ → ℂ := fun n => if n ∈ Λ then z n else 0

theorem projFin38_apply_of_mem {Λ : Finset ℤ} {n : ℤ} (hn : n ∈ Λ) (z : ℤ → ℂ) :
    projFin38 Λ z n = z n := by simp [projFin38, hn]

theorem projFin38_apply_of_not_mem {Λ : Finset ℤ} {n : ℤ} (hn : n ∉ Λ) (z : ℤ → ℂ) :
    projFin38 Λ z n = 0 := by simp [projFin38, hn]

theorem finite_support_projFin38 (Λ : Finset ℤ) (z : ℤ → ℂ) :
    {n : ℤ | projFin38 Λ z n ≠ 0}.Finite :=
  Λ.finite_toSet.subset (fun n hn => by
    by_contra h
    exact hn (projFin38_apply_of_not_mem h z))

/-- An increasing exhaustion `Λ_N ↑ ℤ` by finite sets. -/
structure IsExhaustion38 (Λ : ℕ → Finset ℤ) : Prop where
  mono : Monotone Λ
  exhaust : ∀ n : ℤ, ∃ N : ℕ, n ∈ Λ N

theorem IsExhaustion38.tendsto_atTop {Λ : ℕ → Finset ℤ} (h : IsExhaustion38 Λ) :
    Tendsto Λ atTop atTop :=
  tendsto_atTop_finset_of_monotone h.mono h.exhaust

theorem IsExhaustion38.eventually_mem {Λ : ℕ → Finset ℤ} (h : IsExhaustion38 Λ) (n : ℤ) :
    ∀ᶠ N in atTop, n ∈ Λ N := by
  obtain ⟨N0, hN0⟩ := h.exhaust n
  exact eventually_atTop.2 ⟨N0, fun N hN => h.mono hN hN0⟩

/-! ### S03.03: projection convergence in every `h^r`, for every exhaustion -/

/-- `‖P_Λ z - z‖²_{h^r} = ‖z‖²_{h^r} - ∑_{n∈Λ} ⟨n⟩^{2r}|z_n|²`. -/
theorem norm_sq_proj_sub38 (r : ℝ) (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 r) (Λ : Finset ℤ) :
    ‖carrierMk38 r (projFin38 Λ z) (finiteSupport_mem_seqSobolev38 r _
        (finite_support_projFin38 Λ z)) - carrierMk38 r z hz‖ ^ 2 =
      ‖carrierMk38 r z hz‖ ^ 2 - ∑ n ∈ Λ, sobolevModeWeight r n * ‖z n‖ ^ 2 := by
  set xN := carrierMk38 r (projFin38 Λ z) (finiteSupport_mem_seqSobolev38 r _
        (finite_support_projFin38 Λ z)) with hxN
  set x := carrierMk38 r z hz with hx
  have h1 := carrier_hasSum_norm_sq38 r (xN - x)
  have h2 := carrier_hasSum_norm_sq38 r x
  have h3 : HasSum (fun n : ℤ => if n ∈ Λ then sobolevModeWeight r n * ‖z n‖ ^ 2 else 0)
      (∑ n ∈ Λ, sobolevModeWeight r n * ‖z n‖ ^ 2) := by
    have h : HasSum (fun n : ℤ => if n ∈ Λ then sobolevModeWeight r n * ‖z n‖ ^ 2 else 0)
        (∑ n ∈ Λ, if n ∈ Λ then sobolevModeWeight r n * ‖z n‖ ^ 2 else 0) :=
      hasSum_sum_of_ne_finset_zero (fun n hn => by simp [hn])
    have e : (∑ n ∈ Λ, if n ∈ Λ then sobolevModeWeight r n * ‖z n‖ ^ 2 else 0) =
        ∑ n ∈ Λ, sobolevModeWeight r n * ‖z n‖ ^ 2 :=
      Finset.sum_congr rfl (fun n hn => by simp [hn])
    rwa [e] at h
  have h4 := h2.sub h3
  have e : ∀ n : ℤ, sobolevModeWeight r n * ‖carrierCoe38 r (xN - x) n‖ ^ 2 =
      sobolevModeWeight r n * ‖carrierCoe38 r x n‖ ^ 2 -
        (if n ∈ Λ then sobolevModeWeight r n * ‖z n‖ ^ 2 else 0) := by
    intro n
    by_cases hn : n ∈ Λ
    · have : carrierCoe38 r (xN - x) n = 0 := by
        show projFin38 Λ z n - z n = 0
        rw [projFin38_apply_of_mem hn]; simp
      rw [this]; simp only [hn, ↓reduceIte]
      show _ = sobolevModeWeight r n * ‖z n‖ ^ 2 - _
      simp
    · have : carrierCoe38 r (xN - x) n = - z n := by
        show projFin38 Λ z n - z n = - z n
        rw [projFin38_apply_of_not_mem hn]; simp
      rw [this, norm_neg]; simp only [hn, ↓reduceIte]
      show _ = sobolevModeWeight r n * ‖z n‖ ^ 2 - 0
      simp
  simp_rw [e] at h1
  exact h1.unique h4

theorem tendsto_carrier_proj38 (r : ℝ) (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 r) {Λ : ℕ → Finset ℤ}
    (hΛ : IsExhaustion38 Λ) :
    Tendsto (fun N : ℕ => carrierMk38 r (projFin38 (Λ N) z) (finiteSupport_mem_seqSobolev38 r _
        (finite_support_projFin38 (Λ N) z))) atTop (𝓝 (carrierMk38 r z hz)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h2 := carrier_hasSum_norm_sq38 r (carrierMk38 r z hz)
  have hF : Tendsto (fun F : Finset ℤ => ∑ n ∈ F, sobolevModeWeight r n *
      ‖carrierCoe38 r (carrierMk38 r z hz) n‖ ^ 2) atTop (𝓝 (‖carrierMk38 r z hz‖ ^ 2)) := h2
  have h5 := hF.comp hΛ.tendsto_atTop
  have h6 : Tendsto (fun N : ℕ => ‖carrierMk38 r z hz‖ ^ 2 -
      ∑ n ∈ Λ N, sobolevModeWeight r n * ‖z n‖ ^ 2) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := ‖carrierMk38 r z hz‖ ^ 2)).sub h5
    simpa using this
  have h7 : Tendsto (fun N : ℕ => ‖carrierMk38 r (projFin38 (Λ N) z)
      (finiteSupport_mem_seqSobolev38 r _ (finite_support_projFin38 (Λ N) z)) -
        carrierMk38 r z hz‖ ^ 2) atTop (𝓝 0) := by
    refine h6.congr (fun N => ?_)
    rw [norm_sq_proj_sub38 r z hz (Λ N)]
  have h8 := (Real.continuous_sqrt.tendsto 0).comp h7
  simp only [Real.sqrt_zero, Function.comp_def, Real.sqrt_sq (norm_nonneg _)] at h8
  exact h8

/-! ### Physical Sobolev norm = `h^r` carrier norm of `𝓕 u` -/

theorem sobolevModeWeight_eq_rpow38 (r : ℝ) (n : ℤ) :
    sobolevModeWeight r n = japaneseBracket n ^ (2 * r) := rfl

theorem norm_physicalSobolevL2_eq_carrier38 (r : ℝ) (u : PhysicalL2)
    (hu : SobolevSquareSummable r (physicalFourier u)) :
    ‖physicalSobolevL2 r u hu‖ =
      ‖carrierMk38 r (fourierSeq38 u) ((fourierSeq38_mem_iff r u).2 hu)‖ := by
  have h1 := physicalSobolevL2_norm_sq r u hu
  have h2 := (carrier_hasSum_norm_sq38 r
    (carrierMk38 r (fourierSeq38 u) ((fourierSeq38_mem_iff r u).2 hu))).tsum_eq
  have h3 : ∑' n : ℤ, sobolevModeWeight r n * ‖fourierSeq38 u n‖ ^ 2 =
      ∑' n : ℤ, Real.rpow (japaneseBracket n) (2 * r) * ‖physicalFourier u n‖ ^ 2 := by
    rw [← tsum_comp_neg (fun n : ℤ => Real.rpow (japaneseBracket n) (2 * r) *
      ‖physicalFourier u n‖ ^ 2)]
    refine tsum_congr (fun n => ?_)
    rw [fourierSeq38_apply, norm_neg]
    have hb : japaneseBracket (-n) = japaneseBracket n := by simp [japaneseBracket]
    simp only [hb]
    rfl
  have h4 : ‖physicalSobolevL2 r u hu‖ ^ 2 =
      ‖carrierMk38 r (fourierSeq38 u) ((fourierSeq38_mem_iff r u).2 hu)‖ ^ 2 := by
    rw [h1, ← h3, ← h2]; rfl
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h4

theorem norm_carrierMk_congr38 {r s : ℝ} (h : r = s) (y : ℤ → ℂ) (hr : y ∈ seqSobolev38 r)
    (hs : y ∈ seqSobolev38 s) : ‖carrierMk38 r y hr‖ = ‖carrierMk38 s y hs‖ := by
  subst h; rfl

theorem seqSobolev38_sub {r : ℝ} {x y : ℤ → ℂ} (hx : x ∈ seqSobolev38 r)
    (hy : y ∈ seqSobolev38 r) : x - y ∈ seqSobolev38 r :=
  (weightedSubmodule (sobolevModeWeight r)).sub_mem hx hy

theorem carrierMk38_sub (r : ℝ) (x y : ℤ → ℂ) (hx : x ∈ seqSobolev38 r) (hy : y ∈ seqSobolev38 r) :
    carrierMk38 r (x - y) (seqSobolev38_sub hx hy) = carrierMk38 r x hx - carrierMk38 r y hy :=
  carrierExt38 rfl

/-! ### The cleaned inverse on `h^m` -/

namespace BirkhoffTop38

variable (B : BirkhoffTop38)

theorem fourierSeq38_cleanΦinv (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 0) :
    fourierSeq38 (B.cleanΦinv z) = B.Tinv z := by
  rw [B.cleanΦinv_of_mem z hz, B.fourierSeq38_Φinv]

theorem Φ_cleanΦinv (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 0) : B.Φ (B.cleanΦinv z) = z := by
  rw [B.cleanΦinv_of_mem z hz, B.Φ_Φinv]

theorem sobolev_cleanΦinv38 (m : ℕ) (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 (m : ℝ)) :
    SobolevSquareSummable (m : ℝ) (physicalFourier (B.cleanΦinv z)) := by
  rw [← fourierSeq38_mem_iff, B.fourierSeq38_cleanΦinv z (seqSobolev38_natCast_mono hz)]
  exact B.mapsTo_Tinv m z hz

/-- `I_n(Φ⁻¹ z) = |z_n|²` for `z ∈ h¹` (v2 `A:eq:action`, through the field `action`). -/
theorem action_cleanΦinv38 (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 ((1 : ℕ) : ℝ)) (n : ℤ) :
    actualGapActionAllE02_38 (B.cleanΦinv z) n = ‖z n‖ ^ 2 := by
  have hz0 : z ∈ seqSobolev38 0 := seqSobolev38_natCast_mono hz
  have hs : SobolevSquareSummable 1 (physicalFourier (B.cleanΦinv z)) := by
    simpa using B.sobolev_cleanΦinv38 1 z hz
  rw [← B.sq_norm_Φ_eq_action _ hs n, B.Φ_cleanΦinv z hz0]

/-! ### S03.04: continuity of `Φ⁻¹` along projections, in every `h^m` / `H^m` -/

theorem tendsto_Tinv_proj38 (m : ℕ) (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 (m : ℝ))
    {Λ : ℕ → Finset ℤ} (hΛ : IsExhaustion38 Λ) :
    Tendsto (fun N : ℕ => carrierMk38 (m : ℝ) (B.Tinv (projFin38 (Λ N) z))
        (B.mapsTo_Tinv m _ (finiteSupport_mem_seqSobolev38 _ _ (finite_support_projFin38 (Λ N) z))))
      atTop (𝓝 (carrierMk38 (m : ℝ) (B.Tinv z) (B.mapsTo_Tinv m z hz))) := by
  have h := ((B.continuous_TinvC m).tendsto _).comp (tendsto_carrier_proj38 (m : ℝ) z hz hΛ)
  exact h

/-- **S03.04 (continuity of `Φ⁻¹`).** For `z ∈ h^m` and every increasing exhaustion,
`Φ⁻¹(P_{Λ_N} z) → Φ⁻¹ z` in `H^m` (norm `physicalSobolevL2 m`), for a fixed `m`. -/
theorem tendsto_Φinv_proj_sobolev38 (m : ℕ) (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 (m : ℝ))
    {Λ : ℕ → Finset ℤ} (hΛ : IsExhaustion38 Λ) :
    ∃ h : ∀ N : ℕ, SobolevSquareSummable (m : ℝ)
        (physicalFourier ((B.cleanΦinv (projFin38 (Λ N) z) - B.cleanΦinv z : PhysicalL2))),
      Tendsto (fun N : ℕ => ‖physicalSobolevL2 (m : ℝ)
        (B.cleanΦinv (projFin38 (Λ N) z) - B.cleanΦinv z : PhysicalL2) (h N)‖) atTop (𝓝 0) := by
  have hP : ∀ N : ℕ, projFin38 (Λ N) z ∈ seqSobolev38 (m : ℝ) := fun N =>
    finiteSupport_mem_seqSobolev38 _ _ (finite_support_projFin38 (Λ N) z)
  have hfs : ∀ N : ℕ, fourierSeq38 (B.cleanΦinv (projFin38 (Λ N) z) - B.cleanΦinv z) =
      B.Tinv (projFin38 (Λ N) z) - B.Tinv z := by
    intro N
    rw [fourierSeq38_sub, B.fourierSeq38_cleanΦinv _ (seqSobolev38_natCast_mono (hP N)),
      B.fourierSeq38_cleanΦinv _ (seqSobolev38_natCast_mono hz)]
  have hmem : ∀ N : ℕ, B.Tinv (projFin38 (Λ N) z) - B.Tinv z ∈ seqSobolev38 (m : ℝ) := fun N =>
    seqSobolev38_sub (B.mapsTo_Tinv m _ (hP N)) (B.mapsTo_Tinv m z hz)
  have h : ∀ N : ℕ, SobolevSquareSummable (m : ℝ)
      (physicalFourier ((B.cleanΦinv (projFin38 (Λ N) z) - B.cleanΦinv z : PhysicalL2))) := fun N => by
    rw [← fourierSeq38_mem_iff, hfs N]; exact hmem N
  refine ⟨h, ?_⟩
  have key := tendsto_iff_norm_sub_tendsto_zero.1 (B.tendsto_Tinv_proj38 m z hz hΛ)
  refine key.congr (fun N => ?_)
  rw [norm_physicalSobolevL2_eq_carrier38]
  have e : carrierMk38 (m : ℝ) (fourierSeq38
      (B.cleanΦinv (projFin38 (Λ N) z) - B.cleanΦinv z)) ((fourierSeq38_mem_iff _ _).2 (h N)) =
      carrierMk38 (m : ℝ) (B.Tinv (projFin38 (Λ N) z)) (B.mapsTo_Tinv m _ (hP N)) -
      carrierMk38 (m : ℝ) (B.Tinv z) (B.mapsTo_Tinv m z hz) := by
    rw [← carrierMk38_sub]
    exact carrierExt38 (by simp [hfs N])
  rw [e]

end BirkhoffTop38

/-! ### The reflection into the complex `H¹` carrier, and continuity of the gap integrals (S03.05) -/

/-- `(reflect y)_n = -y_{-n}`: the reflected Fourier sign `𝓕u_n = -û(-n)` of v2 (l.178). -/
def reflect38 (y : ℤ → ℂ) : ℤ → ℂ := fun n => -y (-n)

theorem reflect38_mem {r : ℝ} {y : ℤ → ℂ} (hy : y ∈ seqSobolev38 r) : reflect38 y ∈ seqSobolev38 r := by
  rw [mem_seqSobolev38_iff] at hy ⊢
  unfold SobolevSquareSummable at hy ⊢
  rw [← (Equiv.neg ℤ).summable_iff] at hy
  refine hy.congr (fun n => ?_)
  have hb : japaneseBracket (-n) = japaneseBracket n := by simp [japaneseBracket]
  simp only [Function.comp, Equiv.neg_apply, reflect38, norm_neg, hb]

theorem seqSobolev38_natCast_one : seqSobolev38 ((1 : ℕ) : ℝ) = seqSobolev38 1 := by
  rw [Nat.cast_one]

/-- A sequence of `h¹` (carrier at `((1:ℕ):ℝ)`) reflected into the complex weighted `H¹` carrier of
the Schur bridge `physicalH1ComplexCarrierToL2Actual22`. -/
def reflH1_38 (x : SobolevCarrier38 ((1 : ℕ) : ℝ)) :
    WeightedHilbert (sobolevModeWeight (1 : ℝ)) :=
  ⟨reflect38 (carrierCoe38 _ x), by
    have h := reflect38_mem (carrierCoe38_mem _ x)
    rw [seqSobolev38_natCast_one] at h
    exact h⟩

theorem reflH1_38_apply (x : SobolevCarrier38 ((1 : ℕ) : ℝ)) (n : ℤ) :
    (reflH1_38 x : ℤ → ℂ) n = -carrierCoe38 _ x (-n) := rfl

theorem norm_reflH1_sub38 (x y : SobolevCarrier38 ((1 : ℕ) : ℝ)) :
    ‖reflH1_38 x - reflH1_38 y‖ = ‖x - y‖ := by
  have h1 := weightedHilbert_norm_sq (sobolevModeWeight (1 : ℝ)) (reflH1_38 x - reflH1_38 y)
  have h2 := (carrier_hasSum_norm_sq38 ((1 : ℕ) : ℝ) (x - y)).tsum_eq
  have h3 : ∑' n : ℤ, sobolevModeWeight (1 : ℝ) n *
      ‖((reflH1_38 x - reflH1_38 y : WeightedHilbert (sobolevModeWeight (1 : ℝ))) : ℤ → ℂ) n‖ ^ 2 =
      ∑' n : ℤ, sobolevModeWeight ((1 : ℕ) : ℝ) n * ‖carrierCoe38 ((1 : ℕ) : ℝ) (x - y) n‖ ^ 2 := by
    rw [← tsum_comp_neg (fun n : ℤ => sobolevModeWeight ((1 : ℕ) : ℝ) n *
      ‖carrierCoe38 ((1 : ℕ) : ℝ) (x - y) n‖ ^ 2)]
    refine tsum_congr (fun n => ?_)
    have e : ((reflH1_38 x - reflH1_38 y : WeightedHilbert (sobolevModeWeight (1 : ℝ))) :
        ℤ → ℂ) n = -(carrierCoe38 ((1 : ℕ) : ℝ) (x - y) (-n)) := by
      show -(carrierCoe38 ((1 : ℕ) : ℝ) x (-n)) - -(carrierCoe38 ((1 : ℕ) : ℝ) y (-n)) =
        -(carrierCoe38 ((1 : ℕ) : ℝ) x (-n) - carrierCoe38 ((1 : ℕ) : ℝ) y (-n))
      ring
    have hw1 : sobolevModeWeight ((1 : ℕ) : ℝ) n = sobolevModeWeight 1 n := by rw [Nat.cast_one]
    rw [e, norm_neg, sobolevModeWeight_neg, hw1]
  have h4 : ‖reflH1_38 x - reflH1_38 y‖ ^ 2 = ‖x - y‖ ^ 2 := by
    rw [h1, h3, h2]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h4

theorem continuous_reflH1_38 : Continuous reflH1_38 := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) (fun x y => ?_)).continuous
  rw [dist_eq_norm, dist_eq_norm, norm_reflH1_sub38]
  simp

/-- The gap integral as a function on the real `h¹` carrier. -/
def gapFn38 (c : ℕ → ℝ) (n : ℤ) (x : SobolevCarrier38 ((1 : ℕ) : ℝ)) : ℝ :=
  gapIntegral38 c (NlsGge.Schur.physicalH1ComplexCarrierToL2Actual22 (reflH1_38 x)) n

/-- **E03-cont transported** (v2 `A:eq:gapcontinuous`): `x ↦ (2/π)∫_{g_n} W(2λ) v dλ` is continuous
on the real `h¹` carrier of the Birkhoff coordinates of `Φ⁻¹x`'s Fourier sequence; closed gaps
included. -/
theorem continuous_gapFn38 (c : ℕ → ℝ) (hW : Continuous (weight c)) (n : ℤ) :
    Continuous (gapFn38 c n) :=
  (actualGapAction_continuous_E02_38 n (weight c) hW).comp continuous_reflH1_38

theorem physicalH1_reflH1_fourierSeq38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    NlsGge.Schur.physicalH1ComplexCarrierToL2Actual22
      (reflH1_38 (carrierMk38 ((1 : ℕ) : ℝ) (fourierSeq38 u)
        ((fourierSeq38_mem_iff _ u).2 (by simpa using hu)))) = u := by
  apply fourierSeq38_injective
  funext n
  rw [fourierSeq38_apply, NlsGge.Schur.physicalH1ComplexCarrierToL2Actual22_fourier,
    reflH1_38_apply]
  show _ = fourierSeq38 u n
  simp [fourierSeq38_apply]

theorem gapIntegral38_eq_gapFn38 (c : ℕ → ℝ) (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (n : ℤ) :
    gapIntegral38 c u n = gapFn38 c n (carrierMk38 ((1 : ℕ) : ℝ) (fourierSeq38 u)
        ((fourierSeq38_mem_iff _ u).2 (by simpa using hu))) := by
  unfold gapFn38
  rw [physicalH1_reflH1_fourierSeq38 u hu]

namespace BirkhoffTop38

variable (B : BirkhoffTop38)

/-- **S03.05.** For each fixed gap `n` (closing gaps included), the gap integral of
`Φ⁻¹(P_{Λ_N} z)` converges to that of `Φ⁻¹ z`, for `z ∈ h¹` and every exhaustion. -/
theorem tendsto_gapIntegral_proj38 (c : ℕ → ℝ) (hW : Continuous (weight c)) (z : ℤ → ℂ)
    (hz : z ∈ seqSobolev38 ((1 : ℕ) : ℝ)) {Λ : ℕ → Finset ℤ} (hΛ : IsExhaustion38 Λ) (n : ℤ) :
    Tendsto (fun N : ℕ => gapIntegral38 c (B.cleanΦinv (projFin38 (Λ N) z)) n) atTop
      (𝓝 (gapIntegral38 c (B.cleanΦinv z) n)) := by
  have hP : ∀ N : ℕ, projFin38 (Λ N) z ∈ seqSobolev38 ((1 : ℕ) : ℝ) := fun N =>
    finiteSupport_mem_seqSobolev38 _ _ (finite_support_projFin38 (Λ N) z)
  have h := ((continuous_gapFn38 c hW n).tendsto _).comp (B.tendsto_Tinv_proj38 1 z hz hΛ)
  have e : ∀ (w : ℤ → ℂ) (hw : w ∈ seqSobolev38 ((1 : ℕ) : ℝ)),
      gapIntegral38 c (B.cleanΦinv w) n =
        gapFn38 c n (carrierMk38 ((1 : ℕ) : ℝ) (B.Tinv w) (B.mapsTo_Tinv 1 w hw)) := by
    intro w hw
    have hs : SobolevSquareSummable 1 (physicalFourier (B.cleanΦinv w)) := by
      simpa using B.sobolev_cleanΦinv38 1 w hw
    rw [gapIntegral38_eq_gapFn38 c _ hs n]
    congr 1
    exact carrierExt38 (by
      show fourierSeq38 (B.cleanΦinv w) = B.Tinv w
      exact B.fourierSeq38_cleanΦinv w (seqSobolev38_natCast_mono hw))
  rw [e z hz]
  refine h.congr (fun N => ?_)
  rw [e _ (hP N)]
  rfl

end BirkhoffTop38

/-! ### S03.04 (pathwise `H¹` bound), S03.06 (domination), S03.07 and the pathwise lemma -/

namespace BirkhoffTop38

variable (B : BirkhoffTop38)

/-- `‖Φ⁻¹ z‖_{H¹} = ‖T⁻¹ z‖_{h¹}` (reflection invariance of `⟨n⟩`). -/
theorem norm_physicalSobolevL2_cleanΦinv38 (w : ℤ → ℂ) (hw : w ∈ seqSobolev38 ((1 : ℕ) : ℝ))
    (h : SobolevSquareSummable 1 (physicalFourier (B.cleanΦinv w))) :
    ‖physicalSobolevL2 1 (B.cleanΦinv w) h‖ =
      ‖carrierMk38 ((1 : ℕ) : ℝ) (B.Tinv w) (B.mapsTo_Tinv 1 w hw)‖ := by
  rw [norm_physicalSobolevL2_eq_carrier38]
  have hs : fourierSeq38 (B.cleanΦinv w) ∈ seqSobolev38 ((1 : ℕ) : ℝ) := by
    rw [seqSobolev38_natCast_one]; exact (fourierSeq38_mem_iff 1 _).2 h
  rw [norm_carrierMk_congr38 (Nat.cast_one (R := ℝ)).symm _ _ hs]
  congr 1
  exact carrierExt38 (by
    show fourierSeq38 (B.cleanΦinv w) = B.Tinv w
    exact B.fourierSeq38_cleanΦinv w (seqSobolev38_natCast_mono hw))

/-- **S03.04.** For `z ∈ h¹` and every exhaustion the `H¹` norms of all `Φ⁻¹(P_{Λ_N} z)` and of
`Φ⁻¹ z` are bounded by one finite constant `B ≥ 1` (a convergent sequence is bounded). -/
theorem exists_H1_bound38 (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 ((1 : ℕ) : ℝ)) {Λ : ℕ → Finset ℤ}
    (hΛ : IsExhaustion38 Λ) :
    ∃ Bd : ℝ, 1 ≤ Bd ∧
      (∀ (N : ℕ) (h : SobolevSquareSummable 1 (physicalFourier (B.cleanΦinv (projFin38 (Λ N) z)))),
        ‖physicalSobolevL2 1 (B.cleanΦinv (projFin38 (Λ N) z)) h‖ ≤ Bd) ∧
      (∀ h : SobolevSquareSummable 1 (physicalFourier (B.cleanΦinv z)),
        ‖physicalSobolevL2 1 (B.cleanΦinv z) h‖ ≤ Bd) := by
  have hP : ∀ N : ℕ, projFin38 (Λ N) z ∈ seqSobolev38 ((1 : ℕ) : ℝ) := fun N =>
    finiteSupport_mem_seqSobolev38 _ _ (finite_support_projFin38 (Λ N) z)
  have ht := (B.tendsto_Tinv_proj38 1 z hz hΛ).norm
  obtain ⟨M, hM⟩ := ht.bddAbove_range
  refine ⟨max 1 (max M ‖carrierMk38 ((1 : ℕ) : ℝ) (B.Tinv z) (B.mapsTo_Tinv 1 z hz)‖),
    le_max_left _ _, fun N h => ?_, fun h => ?_⟩
  · rw [B.norm_physicalSobolevL2_cleanΦinv38 _ (hP N) h]
    exact (hM ⟨N, rfl⟩).trans ((le_max_left _ _).trans (le_max_right _ _))
  · rw [B.norm_physicalSobolevL2_cleanΦinv38 _ hz h]
    exact (le_max_right _ _).trans (le_max_right _ _)

/-- **S03.06 (domination).** For every `Bd ≥ 1` there is `C_B` (depending only on the weight bounds
and `Bd`) such that for every `w ∈ h¹` with `‖Φ⁻¹w‖_{H¹} ≤ Bd`, every summand of v2
`A:eq:remainder` is at most `C_B a_n |w_n|² ⟨n⟩^{-3/2}` in absolute value
(v2 `A:eq:symbolcomparison`, `A:eq:remainderbound`, `I_n(Φ⁻¹w) = |w_n|²`). -/
theorem remainderSummand_dominated38 (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) (Bd : ℝ) (hBd : 1 ≤ Bd) :
    ∃ CB : ℝ, 0 < CB ∧ ∀ w : ℤ → ℂ, w ∈ seqSobolev38 ((1 : ℕ) : ℝ) →
      (∀ h : SobolevSquareSummable 1 (physicalFourier (B.cleanΦinv w)),
        ‖physicalSobolevL2 1 (B.cleanΦinv w) h‖ ≤ Bd) →
      ∀ n : ℤ, |remainderSummand38 c (B.cleanΦinv w) n| ≤ CB * (tailWeight38 c n * ‖w n‖ ^ 2) := by
  have hle : lower ≤ upper := (hbound 0).trans (hupper 0)
  obtain ⟨CB, hCB, hCBP⟩ := NlsGge.Weights.uniformSymbolGap38 lower upper hlower hle Bd hBd
  refine ⟨CB, hCB, fun w hw hn n => ?_⟩
  have hs : SobolevSquareSummable 1 (physicalFourier (B.cleanΦinv w)) := by
    simpa using B.sobolev_cleanΦinv38 1 w hw
  have hW := weight_continuous38 hlower hbound hupper
  have h1 := abs_remainderSummand_le38 c hW (B.cleanΦinv w) n
    (CB * fullWeightRate c n * japaneseBracket n ^ (-(3 / 2) : ℝ))
    (fun l hl => (hCBP c hbound hupper _ hs (hn hs) n l hl).2)
  rw [B.action_cleanΦinv38 w hw n] at h1
  refine h1.trans (le_of_eq ?_)
  unfold tailWeight38
  ring

end BirkhoffTop38

namespace BirkhoffTop38

variable (B : BirkhoffTop38)

theorem mem_seqSobolev38_of_Omega038 (c : ℕ → ℝ) {z : ℤ → ℂ} (hz : z ∈ Omega038 c) (m : ℕ) :
    z ∈ seqSobolev38 (m : ℝ) := (mem_seqSobolev38_iff _ _).2 (hz.1 m)

/-- The cleaned finite-gap field `Φ⁻¹(P_Λ z)` has `H^m` regularity for all `m`, finitely many open
gaps, and satisfies `I_n = 1_{n∈Λ}|z_n|²` (v2 proof of `A:lem:remainderconvergence`). -/
theorem finiteGap_structure38 (Λ : Finset ℤ) (z : ℤ → ℂ) :
    SobolevSquareSummable 1 (physicalFourier (B.cleanΦinv (projFin38 Λ z))) ∧
    {n : ℤ | actualGapLowerAllE02_38 (B.cleanΦinv (projFin38 Λ z)) n <
      actualGapUpperAllE02_38 (B.cleanΦinv (projFin38 Λ z)) n}.Finite ∧
    ∀ n : ℤ, actualGapActionAllE02_38 (B.cleanΦinv (projFin38 Λ z)) n =
      if n ∈ Λ then ‖z n‖ ^ 2 else 0 := by
  have hfs := finite_support_projFin38 Λ z
  have h0 : projFin38 Λ z ∈ seqSobolev38 0 := finiteSupport_mem_seqSobolev38 0 _ hfs
  obtain ⟨-, hsob, hΦ, hfin⟩ := B.finiteSupport_regular_finiteGaps _ hfs
  rw [← B.cleanΦinv_of_mem _ h0] at hsob hΦ hfin
  refine ⟨by simpa using hsob 1, hfin, fun n => ?_⟩
  have hs : SobolevSquareSummable 1 (physicalFourier (B.cleanΦinv (projFin38 Λ z))) := by
    simpa using hsob 1
  rw [← B.sq_norm_Φ_eq_action _ hs n, hΦ]
  by_cases hn : n ∈ Λ
  · rw [projFin38_apply_of_mem hn]; simp only [hn, ↓reduceIte]
  · rw [projFin38_apply_of_not_mem hn]; simp only [hn, ↓reduceIte, norm_zero]; norm_num

/-- **S03.07 input.** Every finite-gap remainder `R_W(Φ⁻¹ P_Λ z)` is summable and nonnegative, and
equals `E_W(u) - ∑_{n∈Λ} a_n|z_n|²` (v2 `A:eq:rates`). -/
theorem remainder38_finiteGap_proj (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) (Λ : Finset ℤ) (z : ℤ → ℂ) :
    Summable (fun n : ℤ => remainderSummand38 c (B.cleanΦinv (projFin38 Λ z)) n) ∧
    remainder38 c (B.cleanΦinv (projFin38 Λ z)) =
      (2 / Real.pi) * (∫ l : ℝ, weight c (2 * l) *
        actualGapHeightE02_38 (B.cleanΦinv (projFin38 Λ z)) l) -
      ∑ n ∈ Λ, fullWeightRate c n * ‖z n‖ ^ 2 ∧
    0 ≤ remainder38 c (B.cleanΦinv (projFin38 Λ z)) := by
  obtain ⟨hs, hfin, hact⟩ := B.finiteGap_structure38 Λ z
  obtain ⟨h1, -, h3, h4⟩ := remainder38_finiteGap lower upper c hlower hbound hupper _ hs hfin
  refine ⟨h1, ?_, h4⟩
  rw [h3]
  congr 1
  simp_rw [hact]
  rw [tsum_eq_sum (s := Λ) (fun n hn => by simp [hn])]
  exact Finset.sum_congr rfl (fun n hn => by simp [hn])

/-- **Pathwise remainder convergence (S03.03-S03.07).** For a fixed `z ∈ Ω₀` (`z ∈ ⋂ h^m` and the
tail series finite) and EVERY increasing exhaustion `Λ_N ↑ ℤ`:
the series `R_W(Φ⁻¹z)` and every `R_W(Φ⁻¹P_{Λ_N}z)` are summable, the finite-gap remainders are
nonnegative, `R_W(Φ⁻¹P_{Λ_N}z) → R_W(Φ⁻¹z)`, and the limit is nonnegative (hence finite, in
`[0,∞)`). No expectation of the sample-dependent constant is used. -/
theorem remainder_tendsto_pathwise38 (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) (z : ℤ → ℂ)
    (hz : z ∈ Omega038 c) {Λ : ℕ → Finset ℤ} (hΛ : IsExhaustion38 Λ) :
    Summable (fun n : ℤ => remainderSummand38 c (B.cleanΦinv z) n) ∧
    (∀ N : ℕ, Summable (fun n : ℤ => remainderSummand38 c (B.cleanΦinv (projFin38 (Λ N) z)) n)) ∧
    Tendsto (fun N : ℕ => remainder38 c (B.cleanΦinv (projFin38 (Λ N) z))) atTop
      (𝓝 (remainder38 c (B.cleanΦinv z))) ∧
    (∀ N : ℕ, 0 ≤ remainder38 c (B.cleanΦinv (projFin38 (Λ N) z))) ∧
    0 ≤ remainder38 c (B.cleanΦinv z) := by
  have hW := weight_continuous38 hlower hbound hupper
  have hz1 : z ∈ seqSobolev38 ((1 : ℕ) : ℝ) := mem_seqSobolev38_of_Omega038 c hz 1
  have hP : ∀ N : ℕ, projFin38 (Λ N) z ∈ seqSobolev38 ((1 : ℕ) : ℝ) := fun N =>
    finiteSupport_mem_seqSobolev38 _ _ (finite_support_projFin38 (Λ N) z)
  obtain ⟨Bd, hBd1, hBdN, hBdz⟩ := B.exists_H1_bound38 z hz1 hΛ
  obtain ⟨CB, hCB, hdom⟩ := B.remainderSummand_dominated38 lower upper c hlower hbound hupper Bd hBd1
  set bound : ℤ → ℝ := fun n => CB * (tailWeight38 c n * ‖z n‖ ^ 2) with hbd
  have hbsum : Summable bound := hz.2.mul_left CB
  -- domination of every term, uniformly in N
  have hdomN : ∀ N n, |remainderSummand38 c (B.cleanΦinv (projFin38 (Λ N) z)) n| ≤ bound n := by
    intro N n
    refine (hdom _ (hP N) (fun h => hBdN N h) n).trans ?_
    have hw := tailWeight38_nonneg lower upper c hlower hbound hupper n
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hw) hCB.le
    by_cases hn : n ∈ Λ N
    · rw [projFin38_apply_of_mem hn]
    · rw [projFin38_apply_of_not_mem hn, norm_zero]
      simp
  have hdomz : ∀ n, |remainderSummand38 c (B.cleanΦinv z) n| ≤ bound n :=
    fun n => hdom z hz1 (fun h => hBdz h) n
  -- termwise convergence
  have hterm : ∀ n : ℤ, Tendsto (fun N : ℕ => remainderSummand38 c (B.cleanΦinv (projFin38 (Λ N) z)) n)
      atTop (𝓝 (remainderSummand38 c (B.cleanΦinv z) n)) := by
    intro n
    have hg := B.tendsto_gapIntegral_proj38 c hW z hz1 hΛ n
    have hI : ∀ᶠ N in atTop, actualGapActionAllE02_38 (B.cleanΦinv (projFin38 (Λ N) z)) n =
        actualGapActionAllE02_38 (B.cleanΦinv z) n := by
      filter_upwards [hΛ.eventually_mem n] with N hN
      rw [B.action_cleanΦinv38 _ (hP N), B.action_cleanΦinv38 _ hz1, projFin38_apply_of_mem hN]
    have hI' : Tendsto (fun N : ℕ => actualGapActionAllE02_38 (B.cleanΦinv (projFin38 (Λ N) z)) n)
        atTop (𝓝 (actualGapActionAllE02_38 (B.cleanΦinv z) n)) :=
      tendsto_const_nhds.congr' (hI.mono fun N hN => hN.symm)
    exact hg.sub (hI'.const_mul (fullWeightRate c n))
  have hsumz : Summable (fun n : ℤ => remainderSummand38 c (B.cleanΦinv z) n) :=
    Summable.of_norm_bounded hbsum (fun n => by rw [Real.norm_eq_abs]; exact hdomz n)
  have hfin := fun N : ℕ => B.remainder38_finiteGap_proj lower upper c hlower hbound hupper (Λ N) z
  have hlim : Tendsto (fun N : ℕ => remainder38 c (B.cleanΦinv (projFin38 (Λ N) z))) atTop
      (𝓝 (remainder38 c (B.cleanΦinv z))) :=
    tendsto_tsum_of_dominated_convergence hbsum hterm
      (Filter.Eventually.of_forall fun N n => by rw [Real.norm_eq_abs]; exact hdomN N n)
  refine ⟨hsumz, fun N => (hfin N).1, hlim, fun N => (hfin N).2.2, ?_⟩
  exact ge_of_tendsto' hlim (fun N => (hfin N).2.2)

end BirkhoffTop38


/-- **S03 (v2 `A:lem:remainderconvergence`), conditional on the E01 input `B`.**
There is a measurable probability-one set `Ω₀` for `γ_W` (chosen before, and independently of, any
exhaustion) such that for EVERY `z ∈ Ω₀` and EVERY increasing exhaustion `Λ_N ↑ ℤ` by finite sets,
`R_W(Φ⁻¹ P_{Λ_N} z) → R_W(Φ⁻¹ z) ∈ [0,∞)`, where each `R_W` is the series of
`A:eq:remainder`, summable on `Ω₀`, and the finite-gap remainders are nonnegative. -/
theorem remainder_convergence_S03_38 (B : BirkhoffTop38) (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) :
    ∃ Ω : Set (ℤ → ℂ), MeasurableSet Ω ∧ fullWeightSequenceGaussian c Ωᶜ = 0 ∧
      ∀ z ∈ Ω, Summable (fun n : ℤ => remainderSummand38 c (B.cleanΦinv z) n) ∧
        0 ≤ remainder38 c (B.cleanΦinv z) ∧
        ∀ Λ : ℕ → Finset ℤ, IsExhaustion38 Λ →
          (∀ N : ℕ, Summable (fun n : ℤ =>
            remainderSummand38 c (B.cleanΦinv (projFin38 (Λ N) z)) n)) ∧
          (∀ N : ℕ, 0 ≤ remainder38 c (B.cleanΦinv (projFin38 (Λ N) z))) ∧
          Tendsto (fun N : ℕ => remainder38 c (B.cleanΦinv (projFin38 (Λ N) z))) atTop
            (𝓝 (remainder38 c (B.cleanΦinv z))) :=
  ⟨Omega038 c, measurableSet_Omega038 lower upper c hlower hbound hupper,
    fullWeightSequenceGaussian_Omega038_compl lower upper c hlower hbound hupper,
    fun z hz => by
      -- the standard exhaustion `[-N, N]` gives the nonnegativity/summability of the limit
      have hΛ0 : IsExhaustion38 (fun N : ℕ => Finset.Icc (-(N : ℤ)) N) :=
        ⟨fun a b hab => Finset.Icc_subset_Icc (by omega) (by exact_mod_cast hab),
          fun n => ⟨n.natAbs, Finset.mem_Icc.2 ⟨by omega, by omega⟩⟩⟩
      obtain ⟨h1, -, -, -, h5⟩ := B.remainder_tendsto_pathwise38 lower upper c hlower hbound hupper
        z hz hΛ0
      refine ⟨h1, h5, fun Λ hΛ => ?_⟩
      obtain ⟨-, h2, h3, h4, -⟩ := B.remainder_tendsto_pathwise38 lower upper c hlower hbound hupper
        z hz hΛ
      exact ⟨h2, h4, h3⟩⟩

end NlsGge.Birkhoff
end
