import NlsGge.Birkhoff.F08Bare38f

/-! # F08 / L06.08(a) (user decision D4): `m = 2` Fourier-truncated Gibbs convergence on `H^s`, `s < 3/2`

`L06_08a_38`: the bare Fourier measures `ν_{2,N}`, regarded on `H^s` (`s < 3/2`), converge weakly to
`alQ4Rho38 s β₀ β₁ β₂`, and the relative normalizers converge to `alQ4Z2_38`.  This is the
`m = 2` case of the F08 argument (`F08_tests_tendsto38`, test functions bounded and
a.s. convergent) combined with the F05 identification `L06_08b_38`.  The topology `H^s` with
`1 < s < 3/2` needs the extra step that `γ_2` charges `H^s` and `P_N U → U` there; this is proved
here (`ae_summable_sob38`, `ae_planeElement_tendsto38`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory ProbabilityTheory Filter Topology NlsGge.Measure NlsGge.Pilot
  NlsGge.HierarchyRiccati.Core NlsGge.Sobolev38 NlsGge.SpectralFoundations NlsGge.AblowitzLadik
open scoped ENNReal BoundedContinuousFunction

/-- The Fourier-plane law `dν = 𝒵⁻¹ e^{-E_m(v)} ∏ d²û(n)` in plane coordinates. -/
def nuPlane38 (m : ℕ) (β : ℕ → ℝ) (N : ℕ) : Measure (FourierPlane N) :=
  (finiteComplexVolume (Fin (2 * N + 1))).withDensity
    (fun z => ENNReal.ofReal (Real.exp (-(EmPlane38 m β N z)) / ZcalBare38 m β N))

/-- The bare Fourier measure `ν_{m,N}` regarded as a measure on `H^s` (any `s`). -/
def nuBareS38 (m : ℕ) (β : ℕ → ℝ) (N : ℕ) (s : ℝ) : Measure (SobolevHilbert s) :=
  (nuPlane38 m β N).map (planeElement38 s N)

theorem nuBare38_eq_nuBareS38 (m : ℕ) (β : ℕ → ℝ) (N : ℕ) :
    nuBare38 m β N = nuBareS38 m β N ((m - 1 : ℕ) : ℝ) := rfl

section Plane

variable {m : ℕ} {β : ℕ → ℝ} (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)

include hm hβ in
theorem isProbabilityMeasure_nuPlane38 (N : ℕ) : IsProbabilityMeasure (nuPlane38 m β N) := by
  have h := isProbabilityMeasure_nuBare38 hm hβ N
  have hpe : Measurable (planeElement38 ((m - 1 : ℕ) : ℝ) N) := measurable_finiteElement38 _ _
  refine ⟨?_⟩
  have := h.measure_univ
  unfold nuBare38 at this
  rw [Measure.map_apply hpe MeasurableSet.univ, Set.preimage_univ] at this
  exact this

include hm hβ in
theorem isProbabilityMeasure_nuBareS38 (N : ℕ) (s : ℝ) : IsProbabilityMeasure (nuBareS38 m β N s) := by
  have := isProbabilityMeasure_nuPlane38 hm hβ N
  unfold nuBareS38
  exact (Measure.isProbabilityMeasure_map_iff (measurable_finiteElement38 _ _).aemeasurable).2 inferInstance

include hm hβ in
/-- `∫ g dν_{m,N} = E[g(P_N U) e^{-V_m(P_N U)}] / E[e^{-V_m(P_N U)}]` on the plane. -/
theorem integral_nuPlane38 (N : ℕ) (g : FourierPlane N → ℝ) (hg : Measurable g) :
    ∫ z, g z ∂(nuPlane38 m β N) =
      (∫ ω, g (NlsGge.Ramer.windowProj N ω) * weightN38 m β N ω ∂(gammaM38 m β)) /
        ∫ ω, weightN38 m β N ω ∂(gammaM38 m β) := by
  have hZ := ZcalBare_pos38 hm hβ N
  have hdens : Measurable (fun z : FourierPlane N =>
      ENNReal.ofReal (Real.exp (-(EmPlane38 m β N z)) / ZcalBare38 m β N)) :=
    (Real.measurable_exp.comp (measurable_EmPlane38 hm hβ N).neg |>.div_const _).ennreal_ofReal
  unfold nuPlane38
  rw [integral_withDensity_eq_integral_toReal_smul hdens
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have h1 : ∀ z : FourierPlane N,
      (ENNReal.ofReal (Real.exp (-(EmPlane38 m β N z)) / ZcalBare38 m β N)).toReal • g z =
      (ZcalBare38 m β N)⁻¹ * (g z * Real.exp (-(EmPlane38 m β N z))) := by
    intro z
    rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hZ.le), smul_eq_mul]
    field_simp
  simp_rw [h1]
  rw [integral_const_mul, integral_bare38 hm hβ N g hg, ZcalBare_eq38 hm hβ N]
  have := (gaussConst_pos38 hm hβ N).ne'
  have h2 := (integral_weightN_pos38 hm hβ N).ne'
  field_simp
  rfl

include hm hβ in
theorem integral_nuBareS38 (N : ℕ) (s : ℝ) (F : SobolevHilbert s → ℝ) (hF : Measurable F) :
    ∫ u, F u ∂(nuBareS38 m β N s) =
      (∫ ω, F (planeElement38 s N (NlsGge.Ramer.windowProj N ω)) * weightN38 m β N ω
        ∂(gammaM38 m β)) / ∫ ω, weightN38 m β N ω ∂(gammaM38 m β) := by
  have hpe : Measurable (planeElement38 s N) := measurable_finiteElement38 _ _
  unfold nuBareS38
  rw [integral_map hpe.aemeasurable hF.aestronglyMeasurable]
  exact integral_nuPlane38 hm hβ N _ (hF.comp hpe)

end Plane

section Sobolev

theorem planeElement_window_coeff38 (r : ℝ) (N : ℕ) (ω : ℤ → ℂ) (n : ℤ) :
    (show WeightedHilbert (sobolevModeWeight r) from
      planeElement38 r N (NlsGge.Ramer.windowProj N ω)) n =
      if n ∈ Finset.Icc (-(N : ℤ)) N then ω n else 0 := by
  unfold planeElement38
  rw [finiteElement_apply38 _ _ _ (modeIndex_injective N) n]
  by_cases hn : n ∈ Finset.Icc (-(N : ℤ)) N
  · simp only [hn, ↓reduceIte]
    obtain ⟨i, hi⟩ := modeIndex_covers N n (Finset.mem_Icc.1 hn).1 (Finset.mem_Icc.1 hn).2
    rw [← hi, finiteSeq_of_inj38 _ _ (modeIndex_injective N)]
    rfl
  · simp only [hn, ↓reduceIte]
    unfold finiteSeq38
    refine Finset.sum_eq_zero fun i _ => ?_
    have hne : modeIndex N i ≠ n := fun h => hn (h ▸ Finset.mem_Icc.2 (modeIndex_bounds N i))
    simp [hne]

/-- If `ω ∈ h^s`, then `P_N ω → ω` in `H^s` (plane elements in `H^s`). -/
theorem tendsto_planeElement38 (s : ℝ) (ω : ℤ → ℂ)
    (hω : Summable (fun n : ℤ => sobolevModeWeight s n * ‖ω n‖ ^ 2)) :
    Tendsto (fun N : ℕ => planeElement38 s N (NlsGge.Ramer.windowProj N ω)) atTop
      (𝓝 (seqRealization38 (sobolevModeWeight s) ω)) := by
  have heq : ∀ N : ℕ, planeElement38 s N (NlsGge.Ramer.windowProj N ω) =
      truncSobolev38 s N (seqRealization38 (sobolevModeWeight s) ω) := by
    intro N
    apply Subtype.ext
    funext n
    change (show WeightedHilbert (sobolevModeWeight s) from
        planeElement38 s N (NlsGge.Ramer.windowProj N ω)) n =
      (show WeightedHilbert (sobolevModeWeight s) from
        truncSobolev38 s N (seqRealization38 (sobolevModeWeight s) ω)) n
    rw [planeElement_window_coeff38, truncSobolev38_apply, seqRealization_apply38 _ ω hω n]
  simp_rw [heq]
  exact tendsto_truncSobolev38 _ _

variable {β₀ β₁ β₂ : ℝ}

/-- `γ_2` charges `H^s`, `s < 3/2`: `Σ ⟨n⟩^{2s}|ω_n|² < ∞` almost surely (`a_{2,n} ≳ ⟨n⟩⁴`). -/
theorem ae_summable_sob38 (h0 : 0 < β₀) (h1 : 0 < β₁) (h2 : 0 < β₂) (s : ℝ) (hs : s < 3 / 2) :
    ∀ᵐ ω ∂(gammaM38 2 (alQ4Beta38 β₀ β₁ β₂)),
      Summable (fun n : ℤ => sobolevModeWeight s n * ‖ω n‖ ^ 2) := by
  have hβ := hβ_alQ4Beta38 h0 h1 h2
  have hq : ∀ n : ℤ, 0 < finiteHierarchyRate38 2 (alQ4Beta38 β₀ β₁ β₂) n :=
    fun n => rate_pos38 2 _ (by omega) (fun j hj => (hβ j hj).le) (hβ 0 (Nat.zero_le _))
      (hβ 2 le_rfl) n
  refine ae_sequenceSummable (finiteHierarchyRate38 2 (alQ4Beta38 β₀ β₁ β₂)) (sobolevModeWeight s)
    hq (fun n => (Real.rpow_nonneg (japaneseBracket_pos n).le _)) ?_
  refine Summable.of_nonneg_of_le (fun n => div_nonneg (Real.rpow_nonneg (japaneseBracket_pos n).le _)
    (hq n).le) (fun n => ?_) (alQ4B_summable38 h0 h2 s hs)
  have hle : alQ4B38 β₀ β₂ n ≤ finiteHierarchyRate38 2 (alQ4Beta38 β₀ β₁ β₂) n := by
    rw [alQ4Rate_eq_hierarchy38]
    exact alQ4B_le_rateC38 h0 h1.le h2.le n
  have hw : 0 ≤ sobolevModeWeight s n := Real.rpow_nonneg (japaneseBracket_pos n).le _
  exact div_le_div_of_nonneg_left hw (alQ4B_pos38 h0 h2 n) hle

end Sobolev

section L0608a

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {β₀ β₁ β₂ : ℝ}

include B O in
/-- **L06.08(a) (user decision D4; `m = 2` of v2 `C:thm:bare` and the Fourier clause of
`C:thm:AL`).**  For `β_0, β_1, β_2 > 0` and `s < 3/2`, with `β = alQ4Beta38 β₀ β₁ β₂`:

1. the Fourier-truncated Gibbs measures `ν_{2,N}`, regarded on `H^s`, converge weakly to
   `alQ4Rho38 s β₀ β₁ β₂` (convergence of `∫ φ dν_{2,N}` for every bounded continuous `φ` on `H^s`);
2. the relative normalizers `𝒵_{2,N} / ∏_{|n|≤N} (π/a_{2,n})` converge to `alQ4Z2_38 β₀ β₁ β₂`.

Conditional on `B`, `O` (through F05 / F07). -/
theorem L06_08a_38 (h0 : 0 < β₀) (h1 : 0 < β₁) (h2 : 0 < β₂) {s : ℝ} (hs : s < 3 / 2) :
    (∀ φ : SobolevHilbert s →ᵇ ℝ,
      Tendsto (fun N : ℕ => ∫ u, φ u ∂(nuBareS38 2 (alQ4Beta38 β₀ β₁ β₂) N s)) atTop
        (𝓝 (∫ u, φ u ∂(alQ4Rho38 s β₀ β₁ β₂)))) ∧
    Tendsto (fun N : ℕ => ZcalBare38 2 (alQ4Beta38 β₀ β₁ β₂) N /
      ∏ n ∈ Finset.Icc (-(N : ℤ)) N,
        (Real.pi / finiteHierarchyRate38 2 (alQ4Beta38 β₀ β₁ β₂) n)) atTop
      (𝓝 (alQ4Z2_38 β₀ β₁ β₂)) := by
  set β := alQ4Beta38 β₀ β₁ β₂ with hβdef
  have hβ := hβ_alQ4Beta38 h0 h1 h2
  have hm : 2 ≤ 2 := le_rfl
  obtain ⟨-, -, hZ, hrho⟩ := L06_08b_38 B O h0 h1 h2 s
  refine ⟨fun φ => ?_, ?_⟩
  · have hφm : Measurable (fun u : SobolevHilbert s => φ u) := φ.continuous.measurable
    have hae := ae_summable_sob38 h0 h1 h2 s hs
    have hconv : ∀ᵐ ω ∂(gammaM38 2 β), Tendsto (fun N : ℕ =>
        φ (planeElement38 s N (NlsGge.Ramer.windowProj N ω))) atTop
        (𝓝 (φ (seqRealization38 (sobolevModeWeight s) ω))) := by
      filter_upwards [hae] with ω hω
      exact (φ.continuous.tendsto _).comp (tendsto_planeElement38 s ω hω)
    have h := BirkhoffInput38.F08_tests_tendsto38 B O hm hβ
      (Gs := fun N ω => φ (planeElement38 s N (NlsGge.Ramer.windowProj N ω)))
      (G := fun ω => φ (seqRealization38 (sobolevModeWeight s) ω)) (C := ‖φ‖)
      (fun N => hφm.comp ((measurable_finiteElement38 _ _).comp (NlsGge.Ramer.measurable_windowProj N)))
      (fun N ω => by simpa using φ.norm_coe_le_norm _) hconv
    -- identify the limit
    have hlim : ∫ u, φ u ∂(alQ4Rho38 s β₀ β₁ β₂) =
        (∫ ω, φ (seqRealization38 (sobolevModeWeight s) ω) * weightInf38 2 β ω ∂(gammaM38 2 β)) /
          ZM38 B 2 β := by
      rw [← hrho, integral_map (measurable_reSob38 _ s).aemeasurable hφm.aestronglyMeasurable]
      rw [BirkhoffInput38.integral_muM38_eq B O hm hβ (fun u => φ (reSob38 ((2 - 1 : ℕ) : ℝ) s u))
        (hφm.comp (measurable_reSob38 _ s))]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [ae_summable38 (m := 2) (β := β) hm (fun j hj => (hβ j hj).le)
        (hβ 0 (Nat.zero_le _)) (hβ 2 le_rfl)] with ω hω
      have hω' : Summable (fun n : ℤ => sobolevModeWeight ((2 - 1 : ℕ) : ℝ) n * ‖ω n‖ ^ 2) := hω
      have := reSob38_realization _ s ω hω'
      simp only [gaussianRealization38, this]
      rfl
    rw [hlim]
    refine h.congr fun N => ?_
    rw [integral_nuBareS38 hm hβ N s _ hφm]
  · have := BirkhoffInput38.F08_normalizer_38 B O (m := 2) (β := β) hm hβ
    rwa [hZ] at this

end L0608a

end NlsGge.Birkhoff

end
