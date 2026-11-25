import NlsGge.Birkhoff.W11Equivalence38c

/-! # W11 (`D:thm:equivalence`), part d: weak convergence implies boundedness in probability (W11.03)

Source: `paper/v2.tex` l.1684: "Weak convergence in that space implies `eq:remainingtight`, since its embedding
into `H²` is continuous and the limiting `H²` norm is finite."

Test function: `F = 1 - χ_R` (continuous on `E_s` since `E_s ↪ h²` is continuous; `chiR38`), with
`1_{‖u‖_{H²} > 2R} ≤ 1 - χ_R ≤ 1_{‖u‖_{H²} > R}`. The limit `μ_W` lives on `H²` (S04.05: `μ_W`-a.e. field lies
in every `H^m`), so `μ_W(‖u‖_{H²} > R) → 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.HierarchyRiccati.Core NlsGge.Ramer Filter Topology
open scoped ENNReal Real

section Defs

variable {lower upper : ℝ}

/-- **(1) of `D:thm:equivalence`:** `Z_N → Z_W`. -/
def W11Normalizer38 (B : BirkhoffInput38) (c : BoundedCoefficients lower upper) : Prop :=
  Tendsto (fun N : ℕ => relativePartition38 c N) atTop (𝓝 (B.ZW38 c.val))

/-- **(3) of `D:thm:equivalence`:** `ν_{W,N} ⇀ μ_W` on `𝓕⁻¹E_s`: for every `F` bounded and continuous on
`𝓕⁻¹E_s` (i.e. `F ∘ 𝓕⁻¹ : E_s → ℝ` bounded continuous), `∫ F dν_{W,N} → ∫ F dμ_W`. -/
def W11Weak38 (B : BirkhoffInput38) (c : BoundedCoefficients lower upper) (s : ℝ) : Prop :=
  ∀ F : PhysicalL2 → ℝ, Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y)) →
    (∃ M, ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) →
    Tendsto (fun N : ℕ => ∫ u, F u ∂(nuWN38 c N)) atTop (𝓝 (∫ u, F u ∂(B.muW38 c.val)))

/-- **(4) of `D:thm:equivalence` (`eq:remainingtight`):**
`lim_{R→∞} limsup_{N→∞} ν_{W,N}(‖u‖_{H²} > R) = 0` (limsup in `[0,∞]`). -/
def W11Tight38 (c : BoundedCoefficients lower upper) : Prop :=
  Tendsto (fun R : ℝ => limsup (fun N : ℕ => nuWN38 c N (h2Tail38 R)) atTop) atTop (𝓝 0)

end Defs

section Measures

theorem measure_le_ofReal_integral_W11 {ρ : Measure PhysicalL2} (S : Set PhysicalL2)
    (hS : MeasurableSet S) (F : PhysicalL2 → ℝ) (hF : Integrable F ρ) (hF0 : ∀ u, 0 ≤ F u)
    (hSF : ∀ u ∈ S, 1 ≤ F u) : ρ S ≤ ENNReal.ofReal (∫ u, F u ∂ρ) := by
  rw [ofReal_integral_eq_lintegral_ofReal hF (Eventually.of_forall hF0), ← lintegral_indicator_one hS]
  refine lintegral_mono fun u => ?_
  by_cases hu : u ∈ S
  · simp only [Set.indicator_of_mem hu, Pi.one_apply]
    exact ENNReal.one_le_ofReal.2 (hSF u hu)
  · simp [Set.indicator_of_notMem hu]

theorem ofReal_integral_le_measure_W11 {ρ : Measure PhysicalL2} (S : Set PhysicalL2)
    (hS : MeasurableSet S) (F : PhysicalL2 → ℝ) (hF : Integrable F ρ) (hF0 : ∀ u, 0 ≤ F u)
    (hFS : ∀ u, F u ≤ S.indicator 1 u) : ENNReal.ofReal (∫ u, F u ∂ρ) ≤ ρ S := by
  rw [ofReal_integral_eq_lintegral_ofReal hF (Eventually.of_forall hF0), ← lintegral_indicator_one hS]
  refine lintegral_mono fun u => ?_
  by_cases hu : u ∈ S
  · simp only [Set.indicator_of_mem hu, Pi.one_apply] at hFS ⊢
    have := hFS u
    rw [Set.indicator_of_mem hu] at this
    exact (ENNReal.ofReal_le_ofReal this).trans (by simp)
  · have := hFS u
    rw [Set.indicator_of_notMem hu] at this
    simp only [Set.indicator_of_notMem hu]
    simpa using ENNReal.ofReal_le_ofReal this

end Measures

namespace BirkhoffInput38

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {lower upper : ℝ}
  (c : BoundedCoefficients lower upper) {s : ℝ}

include B O in
/-- For `R > 0`: `limsup_N ν_{W,N}(‖u‖_{H²} > 2R) ≤ μ_W(‖u‖_{H²} > R)`. -/
theorem limsup_tail_le_W11 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) (hweak : W11Weak38 B c s)
    {χ : ℝ → ℝ} (hχ : CutoffProfile38 χ) {R : ℝ} (hR : 0 < R) :
    limsup (fun N : ℕ => nuWN38 c N (h2Tail38 (2 * R))) atTop ≤ B.muW38 c.val (h2Tail38 R) := by
  set F : PhysicalL2 → ℝ := fun u => 1 - chiR38 χ R u with hF
  have hFc : Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y)) :=
    continuous_const.sub (continuous_chiR38_physOfE38 c s hχ hR)
  have hF0 : ∀ u, 0 ≤ F u := fun u => by
    have := chiR38_mem_Icc hχ hR u; simp only [hF]; linarith [this.2]
  have hF1 : ∀ u, F u ≤ 1 := fun u => by
    have := chiR38_mem_Icc hχ hR u; simp only [hF]; linarith [this.1]
  have hFb : ∃ M, ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M :=
    ⟨1, fun y => by rw [abs_of_nonneg (hF0 _)]; exact hF1 _⟩
  have hlim := hweak F hFc hFb
  have hprob := B.isProbabilityMeasure_muW38 lower upper c.val c.property.1 (coef_bound38 c)
    (coef_upper38 c)
  have hFmu : Integrable F (B.muW38 c.val) :=
    Integrable.of_bound (B.aestronglyMeasurable_muW38 O c hs hs' F hFc) 1
      (Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hF0 _)]; exact hF1 _)
  have hFnu : ∀ N, Integrable F (nuWN38 c N) := fun N =>
    integrable_nuWN38_W11 c s hs N F hFc 1 (fun y => by rw [abs_of_nonneg (hF0 _)]; exact hF1 _)
  have hle : ∀ N : ℕ, nuWN38 c N (h2Tail38 (2 * R)) ≤ ENNReal.ofReal (∫ u, F u ∂(nuWN38 c N)) :=
    fun N => measure_le_ofReal_integral_W11 _ (measurableSet_h2Tail38 _) F (hFnu N) hF0
      (fun u hu => by
        simp only [hF, chiR38_eq_zero_of_mem_tail hχ hR hu]; norm_num)
  have h1 : limsup (fun N : ℕ => nuWN38 c N (h2Tail38 (2 * R))) atTop ≤
      limsup (fun N : ℕ => ENNReal.ofReal (∫ u, F u ∂(nuWN38 c N))) atTop :=
    limsup_le_limsup (Eventually.of_forall hle)
  have h2 : limsup (fun N : ℕ => ENNReal.ofReal (∫ u, F u ∂(nuWN38 c N))) atTop =
      ENNReal.ofReal (∫ u, F u ∂(B.muW38 c.val)) :=
    (ENNReal.tendsto_ofReal hlim).limsup_eq
  refine h1.trans (h2.le.trans ?_)
  refine ofReal_integral_le_measure_W11 _ (measurableSet_h2Tail38 _) F hFmu hF0 (fun u => ?_)
  by_cases hu : u ∈ h2Tail38 R
  · rw [Set.indicator_of_mem hu]; exact hF1 u
  · rw [Set.indicator_of_notMem hu]
    simp only [hF, chiR38_eq_one_of_not_tail hχ hR hu]; norm_num

include B in
/-- `μ_W(‖u‖_{H²} > n) → 0`: `μ_W` is concentrated on `H²`. -/
theorem tendsto_muW_tail_W11 :
    Tendsto (fun n : ℕ => B.muW38 c.val (h2Tail38 (n : ℝ))) atTop (𝓝 0) := by
  have hprob := B.isProbabilityMeasure_muW38 lower upper c.val c.property.1 (coef_bound38 c)
    (coef_upper38 c)
  have h := tendsto_measure_iInter_atTop (μ := B.muW38 c.val) (s := fun n : ℕ => h2Tail38 (n : ℝ))
    (fun n => (measurableSet_h2Tail38 _).nullMeasurableSet)
    (fun a b hab => h2Tail38_anti (Nat.cast_nonneg a) (Nat.cast_le.2 hab))
    ⟨0, measure_ne_top _ _⟩
  have hnull : B.muW38 c.val (⋂ n : ℕ, h2Tail38 (n : ℝ)) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    have hae := B.ae_muW38_allSobolev lower upper c.val c.property.1 (coef_bound38 c)
      (coef_upper38 c)
    filter_upwards [hae] with u hu hmem
    have hmem' := (fourierSeq38_mem_iff _ u).2 (hu (1 + 1))
    obtain ⟨n, hn⟩ := exists_nat_ge ‖carrierMk38 (((1 + 1 : ℕ)) : ℝ) (fourierSeq38 u) hmem'‖
    have h3 := Set.mem_iInter.1 hmem n
    have h3' : ENNReal.ofReal ((n : ℝ) ^ 2) < h2SqENN38 u := h3
    rw [h2SqENN38_of_mem u hmem'] at h3'
    have := ((ENNReal.ofReal_lt_ofReal_iff').1 h3').1
    have h4 : ‖carrierMk38 (((1 + 1 : ℕ)) : ℝ) (fourierSeq38 u) hmem'‖ ^ 2 ≤ (n : ℝ) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    linarith
  rw [hnull] at h
  exact h

include B O in
/-- **W11.03.** Weak convergence `ν_{W,N} ⇀ μ_W` on `𝓕⁻¹E_s` implies boundedness in probability
(`eq:remainingtight`). -/
theorem tight_of_weak_W11 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) (hweak : W11Weak38 B c s) :
    W11Tight38 c := by
  obtain ⟨χ, hχ⟩ := exists_cutoffProfile38
  unfold W11Tight38
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hμ := (ENNReal.tendsto_nhds_zero.1 (B.tendsto_muW_tail_W11 c)) ε hε
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hμ
  filter_upwards [eventually_ge_atTop (2 * (N₀ : ℝ) + 2)] with R hR
  have hR0 : 0 < R / 2 := by
    have : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg _
    linarith
  have := B.limsup_tail_le_W11 O c hs hs' hweak hχ hR0
  rw [show 2 * (R / 2) = R by ring] at this
  refine this.trans ((measure_mono (h2Tail38_anti (Nat.cast_nonneg N₀) (by linarith))).trans ?_)
  exact hN₀ N₀ le_rfl

end BirkhoffInput38

end NlsGge.Birkhoff
end
