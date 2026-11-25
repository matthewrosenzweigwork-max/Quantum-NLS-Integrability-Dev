import QuantumNLS.Prop019FullPacket
import QuantumNLS.Prop019FullOperators

/-! Full printed tolerance regime for PROP-019. Every 0 < epsilon <= 1, with
constants and threshold independent of epsilon. The explicit RootSpectralInputs
is the source hypothesis ruled faithful at Terra r156. No probability convergence
or 3 gamma + theta < 1 condition is used for this deterministic comparison. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped InnerProductSpace ComplexConjugate ENNReal
namespace QuantumNLS.Prop019FullLinearization
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BulkResponseActual (IsLimitingRapidityMeasure)
open QuantumNLS.Extrapolation (Gfull)
open QuantumNLS.RootEvent (EN)
open QuantumNLS.ResolventNeighborhood (NbhdN)
open QuantumNLS.Prop017Quantum (qAct eta0)
open QuantumNLS.Prop017Physical (RootSpectralInputs)
open QuantumNLS.PeriodReconstructionCore
open QuantumNLS.Prop019Linearization (pw continuous_pw rect_mem gammaN_abs rect_im_ne rect_wlen_le)
open QuantumNLS.MPContour (nu zθ uθ rectPieces)
open QuantumNLS.MPFamily (BgFam gθ dθ)
open QuantumNLS.MPOps (C0op Lop)
open QuantumNLS.FunctionalLinearization (evol)
open QuantumNLS.TensorCarrier (SymSector HilbertTensorPower reducedDensityPower)
open QuantumNLS.NormalizedTransfer (normalizedTransfer)
open QuantumNLS.Prop019FullOperators (C0 Linear EventProjection eventProjection pieces)
variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- Literal physical marginal trace distance for the printed time-t operators. -/
def comparison {Z : Set ℂ} {d₀ s₁ a₀ c₁ : ℝ} (k q : ℕ) (a h : ℝ) (d : ℕ)
    (p : ℕ → ℝ) (B : BgFam Z d₀ s₁ a₀ c₁) (t : ℝ)
    (φ : SymSector ℂ (L2T L) (k + q)) : ℝ≥0∞ :=
  QuantumNLS.TraceClass.traceNorm
    (reducedDensityPower k q
      ((evol (((k + q : ℕ) : ℂ) • C0 (L := L) (κ := κ) (k + q) a h d p B) t φ :
        SymSector ℂ (L2T L) (k + q)) : HilbertTensorPower ℂ (L2T L) (k + q)) -
     reducedDensityPower k q
      ((evol (((k + q : ℕ) : ℂ) • Linear (L := L) (κ := κ) (k + q) a h d p B.D) t φ :
        SymSector ℂ (L2T L) (k + q)) : HilbertTensorPower ℂ (L2T L) (k + q)))

/-- General designated-cut version, stronger than a fixed power radius. The packet,
its orthogonal projection, background, operators and physical marginals are all bound. -/
theorem prop019_full (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ}
    (hηh : eta0 L κ < h) (hδ : 0 < δ) (hd0 : 0 < d0)
    (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (b pc : ℕ) (hb : 1 ≤ b) (hbpc : b ≤ 2 * pc) (d k : ℕ) :
    ∃ ρ R0 η M c1 C : ℝ, 0 < ρ ∧ 2 * ρ < h ∧ 1 ≤ R0 ∧ 0 < η ∧ 1 ≤ M ∧ 0 ≤ c1 ∧ 0 ≤ C ∧
      ∃ N0 : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ q : ℕ, N0 ≤ k + q → ∀ hN : 1 ≤ k + q,
      ∀ R : ℝ, R0 ≤ R → ∀ l : ℕ, l0 ≤ l → ∀ a : ℝ,
      a = QuantumNLS.PROP017UniformN.cutSeq L l → 2 * R ≤ a →
      ∃ B : BgFam (NbhdN a h (ρ / 8)) η (M + M * M) (1 / M) c1,
        B.c0 = (fun z => Complex.I * κ * Gfull (μ : Measure ℝ) z) ∧
        B.D = Df L κ (Gfull (μ : Measure ℝ)) ∧ B.s = sf L κ (Gfull (μ : Measure ℝ)) ∧
        B.A = Af κ (Gfull (μ : Measure ℝ)) ∧
        ∃ P : EventProjection hκ hN u hu (EN (μ : Measure ℝ) (qAct L κ (k + q)) R a ρ h (eta0 L κ) ε b),
        ∀ φ : SymSector ℂ (L2T L) (k + q), φ ∈ Set.range P.op → ‖φ‖ = 1 →
        ∀ (t : ℝ) (p : ℕ → ℝ),
          comparison (κ := κ) k q a h d p B t φ ≤
            ENNReal.ofReal (C * (|t| * ∑ r ∈ Finset.range (d + 1), |p r|) *
              (1 + a) ^ (d + 1) * (ε + 1 / R ^ b + 1 / ((k + q : ℕ) : ℝ))) := by
  obtain ⟨ρ, R0, η, M, c1, Kd, hρ0, h2ρ, hR01, hη, hM1, hc1, hKd, N0, hpkt⟩ :=
    QuantumNLS.Prop019FullPacket.uniform_packet hκ u hu hμ hηh hδ hd0 hin b pc hb hbpc
  have hh : 0 < h := by linarith
  have hM0 : 0 < M := by linarith
  obtain ⟨C, hC0, hCb⟩ := QuantumNLS.Prop019Discharge.mp_statement L hκ h k
    η (M + M * M) (1 / M) c1 hη (by positivity) (by positivity) hc1
  refine ⟨ρ, R0, η, M, c1, C * (2 * Real.pi * κ)⁻¹ * Kd * (12 * (1 + h) ^ (d + 1)),
    hρ0, h2ρ, hR01, hη, hM1, hc1, by positivity, N0, ?_⟩
  intro ε hε hε1 q hN0 hN R hR l hl a ha h2R
  obtain ⟨B, hBc, hBD, hBs, hBA, hdev⟩ := hpkt ε hε hε1 (k + q) hN0 hN R hR l hl a ha h2R
  let P := eventProjection hκ hN u hu (EN (μ : Measure ℝ) (qAct L κ (k + q)) R a ρ h (eta0 L κ) ε b)
  refine ⟨B, hBc, hBD, hBs, hBA, P, ?_⟩
  intro φ hφrange hφ t p
  have hsupp := (P.range_iff φ).1 hφrange
  have hNr : (0 : ℝ) < ((k + q : ℕ) : ℝ) := by exact_mod_cast hN
  have ha2 : 2 ≤ a := by linarith [hR01.trans hR]
  let δN : ℝ := ε + 1 / R ^ b + 1 / ((k + q : ℕ) : ℝ)
  have hδN0 : 0 ≤ δN := by
    have hRp : 0 < R := by linarith [hR01.trans hR]
    dsimp [δN]
    positivity
  have hZ : ∀ i, ∀ τ ∈ Icc (0 : ℝ) 1,
      (rectPieces a h (pw d t p) (continuous_pw d t p) i).γ τ ∈ NbhdN a h (ρ / 8) := fun i τ hτ =>
    ⟨_, rect_mem (by linarith) hh.le _ _ i hτ, by rw [sub_self, norm_zero]; positivity⟩
  have hmain := hCb q hN (NbhdN a h (ρ / 8)) (rectPieces a h (pw d t p) (continuous_pw d t p)) hZ
    (fun i τ hτ => (gammaN_abs (by linarith) hh.le (rect_mem (by linarith) hh.le _ _ i hτ)).2)
    (fun i τ hτ => rect_im_ne hh _ _ i hτ) B φ hφ (fun _ => Kd * δN)
    (fun _ => mul_nonneg hKd hδN0)
    (fun i τ hτ => by
      have := hdev φ hsupp _ (hZ i τ hτ)
      rw [hφ, mul_one] at this
      exact this)
  have htOps := QuantumNLS.Prop019FullOperators.operators_time (L := L) (κ := κ) (k + q) a h hh d t p B
  have htrace := hmain
  simp only [Complex.ofReal_natCast] at htrace
  rw [htOps.1, htOps.2, QuantumNLS.Prop019FullOperators.evol_time,
    QuantumNLS.Prop019FullOperators.evol_time] at htrace
  change comparison (κ := κ) k q a h d p B t φ ≤ _ at htrace
  refine htrace.trans (ENNReal.ofReal_le_ofReal ?_)
  have hw := rect_wlen_le (by linarith : (0 : ℝ) ≤ a) hh.le d t p
  rw [← Finset.mul_sum]
  have hk0 : 0 ≤ C * (2 * Real.pi * κ)⁻¹ * Kd := by positivity
  calc C * ((2 * Real.pi * κ)⁻¹ * (Kd * δN * ∑ i : Fin 6, ∫ τ : unitInterval,
        ‖(rectPieces a h (pw d t p) (continuous_pw d t p) i).ω
          ((rectPieces a h (pw d t p) (continuous_pw d t p) i).γ τ)‖ *
        ‖(rectPieces a h (pw d t p) (continuous_pw d t p) i).γ' τ‖))
      = C * (2 * Real.pi * κ)⁻¹ * Kd * δN * ∑ i : Fin 6, ∫ τ : unitInterval,
        ‖(rectPieces a h (pw d t p) (continuous_pw d t p) i).ω
          ((rectPieces a h (pw d t p) (continuous_pw d t p) i).γ τ)‖ *
        ‖(rectPieces a h (pw d t p) (continuous_pw d t p) i).γ' τ‖ := by ring
    _ ≤ C * (2 * Real.pi * κ)⁻¹ * Kd * δN *
        (12 * (|t| * ∑ r ∈ Finset.range (d + 1), |p r|) * ((1 + a) * (1 + h)) ^ (d + 1)) :=
        mul_le_mul_of_nonneg_left hw (mul_nonneg hk0 hδN0)
    _ = C * (2 * Real.pi * κ)⁻¹ * Kd * (12 * (1 + h) ^ (d + 1)) *
        (|t| * ∑ r ∈ Finset.range (d + 1), |p r|) * (1 + a) ^ (d + 1) * δN := by
        rw [mul_pow]; ring

/-- Fixed power radius, all printed tolerances; the eventual threshold is uniform in epsilon. -/
theorem prop019_power_radius (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ}
    (hηh : eta0 L κ < h) (hδ : 0 < δ) (hd0 : 0 < d0)
    (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (b pc : ℕ) (hb : 1 ≤ b) (hbpc : b ≤ 2 * pc) (d k : ℕ) (θ : ℝ) (hθ : 0 < θ) :
    ∃ ρ R0 η M c1 C : ℝ, 0 < ρ ∧ 2 * ρ < h ∧ 1 ≤ R0 ∧ 0 < η ∧ 1 ≤ M ∧ 0 ≤ c1 ∧ 0 ≤ C ∧
      ∀ᶠ q : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ hN : 1 ≤ k + q,
      let a := QuantumNLS.PROP018Probability.cutN L θ (k + q)
      let R := (((k + q : ℕ) : ℝ) ^ θ)
      ∃ B : BgFam (NbhdN a h (ρ / 8)) η (M + M * M) (1 / M) c1,
        B.c0 = (fun z => Complex.I * κ * Gfull (μ : Measure ℝ) z) ∧
        B.D = Df L κ (Gfull (μ : Measure ℝ)) ∧ B.s = sf L κ (Gfull (μ : Measure ℝ)) ∧
        B.A = Af κ (Gfull (μ : Measure ℝ)) ∧
        ∃ P : EventProjection hκ hN u hu (EN (μ : Measure ℝ) (qAct L κ (k + q)) R a ρ h (eta0 L κ) ε b),
        ∀ φ : SymSector ℂ (L2T L) (k + q), φ ∈ Set.range P.op → ‖φ‖ = 1 →
        ∀ (t : ℝ) (p : ℕ → ℝ),
          comparison (κ := κ) k q a h d p B t φ ≤
            ENNReal.ofReal (C * (|t| * ∑ r ∈ Finset.range (d + 1), |p r|) *
              (1 + a) ^ (d + 1) * (ε + 1 / R ^ b + 1 / ((k + q : ℕ) : ℝ))) := by
  obtain ⟨ρ, R0, η, M, c1, C, hρ, h2ρ, hR01, hη, hM, hc1, hC, N0, hfull⟩ :=
    prop019_full hκ u hu hμ hηh hδ hd0 hin b pc hb hbpc d k
  refine ⟨ρ, R0, η, M, c1, C, hρ, h2ρ, hR01, hη, hM, hc1, hC, ?_⟩
  have hkq : Tendsto (fun q : ℕ => k + q) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat k
  filter_upwards [hkq.eventually (QuantumNLS.PROP018Probability.regime_eventually
    (Fact.out : 0 < L) hθ (show (0 : ℝ) < 1 by norm_num) R0 l0),
    hkq.eventually (eventually_ge_atTop N0)] with q hreg hN0
  intro ε hε hε1 hN
  exact hfull ε hε hε1 q hN0 hN _ hreg.1 _ hreg.2.1 _ rfl hreg.2.2.1

/-- Arbitrary growing source-admissible radius and cuts; no tolerance rate condition. -/
theorem prop019_sequences (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ}
    (hηh : eta0 L κ < h) (hδ : 0 < δ) (hd0 : 0 < d0)
    (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (b pc : ℕ) (hb : 1 ≤ b) (hbpc : b ≤ 2 * pc) (d k : ℕ) (R a : ℕ → ℝ) (idx : ℕ → ℕ)
    (hR : Tendsto R atTop atTop)
    (hcut : ∀ᶠ N : ℕ in atTop, l0 ≤ idx N ∧
      a N = QuantumNLS.PROP017UniformN.cutSeq L (idx N) ∧ 2 * R N ≤ a N) :
    ∃ ρ R0 η M c1 C : ℝ, 0 < ρ ∧ 2 * ρ < h ∧ 1 ≤ R0 ∧ 0 < η ∧ 1 ≤ M ∧ 0 ≤ c1 ∧ 0 ≤ C ∧
      ∀ᶠ q : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ hN : 1 ≤ k + q,
      let a := a (k + q)
      let R := R (k + q)
      ∃ B : BgFam (NbhdN a h (ρ / 8)) η (M + M * M) (1 / M) c1,
        B.c0 = (fun z => Complex.I * κ * Gfull (μ : Measure ℝ) z) ∧
        B.D = Df L κ (Gfull (μ : Measure ℝ)) ∧ B.s = sf L κ (Gfull (μ : Measure ℝ)) ∧
        B.A = Af κ (Gfull (μ : Measure ℝ)) ∧
        ∃ P : EventProjection hκ hN u hu (EN (μ : Measure ℝ) (qAct L κ (k + q)) R a ρ h (eta0 L κ) ε b),
        ∀ φ : SymSector ℂ (L2T L) (k + q), φ ∈ Set.range P.op → ‖φ‖ = 1 →
        ∀ (t : ℝ) (p : ℕ → ℝ),
          comparison (κ := κ) k q a h d p B t φ ≤
            ENNReal.ofReal (C * (|t| * ∑ r ∈ Finset.range (d + 1), |p r|) *
              (1 + a) ^ (d + 1) * (ε + 1 / R ^ b + 1 / ((k + q : ℕ) : ℝ))) := by
  obtain ⟨ρ, R0, η, M, c1, C, hρ, h2ρ, hR01, hη, hM, hc1, hC, N0, hfull⟩ :=
    prop019_full hκ u hu hμ hηh hδ hd0 hin b pc hb hbpc d k
  refine ⟨ρ, R0, η, M, c1, C, hρ, h2ρ, hR01, hη, hM, hc1, hC, ?_⟩
  have hkq : Tendsto (fun q : ℕ => k + q) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat k
  filter_upwards [hkq.eventually hcut, hkq.eventually (hR.eventually_ge_atTop R0),
    hkq.eventually (eventually_ge_atTop N0)] with q hcuts hRN hN0
  intro ε hε hε1 hN
  exact hfull ε hε hε1 q hN0 hN _ hRN _ hcuts.1 _ hcuts.2.1 hcuts.2.2

/-- The displayed source estimate, uniformly for all normalized states and |t| <= T. -/
theorem prop019_printed (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ}
    (hηh : eta0 L κ < h) (hδ : 0 < δ) (hd0 : 0 < d0)
    (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (b pc : ℕ) (hb : 1 ≤ b) (hbpc : b ≤ 2 * pc) (d k : ℕ) (θ : ℝ) (hθ : 0 < θ) :
    ∃ ρ R0 η M c1 C : ℝ, 0 < ρ ∧ 2 * ρ < h ∧ 1 ≤ R0 ∧ 0 < η ∧ 1 ≤ M ∧ 0 ≤ c1 ∧ 0 ≤ C ∧
      ∀ᶠ q : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ hN : 1 ≤ k + q,
      let a := QuantumNLS.PROP018Probability.cutN L θ (k + q)
      let R := (((k + q : ℕ) : ℝ) ^ θ)
      ∃ B : BgFam (NbhdN a h (ρ / 8)) η (M + M * M) (1 / M) c1,
        B.c0 = (fun z => Complex.I * κ * Gfull (μ : Measure ℝ) z) ∧
        B.D = Df L κ (Gfull (μ : Measure ℝ)) ∧ B.s = sf L κ (Gfull (μ : Measure ℝ)) ∧
        B.A = Af κ (Gfull (μ : Measure ℝ)) ∧
        ∃ P : EventProjection hκ hN u hu (EN (μ : Measure ℝ) (qAct L κ (k + q)) R a ρ h (eta0 L κ) ε b),
        ∀ φ : SymSector ℂ (L2T L) (k + q), φ ∈ Set.range P.op → ‖φ‖ = 1 →
        ∀ (T : ℝ), 0 ≤ T → ∀ (p : ℕ → ℝ) (t : ℝ), |t| ≤ T →
          comparison (κ := κ) k q a h d p B t φ ≤
            ENNReal.ofReal (C * (T * ∑ r ∈ Finset.range (d + 1), |p r|) *
              (1 + a) ^ (d + 1) * (ε + 1 / R ^ b + 1 / ((k + q : ℕ) : ℝ))) := by
  obtain ⟨ρ, R0, η, M, c1, C, hρ, h2ρ, hR01, hη, hM, hc1, hC, hpw⟩ :=
    prop019_power_radius hκ u hu hμ hηh hδ hd0 hin b pc hb hbpc d k θ hθ
  refine ⟨ρ, R0, η, M, c1, C, hρ, h2ρ, hR01, hη, hM, hc1, hC, ?_⟩
  filter_upwards [hpw, (show Tendsto (fun q : ℕ => k + q) atTop atTop by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat k).eventually (eventually_ge_atTop 1)] with q hq hq1
  intro ε hε hε1 hN
  obtain ⟨B, hBc, hBD, hBs, hBA, P, H⟩ := hq ε hε hε1 hN
  refine ⟨B, hBc, hBD, hBs, hBA, P, ?_⟩
  intro φ hφrange hφ T hT p t ht
  refine (H φ hφrange hφ t p).trans (ENNReal.ofReal_le_ofReal ?_)
  have hNr : (0 : ℝ) < ((k + q : ℕ) : ℝ) := by exact_mod_cast hq1
  have hR : 0 < (((k + q : ℕ) : ℝ) ^ θ) := Real.rpow_pos_of_pos hNr θ
  have ha : 0 ≤ QuantumNLS.PROP018Probability.cutN L θ (k + q) := by
    unfold QuantumNLS.PROP018Probability.cutN QuantumNLS.PROP017CutFamily.cutSeq
    have := (Fact.out : 0 < L)
    positivity
  gcongr

/-- Direct reuse of the r84 general-sequence regime; its vanishing error implies growing radius. -/
theorem prop019_r84_sequences (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ}
    (hηh : eta0 L κ < h) (hδ : 0 < δ) (hd0 : 0 < d0)
    (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (b pc : ℕ) (hb : 1 ≤ b) (hbpc : b ≤ 2 * pc) (d k : ℕ) (R a : ℕ → ℝ) (idx : ℕ → ℕ)
    (εseq : ℕ → ℝ) (hRpos : ∀ N, 0 < R N) (hεpos : ∀ N, 0 < εseq N)
    (hseq : Tendsto (fun N : ℕ => εseq N + 1 / R N ^ b + 1 / (N : ℝ)) atTop (𝓝 0))
    (hcut : ∀ᶠ N : ℕ in atTop, l0 ≤ idx N ∧
      a N = QuantumNLS.PROP017UniformN.cutSeq L (idx N) ∧ 2 * R N ≤ a N) :
    ∃ ρ R0 η M c1 C : ℝ, 0 < ρ ∧ 2 * ρ < h ∧ 1 ≤ R0 ∧ 0 < η ∧ 1 ≤ M ∧ 0 ≤ c1 ∧ 0 ≤ C ∧
      ∀ᶠ q : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ hN : 1 ≤ k + q,
      let a := a (k + q)
      let R := R (k + q)
      ∃ B : BgFam (NbhdN a h (ρ / 8)) η (M + M * M) (1 / M) c1,
        B.c0 = (fun z => Complex.I * κ * Gfull (μ : Measure ℝ) z) ∧
        B.D = Df L κ (Gfull (μ : Measure ℝ)) ∧ B.s = sf L κ (Gfull (μ : Measure ℝ)) ∧
        B.A = Af κ (Gfull (μ : Measure ℝ)) ∧
        ∃ P : EventProjection hκ hN u hu (EN (μ : Measure ℝ) (qAct L κ (k + q)) R a ρ h (eta0 L κ) ε b),
        ∀ φ : SymSector ℂ (L2T L) (k + q), φ ∈ Set.range P.op → ‖φ‖ = 1 →
        ∀ (t : ℝ) (p : ℕ → ℝ),
          comparison (κ := κ) k q a h d p B t φ ≤
            ENNReal.ofReal (C * (|t| * ∑ r ∈ Finset.range (d + 1), |p r|) *
              (1 + a) ^ (d + 1) * (ε + 1 / R ^ b + 1 / ((k + q : ℕ) : ℝ))) := by
  have htR : Tendsto R atTop atTop := tendsto_atTop.2 fun A =>
    (QuantumNLS.Prop018SequenceBundle.sequence_regime hb R εseq a idx hRpos hεpos hseq hcut A).mono
      (fun N hN => hN.1)
  exact prop019_sequences hκ u hu hμ hηh hδ hd0 hin b pc hb hbpc d k R a idx htR hcut

end QuantumNLS.Prop019FullLinearization
#print axioms QuantumNLS.Prop019FullLinearization.prop019_full

#print axioms QuantumNLS.Prop019FullLinearization.prop019_power_radius
#print axioms QuantumNLS.Prop019FullLinearization.prop019_sequences

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop019FullLinearization." then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."

#print axioms QuantumNLS.Prop019FullLinearization.prop019_printed

#print axioms QuantumNLS.Prop019FullLinearization.prop019_r84_sequences
