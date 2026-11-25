import QuantumNLS.Prop017Quantum
import QuantumNLS.PROP017Designated
import QuantumNLS.EnergyProjection

/-!
# PROP-017 `Q7A:prop:packet` for the actual Bethe model (window_reconstruction.tex:92-104, proof 110-125)

Owner-approved reading: ε-indexed events. This module binds the reviewed designated-cut theorem
`PROP017UniformN.prop017_uniform` (f5974b78; re-exported by `PROP017Designated` 315bfbe8, Terra r129 conditional support) to the
actual physical objects:

* the Born root law `P_{N,u} = bornMeasure (physBasis L hκ N) u` of the complete actual Bethe basis (UBB1) and the measurable root
  vector `qAct L κ N = arrRoots L (κ/N)` (DEF-006) — `Prop017Quantum`;
* `μ = μ_{κ,u}`, the quantum-derived limiting measure of R-09E1EAE9 (`IsLimitingRapidityMeasure`; unique), whose Cauchy transform is
  `gStar` on the high half-plane;
* the quantum hypotheses `Q7A:eq:tail` (`tail_actual`) and `Q7A:eq:ms` (`ms_actual`), PROVED for the actual law;
* the classical inputs that the source takes from `thm:root-spectral-density` (R-7E0532E7, not yet accepted) and the positive scalar
  moment construction are stated as the explicit named proposition **`RootSpectralInputs`** over the actual `μ` (all even moments;
  support gap `δ` at the designated cuts `a_ℓ = (2ℓ+1)π/L`, `ℓ ≥ ℓ₀`; `|D| ≥ d₀` on the rectangles `Γ_ℓ` of height `h > η₀`). It is a
  hypothesis of the theorems below, and nothing stronger is assumed. This is the recorded dependency on R-7E0532E7.

Results:
* **`prop017_physical`**: PROP-017 for the actual model: `∃ ρ, R₀, r, N₀` such that for every `0 < ε ≤ 1`, `N ≥ N₀`, `R ≥ R₀`, and every
  designated cut `a = a_ℓ ≥ 2R`: `P_{N,u}(𝓔_N(ε)ᶜ) ≤ N C_p R^{−2p} + D_p/R + C_b(1+a)/(N ε³)` (`eq:bad`), and on `𝓔_N(ε)`: all roots in
  `[−R,R]` (`eq:allroots`), `|G_N − G| ≤ 2K_b(ε + R^{−b})` on the `ρ`-neighbourhood (`eq:Gneighbor`), the derivative bounds
  (`eq:derivative`), and `|D| ≥ d₀/2` on the `ρ/4`-neighbourhood.
* **`prop017_physical_diagonal`**: along `R_N = N^θ`, `ε_N = N^{−γ}`, `a_N = cutN L θ N` with `θ, γ > 0`, `3γ + θ < 1`, `1 < 2pθ`:
  `P_{N,u}(𝓔_N(ε_N)ᶜ) → 0`, and the `eq:Gneighbor` error on the event tends to `0`.
* **`event_projection`**: the spectral projection `P^𝓔_N` onto the event (diagonal mask in the actual Bethe basis) satisfies
  `‖(1 − P^𝓔_N) u^{⊗N}‖² = P_{N,u}(𝓔ᶜ)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.Prop017Physical

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr arrRoots)
open QuantumNLS.BetheCoefficientTransform (bornLaw)
open QuantumNLS.RootMeasureConcentrationSharp (Csharp)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis IsLimitingRapidityMeasure)
open QuantumNLS.Extrapolation (Gfull GN)
open QuantumNLS.RootEvent (tailFraction EN prop017Cb)
open QuantumNLS.ResolventNeighborhood (GammaN NbhdN rNbhd KGN sNsrc sLimsrc)
open QuantumNLS.NonvanishingD (Dsrc)
open QuantumNLS.PROP017UniformN (cutSeq prop017_uniform)
open QuantumNLS.PROP018Probability (cutN cutIdx propBound regime_eventually tendsto_of_bound)
open QuantumNLS.Prop017Quantum (qAct measurable_qAct eta0 eta0_pos ms_actual tail_actual Ctail Dtail)

/-! ## 1. The classical inputs from `thm:root-spectral-density` (named proposition) -/

/-- **The classical model inputs for the actual measure** (source model hypotheses 1 (classical part) and 2), which the source
derives from `thm:root-spectral-density` (R-7E0532E7) and the positive scalar moment construction: all even moments of `μ`, the support
gap `δ` at the designated cuts `a_ℓ = (2ℓ+1)π/L` (`ℓ ≥ ℓ₀`), and `|D| ≥ d₀` on the rectangles `Γ_ℓ` with heights `±h`. -/
structure RootSpectralInputs (L κ : ℝ) (μ : Measure ℝ) (h δ d0 : ℝ) (l0 : ℕ) : Prop where
  moments : ∀ p : ℕ, Integrable (fun x : ℝ => x ^ (2 * p)) μ
  gap : ∀ l : ℕ, l0 ≤ l → ∀ᵐ (x : ℝ) ∂μ, δ ≤ |x - cutSeq L l| ∧ δ ≤ |x + cutSeq L l|
  discr : ∀ l : ℕ, l0 ≤ l → ∀ w ∈ GammaN (cutSeq L l) h, d0 ≤ ‖Dsrc κ L μ w‖

/-! ## 2. PROP-017 for the actual model -/

section Main

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- **PROP-017 `Q7A:prop:packet` for the actual Bethe model** (ε-indexed events, designated cuts). -/
theorem prop017_physical (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ} (hηh : eta0 L κ < h)
    (hδ : 0 < δ) (hd0 : 0 < d0) (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (b pc : ℕ) (hb : 1 ≤ b) (hbpc : b ≤ 2 * pc) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ R0 : ℝ, 1 ≤ R0 ∧ ∃ r : ℝ, 0 < r ∧
      (∀ R : ℝ, R0 ≤ R → ∀ a : ℝ, 2 * R ≤ a → r ≤ rNbhd a h ρ R δ) ∧
      ∃ N0 : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ N : ℕ, N0 ≤ N → 1 ≤ N →
        ∀ R : ℝ, R0 ≤ R → ∀ l : ℕ, l0 ≤ l → ∀ a : ℝ, a = cutSeq L l → 2 * R ≤ a →
          (∀ p : ℕ, 1 ≤ p → eta0 L κ ≤ R →
              (bornMeasure (physBasis L hκ N) u hu).real (EN (μ : Measure ℝ) (qAct L κ N) R a ρ h (eta0 L κ) ε b)ᶜ
                ≤ (N : ℝ) * (Ctail (μ : Measure ℝ) p * (1 / R ^ (2 * p))) + Dtail κ p / R
                  + prop017Cb (eta0 L κ) h ρ Csharp b * (1 + a) / ((N : ℝ) * ε ^ 3)) ∧
          (∀ m ∈ EN (μ : Measure ℝ) (qAct L κ N) R a ρ h (eta0 L κ) ε b,
              (∀ j, |qAct L κ N m j| ≤ R) ∧
              (∀ z ∈ NbhdN a h ρ, ‖Gfull (μ : Measure ℝ) z - GN (qAct L κ N m) z‖ ≤
                2 * KGN (eta0 L κ) δ ρ (h + 5) Csharp b pc (μ : Measure ℝ) * (ε + 1 / R ^ b)) ∧
              (∀ z ∈ NbhdN a h (ρ / 2), ∀ n : ℕ,
                ‖iteratedDeriv n (fun w => sNsrc κ L (qAct L κ N m) w - sLimsrc κ L (μ : Measure ℝ) w) z‖ ≤
                  n.factorial * (Real.exp (|κ| / r) * (1 + Real.exp (|L| * (h + 2 * ρ)))
                    * max (κ ^ 2 / r ^ 2) (|κ| * (2 * KGN (eta0 L κ) δ ρ (h + 5) Csharp b pc (μ : Measure ℝ)))
                    * (ε + 1 / R ^ b + 1 / (N : ℝ))) / (ρ / 2) ^ n)) ∧
          (∀ z ∈ NbhdN a h (ρ / 4), d0 / 2 ≤ ‖Dsrc κ L (μ : Measure ℝ) z‖) := by
  have hL : 0 < L := Fact.out
  have hCms : 0 ≤ Csharp := by
    unfold Csharp; have := QuantumNLS.RootMeasureConcentrationSharp.Kc_nonneg; linarith
  obtain ⟨ρ, hρ0, R0, hR01, r, hr0, hrad, N0, hfam⟩ :=
    prop017_uniform (μ : Measure ℝ) κ L h (eta0 L κ) δ d0 hL l0 b pc hb hbpc hin.moments
      (eta0_pos hκ) hηh hδ hd0 (fun l hl => ⟨hin.gap l hl, hin.discr l hl⟩)
      (Ctail (μ : Measure ℝ)) (Dtail κ) (fun _ => eta0 L κ) Csharp hCms
  refine ⟨ρ, hρ0, R0, hR01, r, hr0, hrad, N0, fun ε hε0 hε1 N hN0 hN1 R hR l hl a ha h2R => ?_⟩
  have hN : 0 < N := hN1
  have hfam' := hfam ε hε0 hε1 N hN0 (MArr N) (bornMeasure (physBasis L hκ N) u hu) (qAct L κ N)
    (measurable_qAct L κ N)
    (fun p _ R' hR' _ => tail_actual hκ u hu hμ hin.moments hN p R' hR')
    (fun x y hy => ms_actual hκ u hu hμ hN x y hy) R hR l hl a ha h2R
  obtain ⟨hbad, hev, hD⟩ := hfam'
  exact ⟨fun p hp hRt => hbad p hp hRt, hev, hD⟩

/-- **The diagonal regime for the actual model**: `R_N = N^θ`, `ε_N = N^{−γ}`, designated cut `a_N = cutN L θ N`, with
`θ, γ > 0`, `3γ + θ < 1`, `1 < 2pθ`. -/
theorem prop017_physical_diagonal (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ} (hηh : eta0 L κ < h)
    (hδ : 0 < δ) (hd0 : 0 < d0) (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (b pc : ℕ) (hb : 1 ≤ b) (hbpc : b ≤ 2 * pc)
    (θ γ : ℝ) (hθ : 0 < θ) (hγ : 0 < γ) (hsum : 3 * γ + θ < 1) (p : ℕ) (hp : 1 < 2 * (p : ℝ) * θ) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real
        (EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h (eta0 L κ) ((N : ℝ) ^ (-γ)) b)ᶜ)
        atTop (𝓝 0) ∧
      (∀ᶠ N : ℕ in atTop, ∀ m ∈ EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h (eta0 L κ)
          ((N : ℝ) ^ (-γ)) b,
        (∀ j, |qAct L κ N m j| ≤ (N : ℝ) ^ θ) ∧
        ∀ z ∈ NbhdN (cutN L θ N) h ρ, ‖Gfull (μ : Measure ℝ) z - GN (qAct L κ N m) z‖ ≤
          2 * KGN (eta0 L κ) δ ρ (h + 5) Csharp b pc (μ : Measure ℝ) * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b)) ∧
      Tendsto (fun N : ℕ => 2 * KGN (eta0 L κ) δ ρ (h + 5) Csharp b pc (μ : Measure ℝ) *
        ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b)) atTop (𝓝 0) := by
  have hL : 0 < L := Fact.out
  obtain ⟨ρ, hρ0, R0, hR01, r, hr0, hrad, N0, hfam⟩ :=
    prop017_physical hκ u hu hμ hηh hδ hd0 hin b pc hb hbpc
  have hCms : 0 ≤ Csharp := by
    unfold Csharp; have := QuantumNLS.RootMeasureConcentrationSharp.Kc_nonneg; linarith
  have hCb : 0 ≤ prop017Cb (eta0 L κ) h ρ Csharp b := QuantumNLS.PROP017UniformN.prop017Cb_nonneg hρ0 hCms
  have hp1 : 1 ≤ p := by
    by_contra hcon
    have h0 : p = 0 := by omega
    subst h0
    norm_num at hp
  have hb0 : b ≠ 0 := by omega
  have hmain : ∀ᶠ N : ℕ in atTop,
      (bornMeasure (physBasis L hκ N) u hu).real
          (EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h (eta0 L κ) ((N : ℝ) ^ (-γ)) b)ᶜ ≤
        propBound (Ctail (μ : Measure ℝ) p) (Dtail κ p) (prop017Cb (eta0 L κ) h ρ Csharp b) p (N : ℝ)
          ((N : ℝ) ^ θ) (cutN L θ N) ((N : ℝ) ^ (-γ)) ∧
      (∀ m ∈ EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h (eta0 L κ) ((N : ℝ) ^ (-γ)) b,
        (∀ j, |qAct L κ N m j| ≤ (N : ℝ) ^ θ) ∧
        ∀ z ∈ NbhdN (cutN L θ N) h ρ, ‖Gfull (μ : Measure ℝ) z - GN (qAct L κ N m) z‖ ≤
          2 * KGN (eta0 L κ) δ ρ (h + 5) Csharp b pc (μ : Measure ℝ) *
            ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b)) := by
    filter_upwards [regime_eventually hL hθ hγ (max R0 (eta0 L κ)) l0, eventually_ge_atTop N0,
      eventually_ge_atTop 1] with N hreg hN0 hN1
    have hle := hfam ((N : ℝ) ^ (-γ)) hreg.2.2.2.1 hreg.2.2.2.2 N hN0 hN1 ((N : ℝ) ^ θ)
      (le_trans (le_max_left _ _) hreg.1) (cutIdx L θ N) hreg.2.1 (cutN L θ N) rfl hreg.2.2.1
    obtain ⟨hbd, hG, -⟩ := hle
    refine ⟨?_, fun m hm => ⟨(hG m hm).1, (hG m hm).2.1⟩⟩
    have := hbd p hp1 (le_trans (le_max_right _ _) hreg.1)
    refine this.trans (le_of_eq ?_)
    unfold propBound; ring
  have hA := tendsto_of_bound hL hθ hγ hsum p hp (Ctail (μ : Measure ℝ) p) (Dtail κ p)
    (prop017Cb (eta0 L κ) h ρ Csharp b) hCb _ (Eventually.of_forall fun N => measureReal_nonneg)
    (hmain.mono fun N h => h.1)
  have hε : Tendsto (fun N : ℕ => (N : ℝ) ^ (-γ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hγ).comp tendsto_natCast_atTop_atTop
  have hR' : Tendsto (fun N : ℕ => (N : ℝ) ^ θ) atTop atTop :=
    (tendsto_rpow_atTop hθ).comp tendsto_natCast_atTop_atTop
  have hRb : Tendsto (fun N : ℕ => 1 / ((N : ℝ) ^ θ) ^ b) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop hb0).comp hR')
  have hC : Tendsto (fun N : ℕ => 2 * KGN (eta0 L κ) δ ρ (h + 5) Csharp b pc (μ : Measure ℝ) *
      ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b)) atTop (𝓝 0) := by
    have h := (hε.add hRb).const_mul (2 * KGN (eta0 L κ) δ ρ (h + 5) Csharp b pc (μ : Measure ℝ))
    rw [add_zero, mul_zero] at h
    exact h
  exact ⟨ρ, hρ0, hA, hmain.mono fun N h => h.2, hC⟩

end Main

/-! ## 3. The spectral projection onto the event -/

section Projection

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

open Classical in
/-- **The physical event projection**: the diagonal projection `P^𝓔_N` onto the span of the actual Bethe vectors whose labels lie in
`S`, with `‖(1 − P^𝓔_N) u^{⊗N}‖² = P_{N,u}(Sᶜ)`. -/
theorem event_projection (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (u : L2T L) (hu : ‖u‖ = 1) (S : Set (MArr N)) :
    ∃ PE : QuantumNLS.KernelDefinition.BoundedSymmetricKernel (L2T L) N,
      (∀ m, PE (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ m) =
        (if m ∈ S then (1 : ℂ) else 0) • QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ m) ∧
      PE * PE = PE ∧ ContinuousLinearMap.adjoint PE = PE ∧
      ‖(1 - PE) (QuantumNLS.HighMomentsOps.wvec N u)‖ ^ 2 = (bornMeasure (physBasis L hκ N) u hu).real Sᶜ := by
  set Ψ := QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ with hΨ
  obtain ⟨PE, hPE, hidem, hsa⟩ := QuantumNLS.EnergyProjection.diag_projection Ψ
    (fun m => if m ∈ S then (1 : ℝ) else 0) (fun m => by split_ifs <;> simp)
  have hPE' : ∀ m, PE (Ψ m) = (if m ∈ S then (1 : ℂ) else 0) • Ψ m := fun m => by
    rw [hPE m]; split_ifs <;> simp
  refine ⟨PE, hPE', hidem, hsa, ?_⟩
  -- the norm as a Born sum
  have h1 := QuantumNLS.RootMeasureTransfer.hasSum_norm_sq_diag Ψ PE (fun m => if m ∈ S then (1 : ℂ) else 0)
    hPE' 1 (QuantumNLS.HighMomentsOps.wvec N u)
  have e1 : ‖(1 - PE) (QuantumNLS.HighMomentsOps.wvec N u)‖ =
      ‖(PE - (1 : ℂ) • (1 : QuantumNLS.KernelDefinition.BoundedSymmetricKernel (L2T L) N))
        (QuantumNLS.HighMomentsOps.wvec N u)‖ := by
    rw [one_smul, ← norm_neg, ← neg_apply, neg_sub]
  rw [e1, ← h1.tsum_eq]
  -- the measure as a Born sum
  rw [QuantumNLS.RootMeasureExistence.physBasis_eq hκ (by omega : 1 ≤ N)]
  have hmu : ∀ m : MArr N, (bornMeasure Ψ u hu).real {m} = bornLaw Ψ u m := by
    intro m
    rw [measureReal_def, QuantumNLS.EmpiricalRapidity.bornMeasure_singleton,
      ENNReal.toReal_ofReal (QuantumNLS.BetheCoefficientTransform.bornLaw_nonneg _ _ _)]
  have hint : Integrable (Sᶜ.indicator (1 : MArr N → ℝ)) (bornMeasure Ψ u hu) :=
    (integrable_const (1 : ℝ)).indicator (MeasurableSet.of_discrete)
  rw [← integral_indicator_one MeasurableSet.of_discrete, integral_countable hint]
  refine tsum_congr fun m => ?_
  rw [hmu, smul_eq_mul]
  have hb : ‖⟪Ψ m, QuantumNLS.HighMomentsOps.wvec N u⟫_ℂ‖ ^ 2 = bornLaw Ψ u m := rfl
  rw [hb]
  by_cases hm : m ∈ S
  · simp [hm]
  · simp [hm]

end Projection

end QuantumNLS.Prop017Physical

#print axioms QuantumNLS.Prop017Physical.prop017_physical
#print axioms QuantumNLS.Prop017Physical.prop017_physical_diagonal
#print axioms QuantumNLS.Prop017Physical.event_projection
