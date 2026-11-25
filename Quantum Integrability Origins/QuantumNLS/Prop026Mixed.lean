import Mathlib
import QuantumNLS.Prop009FixedProjection
import QuantumNLS.Prop019Linearization
import QuantumNLS.MPLinearizationContours
import QuantumNLS.MPFixedContour

/-!
# PROP-026 `lem:MP-linearization` (`mixed_propagation.tex:354`) for the ACTUAL mixed model, as one theorem

Source statement (`eq:MP-linearization`): for normalized `φ ∈ ran P_N`, uniformly on the boxes,
`‖γ^{(k)}_{e^{-iNC_{0,N}(t,θ)}φ} − γ^{(k)}_{e^{-iNL_N(t,θ)}φ}‖₁ ≤ C_k (W_a Δ_N + ρ^I_N)`, with `W_a = (1+a)^{d+1}`, `Δ_N = ε + R^{-b} + N^{-1}`
(`ε_N = N^{-γ}`, `R_N = N^θ`, `a = a_N` the designated cut), the fixed-contour error `ρ^I_N` NOT multiplied by `W_a`, and
`P_N = P^I_N P^g_N` the common spectral projection.

Assembly (new module; every ingredient is an accepted or frozen module, imported read-only; nothing new is assumed):
* the growing-window bundle (`Prop018Bundle.moving_contour_bundle`, the review) gives `P^g_N` (event `EN`), `Pr(EN^c) → 0`, the deviation
  `‖(S_N − s)φ‖ ≤ max(K_d,0) Δ_N‖φ‖` on the `ρ/8`-neighbourhood of `Γ_a` (`Prop019Deviation.deviation_of_bundle`) and the large-contour
  background bounds (exactly as in `Prop019Linearization.prop019_linearization`);
* `Prop009FixedProjection.fixed_projection` (frozen `0571516f`) gives `P^I_N` (event `E^I_N`), `η^I_N = Pr((E^I_N)^c) → 0`, and the fixed-contour
  deviation `‖(S_N − s)φ‖ ≤ ρ^I_N‖φ‖` on the fixed contours `Γ_n`, `n ∈ I`;
* `common_projection`: `P_N = P^g_N P^I_N` is the diagonal projection onto `E^g ∩ E^I` (`ext_of_hilbertBasis`), and
  `‖(1−P_N)u^{⊗N}‖² ≤ η^g_N + η^I_N` (`measure_union_le` on the complements; the source's `eq:MP-projection-distance` input);
* `MPFixedContour.bgfamOfG_union` builds ONE `BgFam` on `Γ_a`'s neighbourhood ∪ the fixed contours `Γ_n`, with `c₀ = iκG_μ`, `D = D_f`, `s = s_f`,
  `A = A_f` and the combined bounds (`min η`, `max M`); the fixed part of the bounds is `gam_family_background` (from `MPFixedContour.gam_background`);
* `MPLinearizationContours.mp_linearization_contours` (frozen `775c5145`; the combined-contour theorem with the fixed term unamplified) is applied
  to the six pieces of `Γ_a` (weight `p_t = Σ_{r∈R} t_r z^r`) followed by the fixed pieces `Pf` (weights `θ_n`).

Only the carried hypotheses appear: `hμ` (the accepted limiting measure `μ_{κ,u}`), `hS : μ = S.μ` for the `IndexedScalarMeasureCuts` datum
(pending DEF-014, item (1)), the PROP-006 label brackets of the fixed contours, and `hin : RootSpectralInputs` (which carries the even moments
`EvenMoments μ`, the printed hypothesis per Terra r156) for the large contour.  The derivative part `‖(S_N' − s')P^I_N‖` of
`eq:MP-fixed-deviation` is not used by `lem:MP-linearization` (it enters `eq:MP-correction-scalar` only) and is not proved here.
-/

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace QuantumNLS.Prop026Mixed

open QuantumNLS.PhysicalTensor (L2T physSector)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis IsLimitingRapidityMeasure)
open QuantumNLS.Extrapolation (Gfull GN)
open QuantumNLS.RootEvent (EN)
open QuantumNLS.ResolventNeighborhood (GammaN NbhdN)
open QuantumNLS.PROP018Probability (cutN regime_eventually)
open QuantumNLS.Prop017Quantum (qAct eta0 Gfull_eq)
open QuantumNLS.Prop017Physical (RootSpectralInputs)
open QuantumNLS.PeriodReconstructionCore
open QuantumNLS.PeriodReconstruction (Gam)
open QuantumNLS.Prop018Bundle (moving_contour_bundle)
open QuantumNLS.Prop019Deviation (deviation_of_bundle)
open QuantumNLS.Prop019Linearization (rect_mem rect_im_ne gammaN_abs)
open QuantumNLS.MPContour (Piece ThetaSpace nu zθ uθ rectPieces polyT continuous_polyT wlen)
open QuantumNLS.MPFamily (BgFam gθ dθ)
open QuantumNLS.MPOps (C0op Lop)
open QuantumNLS.FunctionalLinearization (evol)
open QuantumNLS.TensorCarrier (SymSector HilbertTensorPower reducedDensityPower)
open QuantumNLS.NormalizedTransfer (normalizedTransfer)
open QuantumNLS.UnconditionalBetheBasis (meanField_physicalBasis)
open QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts
open QuantumNLS.MPFixedContour (gam_background bgfamOfG_union)
open QuantumNLS.MPLinearizationContours (mp_linearization_contours)
open QuantumNLS.Prop009ProbeDev (exists_pos_le_all Gam_im_le)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-! ### 1. The fixed contours: uniform background bounds -/

theorem gam_family_background (S : IndexedScalarMeasureCuts L κ) {r : ℕ} {n : Fin r → ℤ} {xm xp h : Fin r → ℝ}
    (hxm : ∀ i, xm i ∈ S.cuts) (hxp : ∀ i, xp i ∈ S.cuts) (hlt : ∀ i, xm i < xp i) (hh : ∀ i, 0 < h i)
    (h1 : ∀ i, 2 * Real.pi * (n i - 1) < exteriorForce L κ S.μ (xm i))
    (h2 : ∀ i, exteriorForce L κ S.μ (xm i) < 2 * Real.pi * n i)
    (h3 : ∀ i, 2 * Real.pi * n i < exteriorForce L κ S.μ (xp i))
    (h4 : ∀ i, exteriorForce L κ S.μ (xp i) < 2 * Real.pi * (n i + 1)) :
    ∃ η M Gb : ℝ, 0 < η ∧ 1 ≤ M ∧ 0 ≤ Gb ∧ ∀ i, ∀ z ∈ Gam (xm i) (xp i) (h i),
      DifferentiableAt ℂ (EmpiricalRapidity.cauchyTransform S.μ) z ∧
      η ≤ ‖Df L κ (EmpiricalRapidity.cauchyTransform S.μ) z‖ ∧
      ‖Af κ (EmpiricalRapidity.cauchyTransform S.μ) z‖ ≤ M ∧
      ‖(Af κ (EmpiricalRapidity.cauchyTransform S.μ) z)⁻¹‖ ≤ M ∧ ‖ef L z‖ ≤ M ∧
      ‖EmpiricalRapidity.cauchyTransform S.μ z‖ ≤ Gb := by
  choose η M Gb hη hM hGb hb using fun i => gam_background S (hxm i) (hxp i) (hlt i) (hh i) (h1 i) (h2 i) (h3 i) (h4 i)
  obtain ⟨η', hη', hη'le⟩ := exists_pos_le_all η hη
  have hMs : ∀ i, M i ≤ ∑ j, M j := fun i =>
    Finset.single_le_sum (f := M) (fun j _ => by linarith [hM j]) (Finset.mem_univ i)
  have hGs : ∀ i, Gb i ≤ ∑ j, Gb j := fun i =>
    Finset.single_le_sum (f := Gb) (fun j _ => hGb j) (Finset.mem_univ i)
  have hMsum : 0 ≤ ∑ j, M j := Finset.sum_nonneg (fun j _ => by linarith [hM j])
  refine ⟨η', 1 + ∑ j, M j, ∑ j, Gb j, hη', by linarith, Finset.sum_nonneg (fun j _ => hGb j), fun i z hz => ?_⟩
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hb i z hz
  have := hMs i
  exact ⟨d1, (hη'le i).trans d2, d3.trans (by linarith), d4.trans (by linarith), d5.trans (by linarith),
    d6.trans (hGs i)⟩

/-! ### 2. The common projection `P_N = P^g_N P^I_N` -/

open Classical in
/-- `P` is the diagonal projection onto the Bethe vectors with labels in `E`, with `‖(1 − P)u^{⊗N}‖² = P_{N,u}(Eᶜ)`. -/
def IsEventProj (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {N : ℕ} (hN : 0 < N) (E : Set (MArr N))
    (P : QuantumNLS.KernelDefinition.BoundedSymmetricKernel (L2T L) N) : Prop :=
  (∀ m, P (meanField_physicalBasis L N hN hκ m) =
      (if m ∈ E then (1 : ℂ) else 0) • meanField_physicalBasis L N hN hκ m) ∧
    P * P = P ∧ ContinuousLinearMap.adjoint P = P ∧
    ‖(1 - P) (QuantumNLS.HighMomentsOps.wvec N u)‖ ^ 2 = (bornMeasure (physBasis L hκ N) u hu).real Eᶜ

open Classical in
theorem common_projection (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {N : ℕ} (hN : 0 < N) (E1 E2 : Set (MArr N)) :
    ∃ P1 P2 P : QuantumNLS.KernelDefinition.BoundedSymmetricKernel (L2T L) N,
      IsEventProj hκ u hu hN E1 P1 ∧ IsEventProj hκ u hu hN E2 P2 ∧ IsEventProj hκ u hu hN (E1 ∩ E2) P ∧
      P = P1 * P2 ∧
      ‖(1 - P) (QuantumNLS.HighMomentsOps.wvec N u)‖ ^ 2 ≤
        ‖(1 - P1) (QuantumNLS.HighMomentsOps.wvec N u)‖ ^ 2 + ‖(1 - P2) (QuantumNLS.HighMomentsOps.wvec N u)‖ ^ 2 := by
  obtain ⟨P1, h1m, h1i, h1s, h1n⟩ := QuantumNLS.Prop017Physical.event_projection hκ hN u hu E1
  obtain ⟨P2, h2m, h2i, h2s, h2n⟩ := QuantumNLS.Prop017Physical.event_projection hκ hN u hu E2
  obtain ⟨P, hPm, hPi, hPs, hPn⟩ := QuantumNLS.Prop017Physical.event_projection hκ hN u hu (E1 ∩ E2)
  have hP : P = P1 * P2 := by
    refine QuantumNLS.TransferNormality.ext_of_hilbertBasis (meanField_physicalBasis L N hN hκ) (fun m => ?_)
    rw [ContinuousLinearMap.mul_apply, h2m m, map_smul, h1m m, smul_smul, hPm m]
    by_cases ha : m ∈ E1 <;> by_cases hb : m ∈ E2 <;> simp [ha, hb]
  refine ⟨P1, P2, P, ⟨h1m, h1i, h1s, h1n⟩, ⟨h2m, h2i, h2s, h2n⟩, ⟨hPm, hPi, hPs, hPn⟩, hP, ?_⟩
  rw [hPn, h1n, h2n, Set.compl_inter]
  exact measureReal_union_le _ _

/-! ### 3. The printed operators on the combined contour -/

/-- The trace-norm distance of the statement: `‖γ^{(k)}_{e^{-iNC_{0,N}}φ} − γ^{(k)}_{e^{-iNL_N}φ}‖₁` for the combined contour
(the six pieces of `Γ_a` with weight `p_t = Σ_{r∈R} t_r z^r`, followed by the fixed pieces `Pf`) and the background `B`. -/
def mixedGap (L : ℝ) [Fact (0 < L)] (κ h : ℝ) (k q : ℕ) (a : ℝ) (R : Finset ℕ) (t : ℕ → ℝ)
    {nf : ℕ} (Pf : Fin nf → Piece) {Z : Set ℂ} {d₀ s₁ a₀ c₁ : ℝ} (B : BgFam Z d₀ s₁ a₀ c₁)
    (phi : SymSector ℂ (L2T L) (k + q)) : ℝ≥0∞ :=
  QuantumNLS.TraceClass.traceNorm
    (reducedDensityPower k q
        ((evol (((((k + q : ℕ) : ℝ) : ℂ)) •
          C0op (nu (6 + nf)) (fun θ => normalizedTransfer L κ (k + q)
            (zθ (Fin.append (rectPieces a h (polyT R t) (continuous_polyT R t)) Pf) θ))
            (uθ κ (Fin.append (rectPieces a h (polyT R t) (continuous_polyT R t)) Pf))
            (gθ (Fin.append (rectPieces a h (polyT R t) (continuous_polyT R t)) Pf) B)) 1 phi :
          SymSector ℂ (L2T L) (k + q)) : HilbertTensorPower ℂ (L2T L) (k + q)) -
      reducedDensityPower k q
        ((evol (((((k + q : ℕ) : ℝ) : ℂ)) •
          Lop (nu (6 + nf)) (fun θ => normalizedTransfer L κ (k + q)
            (zθ (Fin.append (rectPieces a h (polyT R t) (continuous_polyT R t)) Pf) θ))
            (uθ κ (Fin.append (rectPieces a h (polyT R t) (continuous_polyT R t)) Pf))
            (dθ (Fin.append (rectPieces a h (polyT R t) (continuous_polyT R t)) Pf) B)) 1 phi :
          SymSector ℂ (L2T L) (k + q)) : HilbertTensorPower ℂ (L2T L) (k + q)))

/-! ### 4. PROP-026 for the actual mixed model -/

/-- The PROP-017 growing-window event `𝓔_N` (support of `P^g_N`). -/
abbrev gEvent (L κ : ℝ) (μ : Measure ℝ) (θ γ ρ h : ℝ) (b : ℕ) (N : ℕ) : Set (MArr N) :=
  EN μ (qAct L κ N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h (eta0 L κ) ((N : ℝ) ^ (-γ)) b

open Classical in
/-- **PROP-026 `lem:MP-linearization`, actual mixed model, one theorem.**  See the module header. -/
theorem prop026_mixed (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ} (hηh : eta0 L κ < h)
    (hδ : 0 < δ) (hd0 : 0 < d0) (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (b pc : ℕ) (hb : 1 ≤ b) (hbpc : b ≤ 2 * pc)
    (θ γ : ℝ) (hθ : 0 < θ) (hγ : 0 < γ) (hsum : 3 * γ + θ < 1) (pt : ℕ) (hpt : 1 < 2 * (pt : ℝ) * θ)
    (d k : ℕ) (R : Finset ℕ) (hRd : ∀ r ∈ R, r ≤ d) (T : ℕ → ℝ)
    -- the fixed-action datum
    (S : IndexedScalarMeasureCuts L κ) (hS : (μ : Measure ℝ) = S.μ)
    {r : ℕ} {n : Fin r → ℤ} {xm xp hf : Fin r → ℝ}
    (hxm : ∀ i, xm i ∈ S.cuts) (hxp : ∀ i, xp i ∈ S.cuts) (hlt : ∀ i, xm i < xp i) (hfpos : ∀ i, 0 < hf i)
    (hfh : ∀ i, hf i ≤ h)
    (h1 : ∀ i, 2 * Real.pi * (n i - 1) < exteriorForce L κ S.μ (xm i))
    (h2 : ∀ i, exteriorForce L κ S.μ (xm i) < 2 * Real.pi * n i)
    (h3 : ∀ i, 2 * Real.pi * n i < exteriorForce L κ S.μ (xp i))
    (h4 : ∀ i, exteriorForce L κ S.μ (xp i) < 2 * Real.pi * (n i + 1))
    -- the fixed pieces (weights `θ_n`) lying on the fixed contours
    {nf : ℕ} (Pf : Fin nf → Piece) (Λ : ℝ) (hΛ0 : 0 ≤ Λ) (hΛ : ∑ j, wlen (Pf j) ≤ Λ)
    (hPfZ : ∀ j, ∀ τ ∈ Icc (0 : ℝ) 1, ∃ i, (Pf j).γ τ ∈ Gam (xm i) (xp i) (hf i))
    (hPfreal : ∀ j, ∀ τ ∈ Ioo (0 : ℝ) 1, ((Pf j).γ τ).im ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ (EI : ∀ N : ℕ, Set (MArr N)) (ρI : ℕ → ℝ), (∀ N, 0 ≤ ρI N) ∧ Tendsto ρI atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real (EI N)ᶜ) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real
        (gEvent L κ (μ : Measure ℝ) θ γ ρ h b N ∩ EI N)ᶜ) atTop (𝓝 0) ∧
      (∀ (N : ℕ) (hN : 0 < N), ∃ Pg PI P : QuantumNLS.KernelDefinition.BoundedSymmetricKernel (L2T L) N,
        IsEventProj hκ u hu hN (gEvent L κ (μ : Measure ℝ) θ γ ρ h b N) Pg ∧ IsEventProj hκ u hu hN (EI N) PI ∧
        IsEventProj hκ u hu hN (gEvent L κ (μ : Measure ℝ) θ γ ρ h b N ∩ EI N) P ∧ P = Pg * PI ∧
        ‖(1 - P) (QuantumNLS.HighMomentsOps.wvec N u)‖ ^ 2 ≤
          ‖(1 - Pg) (QuantumNLS.HighMomentsOps.wvec N u)‖ ^ 2 + ‖(1 - PI) (QuantumNLS.HighMomentsOps.wvec N u)‖ ^ 2) ∧
      ∃ d₀ s₁ a₀ c₁ C : ℝ, 0 < d₀ ∧ 0 ≤ s₁ ∧ 0 < a₀ ∧ 0 ≤ c₁ ∧ 0 ≤ C ∧
        ∀ᶠ q : ℕ in atTop, ∀ (hN : 1 ≤ k + q) (φ : SymSector ℂ (L2T L) (k + q)), ‖φ‖ = 1 →
          (∀ m ∉ gEvent L κ (μ : Measure ℝ) θ γ ρ h b (k + q) ∩ EI (k + q),
            ⟪meanField_physicalBasis L (k + q) hN hκ m, φ⟫_ℂ = 0) →
          ∃ B : BgFam (NbhdN (cutN L θ (k + q)) h (ρ / 8) ∪ ⋃ i, Gam (xm i) (xp i) (hf i)) d₀ s₁ a₀ c₁,
            B.c0 = (fun z => Complex.I * κ * Gfull (μ : Measure ℝ) z) ∧ B.D = Df L κ (Gfull (μ : Measure ℝ)) ∧
            B.s = sf L κ (Gfull (μ : Measure ℝ)) ∧ B.A = Af κ (Gfull (μ : Measure ℝ)) ∧
            ∀ (t : ℕ → ℝ), (∀ r ∈ R, |t r| ≤ T r) →
              mixedGap L κ h k q (cutN L θ (k + q)) R t Pf B φ ≤
                ENNReal.ofReal (C * ((1 + cutN L θ (k + q)) ^ (d + 1) *
                  ((((k + q : ℕ) : ℝ)) ^ (-γ) + 1 / ((((k + q : ℕ) : ℝ)) ^ θ) ^ b + 1 / ((k + q : ℕ) : ℝ)) +
                  ρI (k + q))) := by
  have hL : 0 < L := Fact.out
  obtain ⟨ρ, hρ0, h2ρ, hprob, C0, M, η, rr, K, Kd, hM1, hη, hr0, hK0, hev⟩ :=
    moving_contour_bundle hκ u hu hμ hηh hδ hd0 hin b pc hb hbpc θ γ hθ hγ hsum pt hpt
  have hh : 0 < h := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  obtain ⟨EI, ρI, hρI0, hρIlim, hmassI, -, hfix⟩ :=
    QuantumNLS.Prop009FixedProjection.fixed_projection hκ u hu hμ S hS hxm hxp hlt hfpos h1 h2 h3 h4
  obtain ⟨ηf, Mf, Gbf, hηf, hMf, hGbf, hbf⟩ := gam_family_background S hxm hxp hlt hfpos h1 h2 h3 h4
  have hGeq : Gfull (μ : Measure ℝ) = EmpiricalRapidity.cauchyTransform S.μ := by
    funext z; rw [Gfull_eq, hS]; rfl
  have hbf' : ∀ z ∈ (⋃ i, Gam (xm i) (xp i) (hf i)),
      DifferentiableAt ℂ (Gfull (μ : Measure ℝ)) z ∧ ηf ≤ ‖Df L κ (Gfull (μ : Measure ℝ)) z‖ ∧
      ‖Af κ (Gfull (μ : Measure ℝ)) z‖ ≤ Mf ∧ ‖(Af κ (Gfull (μ : Measure ℝ)) z)⁻¹‖ ≤ Mf ∧ ‖ef L z‖ ≤ Mf ∧
      ‖Gfull (μ : Measure ℝ) z‖ ≤ Gbf := by
    intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
    rw [hGeq]; exact hbf i z hi
  have hGb1 : 0 ≤ 2 * K + 1 / rr := by positivity
  have hMm : 1 ≤ max M Mf := hM1.trans (le_max_left _ _)
  have hMm0 : 0 < max M Mf := by linarith
  obtain ⟨C, hC0, hCb⟩ := mp_linearization_contours L κ hκ h hh k (min η ηf) (max M Mf + max M Mf * max M Mf)
    (1 / max M Mf) (κ * max (2 * K + 1 / rr) Gbf) (lt_min hη hηf) (by nlinarith) (by positivity)
    (mul_nonneg hκ.le (le_trans hGb1 (le_max_left _ _))) d R hRd T Λ
  set c1 : ℝ := max Kd 0 * (4 * (∑ r ∈ R, T r) * (1 + h) ^ (d + 1)) with hc1
  have hinv : 0 ≤ (2 * Real.pi * κ)⁻¹ := by positivity
  have hkq : Tendsto (fun q : ℕ => k + q) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat k
  refine ⟨ρ, hρ0, EI, ρI, hρI0, hρIlim, hmassI, ?_, fun N hN =>
    common_projection hκ u hu hN (gEvent L κ (μ : Measure ℝ) θ γ ρ h b N) (EI N), min η ηf,
    max M Mf + max M Mf * max M Mf, 1 / max M Mf, κ * max (2 * K + 1 / rr) Gbf,
    C * (2 * Real.pi * κ)⁻¹ * max c1 Λ, lt_min hη hηf, by nlinarith, by positivity,
    mul_nonneg hκ.le (le_trans hGb1 (le_max_left _ _)),
    mul_nonneg (mul_nonneg hC0 hinv) (le_trans hΛ0 (le_max_right _ _)), ?_⟩
  · -- the mass of the common projection
    refine squeeze_zero' (Eventually.of_forall fun N => measureReal_nonneg)
      (Eventually.of_forall fun N => ?_) (by simpa using hprob.add hmassI)
    rw [Set.compl_inter]
    exact measureReal_union_le _ _
  set Eg : (N : ℕ) → Set (MArr N) := fun N => gEvent L κ (μ : Measure ℝ) θ γ ρ h b N with hEg
  have hdev := deviation_of_bundle hκ (μ : Measure ℝ) (h := h) (ρ := ρ) (Kd := Kd) (θ := θ) (γ := γ) (b := b) Eg
    (hev.mono fun N hN m hm z hz => ⟨(hN m hm z hz).1.1, (hN m hm z hz).2.2.2.2.2.2.2.2.2 0⟩)
  filter_upwards [hkq.eventually (hev.and (hdev.and (regime_eventually hL hθ hγ 1 0))), hkq.eventually hfix]
    with q ⟨hevN, hdevN, hreg⟩ hfixN
  intro hN φ hφ hsupp
  have hsuppg : ∀ m ∉ Eg (k + q), ⟪meanField_physicalBasis L (k + q) hN hκ m, φ⟫_ℂ = 0 :=
    fun m hm => hsupp m (fun hmE => hm hmE.1)
  have hsuppI : ∀ m ∉ EI (k + q), ⟪meanField_physicalBasis L (k + q) hN hκ m, φ⟫_ℂ = 0 :=
    fun m hm => hsupp m (fun hmE => hm hmE.2)
  have hNr : (0 : ℝ) < ((k + q : ℕ) : ℝ) := by exact_mod_cast hN
  set a := cutN L θ (k + q) with ha
  have ha2 : 2 ≤ a := by linarith [hreg.1, hreg.2.2.1]
  -- a label of the growing-window event
  obtain ⟨m0, hm0⟩ : ∃ m, m ∈ Eg (k + q) := by
    by_contra hne
    push Not at hne
    have hs := QuantumNLS.RootMeasureTransfer.hasSum_norm_sq (meanField_physicalBasis L (k + q) hN hκ) φ
    have h0 : (fun m => ‖⟪meanField_physicalBasis L (k + q) hN hκ m, φ⟫_ℂ‖ ^ 2) = fun _ => (0 : ℝ) := by
      funext m; rw [hsuppg m (hne m), norm_zero]; ring
    rw [h0] at hs
    have := hs.unique hasSum_zero
    rw [hφ] at this; norm_num at this
  have hP := fun z (hz : z ∈ NbhdN a h (ρ / 8)) => hevN m0 hm0 z hz
  have hGle : ∀ z ∈ NbhdN a h (ρ / 8), ‖Gfull (μ : Measure ℝ) z‖ ≤ 2 * K + 1 / rr := fun z hz => by
    have hPz := hP z hz
    have hG1 := hPz.2.2.1
    have hN1 : 1 ≤ ((k + q : ℕ) : ℝ) ^ θ := hreg.1
    have hRb : 1 / (((k + q : ℕ) : ℝ) ^ θ) ^ b ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ hN1
    have hGN : ‖GN (qAct L κ (k + q) m0) z‖ ≤ 1 / rr := by
      unfold GN
      rw [norm_mul]
      have hs : ‖∑ j, 1 / (z - (qAct L κ (k + q) m0 j : ℂ))‖ ≤ ∑ _j : Fin (k + q), 1 / rr := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_div, norm_one]
        exact one_div_le_one_div_of_le hr0 (hPz.2.2.2.1 j)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
      calc ‖1 / ((k + q : ℕ) : ℂ)‖ * ‖∑ j, 1 / (z - (qAct L κ (k + q) m0 j : ℂ))‖ ≤
            (1 / ((k + q : ℕ) : ℝ)) * (((k + q : ℕ) : ℝ) * (1 / rr)) := by
            refine mul_le_mul (le_of_eq ?_) hs (norm_nonneg _) (by positivity)
            rw [norm_div, norm_one, Complex.norm_natCast]
        _ = 1 / rr := by field_simp
    have := norm_sub_le (Gfull (μ : Measure ℝ) z - GN (qAct L κ (k + q) m0) z) (-GN (qAct L κ (k + q) m0) z)
    rw [sub_neg_eq_add, sub_add_cancel, norm_neg] at this
    have hKb : K * (((k + q : ℕ) : ℝ) ^ (-γ) + 1 / (((k + q : ℕ) : ℝ) ^ θ) ^ b) ≤ K * 2 :=
      mul_le_mul_of_nonneg_left (by linarith [hreg.2.2.2.2]) hK0
    linarith
  have hZ1 : ∀ z ∈ NbhdN a h (ρ / 8), DifferentiableAt ℂ (Gfull (μ : Measure ℝ)) z := fun z hz =>
    (hP z hz).2.2.2.2.1
  let B : BgFam (NbhdN a h (ρ / 8) ∪ ⋃ i, Gam (xm i) (xp i) (hf i)) (min η ηf)
      (max M Mf + max M Mf * max M Mf) (1 / max M Mf) (κ * max (2 * K + 1 / rr) Gbf) :=
    bgfamOfG_union L κ (Gfull (μ : Measure ℝ)) (NbhdN a h (ρ / 8)) (⋃ i, Gam (xm i) (xp i) (hf i))
      hη hηf hM1 hMf hGb1 hGbf hκ.le
      (fun z hz => hz.elim (fun h' => hZ1 z h') (fun h' => (hbf' z h').1))
      (fun z hz => (hP z hz).2.2.2.2.2.1) (fun z hz => (hbf' z hz).2.1)
      (fun z hz => (hP z hz).2.2.2.2.2.2.1) (fun z hz => (hbf' z hz).2.2.1)
      (fun z hz => (hP z hz).2.2.2.2.2.2.2.1) (fun z hz => (hbf' z hz).2.2.2.1)
      (fun z hz => (hP z hz).2.2.2.2.2.2.2.2.1) (fun z hz => (hbf' z hz).2.2.2.2.1)
      hGle (fun z hz => (hbf' z hz).2.2.2.2.2)
  refine ⟨B, rfl, rfl, rfl, rfl, fun t ht => ?_⟩
  set δN : ℝ := ((k + q : ℕ) : ℝ) ^ (-γ) + 1 / (((k + q : ℕ) : ℝ) ^ θ) ^ b + 1 / ((k + q : ℕ) : ℝ) with hδNdef
  have hδN0 : 0 ≤ δN := by
    have : 0 < ((k + q : ℕ) : ℝ) ^ θ := Real.rpow_pos_of_pos hNr θ
    have : 0 < ((k + q : ℕ) : ℝ) ^ (-γ) := Real.rpow_pos_of_pos hNr _
    rw [hδNdef]; positivity
  have hrect : ∀ i : Fin 6, ∀ τ ∈ Icc (0 : ℝ) 1,
      (rectPieces a h (polyT R t) (continuous_polyT R t) i).γ τ ∈ NbhdN a h (ρ / 8) := fun i τ hτ =>
    ⟨_, rect_mem (by linarith) hh.le _ _ i hτ, by rw [sub_self, norm_zero]; positivity⟩
  have hmain := hCb q hN a (by linarith) t ht Pf hΛ (NbhdN a h (ρ / 8) ∪ ⋃ i, Gam (xm i) (xp i) (hf i))
    (fun i τ hτ => Or.inl (hrect i τ hτ))
    (fun j τ hτ => by
      obtain ⟨i, hi⟩ := hPfZ j τ hτ
      exact Or.inr (Set.mem_iUnion.2 ⟨i, hi⟩))
    (fun j τ hτ => by
      obtain ⟨i, hi⟩ := hPfZ j τ hτ
      exact (Gam_im_le (hfpos i).le hi).trans (hfh i))
    hPfreal B φ hφ (max Kd 0 * δN) (ρI (k + q)) (mul_nonneg (le_max_right _ _) hδN0) (hρI0 _)
    (fun i τ hτ => by
      have := hdevN hN φ hsuppg _ (hrect i τ hτ)
      rw [hφ, mul_one] at this
      exact this)
    (fun j τ hτ => by
      obtain ⟨i, hi⟩ := hPfZ j τ hτ
      have := hfixN hN φ hsuppI i _ hi
      rw [hφ, mul_one] at this
      show ‖(normalizedTransfer L κ (k + q) ((Pf j).γ τ) -
        sf L κ (Gfull (μ : Measure ℝ)) ((Pf j).γ τ) • 1) φ‖ ≤ ρI (k + q)
      rw [hGeq]
      exact this)
  refine le_trans hmain (ENNReal.ofReal_le_ofReal ?_)
  have hx : 0 ≤ (1 + a) ^ (d + 1) * δN := by
    have : 0 ≤ 1 + a := by linarith
    positivity
  have hy : 0 ≤ ρI (k + q) := hρI0 _
  have key : c1 * ((1 + a) ^ (d + 1) * δN) + Λ * ρI (k + q) ≤
      max c1 Λ * ((1 + a) ^ (d + 1) * δN + ρI (k + q)) := by
    nlinarith [mul_nonneg (sub_nonneg.2 (le_max_left c1 Λ)) hx, mul_nonneg (sub_nonneg.2 (le_max_right c1 Λ)) hy]
  have hCi : 0 ≤ C * (2 * Real.pi * κ)⁻¹ := mul_nonneg hC0 hinv
  calc C * ((2 * Real.pi * κ)⁻¹ * (max Kd 0 * δN * (4 * (∑ r ∈ R, T r) * (1 + h) ^ (d + 1) * (1 + a) ^ (d + 1)) +
        ρI (k + q) * Λ))
      = C * (2 * Real.pi * κ)⁻¹ * (c1 * ((1 + a) ^ (d + 1) * δN) + Λ * ρI (k + q)) := by
        rw [hc1]; ring
    _ ≤ C * (2 * Real.pi * κ)⁻¹ * (max c1 Λ * ((1 + a) ^ (d + 1) * δN + ρI (k + q))) :=
        mul_le_mul_of_nonneg_left key hCi
    _ = C * (2 * Real.pi * κ)⁻¹ * max c1 Λ * ((1 + a) ^ (d + 1) * δN + ρI (k + q)) := by ring

end QuantumNLS.Prop026Mixed

#print axioms QuantumNLS.Prop026Mixed.gam_family_background
#print axioms QuantumNLS.Prop026Mixed.common_projection
#print axioms QuantumNLS.Prop026Mixed.prop026_mixed
