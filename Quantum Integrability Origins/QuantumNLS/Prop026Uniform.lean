import Mathlib
import QuantumNLS.Prop026Mixed
import QuantumNLS.Prop026FullPacket
import QuantumNLS.Prop026Bound

/-!
# PROP-026 `lem:MP-linearization`, actual mixed model: uniformity over the fixed-action ANGLE BOX, physical scalar datum bound (no `hS`)

Terra r11 hold (`mixed_propagation.tex:73, 354-364`): the statement must hold uniformly for `|θ_n| ≤ Θ_n`, with one event, one threshold and one constant.
* `prop026_uniform_gen`: copy of `Prop026Full.prop026_full` with the quantifiers moved: the common length bound `Λ` (a number, e.g. `Σ Θ_i · length(Γ_i)`) comes first,
  then `ρ, R₀, EI, ρI, d₀, s₁, a₀, c₁, C, N₀` (independent of the fixed pieces), then for each `ε, N, R, a` and each admissible `φ` ONE background `B`,
  and only then ALL fixed pieces `Pf` with `Σ wlen(Pf) ≤ Λ` lying on the fixed contours (`mp_linearization_contours` already quantifies `Pf` after `C`);
* `rectFamily` / `rectFamily_props`: the literal rectangular pieces `∂([x₋,x₊]×[−h,h])` with constant weights `θ_i`, whose weighted length is `≤ Σ|θ_i|(2(x₊−x₋)+4h) ≤ Σ Θ_i(…)` for `|θ_i| ≤ Θ_i`;
* **`prop026_uniform`**: the physical binding. The scalar datum is `Prop026Bound.scalarCuts` (sol_multi, frozen, read-only), the carried `hS` is discharged by
  `Prop026Bound.physical_eq_limit`; the only hypotheses left are `hμ`, `hin : RootSpectralInputs` (even moments, r156) and the PROP-006 brackets of the fixed contours.
-/

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace QuantumNLS.Prop026Uniform

open QuantumNLS.PhysicalTensor (L2T physSector)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis IsLimitingRapidityMeasure)
open QuantumNLS.Extrapolation (Gfull GN)
open QuantumNLS.RootEvent (EN)
open QuantumNLS.ResolventNeighborhood (GammaN NbhdN)
open QuantumNLS.Prop017Quantum (qAct eta0 Gfull_eq)
open QuantumNLS.Prop017Physical (RootSpectralInputs)
open QuantumNLS.PeriodReconstructionCore
open QuantumNLS.PeriodReconstruction (Gam)
open QuantumNLS.Prop019Linearization (rect_mem rect_im_ne gammaN_abs)
open QuantumNLS.MPContour (Piece ThetaSpace nu zθ uθ rectPieces polyT continuous_polyT wlen)
open QuantumNLS.MPFamily (BgFam gθ dθ)
open QuantumNLS.TensorCarrier (SymSector HilbertTensorPower reducedDensityPower)
open QuantumNLS.NormalizedTransfer (normalizedTransfer)
open QuantumNLS.UnconditionalBetheBasis (meanField_physicalBasis)
open QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts
open QuantumNLS.MPFixedContour (bgfamOfG_union)
open QuantumNLS.MPLinearizationContours (mp_linearization_contours)
open QuantumNLS.Prop009ProbeDev (Gam_im_le)
open QuantumNLS.Prop026Mixed (IsEventProj common_projection mixedGap gam_family_background)
open QuantumNLS.MPFixedContour (rectGen rectGen_mem_Gam rectGen_im_ne rectGen_wlen_le)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

open Classical in
/-- **PROP-026 `lem:MP-linearization`, actual mixed model, full tolerance regime `0 < ε ≤ 1`.** -/
theorem prop026_uniform_gen (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ} (hηh : eta0 L κ < h)
    (hδ : 0 < δ) (hd0 : 0 < d0) (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (b pc : ℕ) (hb : 1 ≤ b) (hbpc : b ≤ 2 * pc)
    (d k : ℕ) (ords : Finset ℕ) (hRd : ∀ r ∈ ords, r ≤ d) (T : ℕ → ℝ)
    (S : IndexedScalarMeasureCuts L κ) (hS : (μ : Measure ℝ) = S.μ)
    {r : ℕ} {n : Fin r → ℤ} {xm xp hf : Fin r → ℝ}
    (hxm : ∀ i, xm i ∈ S.cuts) (hxp : ∀ i, xp i ∈ S.cuts) (hlt : ∀ i, xm i < xp i) (hfpos : ∀ i, 0 < hf i)
    (hfh : ∀ i, hf i ≤ h)
    (h1 : ∀ i, 2 * Real.pi * (n i - 1) < exteriorForce L κ S.μ (xm i))
    (h2 : ∀ i, exteriorForce L κ S.μ (xm i) < 2 * Real.pi * n i)
    (h3 : ∀ i, 2 * Real.pi * n i < exteriorForce L κ S.μ (xp i))
    (h4 : ∀ i, exteriorForce L κ S.μ (xp i) < 2 * Real.pi * (n i + 1))
    (Λ : ℝ) (hΛ0 : 0 ≤ Λ) :
    ∃ ρ R0 : ℝ, 0 < ρ ∧ 1 ≤ R0 ∧ ∃ (EI : ∀ N : ℕ, Set (MArr N)) (ρI : ℕ → ℝ), (∀ N, 0 ≤ ρI N) ∧
      Tendsto ρI atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real (EI N)ᶜ) atTop (𝓝 0) ∧
      ∃ d₀ s₁ a₀ c₁ C : ℝ, 0 < d₀ ∧ 0 ≤ s₁ ∧ 0 < a₀ ∧ 0 ≤ c₁ ∧ 0 ≤ C ∧ ∃ N0 : ℕ,
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ q : ℕ, N0 ≤ k + q → ∀ hN : 1 ≤ k + q,
        ∀ R : ℝ, R0 ≤ R → ∀ l : ℕ, l0 ≤ l → ∀ a : ℝ, a = QuantumNLS.PROP017UniformN.cutSeq L l → 2 * R ≤ a →
          (∃ Pg PI P : QuantumNLS.KernelDefinition.BoundedSymmetricKernel (L2T L) (k + q),
            IsEventProj hκ u hu (by omega : 0 < k + q)
              (EN (μ : Measure ℝ) (qAct L κ (k + q)) R a ρ h (eta0 L κ) ε b) Pg ∧
            IsEventProj hκ u hu (by omega : 0 < k + q) (EI (k + q)) PI ∧
            IsEventProj hκ u hu (by omega : 0 < k + q)
              (EN (μ : Measure ℝ) (qAct L κ (k + q)) R a ρ h (eta0 L κ) ε b ∩ EI (k + q)) P ∧
            P = Pg * PI ∧
            ‖(1 - P) (QuantumNLS.HighMomentsOps.wvec (k + q) u)‖ ^ 2 ≤
              ‖(1 - Pg) (QuantumNLS.HighMomentsOps.wvec (k + q) u)‖ ^ 2 +
                ‖(1 - PI) (QuantumNLS.HighMomentsOps.wvec (k + q) u)‖ ^ 2) ∧
          ∀ φ : SymSector ℂ (L2T L) (k + q), ‖φ‖ = 1 →
            (∀ m ∉ EN (μ : Measure ℝ) (qAct L κ (k + q)) R a ρ h (eta0 L κ) ε b ∩ EI (k + q),
              ⟪meanField_physicalBasis L (k + q) hN hκ m, φ⟫_ℂ = 0) →
            ∃ B : BgFam (NbhdN a h (ρ / 8) ∪ ⋃ i, Gam (xm i) (xp i) (hf i)) d₀ s₁ a₀ c₁,
              B.c0 = (fun z => Complex.I * κ * Gfull (μ : Measure ℝ) z) ∧ B.D = Df L κ (Gfull (μ : Measure ℝ)) ∧
              B.s = sf L κ (Gfull (μ : Measure ℝ)) ∧ B.A = Af κ (Gfull (μ : Measure ℝ)) ∧
              ∀ {nf : ℕ} (Pf : Fin nf → Piece), ∑ j, wlen (Pf j) ≤ Λ →
              (∀ j, ∀ τ ∈ Icc (0 : ℝ) 1, ∃ i, (Pf j).γ τ ∈ Gam (xm i) (xp i) (hf i)) →
              (∀ j, ∀ τ ∈ Ioo (0 : ℝ) 1, ((Pf j).γ τ).im ≠ 0) →
              ∀ (t : ℕ → ℝ), (∀ r ∈ ords, |t r| ≤ T r) →
                mixedGap L κ h k q a ords t Pf B φ ≤
                  ENNReal.ofReal (C * ((1 + a) ^ (d + 1) * (ε + 1 / R ^ b + 1 / ((k + q : ℕ) : ℝ)) +
                    ρI (k + q))) := by
  have hL : 0 < L := Fact.out
  obtain ⟨ρ, R0, η, M, rr, Kd, hρ0, h2ρ, hR01, hη, hM1, hr0, hKd, N0p, hpkt⟩ :=
    QuantumNLS.Prop026FullPacket.uniform_packet_data hκ u hu hμ hηh hδ hd0 hin b pc hb hbpc
  have hh : 0 < h := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  obtain ⟨EI, ρI, hρI0, hρIlim, hmassI, -, hfix⟩ :=
    QuantumNLS.Prop009FixedProjection.fixed_projection hκ u hu hμ S hS hxm hxp hlt hfpos h1 h2 h3 h4
  obtain ⟨NI, hNI⟩ := eventually_atTop.1 hfix
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
  have hGb1 : 0 ≤ 1 / rr := by positivity
  have hMm : 1 ≤ max M Mf := hM1.trans (le_max_left _ _)
  have hMm0 : 0 < max M Mf := by linarith
  obtain ⟨C, hC0, hCb⟩ := mp_linearization_contours L κ hκ h hh k (min η ηf) (max M Mf + max M Mf * max M Mf)
    (1 / max M Mf) (κ * max (1 / rr) Gbf) (lt_min hη hηf) (by nlinarith) (by positivity)
    (mul_nonneg hκ.le (le_trans hGb1 (le_max_left _ _))) d ords hRd T Λ
  set c1 : ℝ := Kd * (4 * (∑ r ∈ ords, T r) * (1 + h) ^ (d + 1)) with hc1
  have hinv : 0 ≤ (2 * Real.pi * κ)⁻¹ := by positivity
  refine ⟨ρ, R0, hρ0, hR01, EI, ρI, hρI0, hρIlim, hmassI, min η ηf,
    max M Mf + max M Mf * max M Mf, 1 / max M Mf, κ * max (1 / rr) Gbf,
    C * (2 * Real.pi * κ)⁻¹ * max c1 Λ, lt_min hη hηf, by nlinarith, by positivity,
    mul_nonneg hκ.le (le_trans hGb1 (le_max_left _ _)),
    mul_nonneg (mul_nonneg hC0 hinv) (le_trans hΛ0 (le_max_right _ _)), max N0p NI, ?_⟩
  intro ε hε hε1 q hNq hN R hR l hl a ha h2R
  have hNr : (0 : ℝ) < ((k + q : ℕ) : ℝ) := by exact_mod_cast hN
  have hN0p : N0p ≤ k + q := (le_max_left _ _).trans hNq
  have hNIq : NI ≤ k + q := (le_max_right _ _).trans hNq
  refine ⟨common_projection hκ u hu (by omega : 0 < k + q) _ (EI (k + q)), ?_⟩
  intro φ hφ hsupp
  set Eg : Set (MArr (k + q)) := EN (μ : Measure ℝ) (qAct L κ (k + q)) R a ρ h (eta0 L κ) ε b with hEg
  have hsuppg : ∀ m ∉ Eg, ⟪meanField_physicalBasis L (k + q) hN hκ m, φ⟫_ℂ = 0 :=
    fun m hm => hsupp m (fun hmE => hm hmE.1)
  have hsuppI : ∀ m ∉ EI (k + q), ⟪meanField_physicalBasis L (k + q) hN hκ m, φ⟫_ℂ = 0 :=
    fun m hm => hsupp m (fun hmE => hm hmE.2)
  obtain ⟨hbgP, hdevP⟩ := hpkt ε hε hε1 (k + q) hN0p hN R hR l hl a ha h2R
  have hR1 : 1 ≤ R := hR01.trans hR
  have ha2 : 2 ≤ a := by linarith
  have hZ1 := hbgP
  let B : BgFam (NbhdN a h (ρ / 8) ∪ ⋃ i, Gam (xm i) (xp i) (hf i)) (min η ηf)
      (max M Mf + max M Mf * max M Mf) (1 / max M Mf) (κ * max (1 / rr) Gbf) :=
    bgfamOfG_union L κ (Gfull (μ : Measure ℝ)) (NbhdN a h (ρ / 8)) (⋃ i, Gam (xm i) (xp i) (hf i))
      hη hηf hM1 hMf hGb1 hGbf hκ.le
      (fun z hz => hz.elim (fun h' => (hZ1 z h').1) (fun h' => (hbf' z h').1))
      (fun z hz => (hZ1 z hz).2.1) (fun z hz => (hbf' z hz).2.1)
      (fun z hz => (hZ1 z hz).2.2.1) (fun z hz => (hbf' z hz).2.2.1)
      (fun z hz => (hZ1 z hz).2.2.2.1) (fun z hz => (hbf' z hz).2.2.2.1)
      (fun z hz => (hZ1 z hz).2.2.2.2.1) (fun z hz => (hbf' z hz).2.2.2.2.1)
      (fun z hz => (hZ1 z hz).2.2.2.2.2) (fun z hz => (hbf' z hz).2.2.2.2.2)
  refine ⟨B, rfl, rfl, rfl, rfl, fun {nf} Pf hΛ hPfZ hPfreal t ht => ?_⟩
  set δN : ℝ := ε + 1 / R ^ b + 1 / ((k + q : ℕ) : ℝ) with hδNdef
  have hδN0 : 0 ≤ δN := by
    have : 0 < R := by linarith
    rw [hδNdef]; positivity
  have hrect : ∀ i : Fin 6, ∀ τ ∈ Icc (0 : ℝ) 1,
      (rectPieces a h (polyT ords t) (continuous_polyT ords t) i).γ τ ∈ NbhdN a h (ρ / 8) := fun i τ hτ =>
    ⟨_, rect_mem (by linarith) hh.le _ _ i hτ, by rw [sub_self, norm_zero]; positivity⟩
  have hmain := hCb q hN a (by linarith) t ht Pf hΛ (NbhdN a h (ρ / 8) ∪ ⋃ i, Gam (xm i) (xp i) (hf i))
    (fun i τ hτ => Or.inl (hrect i τ hτ))
    (fun j τ hτ => by
      obtain ⟨i, hi⟩ := hPfZ j τ hτ
      exact Or.inr (Set.mem_iUnion.2 ⟨i, hi⟩))
    (fun j τ hτ => by
      obtain ⟨i, hi⟩ := hPfZ j τ hτ
      exact (Gam_im_le (hfpos i).le hi).trans (hfh i))
    hPfreal B φ hφ (Kd * δN) (ρI (k + q)) (mul_nonneg hKd hδN0) (hρI0 _)
    (fun i τ hτ => by
      have := hdevP φ hsuppg _ (hrect i τ hτ)
      rw [hφ, mul_one] at this
      exact this)
    (fun j τ hτ => by
      obtain ⟨i, hi⟩ := hPfZ j τ hτ
      have := hNI (k + q) hNIq hN φ hsuppI i _ hi
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
  calc C * ((2 * Real.pi * κ)⁻¹ * (Kd * δN * (4 * (∑ r ∈ ords, T r) * (1 + h) ^ (d + 1) * (1 + a) ^ (d + 1)) +
        ρI (k + q) * Λ))
      = C * (2 * Real.pi * κ)⁻¹ * (c1 * ((1 + a) ^ (d + 1) * δN) + Λ * ρI (k + q)) := by
        rw [hc1]; ring
    _ ≤ C * (2 * Real.pi * κ)⁻¹ * (max c1 Λ * ((1 + a) ^ (d + 1) * δN + ρI (k + q))) :=
        mul_le_mul_of_nonneg_left key hCi
    _ = C * (2 * Real.pi * κ)⁻¹ * max c1 Λ * ((1 + a) ^ (d + 1) * δN + ρI (k + q)) := by ring


/-! ### The literal rectangular family and the angle box -/

/-- The six pieces of `∂([x₋,x₊]×[−h,h])` for each fixed contour, with the constant weight `θ_i`. -/
def rectFamily {r : ℕ} (xm xp hf θf : Fin r → ℝ) : Fin (r * 6) → Piece := fun j =>
  rectGen (xm (finProdFinEquiv.symm j).1) (xp (finProdFinEquiv.symm j).1) (hf (finProdFinEquiv.symm j).1)
    (fun _ => ((θf (finProdFinEquiv.symm j).1 : ℝ) : ℂ)) continuous_const (finProdFinEquiv.symm j).2

theorem rectFamily_props {r : ℕ} (xm xp hf θf Θ : Fin r → ℝ) (hlt : ∀ i, xm i < xp i) (hfpos : ∀ i, 0 < hf i)
    (hθ : ∀ i, |θf i| ≤ Θ i) :
    ∑ j, wlen (rectFamily xm xp hf θf j) ≤ ∑ i, Θ i * (2 * (xp i - xm i) + 4 * hf i) ∧
    (∀ j, ∀ τ ∈ Icc (0 : ℝ) 1, ∃ i, (rectFamily xm xp hf θf j).γ τ ∈ Gam (xm i) (xp i) (hf i)) ∧
    (∀ j, ∀ τ ∈ Ioo (0 : ℝ) 1, ((rectFamily xm xp hf θf j).γ τ).im ≠ 0) := by
  refine ⟨?_, ?_, ?_⟩
  · have e : ∑ j, wlen (rectFamily xm xp hf θf j) = ∑ p : Fin r × Fin 6, wlen
        (rectGen (xm p.1) (xp p.1) (hf p.1) (fun _ => ((θf p.1 : ℝ) : ℂ)) continuous_const p.2) := by
      rw [← Equiv.sum_comp finProdFinEquiv.symm]
      rfl
    rw [e, Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 := rectGen_wlen_le (xm i) (xp i) (hf i) ((θf i : ℝ) : ℂ) (hlt i).le (hfpos i).le
    have h2 : (0 : ℝ) ≤ 2 * (xp i - xm i) + 4 * hf i := by linarith [hlt i, hfpos i]
    have h3 : ‖((θf i : ℝ) : ℂ)‖ = |θf i| := by simp
    rw [h3] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (hθ i) h2)
  · intro j τ hτ
    exact ⟨(finProdFinEquiv.symm j).1, rectGen_mem_Gam _ _ _ _ _ (hlt _).le (hfpos _).le _ hτ⟩
  · intro j τ hτ
    exact rectGen_im_ne _ _ _ _ _ (hfpos _) _ hτ

open Classical in
/-- **PROP-026 `lem:MP-linearization` (actual mixed model, full tolerance regime, angle box).** -/
theorem prop026_uniform (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ} (hηh : eta0 L κ < h)
    (hδ : 0 < δ) (hd0 : 0 < d0) (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (b pc : ℕ) (hb : 1 ≤ b) (hbpc : b ≤ 2 * pc)
    (d k : ℕ) (ords : Finset ℕ) (hRd : ∀ r ∈ ords, r ≤ d) (T : ℕ → ℝ)
    {r : ℕ} {n : Fin r → ℤ} {xm xp hf : Fin r → ℝ}
    (hxm : ∀ i, xm i ∈ QuantumNLS.Prop026Bound.cuts κ u) (hxp : ∀ i, xp i ∈ QuantumNLS.Prop026Bound.cuts κ u)
    (hlt : ∀ i, xm i < xp i) (hfpos : ∀ i, 0 < hf i) (hfh : ∀ i, hf i ≤ h)
    (h1 : ∀ i, 2 * Real.pi * (n i - 1) < exteriorForce L κ (QuantumNLS.Prop026Bound.M hκ u) (xm i))
    (h2 : ∀ i, exteriorForce L κ (QuantumNLS.Prop026Bound.M hκ u) (xm i) < 2 * Real.pi * n i)
    (h3 : ∀ i, 2 * Real.pi * n i < exteriorForce L κ (QuantumNLS.Prop026Bound.M hκ u) (xp i))
    (h4 : ∀ i, exteriorForce L κ (QuantumNLS.Prop026Bound.M hκ u) (xp i) < 2 * Real.pi * (n i + 1))
    (Θ : Fin r → ℝ) (hΘ : ∀ i, 0 ≤ Θ i) :
    ∃ ρ R0 : ℝ, 0 < ρ ∧ 1 ≤ R0 ∧ ∃ (EI : ∀ N : ℕ, Set (MArr N)) (ρI : ℕ → ℝ), (∀ N, 0 ≤ ρI N) ∧
      Tendsto ρI atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real (EI N)ᶜ) atTop (𝓝 0) ∧
      ∃ d₀ s₁ a₀ c₁ C : ℝ, 0 < d₀ ∧ 0 ≤ s₁ ∧ 0 < a₀ ∧ 0 ≤ c₁ ∧ 0 ≤ C ∧ ∃ N0 : ℕ,
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ q : ℕ, N0 ≤ k + q → ∀ hN : 1 ≤ k + q,
        ∀ R : ℝ, R0 ≤ R → ∀ l : ℕ, l0 ≤ l → ∀ a : ℝ, a = QuantumNLS.PROP017UniformN.cutSeq L l → 2 * R ≤ a →
          (∃ Pg PI P : QuantumNLS.KernelDefinition.BoundedSymmetricKernel (L2T L) (k + q),
            IsEventProj hκ u hu (by omega : 0 < k + q)
              (EN (μ : Measure ℝ) (qAct L κ (k + q)) R a ρ h (eta0 L κ) ε b) Pg ∧
            IsEventProj hκ u hu (by omega : 0 < k + q) (EI (k + q)) PI ∧
            IsEventProj hκ u hu (by omega : 0 < k + q)
              (EN (μ : Measure ℝ) (qAct L κ (k + q)) R a ρ h (eta0 L κ) ε b ∩ EI (k + q)) P ∧
            P = Pg * PI ∧
            ‖(1 - P) (QuantumNLS.HighMomentsOps.wvec (k + q) u)‖ ^ 2 ≤
              ‖(1 - Pg) (QuantumNLS.HighMomentsOps.wvec (k + q) u)‖ ^ 2 +
                ‖(1 - PI) (QuantumNLS.HighMomentsOps.wvec (k + q) u)‖ ^ 2) ∧
          ∀ φ : SymSector ℂ (L2T L) (k + q), ‖φ‖ = 1 →
            (∀ m ∉ EN (μ : Measure ℝ) (qAct L κ (k + q)) R a ρ h (eta0 L κ) ε b ∩ EI (k + q),
              ⟪meanField_physicalBasis L (k + q) hN hκ m, φ⟫_ℂ = 0) →
            ∃ B : BgFam (NbhdN a h (ρ / 8) ∪ ⋃ i, Gam (xm i) (xp i) (hf i)) d₀ s₁ a₀ c₁,
              B.c0 = (fun z => Complex.I * κ * Gfull (μ : Measure ℝ) z) ∧ B.D = Df L κ (Gfull (μ : Measure ℝ)) ∧
              B.s = sf L κ (Gfull (μ : Measure ℝ)) ∧ B.A = Af κ (Gfull (μ : Measure ℝ)) ∧
              ∀ θf : Fin r → ℝ, (∀ i, |θf i| ≤ Θ i) →
              ∀ (t : ℕ → ℝ), (∀ r ∈ ords, |t r| ≤ T r) →
                mixedGap L κ h k q a ords t (rectFamily xm xp hf θf) B φ ≤
                  ENNReal.ofReal (C * ((1 + a) ^ (d + 1) * (ε + 1 / R ^ b + 1 / ((k + q : ℕ) : ℝ)) +
                    ρI (k + q))) := by
  have hΛ0 : 0 ≤ ∑ i, Θ i * (2 * (xp i - xm i) + 4 * hf i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hΘ i) (by linarith [hlt i, hfpos i])
  obtain ⟨ρ, R0, hρ0, hR01, EI, ρI, e1, e2, e3, d₀, s₁, a₀, c₁, C, f1, f2, f3, f4, f5, N0, H⟩ :=
    prop026_uniform_gen hκ u hu hμ hηh hδ hd0 hin b pc hb hbpc d k ords hRd T
      (QuantumNLS.Prop026Bound.scalarCuts hκ u hu) (QuantumNLS.Prop026Bound.physical_eq_limit hκ u hu hμ).symm
      hxm hxp hlt hfpos hfh h1 h2 h3 h4 (∑ i, Θ i * (2 * (xp i - xm i) + 4 * hf i)) hΛ0
  refine ⟨ρ, R0, hρ0, hR01, EI, ρI, e1, e2, e3, d₀, s₁, a₀, c₁, C, f1, f2, f3, f4, f5, N0,
    fun ε hε hε1 q hNq hN R hR l hl a ha h2R => ?_⟩
  obtain ⟨hproj, hφ⟩ := H ε hε hε1 q hNq hN R hR l hl a ha h2R
  refine ⟨hproj, fun φ hφ1 hsupp => ?_⟩
  obtain ⟨B, hB1, hB2, hB3, hB4, hBb⟩ := hφ φ hφ1 hsupp
  refine ⟨B, hB1, hB2, hB3, hB4, fun θf hθf t ht => ?_⟩
  obtain ⟨hlen, hZ, hreal⟩ := rectFamily_props xm xp hf θf Θ hlt hfpos hθf
  exact hBb (rectFamily xm xp hf θf) hlen hZ hreal t ht

end QuantumNLS.Prop026Uniform

#print axioms QuantumNLS.Prop026Uniform.prop026_uniform_gen
#print axioms QuantumNLS.Prop026Uniform.rectFamily_props
#print axioms QuantumNLS.Prop026Uniform.prop026_uniform
