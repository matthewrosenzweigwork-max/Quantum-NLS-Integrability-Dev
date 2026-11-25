import NlsGge.Atomic.I.I038
import NlsGge.Atomic.I.I027

                                                                                  
                                                                 
                                                                             
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology BoundedContinuousFunction
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Sobolev38
open NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.I
open NlsGge.Atomic.I010 (spectralEnergy)
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.Narrative

private theorem gapTerm_const_mul (W : ℝ → ℝ) (κ : ℝ) (u : PhysicalL2) (n : ℤ) :
    gapRemainderTermE02_38 (fun r => κ * W r) u n = κ * gapRemainderTermE02_38 W u n := by
  unfold gapRemainderTermE02_38
  simp_rw [show ∀ x : ℝ, (κ * W (2 * x) - κ * W (2 * Real.pi * n)) *
      actualGapHeightE02_38 u x =
      κ * ((W (2 * x) - W (2 * Real.pi * n)) * actualGapHeightE02_38 u x) by
    intro x; ring]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- The physical sum scales on its absolutely summable source domain. -/
theorem factorialPower_scaled_remainder (W : ℝ → ℝ) (κ : ℝ) (u : PhysicalL2)
    (hs : Summable (fun n : ℤ => |gapRemainderTermE02_38 W u n|)) :
    Summable (fun n : ℤ => |gapRemainderTermE02_38 (fun r => κ * W r) u n|) ∧
    remainderForWeight (fun r => κ * W r) u = κ * remainderForWeight W u := by
  have hs' : Summable (fun n : ℤ => gapRemainderTermE02_38 W u n) := hs.of_abs
  constructor
  · simpa only [gapTerm_const_mul, abs_mul] using hs.mul_left |κ|
  · unfold remainderForWeight
    simp_rw [gapTerm_const_mul]
    exact hs'.tsum_mul_left κ

/-- Multiplying the symbol means multiplying every charge coefficient, including j=0. -/
theorem factorialPower_scaled_weight (p : ℝ) (hp : 2 < p) (c : BoundedCoefficients 1 2)
    (κ r : ℝ) :
    NlsGge.Atomic.I037.factorialPowerWeight p (fun j => κ * c.val j) r =
      κ * NlsGge.Atomic.I037.factorialPowerWeight p c.val r := by
  have hs := NlsGge.Atomic.I037.summable_term (show 1 ≤ p by linarith) c.property.2.2 r
  unfold NlsGge.Atomic.I037.factorialPowerWeight
  have he : (fun j => NlsGge.Atomic.I037.factorialPowerTerm p (fun j => κ * c.val j) r j) =
      (fun j => κ * NlsGge.Atomic.I037.factorialPowerTerm p c.val r j) := by
    funext j
    unfold NlsGge.Atomic.I037.factorialPowerTerm
    ring
  rw [he]
  exact hs.tsum_mul_left κ

/-- The summability domain is unchanged by a positive multiplier; its Gaussian changes. -/
theorem factorialPower_scaled_good_set (p : ℝ) (c : BoundedCoefficients 1 2)
    (κ : ℝ) (hκ : 0 < κ) :
    {z : ℤ → ℂ | (∀ r : ℕ, SobolevSquareSummable (r : ℝ) z) ∧
      Summable (fun n : ℤ => (κ * NlsGge.Atomic.I037.factorialPowerWeight p c.val
        (2 * Real.pi * (n : ℝ))) * ‖z n‖ ^ 2 * japaneseBracket n ^ (2 / p - 2))} =
    {z : ℤ → ℂ | (∀ r : ℕ, SobolevSquareSummable (r : ℝ) z) ∧
      Summable (fun n : ℤ => NlsGge.Atomic.I037.factorialPowerWeight p c.val
        (2 * Real.pi * (n : ℝ)) * ‖z n‖ ^ 2 * japaneseBracket n ^ (2 / p - 2))} := by
  ext z
  simp only [Set.mem_setOf_eq, mul_assoc, summable_mul_left_iff hκ.ne']

private theorem scaled_facts (p : ℝ) (hp : 2 < p) (c : BoundedCoefficients 1 2)
    (κ : ℝ) (hκ : 0 < κ) :
    let W := fun r => κ * NlsGge.Atomic.I037.factorialPowerWeight p c.val r
    let w := fun n : ℤ => W (2 * Real.pi * (n : ℝ)) * japaneseBracket n ^ (2 / p - 2)
    ContDiff ℝ 2 W ∧ ConvexOn ℝ Set.univ W ∧
    (∀ n : ℤ, 0 < W (2 * Real.pi * (n : ℝ))) ∧
    (∀ n : ℤ, 0 ≤ w n) ∧
    (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : PhysicalL2,
      SobolevSquareSummable 1 (physicalFourier u) → ‖physFS38 1 u‖ ≤ B → ∀ n : ℤ,
        |gapRemainderTermE02_38 W u n| ≤ C * w n * actualGapActionAllE02_38 u n) ∧
    (∀ᵐ z ∂countableComplexGaussian (fun n : ℤ => W (2 * Real.pi * (n : ℝ))),
      (∀ r : ℕ, SobolevSquareSummable (r : ℝ) z) ∧
      Summable (fun n : ℤ => w n * ‖z n‖ ^ 2)) := by
  intro W w
  have hc : ∀ j, 1 ≤ c.val j ∧ c.val j ≤ 2 := c.property.2.2
  have hp1 : 1 ≤ p := by linarith
  have hWbase : ContDiff ℝ 2 (NlsGge.Atomic.I037.factorialPowerWeight p c.val) :=
    I038S.contDiff_weight hp1 hc
  have hW2 : ContDiff ℝ 2 W :=
    ContDiff.mul (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => κ)) hWbase
  have hconv : ConvexOn ℝ Set.univ W := by
    simpa only [smul_eq_mul] using (I038S.convexOn_weight hp1 hc).smul hκ.le
  have hpos : ∀ n : ℤ, 0 < W (2 * Real.pi * (n : ℝ)) := by
    intro n
    exact mul_pos hκ (lt_of_lt_of_le zero_lt_one (NlsGge.Atomic.I037.weight_ge_one hp1 hc _))
  have hw0 : ∀ n : ℤ, 0 ≤ w n := fun n =>
    mul_nonneg (hpos n).le (Real.rpow_nonneg (by unfold japaneseBracket; positivity) _)
  have hgap : ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : PhysicalL2,
      SobolevSquareSummable 1 (physicalFourier u) → ‖physFS38 1 u‖ ≤ B → ∀ n : ℤ,
        |gapRemainderTermE02_38 W u n| ≤ C * w n * actualGapActionAllE02_38 u n := by
    intro B hB
    obtain ⟨C, hC, hg⟩ := I038W.gap_conjunct p hp c B hB
    refine ⟨C, hC, fun u hu hBu n => ?_⟩
    change |gapRemainderTermE02_38 (fun r => κ * NlsGge.Atomic.I037.factorialPowerWeight p c.val r) u n| ≤ _
    rw [gapTerm_const_mul, abs_mul, abs_of_pos hκ]
    calc κ * |gapRemainderTermE02_38 (NlsGge.Atomic.I037.factorialPowerWeight p c.val) u n|
        ≤ κ * (C * NlsGge.Atomic.I037.factorialPowerWeight p c.val (2 * Real.pi * n) *
            actualGapActionAllE02_38 u n * japaneseBracket n ^ (2 / p - 2)) :=
          mul_le_mul_of_nonneg_left (hg u hu hBu n) hκ.le
      _ = C * w n * actualGapActionAllE02_38 u n := by dsimp only [w, W]; ring
  have hsum : Summable (fun n : ℤ => w n / W (2 * Real.pi * (n : ℝ))) := by
    refine (I038W.summable_bracket hp).congr fun n => ?_
    dsimp only [w]
    field_simp [(hpos n).ne'] <;> ring
  have hpoly : ∀ r : ℕ, Summable (fun n : ℤ =>
      sobolevWeight38 r n / W (2 * Real.pi * (n : ℝ))) := by
    intro r
    refine ((I038M.rate_poly hp1 hc r).mul_left κ⁻¹).congr fun n => ?_
    dsimp only [W]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  exact ⟨hW2, hconv, hpos, hw0, hgap,
    I038M.ae_good _ w hpos hw0 hsum hpoly⟩

/-- Complete i038 construction for arbitrary positive multiples of the factorial-power symbol. -/
theorem factorialPower_scaled_construction (p : ℝ) (hp : 2 < p)
    (c : BoundedCoefficients 1 2) (κ : ℝ) (hκ : 0 < κ) :
    let W := fun r => κ * NlsGge.Atomic.I037.factorialPowerWeight p c.val r
    let a := fun n : ℤ => W (2 * Real.pi * (n : ℝ))
    let γ := countableComplexGaussian a
    let Ω := {z : ℤ → ℂ | (∀ r : ℕ, SobolevSquareSummable (r : ℝ) z) ∧
      Summable (fun n : ℤ => a n * ‖z n‖ ^ 2 * japaneseBracket n ^ (2 / p - 2))}
    Summable (fun n : ℤ => japaneseBracket n ^ (2 / p - 2)) ∧
    MeasurableSet Ω ∧ γ Ω = 1 ∧
    (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : PhysicalL2, SobolevSquareSummable 1 (physicalFourier u) →
        ‖physFS38 1 u‖ ≤ B → ∀ n : ℤ,
          |gapRemainderTermE02_38 W u n| ≤
            C * a n * actualGapActionAllE02_38 u n * japaneseBracket n ^ (2 / p - 2)) ∧
    (∀ z ∈ Ω,
      Summable (fun n : ℤ => |gapRemainderTermE02_38 W (physicalOfSequence z) n|) ∧
      sequenceRemainder W z = remainderForWeight W (physicalOfSequence z) ∧
      0 ≤ remainderForWeight W (physicalOfSequence z)) ∧
    (∀ S : Finset ℤ,
      0 < finiteAbsolutePartition W S ∧
      finiteAbsolutePartition W S ≤ ∏ n : S, Real.pi / a n ∧
      0 < finiteRelativeNormalizer W S ∧ finiteRelativeNormalizer W S ≤ 1 ∧
      finiteRelativeNormalizer W S = finiteAbsolutePartition W S / (∏ n : S, Real.pi / a n) ∧
      finiteGapCoordinateLaw W S = (finiteComplexVolume S).withDensity
        (fun w => ENNReal.ofReal (Real.exp (-spectralEnergy W (finiteGapField S w)) /
          finiteAbsolutePartition W S)) ∧
      IsProbabilityMeasure (finiteGapLaw W S) ∧
      ∀ w : S → ℂ,
        Integrable (fun t : ℝ => W (2 * t) * actualGapHeightE02_38 (finiteGapField S w) t) ∧
        HasSum (fun j : ℕ => (κ * c.val j) / ((j.factorial : ℝ) ^ p) *
          chargeFn38 (j + 2) j (finiteGapField S w)) (spectralEnergy W (finiteGapField S w))) ∧
    0 < limitNormalizer W ∧ limitNormalizer W ≤ 1 ∧
    IsProbabilityMeasure (weightedSequenceLaw W) ∧ IsProbabilityMeasure (physicalLaw W) ∧
    weightedSequenceLaw W ≪ γ ∧ γ ≪ weightedSequenceLaw W ∧
    (∀ A : Set (ℤ → ℂ), MeasurableSet A →
      weightedSequenceLaw W A ≤ ENNReal.ofReal ((limitNormalizer W)⁻¹) * γ A) ∧
    (∀ᵐ (u : PhysicalL2) ∂physicalLaw W, ∀ r : ℕ, SobolevSquareSummable (r : ℝ) (physicalFourier u)) ∧
    ∀ Λ : ℕ → Finset ℤ, IsExhaustion38 Λ →
      Tendsto (fun N : ℕ => finiteRelativeNormalizer W (Λ N)) atTop (𝓝 (limitNormalizer W)) ∧
      ∀ (r : ℕ) (F : SobolevHilbert (r : ℝ) →ᵇ ℝ),
        Tendsto (fun N : ℕ => ∫ u : PhysicalL2, F (physFS38 r u) ∂finiteGapLaw W (Λ N))
          atTop (𝓝 (∫ u : PhysicalL2, F (physFS38 r u) ∂physicalLaw W)) := by
  intro W a γ Ω
  let Bk := PDE.actualBirkhoffTop38
  have hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z := actual_inverse_eq_physicalOfSequence
  obtain ⟨hW2, hconv, hpos, hw0, hgap, hΩae⟩ := scaled_facts p hp c κ hκ
  let w : ℤ → ℝ := fun n => a n * japaneseBracket n ^ (2 / p - 2)
  have hset : Ω = {z : ℤ → ℂ | (∀ r : ℕ, SobolevSquareSummable (r : ℝ) z) ∧
      Summable (fun n : ℤ => w n * ‖z n‖ ^ 2)} := by
    ext z
    simp only [Set.mem_setOf_eq]
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, h2.congr fun n => ?_⟩ <;>
      dsimp only [w] <;> ring
  have hΩm : MeasurableSet Ω := by
    rw [hset]
    exact I038M.measurableSet_good w hw0
  have hΩ1 : γ Ω = 1 := by
    rw [hset]
    exact (prob_compl_eq_zero_iff (I038M.measurableSet_good w hw0)).1 (ae_iff.1 hΩae)
  have homega : ∀ z ∈ Ω,
      Summable (fun n : ℤ => |gapRemainderTermE02_38 W (physicalOfSequence z) n|) ∧
      sequenceRemainder W z = remainderForWeight W (physicalOfSequence z) ∧
      0 ≤ remainderForWeight W (physicalOfSequence z) := by
    intro z hz
    rw [hset] at hz
    have hz1 := (mem_seqSobolev38_iff _ _).2 (hz.1 1)
    obtain ⟨h1, -, -, h0⟩ := I038P.pathwise Bk hB W hW2 hconv w hw0 hgap z hz1 hz.2
      stdExh38 isExhaustion_stdExh38
    exact ⟨h1, max_eq_right h0, h0⟩
  obtain ⟨hZ1, hZ2, hP1, hP2, hac1, hac2, hdens⟩ := I038L.limit_gen Bk hB W hW2.continuous
  have hPm : Measurable physicalOfSequence := by
    rw [show physicalOfSequence = Bk.cleanΦinv from (funext hB).symm]
    exact Bk.measurable_cleanΦinv
  have hall : ∀ᵐ (u : PhysicalL2) ∂physicalLaw W, ∀ r : ℕ,
      SobolevSquareSummable (r : ℝ) (physicalFourier u) := by
    unfold physicalLaw
    rw [ae_map_iff hPm.aemeasurable I038L.measurableSet_allSobolev_phys]
    refine hac1.ae_le ?_
    filter_upwards [hΩae] with z hz r
    rw [← hB z]
    exact Bk.sobolev_cleanΦinv38 r z ((mem_seqSobolev38_iff _ _).2 (hz.1 r))
  refine ⟨I038W.summable_bracket hp, hΩm, hΩ1, ?_, homega, ?_,
    hZ1, hZ2, hP1, hP2, hac1, hac2, hdens, hall,
    fun Λ hΛ => I038K.weak_gen Bk hB W hW2 hconv w hw0 hgap hΩae Λ hΛ⟩
  · intro B hBd
    obtain ⟨C, hC, hg⟩ := hgap B hBd
    refine ⟨C, hC, fun u hu hBu n => (hg u hu hBu n).trans (le_of_eq ?_)⟩
    dsimp only [w]
    ring
  · intro S
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := I038B.block Bk hB W hW2 hconv hpos S
    refine ⟨b1, b2, b3, b4, b5, b6, b7, fun v => ⟨b8 v, ?_⟩⟩
    have hcoeff : ∀ j : ℕ, 0 ≤ (κ * c.val j) / ((j.factorial : ℝ) ^ p) := by
      intro j
      exact div_nonneg (mul_nonneg hκ.le (le_trans zero_le_one (c.property.2.2 j).1))
        (Real.rpow_nonneg (by positivity) _)
    have hseries : ∀ r : ℝ, HasSum
        (fun j : ℕ => (κ * c.val j) / ((j.factorial : ℝ) ^ p) * r ^ (2 * j)) (W r) := by
      intro r
      have hs := (NlsGge.Atomic.I037.summable_term (show 1 ≤ p by linarith) c.property.2.2 r).hasSum.mul_left κ
      refine hs.congr_fun fun j => ?_
      unfold NlsGge.Atomic.I037.factorialPowerTerm
      ring
    have hu : ∀ m : ℕ, SobolevSquareSummable (m : ℝ) (physicalFourier (finiteGapField S v)) := by
      intro m
      rw [I017C.field_eq_proj Bk hB S v]
      exact Bk.sobolev_cleanΦinv38 m _ (finiteSupport_mem_seqSobolev38 _ _ (finite_support_projFin38 S _))
    exact I038C.hasSum_charge W _ hcoeff hseries _ hu (b8 v)

/- This is the weight-parametrized version of the already landed density route.
   Its internal premises are discharged concretely by scaled_facts below. -/
private theorem density_l1_for_weight
    (W : ℝ → ℝ) (hW2 : ContDiff ℝ 2 W) (hconv : ConvexOn ℝ Set.univ W)
    (w : ℤ → ℝ) (hw0 : ∀ n, 0 ≤ w n)
    (hgap : ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : PhysicalL2,
      SobolevSquareSummable 1 (physicalFourier u) → ‖physFS38 1 u‖ ≤ B → ∀ n : ℤ,
        |gapRemainderTermE02_38 W u n| ≤ C * w n * actualGapActionAllE02_38 u n)
    (hΩ : ∀ᵐ z ∂countableComplexGaussian (fun n : ℤ => W (2 * Real.pi * (n : ℝ))),
      (∀ r : ℕ, SobolevSquareSummable (r : ℝ) z) ∧ Summable (fun n : ℤ => w n * ‖z n‖ ^ 2))
    (Λ : ℕ → Finset ℤ) (hΛ : IsExhaustion38 Λ) :
    let γ := countableComplexGaussian (fun n : ℤ => W (2 * Real.pi * (n : ℝ)))
    let ρ := fun z : ℤ → ℂ => Real.exp (-sequenceRemainder W z) / limitNormalizer W
    let ρN := fun (N : ℕ) (z : ℤ → ℂ) =>
      Real.exp (-remainderForWeight W (physicalOfSequence (projFin38 (Λ N) z))) /
        finiteRelativeNormalizer W (Λ N)
    (∀ N : ℕ, Integrable (fun z : ℤ → ℂ => |ρN N z - ρ z|) γ) ∧
    Tendsto (fun N : ℕ => ∫ z : ℤ → ℂ, |ρN N z - ρ z| ∂γ) atTop (𝓝 0) := by
  intro γ ρ ρN
  let Bk := PDE.actualBirkhoffTop38
  have hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z := actual_inverse_eq_physicalOfSequence
  have hPm : Measurable physicalOfSequence := by
    rw [show physicalOfSequence = Bk.cleanΦinv from (funext hB).symm]
    exact Bk.measurable_cleanΦinv
  have hRm := I025C.measurable_remainderForWeight W hW2.continuous
  have hSm := I033C.measurable_sequenceRemainder Bk hB W hW2.continuous
  have hS0 := I033C.sequenceRemainder_nonneg W
  have hRN0 : ∀ (S : Finset ℤ) (z : ℤ → ℂ),
      0 ≤ remainderForWeight W (physicalOfSequence (projFin38 S z)) := by
    intro S z
    rw [← hB]
    obtain ⟨hs, hfin, -⟩ := Bk.finiteGap_structure38 S z
    exact (I038F.finiteGap_remainder W hW2 hconv _ hs hfin).2.2
  have hZ : 0 < limitNormalizer W := (I038L.limit_gen Bk hB W hW2.continuous).1
  have hZN : ∀ N : ℕ, 0 < finiteRelativeNormalizer W (Λ N) := by
    intro N
    have hFm : Measurable (finiteGapField (Λ N)) := hPm.comp (measurable_extZero38 (Λ N))
    exact gibbsPartition38_pos _ _ (hRm.comp hFm) (fun v => by
      show 0 ≤ remainderForWeight W (physicalOfSequence (extZero38 (Λ N) v))
      have h := hRN0 (Λ N) (extZero38 (Λ N) v)
      rwa [projFin38_extZero38] at h)
  have hρm : Measurable ρ := (Real.measurable_exp.comp hSm.neg).div_const _
  have hρNm : ∀ N : ℕ, Measurable (ρN N) := fun N =>
    (Real.measurable_exp.comp ((hRm.comp hPm).comp (measurable_projFin38 (Λ N))).neg).div_const _
  have hρ0 : ∀ z, 0 ≤ ρ z := fun z => div_nonneg (Real.exp_pos _).le hZ.le
  have hρN0 : ∀ N z, 0 ≤ ρN N z := fun N z => div_nonneg (Real.exp_pos _).le (hZN N).le
  have hρb : ∀ z, ρ z ≤ 1 / limitNormalizer W := fun z =>
    div_le_div_of_nonneg_right (Real.exp_le_one_iff.2 (neg_nonpos.2 (hS0 z))) hZ.le
  have hρNb : ∀ N z, ρN N z ≤ 1 / finiteRelativeNormalizer W (Λ N) := fun N z =>
    div_le_div_of_nonneg_right (Real.exp_le_one_iff.2 (neg_nonpos.2 (hRN0 _ z))) (hZN N).le
  have hden := (I038K.weak_gen Bk hB W hW2 hconv w hw0 hgap hΩ Λ hΛ).1
  have hlimR : ∀ᵐ z ∂γ, Tendsto
      (fun N : ℕ => remainderForWeight W (physicalOfSequence (projFin38 (Λ N) z)))
      atTop (𝓝 (sequenceRemainder W z)) := by
    filter_upwards [hΩ] with z hz
    have hz1 := (mem_seqSobolev38_iff _ _).2 (hz.1 1)
    obtain ⟨-, -, hlim, h0⟩ := I038P.pathwise Bk hB W hW2 hconv w hw0 hgap z hz1 hz.2 Λ hΛ
    unfold sequenceRemainder
    rw [max_eq_right h0]
    exact hlim
  have hlimρ : ∀ᵐ z ∂γ, Tendsto (fun N : ℕ => ρN N z) atTop (𝓝 (ρ z)) := by
    filter_upwards [hlimR] with z hz
    exact (((Real.continuous_exp.tendsto _).comp hz.neg).div hden hZ.ne')
  constructor
  · intro N
    refine Integrable.of_bound (((hρNm N).sub hρm).abs.aestronglyMeasurable)
      (C := 1 / finiteRelativeNormalizer W (Λ N) + 1 / limitNormalizer W) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_abs]
    calc |ρN N z - ρ z| ≤ |ρN N z| + |ρ z| := abs_sub _ _
      _ = ρN N z + ρ z := by rw [abs_of_nonneg (hρN0 N z), abs_of_nonneg (hρ0 z)]
      _ ≤ 1 / finiteRelativeNormalizer W (Λ N) + 1 / limitNormalizer W :=
        add_le_add (hρNb N z) (hρb z)
  · have hevent : ∀ᶠ N in atTop, limitNormalizer W / 2 < finiteRelativeNormalizer W (Λ N) :=
      (tendsto_order.1 hden).1 _ (by linarith)
    refine NlsGge.Birkhoff.tendsto_integral_abs_sub38 γ ρN ρ (2 / limitNormalizer W)
      hρNm hρm ?_ ?_ hlimρ
    · filter_upwards [hevent] with N hN z
      rw [abs_of_nonneg (hρN0 N z)]
      refine (hρNb N z).trans ?_
      apply (div_le_div_iff₀ (hZN N) hZ).2
      linarith
    · intro z
      rw [abs_of_nonneg (hρ0 z)]
      exact (hρb z).trans (div_le_div_of_nonneg_right (by norm_num) hZ.le)

/-- Common-product normalized densities for κW converge in L1 of the κW Gaussian. -/
theorem factorialPower_scaled_density_l1 (p : ℝ) (hp : 2 < p)
    (c : BoundedCoefficients 1 2) (κ : ℝ) (hκ : 0 < κ)
    (Λ : ℕ → Finset ℤ) (hΛ : IsExhaustion38 Λ) :
    let W := fun r => κ * NlsGge.Atomic.I037.factorialPowerWeight p c.val r
    let γ := countableComplexGaussian (fun n : ℤ => W (2 * Real.pi * (n : ℝ)))
    let ρ := fun z : ℤ → ℂ => Real.exp (-sequenceRemainder W z) / limitNormalizer W
    let ρN := fun (N : ℕ) (z : ℤ → ℂ) =>
      Real.exp (-remainderForWeight W (physicalOfSequence (projFin38 (Λ N) z))) /
        finiteRelativeNormalizer W (Λ N)
    (∀ N : ℕ, Integrable (fun z : ℤ → ℂ => |ρN N z - ρ z|) γ) ∧
    Tendsto (fun N : ℕ => ∫ z : ℤ → ℂ, |ρN N z - ρ z| ∂γ) atTop (𝓝 0) := by
  obtain ⟨hW2, hconv, -, hw0, hgap, hΩ⟩ := scaled_facts p hp c κ hκ
  exact density_l1_for_weight _ hW2 hconv _ hw0 hgap hΩ Λ hΛ

/-- The exact M02 head; integrability is asserted for every cutoff. -/
theorem factorialPower_density_l1 (p : ℝ) (hp : 2 < p)
    (c : BoundedCoefficients 1 2) (Λ : ℕ → Finset ℤ) (hΛ : IsExhaustion38 Λ) :
    let W := NlsGge.Atomic.I037.factorialPowerWeight p c.val
    let γ := countableComplexGaussian (fun n : ℤ => W (2 * Real.pi * (n : ℝ)))
    let ρ := fun z : ℤ → ℂ => Real.exp (-sequenceRemainder W z) / limitNormalizer W
    let ρN := fun (N : ℕ) (z : ℤ → ℂ) =>
      Real.exp (-remainderForWeight W (physicalOfSequence (projFin38 (Λ N) z))) /
        finiteRelativeNormalizer W (Λ N)
    (∀ N : ℕ, Integrable (fun z : ℤ → ℂ => |ρN N z - ρ z|) γ) ∧
    Tendsto (fun N : ℕ => ∫ z : ℤ → ℂ, |ρN N z - ρ z| ∂γ) atTop (𝓝 0) := by
  simpa only [one_mul] using factorialPower_scaled_density_l1 p hp c 1 zero_lt_one Λ hΛ

/-- Compatibility with the literal unscaled good set, including the chosen representative. -/
theorem factorialPower_scaled_remainder_compatibility (p : ℝ) (hp : 2 < p)
    (c : BoundedCoefficients 1 2) (κ : ℝ) (hκ : 0 < κ) :
    let W0 := NlsGge.Atomic.I037.factorialPowerWeight p c.val
    let W := fun r : ℝ => κ * W0 r
    let Ω0 := {z : ℤ → ℂ | (∀ r : ℕ, SobolevSquareSummable (r : ℝ) z) ∧
      Summable (fun n : ℤ => W0 (2 * Real.pi * (n : ℝ)) * ‖z n‖ ^ 2 *
        japaneseBracket n ^ (2 / p - 2))}
    ∀ z ∈ Ω0,
      Summable (fun n : ℤ => |gapRemainderTermE02_38 W0 (physicalOfSequence z) n|) ∧
      Summable (fun n : ℤ => |gapRemainderTermE02_38 W (physicalOfSequence z) n|) ∧
      remainderForWeight W (physicalOfSequence z) =
        κ * remainderForWeight W0 (physicalOfSequence z) ∧
      sequenceRemainder W z = κ * sequenceRemainder W0 z := by
  intro W0 W Ω0 z hz
  obtain ⟨hs, hseq, h0⟩ := I038O.omega_remainder_of PDE.actualBirkhoffTop38
    actual_inverse_eq_physicalOfSequence p hp c z hz
  obtain ⟨hscaled, heq⟩ := factorialPower_scaled_remainder W0 κ (physicalOfSequence z) hs
  refine ⟨hs, hscaled, heq, ?_⟩
  rw [hseq]
  change max 0 (remainderForWeight W (physicalOfSequence z)) =
    κ * remainderForWeight W0 (physicalOfSequence z)
  rw [heq, max_eq_right (mul_nonneg hκ.le h0)]

private theorem gapTerm_sub (V U : ℝ → ℝ) (hV : Continuous V) (hU : Continuous U)
    (u : PhysicalL2) (n : ℤ) :
    gapRemainderTermE02_38 (fun r => V r - U r) u n =
      gapRemainderTermE02_38 V u n - gapRemainderTermE02_38 U u n := by
  have hVi : IntervalIntegrable
      (fun x : ℝ => (V (2 * x) - V (2 * Real.pi * n)) * actualGapHeightE02_38 u x)
      volume (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) :=
    (((hV.comp (continuous_const.mul continuous_id)).sub continuous_const).mul
      (continuous_actualGapHeightE02_38 u)).intervalIntegrable _ _
  have hUi : IntervalIntegrable
      (fun x : ℝ => (U (2 * x) - U (2 * Real.pi * n)) * actualGapHeightE02_38 u x)
      volume (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) :=
    (((hU.comp (continuous_const.mul continuous_id)).sub continuous_const).mul
      (continuous_actualGapHeightE02_38 u)).intervalIntegrable _ _
  unfold gapRemainderTermE02_38
  simp_rw [show ∀ x : ℝ, ((V (2 * x) - U (2 * x)) -
      (V (2 * Real.pi * n) - U (2 * Real.pi * n))) * actualGapHeightE02_38 u x =
      (V (2 * x) - V (2 * Real.pi * n)) * actualGapHeightE02_38 u x -
      (U (2 * x) - U (2 * Real.pi * n)) * actualGapHeightE02_38 u x by intro x; ring]
  rw [intervalIntegral.integral_sub hVi hUi]
  ring

/- The following estimates extend the original coefficientwise series argument.
   A is the same factorial-power weight with every numerator equal to one. -/
private theorem bounded_series (p : ℝ) (hp : 1 ≤ p)
    (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    (∀ r : ℝ, Summable (NlsGge.Atomic.I037.factorialPowerTerm p c.val r)) ∧
    ∀ r : ℝ,
      lower * NlsGge.Atomic.I037.factorialPowerWeight p (fun _ => 1) r ≤
        NlsGge.Atomic.I037.factorialPowerWeight p c.val r ∧
      NlsGge.Atomic.I037.factorialPowerWeight p c.val r ≤
        upper * NlsGge.Atomic.I037.factorialPowerWeight p (fun _ => 1) r := by
  have hc0 : ∀ j, 0 ≤ c.val j := fun j => c.property.1.le.trans (c.property.2.2 j).1
  have hterm0 : ∀ (r : ℝ) (j : ℕ),
      0 ≤ NlsGge.Atomic.I037.factorialPowerTerm p c.val r j := by
    intro r j
    unfold NlsGge.Atomic.I037.factorialPowerTerm
    exact div_nonneg (mul_nonneg (hc0 j) (by rw [pow_mul]; positivity))
      (Real.rpow_nonneg (by positivity) _)
  have hlo : ∀ (r : ℝ) (j : ℕ),
      lower * NlsGge.Atomic.I037.factorialPowerTerm p (fun _ => 1) r j ≤
        NlsGge.Atomic.I037.factorialPowerTerm p c.val r j := by
    intro r j
    unfold NlsGge.Atomic.I037.factorialPowerTerm
    simp only [one_mul]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (c.property.2.2 j).1 (by rw [pow_mul]; positivity))
      (Real.rpow_nonneg (by positivity) _)
  have hhi : ∀ (r : ℝ) (j : ℕ),
      NlsGge.Atomic.I037.factorialPowerTerm p c.val r j ≤
        upper * NlsGge.Atomic.I037.factorialPowerTerm p (fun _ => 1) r j := by
    intro r j
    unfold NlsGge.Atomic.I037.factorialPowerTerm
    simp only [one_mul]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (c.property.2.2 j).2 (by rw [pow_mul]; positivity))
      (Real.rpow_nonneg (by positivity) _)
  have h1 : ∀ r : ℝ, Summable (NlsGge.Atomic.I037.factorialPowerTerm p (fun _ => 1) r) :=
    fun r => NlsGge.Atomic.I037.summable_term hp (fun _ => ⟨le_rfl, by norm_num⟩) r
  have hs : ∀ r : ℝ, Summable (NlsGge.Atomic.I037.factorialPowerTerm p c.val r) :=
    fun r => Summable.of_nonneg_of_le (hterm0 r) (hhi r) ((h1 r).mul_left upper)
  refine ⟨hs, fun r => ?_⟩
  constructor
  · change lower * (∑' j, NlsGge.Atomic.I037.factorialPowerTerm p (fun _ => 1) r j) ≤
      ∑' j, NlsGge.Atomic.I037.factorialPowerTerm p c.val r j
    rw [← (h1 r).tsum_mul_left lower]
    exact Summable.tsum_le_tsum (hlo r) ((h1 r).mul_left lower) (hs r)
  · change (∑' j, NlsGge.Atomic.I037.factorialPowerTerm p c.val r j) ≤
      upper * ∑' j, NlsGge.Atomic.I037.factorialPowerTerm p (fun _ => 1) r j
    rw [← (h1 r).tsum_mul_left upper]
    exact Summable.tsum_le_tsum (hhi r) (hs r) ((h1 r).mul_left upper)

private theorem bounded_convex (p : ℝ) (hp : 1 ≤ p)
    (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    ConvexOn ℝ Set.univ (NlsGge.Atomic.I037.factorialPowerWeight p c.val) := by
  have hs := (bounded_series p hp lower upper c).1
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hterm : ∀ j : ℕ,
      NlsGge.Atomic.I037.factorialPowerTerm p c.val (a • x + b • y) j ≤
        a • NlsGge.Atomic.I037.factorialPowerTerm p c.val x j +
          b • NlsGge.Atomic.I037.factorialPowerTerm p c.val y j := by
    intro j
    have hβ : 0 ≤ c.val j / (Nat.factorial j : ℝ) ^ p :=
      div_nonneg (c.property.1.le.trans (c.property.2.2 j).1)
        (Real.rpow_nonneg (by positivity) _)
    have hcv := ((Even.convexOn_pow (n := 2 * j) (even_two_mul j)).smul hβ).2
      (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    have e : ∀ r : ℝ, NlsGge.Atomic.I037.factorialPowerTerm p c.val r j =
        (c.val j / (Nat.factorial j : ℝ) ^ p) • r ^ (2 * j) := by
      intro r
      unfold NlsGge.Atomic.I037.factorialPowerTerm
      rw [smul_eq_mul]
      ring
    rw [e, e, e]
    exact hcv
  unfold NlsGge.Atomic.I037.factorialPowerWeight
  calc ∑' j, NlsGge.Atomic.I037.factorialPowerTerm p c.val (a • x + b • y) j
      ≤ ∑' j, (a • NlsGge.Atomic.I037.factorialPowerTerm p c.val x j +
          b • NlsGge.Atomic.I037.factorialPowerTerm p c.val y j) :=
        Summable.tsum_le_tsum hterm (hs _) (((hs x).mul_left a).add ((hs y).mul_left b))
    _ = a • ∑' j, NlsGge.Atomic.I037.factorialPowerTerm p c.val x j +
        b • ∑' j, NlsGge.Atomic.I037.factorialPowerTerm p c.val y j := by
      simp only [smul_eq_mul]
      rw [((hs x).mul_left a).tsum_add ((hs y).mul_left b), tsum_mul_left, tsum_mul_left]

private theorem bounded_scaled_facts (p : ℝ) (hp : 2 < p)
    (lower upper : ℝ) (c : BoundedCoefficients lower upper) (κ : ℝ) (hκ : 0 < κ) :
    let W := fun r : ℝ => κ * NlsGge.Atomic.I037.factorialPowerWeight p c.val r
    ∃ w : ℤ → ℝ,
      ContDiff ℝ 2 W ∧ ConvexOn ℝ Set.univ W ∧ (∀ n : ℤ, 0 ≤ w n) ∧
      (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : PhysicalL2,
        SobolevSquareSummable 1 (physicalFourier u) → ‖physFS38 1 u‖ ≤ B → ∀ n : ℤ,
          |gapRemainderTermE02_38 W u n| ≤ C * w n * actualGapActionAllE02_38 u n) ∧
      (∀ᵐ z ∂countableComplexGaussian (fun n : ℤ => W (2 * Real.pi * (n : ℝ))),
        (∀ r : ℕ, SobolevSquareSummable (r : ℝ) z) ∧
        Summable (fun n : ℤ => w n * ‖z n‖ ^ 2)) := by
  intro W
  have hp1 : 1 ≤ p := by linarith
  have hl : 0 < lower := c.property.1
  have hu : 0 < upper := hl.trans_le c.property.2.1
  let ones : BoundedCoefficients 1 2 :=
    ⟨fun _ => 1, by refine ⟨by norm_num, by norm_num, fun _ => ?_⟩; norm_num⟩
  let d : BoundedCoefficients 1 2 := ⟨fun j => 1 + c.val j / upper, by
    refine ⟨by norm_num, by norm_num, fun j => ?_⟩
    have h0 : 0 ≤ c.val j / upper :=
      div_nonneg (hl.le.trans (c.property.2.2 j).1) hu.le
    have h1 : c.val j / upper ≤ 1 := (div_le_one hu).2 (c.property.2.2 j).2
    constructor <;> linarith⟩
  let A := NlsGge.Atomic.I037.factorialPowerWeight p ones.val
  let D := NlsGge.Atomic.I037.factorialPowerWeight p d.val
  let U := κ * upper
  let L := κ * lower
  have hU : 0 < U := mul_pos hκ hu
  have hL : 0 < L := mul_pos hκ hl
  obtain ⟨hseries, hbounds⟩ := bounded_series p hp1 lower upper c
  have hbase : ∀ r : ℝ, NlsGge.Atomic.I037.factorialPowerWeight p c.val r =
      upper * (D r - A r) := by
    intro r
    have hd := NlsGge.Atomic.I037.summable_term hp1 d.property.2.2 r
    have h1 := NlsGge.Atomic.I037.summable_term hp1 ones.property.2.2 r
    have ht : ∀ j : ℕ,
        upper * (NlsGge.Atomic.I037.factorialPowerTerm p d.val r j -
          NlsGge.Atomic.I037.factorialPowerTerm p ones.val r j) =
            NlsGge.Atomic.I037.factorialPowerTerm p c.val r j := by
      intro j
      dsimp only [d, ones, NlsGge.Atomic.I037.factorialPowerTerm]
      field_simp [hu.ne'] <;> ring
    have hx := (hd.hasSum.sub h1.hasSum).mul_left upper
    exact (hseries r).hasSum.unique (hx.congr_fun (fun j => (ht j).symm))
  have hW : W = fun r : ℝ => U * (D r - A r) := by
    funext r
    dsimp only [W, U]
    rw [hbase r]
    ring
  have hA : ContDiff ℝ 2 A := I038S.contDiff_weight hp1 ones.property.2.2
  have hD : ContDiff ℝ 2 D := I038S.contDiff_weight hp1 d.property.2.2
  have hW2 : ContDiff ℝ 2 W := by
    rw [hW]
    exact ContDiff.mul (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => U)) (ContDiff.sub hD hA)
  have hconv : ConvexOn ℝ Set.univ W := by
    simpa only [smul_eq_mul] using (bounded_convex p hp1 lower upper c).smul hκ.le
  have hApos : ∀ r : ℝ, 0 < A r := fun r =>
    lt_of_lt_of_le zero_lt_one (NlsGge.Atomic.I037.weight_ge_one hp1 ones.property.2.2 r)
  have hDpos : ∀ r : ℝ, 0 < D r := fun r =>
    lt_of_lt_of_le zero_lt_one (NlsGge.Atomic.I037.weight_ge_one hp1 d.property.2.2 r)
  have hD2 : ∀ r : ℝ, D r ≤ 2 * A r := by
    intro r
    have hx := (hbounds r).2
    rw [hbase r] at hx
    have hmul : upper * D r ≤ upper * (2 * A r) := by
      nlinarith only [hx]
    exact le_of_mul_le_mul_left hmul hu
  have hlow : ∀ r : ℝ, L * A r ≤ W r := by
    intro r
    calc L * A r = κ * (lower * A r) := by dsimp only [L]; ring
      _ ≤ κ * NlsGge.Atomic.I037.factorialPowerWeight p c.val r :=
        mul_le_mul_of_nonneg_left (hbounds r).1 hκ.le
      _ = W r := rfl
  have hpos : ∀ r : ℝ, 0 < W r := fun r => lt_of_lt_of_le (mul_pos hL (hApos r)) (hlow r)
  let w : ℤ → ℝ := fun n =>
    U * (D (2 * Real.pi * (n : ℝ)) + A (2 * Real.pi * (n : ℝ))) *
      japaneseBracket n ^ (2 / p - 2)
  have hpow0 : ∀ n : ℤ, 0 ≤ japaneseBracket n ^ (2 / p - 2) := fun n =>
    Real.rpow_nonneg (by unfold japaneseBracket; positivity) _
  have hw0 : ∀ n : ℤ, 0 ≤ w n := fun n =>
    mul_nonneg (mul_nonneg hU.le (add_nonneg (hDpos _).le (hApos _).le)) (hpow0 n)
  have hgap : ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : PhysicalL2,
      SobolevSquareSummable 1 (physicalFourier u) → ‖physFS38 1 u‖ ≤ B → ∀ n : ℤ,
        |gapRemainderTermE02_38 W u n| ≤ C * w n * actualGapActionAllE02_38 u n := by
    intro B hB
    obtain ⟨CD, hCD, hgD⟩ := I038W.gap_conjunct p hp d B hB
    obtain ⟨CA, hCA, hgA⟩ := I038W.gap_conjunct p hp ones B hB
    refine ⟨CD + CA, add_nonneg hCD hCA, fun u hu hBu n => ?_⟩
    have hlin : gapRemainderTermE02_38 W u n =
        U * (gapRemainderTermE02_38 D u n - gapRemainderTermE02_38 A u n) := by
      rw [hW, gapTerm_const_mul, gapTerm_sub D A hD.continuous hA.continuous]
    have hcoef : CD * D (2 * Real.pi * (n : ℝ)) + CA * A (2 * Real.pi * (n : ℝ)) ≤
        (CD + CA) * (D (2 * Real.pi * (n : ℝ)) + A (2 * Real.pi * (n : ℝ))) := by
      nlinarith only [mul_nonneg hCD (hApos (2 * Real.pi * (n : ℝ))).le,
        mul_nonneg hCA (hDpos (2 * Real.pi * (n : ℝ))).le]
    have hI : 0 ≤ actualGapActionAllE02_38 u n := actualGapAction_nonneg38 u n
    calc |gapRemainderTermE02_38 W u n|
        = U * |gapRemainderTermE02_38 D u n - gapRemainderTermE02_38 A u n| := by
          rw [hlin, abs_mul, abs_of_pos hU]
      _ ≤ U * (|gapRemainderTermE02_38 D u n| + |gapRemainderTermE02_38 A u n|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) hU.le
      _ ≤ U * (CD * D (2 * Real.pi * (n : ℝ)) * actualGapActionAllE02_38 u n *
          japaneseBracket n ^ (2 / p - 2) +
          CA * A (2 * Real.pi * (n : ℝ)) * actualGapActionAllE02_38 u n *
          japaneseBracket n ^ (2 / p - 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add (hgD u hu hBu n) (hgA u hu hBu n)) hU.le
      _ = U * (CD * D (2 * Real.pi * (n : ℝ)) + CA * A (2 * Real.pi * (n : ℝ))) *
          (actualGapActionAllE02_38 u n * japaneseBracket n ^ (2 / p - 2)) := by ring
      _ ≤ U * ((CD + CA) * (D (2 * Real.pi * (n : ℝ)) + A (2 * Real.pi * (n : ℝ)))) *
          (actualGapActionAllE02_38 u n * japaneseBracket n ^ (2 / p - 2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef hU.le) (mul_nonneg hI (hpow0 n))
      _ = (CD + CA) * w n * actualGapActionAllE02_38 u n := by dsimp only [w]; ring
  have hsum : Summable (fun n : ℤ => w n / W (2 * Real.pi * (n : ℝ))) := by
    refine Summable.of_nonneg_of_le
      (fun n => div_nonneg (hw0 n) (hpos _).le) (fun n => ?_)
      ((I038W.summable_bracket hp).mul_left (3 * U / L))
    apply (div_le_iff₀ (hpos _)).2
    have hDA : D (2 * Real.pi * (n : ℝ)) + A (2 * Real.pi * (n : ℝ)) ≤
        3 * A (2 * Real.pi * (n : ℝ)) := by linarith only [hD2 (2 * Real.pi * (n : ℝ))]
    calc w n
        ≤ U * (3 * A (2 * Real.pi * (n : ℝ))) * japaneseBracket n ^ (2 / p - 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDA hU.le) (hpow0 n)
      _ = (3 * U / L * japaneseBracket n ^ (2 / p - 2)) *
          (L * A (2 * Real.pi * (n : ℝ))) := by field_simp [hL.ne'] <;> ring
      _ ≤ (3 * U / L * japaneseBracket n ^ (2 / p - 2)) * W (2 * Real.pi * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left (hlow _) (mul_nonneg (by positivity) (hpow0 n))
  have hpoly : ∀ r : ℕ, Summable (fun n : ℤ =>
      sobolevWeight38 r n / W (2 * Real.pi * (n : ℝ))) := by
    intro r
    refine Summable.of_nonneg_of_le
      (fun n => div_nonneg (sobolevWeight38_nonneg r n) (hpos _).le) (fun n => ?_)
      ((I038M.rate_poly hp1 ones.property.2.2 r).mul_left L⁻¹)
    calc sobolevWeight38 r n / W (2 * Real.pi * (n : ℝ))
        ≤ sobolevWeight38 r n / (L * A (2 * Real.pi * (n : ℝ))) :=
          div_le_div_of_nonneg_left (sobolevWeight38_nonneg r n) (mul_pos hL (hApos _)) (hlow _)
      _ = L⁻¹ * (sobolevWeight38 r n / A (2 * Real.pi * (n : ℝ))) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  exact ⟨w, hW2, hconv, hw0, hgap,
    I038M.ae_good _ w (fun n => hpos _) hw0 hsum hpoly⟩

/-- Common-space density convergence for every fixed positive numerator interval and multiplier. -/
theorem factorialPower_bounded_scaled_density_l1 (p : ℝ) (hp : 2 < p)
    (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (κ : ℝ) (hκ : 0 < κ) (Λ : ℕ → Finset ℤ) (hΛ : IsExhaustion38 Λ) :
    let W := fun r : ℝ => κ * NlsGge.Atomic.I037.factorialPowerWeight p c.val r
    let γ := countableComplexGaussian (fun n : ℤ => W (2 * Real.pi * (n : ℝ)))
    let ρ := fun z : ℤ → ℂ => Real.exp (-sequenceRemainder W z) / limitNormalizer W
    let ρN := fun (N : ℕ) (z : ℤ → ℂ) =>
      Real.exp (-remainderForWeight W (physicalOfSequence (projFin38 (Λ N) z))) /
        finiteRelativeNormalizer W (Λ N)
    (∀ N : ℕ, Integrable (fun z : ℤ → ℂ => |ρN N z - ρ z|) γ) ∧
    Tendsto (fun N : ℕ => ∫ z : ℤ → ℂ, |ρN N z - ρ z| ∂γ) atTop (𝓝 0) := by
  obtain ⟨w, hW2, hconv, hw0, hgap, hΩ⟩ := bounded_scaled_facts p hp lower upper c κ hκ
  exact density_l1_for_weight _ hW2 hconv w hw0 hgap hΩ Λ hΛ

end NlsGge.ThirdConsultation.Narrative
