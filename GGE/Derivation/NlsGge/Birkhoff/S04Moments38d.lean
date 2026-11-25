import NlsGge.Birkhoff.S04Moments38c
import NlsGge.Spectral.ChargeJensenSobolev38

/-! # S04.06 (part 3): fixed local charges have moments of all finite orders under `μ_W`

v2 l.443-445: "A fixed local charge is a finite integral of products of derivatives. Taking
sufficiently many derivatives in a Sobolev norm bounds its absolute value by a polynomial in that
norm." The local charge on `H^{m-1}` is the project's continuous extension `chargeSobolev38 m j`
(F03/F07: quadratic part plus the finite sum of continuous multilinear monomials; it equals
`localCharge38` on smooth fields by `chargeSobolev38_smooth`, identification in
`S04Moments38e.lean`).

* `chargeSobolev_poly_bound38`: `|Q_{2j}(y)| ≤ A (1+‖y‖_{H^{m-1}})^{2m+2}` (operator norms of the
  monomial multilinear forms);
* `physC38`, `chargeFn38`: the charge functional on fields via the Fourier carrier
  `û = physicalFourier u` (`norm_physC38_eq_physH38`: same `H^k` norm as `𝓕 u`);
* `integrable_muW38_charge_pow`: `|Q_{2j}(u)|^p` is `μ_W`-integrable for all `p` (`j ≤ m-1`).
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Sobolev38 Filter Topology
  NlsGge.HierarchyRiccati.Core
open scoped ENNReal BoundedContinuousFunction ContDiff

/-- Quadratic part: `0 ≤ ∑ (2πn)^{2j}|y_n|² ≤ (1+(2π)^{2j}) ‖y‖²_{H^k}` for `j ≤ k`. -/
theorem chargeQuad_bound38 (k j : ℕ) (hj : j ≤ k) (y : SobolevHilbert (k : ℝ)) :
    0 ≤ chargeQuad38 (k : ℝ) j y ∧
    chargeQuad38 (k : ℝ) j y ≤ (1 + (2 * Real.pi) ^ (2 * j)) * ‖y‖ ^ 2 := by
  have h := carrier_hasSum_norm_sq38 (k : ℝ) (toCarrier38 (k : ℝ) y)
  have hnn : ∀ n : ℤ, 0 ≤ (2 * Real.pi * (n : ℝ)) ^ (2 * j) *
      ‖(show WeightedHilbert (sobolevModeWeight (k : ℝ)) from y) n‖ ^ 2 := fun n =>
    mul_nonneg (by rw [pow_mul]; positivity) (sq_nonneg _)
  have hle : ∀ n : ℤ, (2 * Real.pi * (n : ℝ)) ^ (2 * j) *
      ‖(show WeightedHilbert (sobolevModeWeight (k : ℝ)) from y) n‖ ^ 2 ≤
      (1 + (2 * Real.pi) ^ (2 * j)) * (sobolevModeWeight (k : ℝ) n *
        ‖(show WeightedHilbert (sobolevModeWeight (k : ℝ)) from y) n‖ ^ 2) := fun n => by
    have := chargeQuad_weight_le38 k j hj n
    have h2 := sq_nonneg ‖(show WeightedHilbert (sobolevModeWeight (k : ℝ)) from y) n‖
    nlinarith
  have hs : Summable (fun n : ℤ => (2 * Real.pi * (n : ℝ)) ^ (2 * j) *
      ‖(show WeightedHilbert (sobolevModeWeight (k : ℝ)) from y) n‖ ^ 2) :=
    Summable.of_nonneg_of_le hnn hle (h.summable.mul_left _)
  refine ⟨tsum_nonneg hnn, ?_⟩
  unfold chargeQuad38
  calc ∑' n : ℤ, (2 * Real.pi * (n : ℝ)) ^ (2 * j) *
        ‖(show WeightedHilbert (sobolevModeWeight (k : ℝ)) from y) n‖ ^ 2
      ≤ ∑' n : ℤ, (1 + (2 * Real.pi) ^ (2 * j)) * (sobolevModeWeight (k : ℝ) n *
        ‖(show WeightedHilbert (sobolevModeWeight (k : ℝ)) from y) n‖ ^ 2) :=
        hs.tsum_le_tsum hle (h.summable.mul_left _)
    _ = (1 + (2 * Real.pi) ^ (2 * j)) * ‖y‖ ^ 2 := by
        rw [tsum_mul_left]
        congr 1
        exact h.tsum_eq


/-- Each realized monomial of the remainder is polynomially bounded on `H^{M-1}`. -/
theorem monomialValue_bound38 (M j : ℕ) (q : Jet →₀ ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : SobolevCarrier38 ((M - 1 : ℕ) : ℝ),
      |localRemainderMonomialValue38 M j q y| ≤ K * (1 + ‖y‖) ^ (2 * M + 2) := by
  by_cases h : 2 ≤ M ∧ j ≤ M ∧ q ∈ (normalizedRemainder38 j).support
  · refine ⟨‖riccatiMonomialSobolevCMM38 (M - 1) q ((normalizedRemainder38 j).coeff q)
      (normalizedRemainder38_top M j h.1 h.2.1 q h.2.2)‖, norm_nonneg _, fun y => ?_⟩
    have hdeg : monomialSlotCount38 q ≤ 2 * M + 2 := by
      rw [monomialSlotCount38_eq_degree]
      exact normalizedRemainder38_degree M j h.2.1 q h.2.2
    have h1 := ContinuousMultilinearMap.le_opNorm
      (riccatiMonomialSobolevCMM38 (M - 1) q ((normalizedRemainder38 j).coeff q)
        (normalizedRemainder38_top M j h.1 h.2.1 q h.2.2)) (fun _ => y)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
    unfold localRemainderMonomialValue38
    simp only [h, and_self, ↓reduceDIte]
    rw [← Real.norm_eq_abs]
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    calc ‖y‖ ^ monomialSlotCount38 q ≤ (1 + ‖y‖) ^ monomialSlotCount38 q :=
          pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
      _ ≤ (1 + ‖y‖) ^ (2 * M + 2) :=
          pow_le_pow_right₀ (by linarith [norm_nonneg y]) hdeg
  · refine ⟨0, le_rfl, fun y => ?_⟩
    unfold localRemainderMonomialValue38
    simp only [h, ↓reduceDIte]
    simp

/-- **Polynomial bound for the continuous extension of `Q_{2j}` to `H^{m-1}`** (v2 l.443-444:
a fixed local charge is bounded by a polynomial in a Sobolev norm). -/
theorem chargeSobolev_poly_bound38 (m j : ℕ) (hj : j ≤ m - 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ y : SobolevHilbert ((m - 1 : ℕ) : ℝ),
      |chargeSobolev38 m j y| ≤ A * (1 + ‖y‖) ^ (2 * m + 2) := by
  have hK : ∀ q : Jet →₀ ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ y : SobolevCarrier38 ((m - 1 : ℕ) : ℝ),
      |localRemainderMonomialValue38 m j q y| ≤ K * (1 + ‖y‖) ^ (2 * m + 2) :=
    fun q => monomialValue_bound38 m j q
  choose K hK0 hKb using hK
  set S := (normalizedRemainder38 j).support with hS
  refine ⟨(1 + (2 * Real.pi) ^ (2 * j)) + ∑ q ∈ S, K q, by
    have := Finset.sum_nonneg (fun q (_ : q ∈ S) => hK0 q); positivity, fun y => ?_⟩
  obtain ⟨hq0, hq1⟩ := chargeQuad_bound38 (m - 1) j hj y
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hp : (1 + ‖y‖) ^ 2 ≤ (1 + ‖y‖) ^ (2 * m + 2) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have hQ : chargeQuad38 ((m - 1 : ℕ) : ℝ) j y ≤ (1 + (2 * Real.pi) ^ (2 * j)) * (1 + ‖y‖) ^ (2 * m + 2) :=
    hq1.trans (mul_le_mul_of_nonneg_left (by nlinarith) (by positivity))
  have hM : |∑ q ∈ S, localRemainderMonomialValue38 m j q (toCarrier38 _ y)| ≤
      (∑ q ∈ S, K q) * (1 + ‖y‖) ^ (2 * m + 2) := by
    calc |∑ q ∈ S, localRemainderMonomialValue38 m j q (toCarrier38 _ y)|
        ≤ ∑ q ∈ S, |localRemainderMonomialValue38 m j q (toCarrier38 _ y)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ S, K q * (1 + ‖y‖) ^ (2 * m + 2) :=
          Finset.sum_le_sum (fun q _ => hKb q (toCarrier38 _ y))
      _ = _ := by rw [Finset.sum_mul]
  unfold chargeSobolev38
  rw [← hS]
  calc |chargeQuad38 ((m - 1 : ℕ) : ℝ) j y +
        ∑ q ∈ S, localRemainderMonomialValue38 m j q (toCarrier38 _ y)|
      ≤ |chargeQuad38 ((m - 1 : ℕ) : ℝ) j y| +
        |∑ q ∈ S, localRemainderMonomialValue38 m j q (toCarrier38 _ y)| := abs_add_le _ _
    _ ≤ (1 + (2 * Real.pi) ^ (2 * j)) * (1 + ‖y‖) ^ (2 * m + 2) +
        (∑ q ∈ S, K q) * (1 + ‖y‖) ^ (2 * m + 2) := by
        rw [abs_of_nonneg hq0]; exact add_le_add hQ hM
    _ = _ := by ring


/-! ## The physical-Fourier carrier and the charge functional on fields -/

theorem physicalFourier_eq_neg_fourierSeq38 (u : PhysicalL2) (n : ℤ) :
    physicalFourier u n = -fourierSeq38 u (-n) := by
  rw [fourierSeq38_apply]; simp

/-- The element of `h^k` with coordinates `û(n) = physicalFourier u n` (the `H^k` Fourier carrier
used by the charge functionals `chargeSobolev38`); cleaned (value `0`) off `H^k`. -/
def physC38 (k : ℕ) (u : PhysicalL2) : SobolevCarrier38 (k : ℝ) :=
  Function.extend (carrierCoe38 (k : ℝ)) id (fun _ => 0) (fun n => physicalFourier u n)

theorem measurable_physicalFourierSeq38 : Measurable (fun u : PhysicalL2 => fun n : ℤ => physicalFourier u n) := by
  refine measurable_pi_iff.2 (fun n => ?_)
  have : (fun u : PhysicalL2 => physicalFourier u n) = fun u => -fourierSeq38 u (-n) :=
    funext (fun u => physicalFourier_eq_neg_fourierSeq38 u n)
  rw [this]
  exact ((measurable_pi_apply (-n)).comp measurable_fourierSeq38).neg

theorem measurable_physC38 (k : ℕ) [MeasurableSpace (SobolevCarrier38 (k : ℝ))]
    [BorelSpace (SobolevCarrier38 (k : ℝ))] : Measurable (physC38 k) :=
  ((measurableEmbedding_carrierCoe38 (k : ℝ)).measurable_extend measurable_id
    measurable_const).comp measurable_physicalFourierSeq38

theorem physC38_of_mem (k : ℕ) (u : PhysicalL2) (hu : (fun n => physicalFourier u n) ∈ seqSobolev38 (k : ℝ)) :
    physC38 k u = carrierMk38 (k : ℝ) _ hu :=
  (carrierCoe38_injective (k : ℝ)).extend_apply id (fun _ => 0) (carrierMk38 (k : ℝ) _ hu)

theorem physC38_of_not_mem (k : ℕ) (u : PhysicalL2)
    (hu : (fun n => physicalFourier u n) ∉ seqSobolev38 (k : ℝ)) : physC38 k u = 0 := by
  refine Function.extend_apply' _ _ _ ?_
  rintro ⟨a, ha⟩
  exact hu (ha ▸ carrierCoe38_mem _ a)

theorem physicalFourier_mem_iff38 (k : ℕ) (u : PhysicalL2) :
    (fun n => physicalFourier u n) ∈ seqSobolev38 (k : ℝ) ↔ fourierSeq38 u ∈ seqSobolev38 (k : ℝ) := by
  rw [fourierSeq38_mem_iff, mem_seqSobolev38_iff]

theorem norm_physC38_eq_physH38 (k : ℕ) (u : PhysicalL2) : ‖physC38 k u‖ = ‖physH38 k u‖ := by
  by_cases hu : fourierSeq38 u ∈ seqSobolev38 (k : ℝ)
  · have hu' : (fun n => physicalFourier u n) ∈ seqSobolev38 (k : ℝ) :=
      (physicalFourier_mem_iff38 k u).2 hu
    rw [physC38_of_mem k u hu', physH38_of_mem k u hu]
    have h1 := carrier_hasSum_norm_sq38 (k : ℝ) (carrierMk38 (k : ℝ) _ hu')
    have h2 := carrier_hasSum_norm_sq38 (k : ℝ) (carrierMk38 (k : ℝ) _ hu)
    simp only [carrierCoe38_mk] at h1 h2
    have h3 : (fun n : ℤ => sobolevModeWeight (k : ℝ) n * ‖physicalFourier u n‖ ^ 2) =
        fun n => sobolevModeWeight (k : ℝ) (-n) * ‖fourierSeq38 u (-n)‖ ^ 2 := by
      funext n
      rw [physicalFourier_eq_neg_fourierSeq38, norm_neg, sobolevModeWeight_neg]
    rw [h3] at h1
    have h4 : HasSum (fun n : ℤ => sobolevModeWeight (k : ℝ) n * ‖fourierSeq38 u n‖ ^ 2)
        (‖carrierMk38 (k : ℝ) _ hu'‖ ^ 2) :=
      (Equiv.neg ℤ).hasSum_iff.1 h1
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (h4.unique h2)
  · have hu' : (fun n => physicalFourier u n) ∉ seqSobolev38 (k : ℝ) := fun h =>
      hu ((physicalFourier_mem_iff38 k u).1 h)
    rw [physC38_of_not_mem k u hu', physH38_of_not_mem k u hu]


/-- The local charge functional `Q_{2j}` on fields: the continuous extension `chargeSobolev38 m j`
to `H^{m-1}` (which equals the local charge `∫ (-1)^{j+1} u p_{2j+1}` on smooth fields, by
`chargeSobolev38_smooth`), evaluated on the Fourier carrier of `u`; cleaned (value of the zero
element) off `H^{m-1}`. -/
def chargeFn38 (m j : ℕ) (u : PhysicalL2) : ℝ :=
  chargeSobolev38 m j (ofCarrier38 ((m - 1 : ℕ) : ℝ) (physC38 (m - 1) u))

namespace BirkhoffTop38

variable (B : BirkhoffTop38)

section Charges

variable (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
  (hupper : ∀ j : ℕ, c j ≤ upper)

include hlower hbound hupper

/-- **S04.06: fixed local charges have moments of all finite orders under `μ_W`**
(v2 l.443-445), for every `j ≤ m - 1` and every power `p`. -/
theorem integrable_muW38_charge_pow (hM : BirkhoffMolnar38 B) (m j : ℕ) (hj : j ≤ m - 1) (p : ℕ) :
    Integrable (fun u : PhysicalL2 => |chargeFn38 m j u| ^ p) (B.muW38 c) := by
  let _ : MeasurableSpace (SobolevCarrier38 ((m - 1 : ℕ) : ℝ)) := borel _
  have : BorelSpace (SobolevCarrier38 ((m - 1 : ℕ) : ℝ)) := ⟨rfl⟩
  let _ : MeasurableSpace (SobolevHilbert ((m - 1 : ℕ) : ℝ)) := borel _
  have : BorelSpace (SobolevHilbert ((m - 1 : ℕ) : ℝ)) := ⟨rfl⟩
  have := B.isProbabilityMeasure_muW38 lower upper c hlower hbound hupper
  obtain ⟨A, hA, hAb⟩ := chargeSobolev_poly_bound38 m j hj
  set D := 2 * m + 2 with hD
  have hmeas : Measurable (fun u : PhysicalL2 => |chargeFn38 m j u| ^ p) := by
    have h1 : Measurable (fun u : PhysicalL2 => chargeFn38 m j u) :=
      (continuous_chargeSobolev38 m j hj).measurable.comp
        ((continuous_ofCarrier38 _).measurable.comp (measurable_physC38 (m - 1)))
    exact h1.abs.pow_const p
  have hg : Integrable (fun u : PhysicalL2 => A ^ p * 2 ^ (D * p) *
      (1 + ‖physH38 (m - 1) u‖ ^ (2 * (D * p)))) (B.muW38 c) :=
    ((integrable_const (1 : ℝ)).add
      (B.integrable_muW38_sobolev_pow lower upper c hlower hbound hupper hM (m - 1) (2 * (D * p)))).const_mul _
  refine hg.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall (fun u => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
  have ht : ‖ofCarrier38 ((m - 1 : ℕ) : ℝ) (physC38 (m - 1) u)‖ = ‖physH38 (m - 1) u‖ :=
    norm_physC38_eq_physH38 (m - 1) u
  have h1 := hAb (ofCarrier38 ((m - 1 : ℕ) : ℝ) (physC38 (m - 1) u))
  rw [ht] at h1
  set t := ‖physH38 (m - 1) u‖ with htdef
  have ht0 : 0 ≤ t := norm_nonneg _
  unfold chargeFn38
  calc |chargeSobolev38 m j (ofCarrier38 ((m - 1 : ℕ) : ℝ) (physC38 (m - 1) u))| ^ p
      ≤ (A * (1 + t) ^ D) ^ p := pow_le_pow_left₀ (abs_nonneg _) h1 p
    _ = A ^ p * (1 + t) ^ (D * p) := by rw [mul_pow, ← pow_mul]
    _ ≤ A ^ p * (2 ^ (D * p) * (1 + (t ^ 2) ^ (D * p))) :=
        mul_le_mul_of_nonneg_left (pow_one_add_le38 t ht0 (D * p)) (by positivity)
    _ = A ^ p * 2 ^ (D * p) * (1 + t ^ (2 * (D * p))) := by rw [← pow_mul]; ring

end Charges

end BirkhoffTop38

end NlsGge.Birkhoff
