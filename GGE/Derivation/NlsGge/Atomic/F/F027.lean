/- F-027 PRODUCTION01 (proof development landing kit; HELD for landing). Source: proof development/F027_PROOF03.lean.txt (author proof development; independent review proof development/REVIEW_F027_01.md), identical except this header. Target NlsGge/Atomic/F/F027.lean. -/
import NlsGge.Birkhoff.F08Bare38b
import NlsGge.Birkhoff.F05Identity38g
import NlsGge.Hierarchy.FiniteOrderGaussianTail38
import NlsGge.Ramer.CylinderSeparation

/- F-027 PROOF02 (proof development, AUTHOR; not self-reviewed). Statement: defs3 STATEMENTS/F.md "## F-027"; the design
   definitions sobolevCoe and lowModeSigma (DEFINITIONS/F.lean.md:130, :269) are hosted here. The proof is built
   from the house facts chargeSobolev38_zero, truncSobolev38_apply, summable_sq_coeff38, mass_nonneg38, mass_le_norm_sq38,
   continuous_chargeSobolev38, gaussianRealization_moment38, gammaFM38_eq_realization; the lemmas below are proved here. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology

namespace NlsGge.ThirdConsultation.F

open NlsGge.Pilot NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core NlsGge.SpectralFoundations

def sobolevCoe (r : ℝ) (y : SobolevHilbert r) : ℤ → ℂ :=
  fun n => (show WeightedHilbert (sobolevModeWeight r) from y) n

def lowModeSigma (m N : ℕ) : MeasurableSpace (Hm1 m) :=
  MeasurableSpace.comap
    (fun y : Hm1 m => NlsGge.Ramer.windowProj N (sobolevCoe _ y)) inferInstance

/-- Coefficient sequence of a Sobolev element (the same function as `sobolevCoe`). -/
def coeffs (m : ℕ) (u : Hm1 m) : ℤ → ℂ :=
  fun n => (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from u) n

theorem sobolevCoe_eq_coeffs (m : ℕ) (u : Hm1 m) : sobolevCoe _ u = coeffs m u := rfl

theorem charge_zero_coeffs (m : ℕ) (u : Hm1 m) :
    chargeSobolev38 m 0 u = ∑' n : ℤ, ‖coeffs m u n‖ ^ 2 :=
  chargeSobolev38_zero m u

theorem coeffs_sub (m : ℕ) (u v : Hm1 m) (n : ℤ) :
    coeffs m (u - v) n = coeffs m u n - coeffs m v n := rfl

theorem coeffs_trunc (m N : ℕ) (u : Hm1 m) (n : ℤ) :
    coeffs m (truncSobolev38 _ N u) n = if n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then coeffs m u n else 0 :=
  truncSobolev38_apply _ N u n

theorem summable_coeffs_sq (m : ℕ) (u : Hm1 m) : Summable (fun n : ℤ => ‖coeffs m u n‖ ^ 2) :=
  summable_sq_coeff38 (m := m) u

/-- A weighted coordinate is controlled by the weighted norm. -/
theorem wh_coord_sq_le (w : ℤ → ℝ) [hw : Fact (∀ n : ℤ, 0 < w n)] (n : ℤ) (x : WeightedHilbert w) :
    w n * ‖x n‖ ^ 2 ≤ ‖x‖ ^ 2 :=
  le_hasSum (weightedHilbert_hasSum (w := w) x) n (fun j _ => mul_nonneg (hw.out j).le (sq_nonneg _))

/-- The coordinate evaluation of a weighted Hilbert space as a continuous linear functional. -/
def wh_coordCLM (w : ℤ → ℝ) [hw : Fact (∀ n : ℤ, 0 < w n)] (n : ℤ) : WeightedHilbert w →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun x => x n
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (1 / Real.sqrt (w n)) (fun x => by
      have hb := wh_coord_sq_le w n x
      have hs : 0 < Real.sqrt (w n) := Real.sqrt_pos.2 (hw.out n)
      have hsq : (Real.sqrt (w n) * ‖x n‖) ^ 2 ≤ ‖x‖ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (hw.out n).le]; exact hb
      have hle : Real.sqrt (w n) * ‖x n‖ ≤ ‖x‖ :=
        (sq_le_sq₀ (mul_nonneg hs.le (norm_nonneg _)) (norm_nonneg _)).1 hsq
      show ‖x n‖ ≤ 1 / Real.sqrt (w n) * ‖x‖
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hs, mul_comm]
      exact hle)

theorem continuous_sobolevCoe_apply (r : ℝ) (n : ℤ) :
    Continuous (fun y : SobolevHilbert r => sobolevCoe r y n) := by
  haveI : Fact (∀ k : ℤ, 0 < sobolevModeWeight r k) := ⟨fun k => sobolevModeWeight_pos r k⟩
  exact (wh_coordCLM (sobolevModeWeight r) n).continuous

theorem measurable_window_coe (m N : ℕ) :
    Measurable (fun y : Hm1 m => NlsGge.Ramer.windowProj N (sobolevCoe _ y)) := by
  apply Continuous.measurable
  apply continuous_pi
  intro i
  exact continuous_sobolevCoe_apply _ (modeIndex N i)

theorem lowModeSigma_le (m N : ℕ) : lowModeSigma m N ≤ (inferInstance : MeasurableSpace (Hm1 m)) :=
  (measurable_window_coe m N).comap_le

/-- Mass split: the low-mode truncation and its complement have disjoint coefficient supports. -/
theorem charge_split (m N : ℕ) (u : Hm1 m) :
    chargeSobolev38 m 0 u = chargeSobolev38 m 0 (truncSobolev38 _ N u) +
      chargeSobolev38 m 0 (u - truncSobolev38 _ N u) := by
  rw [charge_zero_coeffs m u, charge_zero_coeffs m (truncSobolev38 _ N u),
    charge_zero_coeffs m (u - truncSobolev38 _ N u),
    ← (summable_coeffs_sq m (truncSobolev38 _ N u)).tsum_add
      (summable_coeffs_sq m (u - truncSobolev38 _ N u))]
  congr 1
  funext n
  by_cases hn : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)
  · simp only [coeffs_sub, coeffs_trunc, if_pos hn, sub_self, norm_zero, zero_pow two_ne_zero, add_zero]
  · simp only [coeffs_sub, coeffs_trunc, if_neg hn, sub_zero, norm_zero, zero_pow two_ne_zero, zero_add]

/-- The zero charge of the truncation is a function of the finite window. -/
theorem charge_trunc_eq_window (m N : ℕ) (u : Hm1 m) :
    chargeSobolev38 m 0 (truncSobolev38 _ N u) =
      ∑ i : Fin (2 * N + 1), ‖NlsGge.Ramer.windowProj N (sobolevCoe _ u) i‖ ^ 2 := by
  rw [charge_zero_coeffs m (truncSobolev38 _ N u)]
  rw [tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun b hb => by
    simp only [coeffs_trunc, if_neg hb, norm_zero, zero_pow two_ne_zero])]
  rw [Finset.sum_congr rfl (fun n hn => by rw [coeffs_trunc, if_pos hn])]
  symm
  refine Finset.sum_bij (fun (i : Fin (2 * N + 1)) _ => modeIndex N i)
    (fun i _ => Finset.mem_Icc.2 (modeIndex_bounds N i))
    (fun i _ j _ hij => ?_) (fun n hn => ?_) (fun i _ => rfl)
  · apply Fin.ext
    have := hij
    unfold modeIndex at this
    omega
  · obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 hn
    refine ⟨⟨(n + N).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
    unfold modeIndex
    simp only
    omega

theorem charge_trunc_measurable (m N : ℕ) :
    Measurable[lowModeSigma m N] (fun u : Hm1 m => chargeSobolev38 m 0 (truncSobolev38 _ N u)) := by
  have hG : Continuous (fun z : FourierPlane N => ∑ i : Fin (2 * N + 1), ‖z i‖ ^ 2) :=
    continuous_finset_sum _ (fun i _ => (continuous_norm.comp (continuous_apply i)).pow 2)
  have key : (fun u : Hm1 m => chargeSobolev38 m 0 (truncSobolev38 _ N u)) =
      (fun z : FourierPlane N => ∑ i : Fin (2 * N + 1), ‖z i‖ ^ 2) ∘
        (fun u : Hm1 m => NlsGge.Ramer.windowProj N (sobolevCoe _ u)) :=
    funext (fun u => charge_trunc_eq_window m N u)
  rw [key]
  exact hG.measurable.comp (comap_measurable _)

theorem gammaFM38_isFinite (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j) :
    IsFiniteMeasure (NlsGge.Birkhoff.gammaFM38 m β) := by
  haveI : IsProbabilityMeasure (gammaM38 m β) := NlsGge.Measure.countableComplexGaussian_probability _
  rw [gammaFM38_eq_realization m β]
  infer_instance

theorem integrable_charge_pow_FM (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j) (p : ℕ) :
    Integrable (fun u : Hm1 m => (chargeSobolev38 m 0 u) ^ p) (NlsGge.Birkhoff.gammaFM38 m β) := by
  rw [gammaFM38_eq_realization m β]
  obtain ⟨C, hC, hK, -⟩ := gaussianRealization_moment38 hm (fun i hi => (hβ i hi).le)
    (hβ 0 (Nat.zero_le _)) (hβ m le_rfl) (2 * p)
  have hf : Integrable (fun z : ℤ → ℂ =>
      (chargeSobolev38 m 0 (gaussianRealization38 m z)) ^ p) (gammaM38 m β) := by
    refine Integrable.mono' hK
      (((continuous_chargeSobolev38 m 0 (Nat.zero_le _)).pow p).measurable.comp
        measurable_gaussianRealization38).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (pow_nonneg (mass_nonneg38 (m := m) _) _)]
    calc _ ≤ (‖gaussianRealization38 m z‖ ^ 2) ^ p :=
          pow_le_pow_left₀ (mass_nonneg38 (m := m) _) (mass_le_norm_sq38 (m := m) _) p
      _ = ‖gaussianRealization38 m z‖ ^ (2 * p) := by rw [← pow_mul]
  exact (integrable_map_measure
    ((continuous_chargeSobolev38 m 0 (Nat.zero_le _)).pow p).aestronglyMeasurable
    measurable_gaussianRealization38.aemeasurable).2 hf

theorem f027 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j) :
    (∀ p : ℕ, Integrable (fun u : Hm1 m => (chargeSobolev38 m 0 u) ^ p)
      (NlsGge.Birkhoff.gammaFM38 m β)) ∧
    ∀ N : ℕ,
      (∀ u : Hm1 m, chargeSobolev38 m 0 u =
        chargeSobolev38 m 0 (truncSobolev38 _ N u) +
          chargeSobolev38 m 0 (u - truncSobolev38 _ N u)) ∧
      (fun u : Hm1 m => (chargeSobolev38 m 0 (truncSobolev38 _ N u)) ^ m)
        ≤ᵐ[NlsGge.Birkhoff.gammaFM38 m β]
          (NlsGge.Birkhoff.gammaFM38 m β)[fun u => (chargeSobolev38 m 0 u) ^ m | lowModeSigma m N] := by
  haveI := gammaFM38_isFinite m hm β hβ
  refine ⟨fun p => integrable_charge_pow_FM m hm β hβ p, fun N => ⟨fun u => charge_split m N u, ?_⟩⟩
  have hI : Integrable (fun u : Hm1 m => (chargeSobolev38 m 0 u) ^ m)
      (NlsGge.Birkhoff.gammaFM38 m β) := integrable_charge_pow_FM m hm β hβ m
  have hpt : ∀ u : Hm1 m, chargeSobolev38 m 0 (truncSobolev38 _ N u) ≤ chargeSobolev38 m 0 u := by
    intro u
    rw [charge_split m N u]
    linarith [mass_nonneg38 (m := m) (u - truncSobolev38 _ N u)]
  have hpow : ∀ u : Hm1 m, (chargeSobolev38 m 0 (truncSobolev38 _ N u)) ^ m ≤
      (chargeSobolev38 m 0 u) ^ m := fun u =>
    pow_le_pow_left₀ (mass_nonneg38 (m := m) _) (hpt u) m
  have hJmeas : Measurable[lowModeSigma m N]
      (fun u : Hm1 m => (chargeSobolev38 m 0 (truncSobolev38 _ N u)) ^ m) :=
    (charge_trunc_measurable m N).pow_const m
  have hJ : Integrable (fun u : Hm1 m => (chargeSobolev38 m 0 (truncSobolev38 _ N u)) ^ m)
      (NlsGge.Birkhoff.gammaFM38 m β) := by
    refine Integrable.mono' hI
      ((hJmeas.mono (lowModeSigma_le m N) le_rfl).aestronglyMeasurable)
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_of_nonneg (pow_nonneg (mass_nonneg38 (m := m) _) _)]
    exact hpow u
  have hstrong : StronglyMeasurable[lowModeSigma m N]
      (fun u : Hm1 m => (chargeSobolev38 m 0 (truncSobolev38 _ N u)) ^ m) :=
    hJmeas.stronglyMeasurable
  have hcond : (NlsGge.Birkhoff.gammaFM38 m β)[fun u : Hm1 m =>
      (chargeSobolev38 m 0 (truncSobolev38 _ N u)) ^ m | lowModeSigma m N] =
      (fun u : Hm1 m => (chargeSobolev38 m 0 (truncSobolev38 _ N u)) ^ m) :=
    condExp_of_stronglyMeasurable (lowModeSigma_le m N) hstrong hJ
  have hmono := condExp_mono (m := lowModeSigma m N) hJ hI (Eventually.of_forall hpow)
  filter_upwards [hmono] with u hu
  rw [hcond] at hu
  exact hu

end NlsGge.ThirdConsultation.F
end
