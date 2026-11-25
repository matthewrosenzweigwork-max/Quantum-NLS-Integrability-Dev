import NlsGge.Birkhoff.F11Claim38b
import NlsGge.Birkhoff.F09Limit38f
import NlsGge.Birkhoff.S04Moments38d
import NlsGge.Birkhoff.S01Equivariance38b

/-! # NEW-F11 (`F:cor:charge`), file 3: the exact finite-dimensional identity (NEW-F11.03), `B`-free

Source: `paper/v2.tex` l.1813-1816:
`∫ e^{Σ t_j Q_{2j}} dν_{W,N} = D_{p,N}^{-1} Z_N(W-p)/Z_N(W)`.

* `tiltCharge38 J t N z = Σ_{j≤J} t_j Q_{2j}(z)` on the Fourier plane (`Q_{2j}(z) = localCharge38 (planeReal N z) j`);
* `fullEnergy38_tilt`: `E_W = E_{W-p} + Σ t_j Q_{2j}` on every plane (the complete charge series is summable, so
  the totalized `tsum` splits exactly);
* `freeNormalizer38_tilt`: `∏ π/a*_n = D_{p,N}^{-1} ∏ π/a_n`;
* `chargeFn38_planeL2`: for `2 ≤ m`, `j ≤ m`, the charge functional `chargeFn38 m j` (continuous extension of the
  local charge to `H^{m-1}`, cleaned off `H^{m-1}`) equals the local charge `localCharge38 (planeReal N z) j` of the
  plane field `planeL2 N z`;
* `integral_tilt_nuWN38`: `G(planeL2 z) = e^{tiltCharge z}` (all `z`) implies `G` is `ν_{W,N}`-integrable and
  `∫ G dν_{W,N} = 𝒵_{W-p,N}/𝒵_{W,N}`;
* `exact_identity38` (NEW-F11.03): `∫ exp(Σ t_j chargeFn38 m j) dν_{W,N} = D_{p,N}⁻¹ Z_N(W-p)/Z_N(W)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.HierarchyRiccati.Core NlsGge.HierarchyRiccati Filter Topology
open scoped ENNReal Real ContDiff

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

section Plane

variable {lower upper : ℝ}

/-- `Σ_{j ≤ J} t_j Q_{2j}` on the Fourier plane `ℂ^{2N+1}`. -/
def tiltCharge38 (J : ℕ) (t : ℕ → ℝ) (N : ℕ) (z : FourierPlane N) : ℝ :=
  ∑ j ∈ Finset.range (J + 1), t j * localCharge38 (planeReal N z) j

theorem continuous_tiltCharge38 (J : ℕ) (t : ℕ → ℝ) (N : ℕ) : Continuous (tiltCharge38 J t N) := by
  unfold tiltCharge38
  exact continuous_finset_sum _ fun j _ => continuous_const.mul (continuous_localCharge38 N j)

/-- **NEW-F11.03 (energy split).** `E_W = E_{W-p} + Σ_{j≤J} t_j Q_{2j}` on every plane. -/
theorem fullEnergy38_tilt (c : BoundedCoefficients lower upper) {J : ℕ} {t : ℕ → ℝ}
    (ht : TiltAdmissible38 c J t) (N : ℕ) (z : FourierPlane N) :
    fullEnergy38 c N z =
      fullEnergy38 (tiltedCoefficients38 c ht) N z + tiltCharge38 J t N z := by
  have hs' := fullEnergy38_summable (tiltedCoefficients38 c ht) N z
  have hg : Summable (fun j : ℕ => if j ≤ J then t j * localCharge38 (planeReal N z) j else 0) := by
    refine summable_of_ne_finset_zero (s := Finset.range (J + 1)) fun j hj => ?_
    have : ¬ j ≤ J := fun h => hj (by simpa [Nat.lt_succ_iff] using h)
    simp [this]
  have key : ∀ j : ℕ, c.val j / ((j.factorial : ℝ)) ^ 4 * localCharge38 (planeReal N z) j =
      (tiltedCoefficients38 c ht).val j / ((j.factorial : ℝ)) ^ 4 * localCharge38 (planeReal N z) j +
        (if j ≤ J then t j * localCharge38 (planeReal N z) j else 0) := by
    intro j
    have hf : ((j.factorial : ℝ)) ^ 4 ≠ 0 := by positivity
    simp only [tiltedCoefficients38_val, tiltCoeff38]
    split_ifs
    · field_simp; ring
    · simp
  have hgs : ∑' j : ℕ, (if j ≤ J then t j * localCharge38 (planeReal N z) j else 0) =
      tiltCharge38 J t N z := by
    rw [tsum_eq_sum (s := Finset.range (J + 1))]
    · unfold tiltCharge38
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j ≤ J := by simpa [Nat.lt_succ_iff] using hj
      simp only [hj', ↓reduceIte]
    · intro j hj
      have : ¬ j ≤ J := fun h => hj (by simpa [Nat.lt_succ_iff] using h)
      simp [this]
  unfold fullEnergy38
  rw [show (fun j : ℕ => c.val j / ((j.factorial : ℝ)) ^ 4 * localCharge38 (planeReal N z) j) =
    fun j => (tiltedCoefficients38 c ht).val j / ((j.factorial : ℝ)) ^ 4 *
        localCharge38 (planeReal N z) j +
      (if j ≤ J then t j * localCharge38 (planeReal N z) j else 0) from funext key,
    hs'.tsum_add hg, hgs]

theorem exp_tiltCharge_mul38 (c : BoundedCoefficients lower upper) {J : ℕ} {t : ℕ → ℝ}
    (ht : TiltAdmissible38 c J t) (N : ℕ) (z : FourierPlane N) :
    Real.exp (tiltCharge38 J t N z) * Real.exp (-fullEnergy38 c N z) =
      Real.exp (-fullEnergy38 (tiltedCoefficients38 c ht) N z) := by
  rw [← Real.exp_add, fullEnergy38_tilt c ht N z]
  congr 1; ring

/-- `∏ π/a*_n = D_{p,N}^{-1} ∏ π/a_n` (free Gaussian normalizers of `W - p` and `W`). -/
theorem freeNormalizer38_tilt (c : BoundedCoefficients lower upper) {J : ℕ} {t : ℕ → ℝ}
    (ht : TiltAdmissible38 c J t) (N : ℕ) :
    freeNormalizer38 (tiltedCoefficients38 c ht) N = freeNormalizer38 c N / tiltDet38 c J t N := by
  unfold freeNormalizer38 tiltDet38
  rw [← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [one_sub_tiltX38 ht]
  have h1 := fullWeightRate_pos38 c (modeIndex N i)
  have h2 := fullWeightRate_pos38 (tiltedCoefficients38 c ht) (modeIndex N i)
  have h2' : 0 < fullWeightRate (tiltCoeff38 c.val J t) (modeIndex N i) := h2
  have : (tiltedCoefficients38 c ht).val = tiltCoeff38 c.val J t := rfl
  rw [this]
  field_simp

theorem fullPartition38_tilt (c : BoundedCoefficients lower upper) {J : ℕ} {t : ℕ → ℝ}
    (ht : TiltAdmissible38 c J t) (N : ℕ) :
    fullPartition38 (tiltedCoefficients38 c ht) N / fullPartition38 c N =
      (relativePartition38 (tiltedCoefficients38 c ht) N / relativePartition38 c N) /
        tiltDet38 c J t N := by
  have hD := tiltDet_pos38 ht N
  have hF := freeNormalizer38_pos c N
  have hR := relativePartition38_pos c N
  rw [← relativePartition38_mul c N, ← relativePartition38_mul (tiltedCoefficients38 c ht) N,
    freeNormalizer38_tilt c ht N]
  field_simp

end Plane

/-! ### The charge functional on plane fields -/

theorem lift_planeReal_F11_38 (N : ℕ) (z : FourierPlane N) :
    riccatiSmoothPeriodicLiftContinuousMapRecovery30First (planeReal N z)
      (contDiff_planeReal N z).continuous (planeReal_periodic N z) = planeContinuous N z := by
  ext y
  obtain ⟨t, ht, rfl⟩ := exists_Ioc_rep38 y
  have ht' : t ∈ Set.Ioc (0 : ℝ) (0 + 1) := by simpa using ht
  simp only [riccatiSmoothPeriodicLiftContinuousMapRecovery30First, ContinuousMap.coe_mk]
  rw [AddCircle.liftIoc_coe_apply ht']
  rfl

theorem physicalFourier_planeL2_mem38 (k : ℕ) (N : ℕ) (z : FourierPlane N) :
    (fun n => physicalFourier (planeL2 N z) n) ∈ seqSobolev38 (k : ℝ) := by
  rw [mem_seqSobolev38_iff]
  refine summable_of_ne_finset_zero (s := symmetricModes N) fun n hn => ?_
  have hout : n < -(N : ℤ) ∨ (N : ℤ) < n := by
    simp only [symmetricModes, Finset.mem_Icc] at hn
    omega
  have h0 : physicalFourier (planeL2 N z) n = 0 := by
    rw [physicalFourier_planeL2]; exact physicalFourier_planeField_outside N z n hout
  show _ * ‖physicalFourier (planeL2 N z) n‖ ^ 2 = 0
  rw [h0]; simp

/-- **The charge functional on plane fields.** For `2 ≤ m` and `j ≤ m`,
`chargeFn38 m j (planeL2 N z) = Q_{2j}(planeReal N z)` (the local charge of the trigonometric polynomial). -/
theorem chargeFn38_planeL2 (m j : ℕ) (hm : 2 ≤ m) (hjm : j ≤ m) (N : ℕ) (z : FourierPlane N) :
    chargeFn38 m j (planeL2 N z) = localCharge38 (planeReal N z) j := by
  have hmem := physicalFourier_planeL2_mem38 (m - 1) N z
  have hU : ContDiff ℝ ∞ (planeReal N z) := (contDiff_planeReal N z).of_le le_top
  set x : SobolevHilbert ((m - 1 : ℕ) : ℝ) :=
    ofCarrier38 ((m - 1 : ℕ) : ℝ) (physC38 (m - 1) (planeL2 N z)) with hx
  have hsource : ∀ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from x) n =
        physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First (planeReal N z)
            hU.continuous (planeReal_periodic N z))) n := by
    intro n
    have e : ContinuousMap.toLp 2 spatialMeasure ℂ
        (riccatiSmoothPeriodicLiftContinuousMapRecovery30First (planeReal N z)
          hU.continuous (planeReal_periodic N z)) = planeL2 N z := by
      rw [lift_planeReal_F11_38]; rfl
    rw [e]
    have : x = carrierMk38 ((m - 1 : ℕ) : ℝ) _ hmem := by
      rw [hx]; exact physC38_of_mem (m - 1) _ hmem
    rw [this]
    rfl
  have h := chargeSobolev38_smooth m j hm hjm (planeReal N z) hU
    (planeReal_periodic N z) x hsource
  exact h

section Exact

variable {lower upper : ℝ}

/-- Integrability against `ν_{W,N}` and the value of the integral of a function that is `e^{tiltCharge}` on every
plane point. -/
theorem integral_tilt_nuWN38 (c : BoundedCoefficients lower upper) {J : ℕ} {t : ℕ → ℝ}
    (ht : TiltAdmissible38 c J t) (N : ℕ) (G : PhysicalL2 → ℝ)
    (hG : ∀ z : FourierPlane N, G (planeL2 N z) = Real.exp (tiltCharge38 J t N z)) :
    Integrable G (nuWN38 c N) ∧
      ∫ u, G u ∂(nuWN38 c N) =
        fullPartition38 (tiltedCoefficients38 c ht) N / fullPartition38 c N := by
  have hGeq : (fun z : FourierPlane N => G (planeL2 N z)) = fun z => Real.exp (tiltCharge38 J t N z) :=
    funext hG
  have hGc : Continuous (fun z : FourierPlane N => G (planeL2 N z)) := by
    rw [hGeq]; exact (continuous_tiltCharge38 J t N).rexp
  have hρ : Measurable (fun z : FourierPlane N => ENNReal.ofReal (Real.exp (-fullEnergy38 c N z))) :=
    (continuous_fullEnergy38 c N).neg.rexp.measurable.ennreal_ofReal
  refine ⟨?_, ?_⟩
  · unfold nuWN38
    refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
    rw [(measurableEmbedding_planeL2_38 N).integrable_map_iff]
    rw [integrable_withDensity_iff_integrable_smul' hρ
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine (integrable_exp_neg_fullEnergy38 (tiltedCoefficients38 c ht) N).congr
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [Function.comp, ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
    rw [hG z, ← exp_tiltCharge_mul38 c ht N z, mul_comm]
  · rw [integral_nuWN38_plane c N G hGc.aestronglyMeasurable]
    have h1 : ∫ z, G (planeL2 N z) * Real.exp (-fullEnergy38 c N z) ∂(planeVolume N) =
        fullPartition38 (tiltedCoefficients38 c ht) N := by
      unfold fullPartition38
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only
      rw [hG z, exp_tiltCharge_mul38 c ht N z]
    rw [h1]
    ring

/-- **NEW-F11.03 (exact finite-dimensional identity), plane form.** -/
theorem exact_identity_plane38 (c : BoundedCoefficients lower upper) {J : ℕ} {t : ℕ → ℝ}
    (ht : TiltAdmissible38 c J t) (N : ℕ) (G : PhysicalL2 → ℝ)
    (hG : ∀ z : FourierPlane N, G (planeL2 N z) = Real.exp (tiltCharge38 J t N z)) :
    Integrable G (nuWN38 c N) ∧
      ∫ u, G u ∂(nuWN38 c N) =
        (tiltDet38 c J t N)⁻¹ *
          (relativePartition38 (tiltedCoefficients38 c ht) N / relativePartition38 c N) := by
  obtain ⟨h1, h2⟩ := integral_tilt_nuWN38 c ht N G hG
  refine ⟨h1, ?_⟩
  rw [h2, fullPartition38_tilt c ht N]
  ring

/-- **NEW-F11.03 (exact finite-dimensional identity).** For `2 ≤ m`, `J < m`, `0 ≤ t_j < β_j` (`j ≤ J`):
`∫ exp(Σ_{j≤J} t_j Q_{2j}) dν_{W,N} = D_{p,N}⁻¹ Z_N(W-p)/Z_N(W)` (`Q_{2j} = chargeFn38 m j`), and the integrand
is `ν_{W,N}`-integrable. -/
theorem exact_identity38 (c : BoundedCoefficients lower upper) {J : ℕ} {t : ℕ → ℝ}
    (ht : TiltAdmissible38 c J t) (m : ℕ) (hm : 2 ≤ m) (hJ : J ≤ m) (N : ℕ) :
    Integrable (fun u => Real.exp (∑ j ∈ Finset.range (J + 1), t j * chargeFn38 m j u))
        (nuWN38 c N) ∧
      ∫ u, Real.exp (∑ j ∈ Finset.range (J + 1), t j * chargeFn38 m j u) ∂(nuWN38 c N) =
        (tiltDet38 c J t N)⁻¹ *
          (relativePartition38 (tiltedCoefficients38 c ht) N / relativePartition38 c N) := by
  refine exact_identity_plane38 c ht N _ fun z => ?_
  unfold tiltCharge38
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [chargeFn38_planeL2 m j hm (by simpa [Nat.lt_succ_iff] using (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) |>.trans hJ) N z]

end Exact

end NlsGge.Birkhoff
end
