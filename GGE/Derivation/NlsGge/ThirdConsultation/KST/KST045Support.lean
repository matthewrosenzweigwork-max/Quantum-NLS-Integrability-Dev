import Mathlib
import Mathlib.Analysis.Normed.Group.Tannery
import NlsGge.Sobolev.PeriodicBridge
import NlsGge.Sobolev.WeightedHilbert
import NlsGge.Atomic.DM.DM004
import NlsGge.Atomic.KST.KST001
import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST022
import NlsGge.Atomic.KST.KST027
import NlsGge.Atomic.KST.KST035
import NlsGge.Atomic.KST.KST042
import NlsGge.Atomic.DM.DM047
import NlsGge.ThirdConsultation.KST.Basic
import NlsGge.ThirdConsultation.KST.KST029Support
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST033Host
import NlsGge.ThirdConsultation.KST.KST034Host
import NlsGge.ThirdConsultation.KST.KST035Host
import NlsGge.ThirdConsultation.KST.KST035Lift

/- KST045Support PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target
   NlsGge/ThirdConsultation/KST/KST045Support.lean, namespace NlsGge.ThirdConsultation.KST.KST045S.
   SUPPORT module (no packet increment) shared by KST-045 and KST-046.  No definitions; lemmas only:
   (1) rawEnergy_cutoff_tendsto: ENNReal tsum -> real tsum, Tannery dominated convergence, back to ENNReal:
       rawEnergy (w * v_eps) r -> rawEnergy w r as eps -> 0+ when rawEnergy (w * v) r < top and v >= 1;
   (2) rawEnergy_add_le: crude energy triangle (2a + 2b);
   (3) rawEnergy_rawFourier: rawEnergy w (rawFourier phi) = weightedNormSq₂ w (periodicPair phi);
   (4) exists_weighted_of_rawEnergy: finite raw energy <= R^2 gives a genuine Weighted element in the component ball;
   (5) weightedNormSq₂_lt_top_of_eventually_eq: finite-energy transfer along weights equal off a finite set;
   (6) rawEnergy_adapted_lt: strict half-ball margin for the w-energy of the adapted coefficients (KST-035 at the
       secondary weight 1);
   (7) energy_of_inverse: the KST-042 step (weighted preimage) gives finite wu-energy of the physical pair. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ENNReal
open NlsGge.Atomic.KST (SlowWeight)
open NlsGge.Atomic.KST001 NlsGge.Atomic.KST002 NlsGge.Pilot

namespace NlsGge.ThirdConsultation.KST

namespace KST045S

theorem rawEnergy_cutoff_tendsto (w v : ℤ → ℝ) (hv1 : ∀ k, 1 ≤ v k) (r : RawPair)
    (hfin : rawEnergy (productWeight w v) r ≠ ⊤) :
    Tendsto (fun ε : ℝ =>
        rawEnergy (productWeight w (NlsGge.Atomic.DM047.secondaryCutoff v ε)) r)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (rawEnergy w r)) := by
  have hS : ∀ m : ℤ, 0 ≤ ‖r true m‖ ^ 2 + ‖r false m‖ ^ 2 := fun m => by positivity
  have hfin' : ∑' m : ℤ, ENNReal.ofReal
      ((w (2*m) * v (2*m)) ^ 2 * (‖r true m‖ ^ 2 + ‖r false m‖ ^ 2)) ≠ ⊤ := hfin
  have hbound : Summable (fun m : ℤ =>
      (w (2*m) * v (2*m)) ^ 2 * (‖r true m‖ ^ 2 + ‖r false m‖ ^ 2)) :=
    (ENNReal.summable_toReal hfin').congr
      (fun m => ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg _) (hS m)))
  have hcutpos : ∀ (ε : ℝ) (k : ℤ), 0 < NlsGge.Atomic.DM047.secondaryCutoff v ε k := by
    intro ε k
    exact lt_min (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one (hv1 k))
  have hcutle : ∀ (ε : ℝ) (k : ℤ), NlsGge.Atomic.DM047.secondaryCutoff v ε k ≤ v k :=
    fun ε k => min_le_right _ _
  have hpoint (m : ℤ) : Tendsto
      (fun ε : ℝ => (w (2*m) * NlsGge.Atomic.DM047.secondaryCutoff v ε (2*m)) ^ 2 *
        (‖r true m‖ ^ 2 + ‖r false m‖ ^ 2))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (w (2*m) ^ 2 * (‖r true m‖ ^ 2 + ‖r false m‖ ^ 2))) := by
    have hc : Continuous (fun ε : ℝ => NlsGge.Atomic.DM047.secondaryCutoff v ε (2*m)) := by
      unfold NlsGge.Atomic.DM047.secondaryCutoff
      exact (Real.continuous_exp.comp (continuous_id.mul continuous_const)).min continuous_const
    have h0 : NlsGge.Atomic.DM047.secondaryCutoff v 0 (2*m) = 1 := by
      simp only [NlsGge.Atomic.DM047.secondaryCutoff, zero_mul, Real.exp_zero]
      exact min_eq_left (hv1 (2*m))
    have hcut : Tendsto (fun ε : ℝ => NlsGge.Atomic.DM047.secondaryCutoff v ε (2*m))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
      have := hc.tendsto 0
      rw [h0] at this
      exact this.mono_left nhdsWithin_le_nhds
    have := ((hcut.const_mul (w (2*m))).pow 2).mul_const
      (‖r true m‖ ^ 2 + ‖r false m‖ ^ 2)
    simpa using this
  have hle : ∀ (ε : ℝ) (m : ℤ),
      (w (2*m) * NlsGge.Atomic.DM047.secondaryCutoff v ε (2*m)) ^ 2 *
        (‖r true m‖ ^ 2 + ‖r false m‖ ^ 2) ≤
      (w (2*m) * v (2*m)) ^ 2 * (‖r true m‖ ^ 2 + ‖r false m‖ ^ 2) := by
    intro ε m
    refine mul_le_mul_of_nonneg_right ?_ (hS m)
    rw [mul_pow, mul_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (hcutpos ε (2*m)).le (hcutle ε (2*m)) 2) (sq_nonneg _)
  have hdom : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), ∀ m : ℤ,
      ‖(w (2*m) * NlsGge.Atomic.DM047.secondaryCutoff v ε (2*m)) ^ 2 *
        (‖r true m‖ ^ 2 + ‖r false m‖ ^ 2)‖ ≤
      (w (2*m) * v (2*m)) ^ 2 * (‖r true m‖ ^ 2 + ‖r false m‖ ^ 2) := by
    filter_upwards with ε
    intro m
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hS m))]
    exact hle ε m
  have hsum := tendsto_tsum_of_dominated_convergence hbound hpoint hdom
  have hsumm : ∀ ε : ℝ, Summable (fun m : ℤ =>
      (w (2*m) * NlsGge.Atomic.DM047.secondaryCutoff v ε (2*m)) ^ 2 *
        (‖r true m‖ ^ 2 + ‖r false m‖ ^ 2)) := by
    intro ε
    exact Summable.of_nonneg_of_le (fun m => mul_nonneg (sq_nonneg _) (hS m))
      (fun m => hle ε m) hbound
  have hlimsumm : Summable (fun m : ℤ => w (2*m) ^ 2 * (‖r true m‖ ^ 2 + ‖r false m‖ ^ 2)) := by
    refine Summable.of_nonneg_of_le (fun m => mul_nonneg (sq_nonneg _) (hS m))
      (fun m => ?_) hbound
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (hS m)
    have h1 := hv1 (2*m)
    have : 1 ≤ v (2*m) ^ 2 := one_le_pow₀ h1
    nlinarith [sq_nonneg (w (2*m))]
  have hE : ∀ ε : ℝ,
      rawEnergy (productWeight w (NlsGge.Atomic.DM047.secondaryCutoff v ε)) r =
        ENNReal.ofReal (∑' m : ℤ, (w (2*m) * NlsGge.Atomic.DM047.secondaryCutoff v ε (2*m)) ^ 2 *
          (‖r true m‖ ^ 2 + ‖r false m‖ ^ 2)) := by
    intro ε
    unfold rawEnergy productWeight
    exact (ENNReal.ofReal_tsum_of_nonneg (fun m => mul_nonneg (sq_nonneg _) (hS m))
      (hsumm ε)).symm
  have hE0 : rawEnergy w r =
      ENNReal.ofReal (∑' m : ℤ, w (2*m) ^ 2 * (‖r true m‖ ^ 2 + ‖r false m‖ ^ 2)) := by
    unfold rawEnergy
    exact (ENNReal.ofReal_tsum_of_nonneg (fun m => mul_nonneg (sq_nonneg _) (hS m))
      hlimsumm).symm
  rw [hE0]
  exact (tendsto_congr hE).2 (ENNReal.tendsto_ofReal hsum)

theorem two_mul_ofReal (a : ℝ) : 2 * ENNReal.ofReal a = ENNReal.ofReal (2 * a) := by
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

theorem rawEnergy_add_le (ω : ℤ → ℝ) (r₁ r₂ : RawPair) :
    rawEnergy ω (r₁ + r₂) ≤ 2 * rawEnergy ω r₁ + 2 * rawEnergy ω r₂ := by
  unfold rawEnergy
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum (fun m => ?_)
  have hn : ∀ ch : Bool, ‖(r₁ + r₂) ch m‖ ^ 2 ≤ 2 * ‖r₁ ch m‖ ^ 2 + 2 * ‖r₂ ch m‖ ^ 2 := by
    intro ch
    have h1 : ‖(r₁ + r₂) ch m‖ ≤ ‖r₁ ch m‖ + ‖r₂ ch m‖ := by
      simpa using norm_add_le (r₁ ch m) (r₂ ch m)
    nlinarith [norm_nonneg ((r₁ + r₂) ch m), norm_nonneg (r₁ ch m), norm_nonneg (r₂ ch m),
      sq_nonneg (‖r₁ ch m‖ - ‖r₂ ch m‖)]
  have hpt : ω (2*m) ^ 2 * (‖(r₁ + r₂) true m‖ ^ 2 + ‖(r₁ + r₂) false m‖ ^ 2) ≤
      2 * (ω (2*m) ^ 2 * (‖r₁ true m‖ ^ 2 + ‖r₁ false m‖ ^ 2)) +
        2 * (ω (2*m) ^ 2 * (‖r₂ true m‖ ^ 2 + ‖r₂ false m‖ ^ 2)) := by
    have h := mul_le_mul_of_nonneg_left (add_le_add (hn true) (hn false)) (sq_nonneg (ω (2*m)))
    nlinarith [h]
  calc ENNReal.ofReal (ω (2*m) ^ 2 * (‖(r₁ + r₂) true m‖ ^ 2 + ‖(r₁ + r₂) false m‖ ^ 2))
      ≤ ENNReal.ofReal (2 * (ω (2*m) ^ 2 * (‖r₁ true m‖ ^ 2 + ‖r₁ false m‖ ^ 2)) +
        2 * (ω (2*m) ^ 2 * (‖r₂ true m‖ ^ 2 + ‖r₂ false m‖ ^ 2))) :=
        ENNReal.ofReal_le_ofReal hpt
    _ = 2 * ENNReal.ofReal (ω (2*m) ^ 2 * (‖r₁ true m‖ ^ 2 + ‖r₁ false m‖ ^ 2)) +
        2 * ENNReal.ofReal (ω (2*m) ^ 2 * (‖r₂ true m‖ ^ 2 + ‖r₂ false m‖ ^ 2)) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ← two_mul_ofReal, ← two_mul_ofReal]

theorem rawEnergy_rawFourier (ω : ℤ → ℝ) (hω : EvenWeight ω) (φ : Potential) :
    rawEnergy ω (rawFourier φ) = weightedNormSq₂ ω (periodicPair φ) := by
  rw [periodOne_weightedPair_norm ω (periodicPair φ) hω]
  unfold weightedEvenFourierNormSq rawEnergy
  refine tsum_congr (fun m => ?_)
  unfold weightedPairMode
  rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    ← ENNReal.ofReal_mul (sq_nonneg _)]
  rfl

theorem exists_weighted_of_rawEnergy (ω : ℤ → ℝ)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]
    (r : RawPair) (R : ℝ) (hR : 0 ≤ R) (h : rawEnergy ω r ≤ ENNReal.ofReal (R ^ 2)) :
    ∃ y : Weighted ω, y ∈ componentBall ω R ∧ weightedCoeffs ω y = r := by
  have hfin : rawEnergy ω r ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hs := KST035L.summable_of_rawEnergy ω r hfin
  have hmem : ∀ ch, Memℓp (weightedCoordinates (fun k => periodOneWeight ω k ^ 2) (r ch)) 2 :=
    fun ch => (weightedCoordinates_mem_l2_iff _ (fun n => by positivity) (r ch)).2 (hs ch)
  let y : Weighted ω := WithLp.toLp 2 (fun ch =>
    (⟨r ch, hmem ch⟩ : weightedSubmodule (fun k => periodOneWeight ω k ^ 2)))
  refine ⟨y, ?_, ?_⟩
  · intro ch
    have hsum := weightedHilbert_hasSum (fun k => periodOneWeight ω k ^ 2) (y ch)
    have hsum' : HasSum (fun m : ℤ => ω (2 * m) ^ 2 * ‖r ch m‖ ^ 2) (‖y ch‖ ^ 2) := hsum
    have hle : ∀ m : ℤ, ENNReal.ofReal (ω (2 * m) ^ 2 * ‖r ch m‖ ^ 2) ≤
        ENNReal.ofReal (ω (2 * m) ^ 2 * (‖r true m‖ ^ 2 + ‖r false m‖ ^ 2)) := by
      intro m
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
      cases ch
      · exact le_add_of_nonneg_left (sq_nonneg _)
      · exact le_add_of_nonneg_right (sq_nonneg _)
    have h1 : ENNReal.ofReal (‖y ch‖ ^ 2) ≤ ENNReal.ofReal (R ^ 2) := by
      rw [← hsum'.tsum_eq,
        ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum'.summable]
      exact (ENNReal.tsum_le_tsum hle).trans h
    have h2 : ‖y ch‖ ^ 2 ≤ R ^ 2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
    by_contra hlt
    have := mul_self_lt_mul_self hR (not_le.mp hlt)
    nlinarith
  · funext ch m
    rfl

theorem weightedNormSq₂_lt_top_of_eventually_eq (W₁ W₂ : ℤ → ℝ) (φ : PeriodicPair) (N : ℕ)
    (h : ∀ k : ℤ, N < k.natAbs → W₁ k = W₂ k) (hfin : weightedNormSq₂ W₂ φ < ⊤) :
    weightedNormSq₂ W₁ φ < ⊤ := by
  classical
  have hne : ∀ k : ℤ, weightedPairMode W₁ k (periodTwoPairCoeff φ k) ≠ ⊤ := fun k =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
  let g : ℤ → ℝ≥0∞ := fun k =>
    if k.natAbs ≤ N then weightedPairMode W₁ k (periodTwoPairCoeff φ k) else 0
  have hg : ∑' k : ℤ, g k < ⊤ := by
    rw [tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) N)]
    · exact ENNReal.sum_lt_top.2 (fun k _ => by
        by_cases hk : k.natAbs ≤ N
        · exact lt_top_iff_ne_top.2 (by simpa [g, hk] using hne k)
        · simp [g, hk])
    · intro k hk
      have : ¬ k.natAbs ≤ N := by
        intro h'
        apply hk
        rw [Finset.mem_Icc]
        omega
      simp [g, this]
  unfold weightedNormSq₂ at hfin ⊢
  calc ∑' k : ℤ, weightedPairMode W₁ k (periodTwoPairCoeff φ k)
      ≤ ∑' k : ℤ, (weightedPairMode W₂ k (periodTwoPairCoeff φ k) + g k) := by
        refine ENNReal.tsum_le_tsum (fun k => ?_)
        by_cases hk : k.natAbs ≤ N
        · simp only [g, hk, if_true]
          exact le_add_self
        · have hk' : N < k.natAbs := not_le.mp hk
          have : weightedPairMode W₁ k (periodTwoPairCoeff φ k) =
              weightedPairMode W₂ k (periodTwoPairCoeff φ k) := by
            unfold weightedPairMode
            rw [h k hk']
          rw [this]
          exact le_self_add
    _ = ∑' k : ℤ, weightedPairMode W₂ k (periodTwoPairCoeff φ k) + ∑' k : ℤ, g k :=
        ENNReal.tsum_add
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hfin, hg⟩

theorem rawEnergy_adapted_lt (w : ℤ → ℝ) (Cw M : ℝ) (hM : 1 ≤ M)
    (hw : SlowWeight w Cw)
    (hunbounded : Tendsto (fun n : ℕ => w (n : ℤ)) atTop atTop)
    (φ : Potential)
    (hφ : weightedNormSq₂ w (periodicPair φ) < ⊤)
    (hmargin : 8 * Real.sqrt (weightedNormSq₂ w (periodicPair φ)).toReal ≤ M) :
    rawEnergy w (adaptedCoefficients (adaptedThreshold w M) φ) <
      ENNReal.ofReal ((M / 2) ^ 2) := by
  have hM0 : 0 < M := by linarith
  have hwE : EvenWeight w := ⟨hw.one_le, hw.even⟩
  have hEraw : rawEnergy w (rawFourier φ) = weightedNormSq₂ w (periodicPair φ) :=
    rawEnergy_rawFourier w hwE φ
  have hEreal : weightedNormSq₂ w (periodicPair φ) =
      ENNReal.ofReal (weightedNormSq₂ w (periodicPair φ)).toReal :=
    (ENNReal.ofReal_toReal hφ.ne).symm
  have he : (weightedNormSq₂ w (periodicPair φ)).toReal ≤ (M / 8) ^ 2 := by
    have h1 : Real.sqrt (weightedNormSq₂ w (periodicPair φ)).toReal ≤ M / 8 := by linarith
    have h2 := Real.sq_sqrt (ENNReal.toReal_nonneg (a := weightedNormSq₂ w (periodicPair φ)))
    nlinarith [Real.sqrt_nonneg (weightedNormSq₂ w (periodicPair φ)).toReal]
  have hEle : rawEnergy w (rawFourier φ) ≤ ENNReal.ofReal ((M / 8) ^ 2) := by
    rw [hEraw, hEreal]
    exact ENNReal.ofReal_le_ofReal he
  have hcond := (kst035 w Cw M hM hw hunbounded).2.1
  have hv1sec : SecondaryWeight (fun _ : ℤ => (1 : ℝ)) :=
    ⟨⟨fun _ => le_rfl, fun _ => rfl, fun _ _ _ => le_rfl⟩, fun k l => by simp⟩
  have hprod : productWeight w (fun _ : ℤ => (1 : ℝ)) = w := by
    funext k; simp [productWeight]
  have hball : φ ∈ physicalComponentBall (productWeight w (fun _ : ℤ => (1 : ℝ))) (2 * M) := by
    intro ch
    rw [hprod]
    calc ∑' m : ℤ, ENNReal.ofReal (w (2 * m) ^ 2 * ‖physicalFourier (φ ch) m‖ ^ 2)
        ≤ rawEnergy w (rawFourier φ) := by
          unfold rawEnergy
          refine ENNReal.tsum_le_tsum (fun m => ?_)
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
          cases ch
          · exact le_add_of_nonneg_left (sq_nonneg _)
          · exact le_add_of_nonneg_right (sq_nonneg _)
      _ ≤ ENNReal.ofReal ((M / 8) ^ 2) := hEle
      _ ≤ ENNReal.ofReal ((2 * M) ^ 2) := ENNReal.ofReal_le_ofReal (by nlinarith)
  have hD := hcond.2 (fun _ : ℤ => (1 : ℝ)) hv1sec φ hball
  rw [hprod] at hD
  have hr : adaptedCoefficients (adaptedThreshold w M) φ =
      (adaptedCoefficients (adaptedThreshold w M) φ - rawFourier φ) + rawFourier φ :=
    (sub_add_cancel _ _).symm
  calc rawEnergy w (adaptedCoefficients (adaptedThreshold w M) φ)
      = rawEnergy w ((adaptedCoefficients (adaptedThreshold w M) φ - rawFourier φ) +
          rawFourier φ) := congrArg (rawEnergy w) hr
    _ ≤ 2 * rawEnergy w (adaptedCoefficients (adaptedThreshold w M) φ - rawFourier φ) +
          2 * rawEnergy w (rawFourier φ) := rawEnergy_add_le _ _ _
    _ ≤ 2 * ENNReal.ofReal ((M / 16) ^ 2) + 2 * ENNReal.ofReal ((M / 8) ^ 2) :=
        add_le_add (mul_le_mul' (le_refl 2) hD) (mul_le_mul' (le_refl 2) hEle)
    _ = ENNReal.ofReal (2 * (M / 16) ^ 2 + 2 * (M / 8) ^ 2) := by
        rw [two_mul_ofReal, two_mul_ofReal, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ < ENNReal.ofReal ((M / 2) ^ 2) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by nlinarith)

theorem energy_of_inverse (w : ℤ → ℝ) (Cw M : ℝ) (hM : 1 ≤ M) (hw : SlowWeight w Cw)
    (hunbounded : Tendsto (fun n : ℕ => w (n : ℤ)) atTop atTop)
    (u : ℤ → ℝ) (hu : SecondaryWeight u) (φ : Potential)
    (hφ : weightedNormSq₂ w (periodicPair φ) < ⊤)
    (hmargin : 8 * Real.sqrt (weightedNormSq₂ w (periodicPair φ)).toReal ≤ M)
    (hE : rawEnergy (productWeight w u) (adaptedCoefficients (adaptedThreshold w M) φ) ≤
      ENNReal.ofReal ((M / 2) ^ 2)) :
    weightedNormSq₂ (productWeight w u) (periodicPair φ) < ⊤ := by
  have hM0 : 0 < M := by linarith
  have hwE : EvenWeight w := ⟨hw.one_le, hw.even⟩
  letI := weightFact w hw.one_le
  have hex : ∃ x : Weighted w, periodOnePhysicalPair w hwE x = periodicPair φ :=
    periodOnePhysicalPair_exists_of_finite_energy w hwE (periodicPair φ) hφ
  obtain ⟨x, hx⟩ := hex
  have hpot : weightedPotential w hw.one_le x = φ := by
    refine PiLp.ext (fun ch => ?_)
    cases ch
    · exact congrArg Prod.snd hx
    · exact congrArg Prod.fst hx
  have hnorm : weightedNormSq₂ w (periodicPair φ) = ENNReal.ofReal (‖x‖ ^ 2) := by
    rw [← hx]
    exact periodOnePhysicalPair_full_doubled_energy_eq_norm w hwE x
  have hxn : ‖x‖ ≤ M / 8 := by
    rw [hnorm, ENNReal.toReal_ofReal (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hmargin
    linarith
  have hxball : x ∈ componentBall w M := fun ch =>
    (PiLp.norm_apply_le x ch).trans (by linarith)
  have hωone : ∀ k, 1 ≤ productWeight w u k := productOneLe hw.one_le hu.1.1
  letI := weightFact (productWeight w u) hωone
  obtain ⟨y, hyball, hy⟩ := exists_weighted_of_rawEnergy (productWeight w u)
    (adaptedCoefficients (adaptedThreshold w M) φ) (M / 2) (by positivity) hE
  have h42 := kst042 w Cw M hM hw hunbounded u hu
  obtain ⟨z, -, hzp, -⟩ := h42 x hxball y hyball (by rw [hy, hpot])
  have hωE : EvenWeight (productWeight w u) :=
    ⟨hωone, fun k => by
      show w (-k) * u (-k) = w k * u k
      rw [hw.even, hu.1.2.1]⟩
  have hpair : periodOnePhysicalPair (productWeight w u) hωE z = periodicPair φ := by
    have h : periodOnePhysicalPair (productWeight w u) hωE z =
        periodicPair (weightedPotential (productWeight w u) hωone z) := rfl
    rw [h, hzp, hpot]
  rw [← hpair]
  exact periodOnePhysicalPair_full_doubled_energy_finite (productWeight w u) hωE z

end KST045S

end NlsGge.ThirdConsultation.KST
end
