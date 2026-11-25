                                                                                                                                                                                                                                                                                         
                                                                                                                                                                                                                                                                                                                            
import NlsGge.Atomic.KST.KST016
import NlsGge.Atomic.KST.KST017
import NlsGge.Atomic.KST.KST011

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace NlsGge.ThirdConsultation.KST

open NlsGge.Atomic.KST002 NlsGge.Atomic.KST003
open NlsGge.Atomic.KST004 NlsGge.Atomic.KST006 NlsGge.Atomic.KST007
open NlsGge.Atomic.KST012 NlsGge.Atomic.KST013 NlsGge.Atomic.KST016
open NlsGge.Analysis NlsGge.Pilot NlsGge.Schur

def center (n : ℤ) : ℂ := (n : ℂ) * Real.pi

theorem center_mem_strip (n : ℤ) : center n ∈ spectralStrip n := by
  simp only [center, spectralStrip, Set.mem_setOf_eq]
  have : ((n : ℂ) * (Real.pi : ℂ)).re = (n : ℝ) * Real.pi := by simp
  rw [this, sub_self, abs_zero]
  positivity

def abc (φ : Potential) (n : ℤ) (z : ℂ) : ℂ × ℂ × ℂ :=
  localABC n (center n) (center_mem_strip n) (z, φ)

def a (φ : Potential) (n : ℤ) (z : ℂ) : ℂ := (abc φ n z).1

def b (φ : Potential) (n : ℤ) (z : ℂ) : ℂ := (abc φ n z).2.1

def c (φ : Potential) (n : ℤ) (z : ℂ) : ℂ := (abc φ n z).2.2

theorem isUnit_free_of_strips (n : ℤ) (z₀ z : ℂ) (hz₀ : z₀ ∈ spectralStrip n)
    (hz : z ∈ spectralStrip n) :
    IsUnit (1 + (z - z₀) • complementaryMultiplier n z₀ hz₀ : EndH) := by
  set F : EndH := 1 + (z - z₀) • complementaryMultiplier n z₀ hz₀ with hF
  set G : EndH := 1 + (z₀ - z) • complementaryMultiplier n z hz with hG
  have h1 := compMult_comp_free n z₀ z hz₀ hz
  have h2 := compMult_comp_free n z z₀ hz hz₀
  rw [← hF] at h1
  rw [← hG] at h2
  have hGF : G * F = 1 := by
    calc G * F = F + (z₀ - z) • (complementaryMultiplier n z hz * F) := by
          rw [hG, add_mul, one_mul, smul_mul_assoc]
      _ = 1 := by
          rw [h1, hF]
          module
  have hFG : F * G = 1 := by
    calc F * G = G + (z - z₀) • (complementaryMultiplier n z₀ hz₀ * G) := by
          rw [hF, add_mul, one_mul, smul_mul_assoc]
      _ = 1 := by
          rw [h2, hG]
          module
  exact ⟨⟨F, G, hFG, hGF⟩, rfl⟩

theorem abc_eq_reduced (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) :
    abc φ n z = (reducedA φ n z hz, reducedB φ n z hz, reducedC φ n z hz) := by
  unfold abc
  exact localABC_agrees φ n (center n) z (center_mem_strip n) hz
    (isUnit_free_of_strips n (center n) z (center_mem_strip n) hz)

/-! ### Section A: Cauchy-Schwarz for coefficient sums -/

theorem tsum_mul_cs (u : ℤ → ℂ) (g : ℤ → ℝ) (hg : Summable g) (hu : ∀ m, ‖u m‖ ^ 2 ≤ g m)
    (x : lp (fun _ : ℤ => ℂ) 2) :
    ‖∑' m : ℤ, u m * x m‖ ≤ Real.sqrt (∑' m, g m) * ‖x‖ := by
  have hsum : Summable (fun m => ‖u m‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun m => sq_nonneg _) hu hg
  let U : lp (fun _ : ℤ => ℂ) 2 := ⟨fun m => star (u m), memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, norm_star] using hsum)⟩
  have hinner : inner ℂ U x = ∑' m : ℤ, u m * x m := by
    rw [lp.inner_eq_tsum]
    refine tsum_congr (fun m => ?_)
    simp [U, RCLike.inner_apply, mul_comm]
  have hU : ‖U‖ ^ 2 ≤ ∑' m, g m := by
    have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) U
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
    rw [← h.tsum_eq]
    refine Summable.tsum_le_tsum (fun m => ?_) h.summable hg
    simpa [U] using hu m
  have hU' : ‖U‖ ≤ Real.sqrt (∑' m, g m) := by
    have := Real.abs_le_sqrt hU
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  rw [← hinner]
  calc ‖inner ℂ U x‖ ≤ ‖U‖ * ‖x‖ := norm_inner_le_norm U x
    _ ≤ Real.sqrt (∑' m, g m) * ‖x‖ := by gcongr

/-! ### Section B: component norms -/

theorem lpC_hasSum_sq (x : lp (fun _ : ℤ => ℂ) 2) :
    HasSum (fun k : ℤ => ‖x k‖ ^ 2) (‖x‖ ^ 2) := by
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) x
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

theorem lpR_hasSum_sq (x : lp (fun _ : ℤ => ℝ) 2) :
    HasSum (fun k : ℤ => ‖x k‖ ^ 2) (‖x‖ ^ 2) := by
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) x
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

theorem comp_norm_le_A (φ : Potential) (b : Bool) : ‖φ b‖ ≤ ‖majorantSequence φ‖ := by
  have h1 : HasSum (fun k : ℤ => ‖potentialCoeff φ b k‖ ^ 2) (‖φ b‖ ^ 2) := by
    have h := lpC_hasSum_sq ((fourierBasis (T := (2 : ℝ))).repr (naturalPhysicalCoverL2 (φ b)))
    have e : ‖(fourierBasis (T := (2 : ℝ))).repr (naturalPhysicalCoverL2 (φ b))‖ = ‖φ b‖ := by
      exact ((fourierBasis (T := (2 : ℝ))).repr.norm_map _).trans (naturalPhysicalCoverL2_norm _)
    rw [e] at h
    convert h using 2
    simp only [potentialCoeff]
    exact congrArg (fun t => ‖t‖ ^ 2) (fc_repr _ _)
  have h2 : HasSum (fun k : ℤ => (majorantCoeff φ k) ^ 2) (‖majorantSequence φ‖ ^ 2) := by
    have h := lpR_hasSum_sq (majorantSequence φ)
    convert h using 2
    simp [majorantSequence_apply, Real.norm_eq_abs, abs_of_nonneg (majorant_nonneg φ _)]
  have h3 : ‖φ b‖ ^ 2 ≤ ‖majorantSequence φ‖ ^ 2 :=
    hasSum_le (fun k => pow_le_pow_left₀ (norm_nonneg _) (potentialCoeff_norm_le_majorant φ b k) 2) h1 h2
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h3

/-! ### Section C: the first-order coefficient bound -/

def gDen (φ : Potential) (n : ℤ) (k : ℤ) : ℝ :=
  if k = n then 0 else majorantCoeff φ (n + k) ^ 2 / (((n - k : ℤ) : ℝ)) ^ 2

theorem natAbs_sq_eq (d : ℤ) : ((Int.natAbs d : ℕ) : ℝ) ^ 2 = ((d : ℤ) : ℝ) ^ 2 := by
  rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]

theorem majorant_sq_summable' (φ : Potential) : Summable (fun k : ℤ => majorantCoeff φ k ^ 2) := by
  have h := lpR_hasSum_sq (majorantSequence φ)
  refine h.summable.congr (fun k => ?_)
  simp [majorantSequence_apply, Real.norm_eq_abs, abs_of_nonneg (majorant_nonneg φ _)]

theorem gDen_summable (φ : Potential) (n : ℤ) : Summable (gDen φ n) := by
  have hs : Summable (fun k : ℤ => majorantCoeff φ (n + k) ^ 2) :=
    (majorant_sq_summable' φ).comp_injective (add_right_injective n)
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hs
  · unfold gDen; split_ifs <;> positivity
  · unfold gDen
    split_ifs with h
    · positivity
    · have h1 : (1 : ℝ) ≤ ((n - k : ℤ) : ℝ) ^ 2 := by
        have : (1 : ℤ) ≤ |n - k| := Int.one_le_abs (sub_ne_zero.mpr (Ne.symm h))
        have h2 : (1 : ℝ) ≤ |((n - k : ℤ) : ℝ)| := by exact_mod_cast this
        nlinarith [sq_abs ((n - k : ℤ) : ℝ), abs_nonneg ((n - k : ℤ) : ℝ)]
      exact div_le_self (sq_nonneg _) h1

theorem gDen_tsum_le (φ : Potential) (n : ℤ) (hn : n ≠ 0) :
    ∑' k, gDen φ n k ≤
      (∑' j : ℤ, if n.natAbs ≤ j.natAbs then majorantSequence φ j ^ 2 else (0 : ℝ)) +
        ‖majorantSequence φ‖ ^ 2 / (n : ℝ) ^ 2 := by
  have h := NlsGge.Atomic.KST.coefficient_denominator_sum_le (majorantSequence φ) n hn
    (fun k => majorant_nonneg φ k) (fun k => majorant_even φ k)
  simpa only [gDen, majorantSequence_apply] using h

theorem frame_inner_q_le (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n)
    (b : Bool) (y : H) :
    ‖inner ℂ (frame n b : H) (qOperator φ n z hz y)‖ ≤
      Real.sqrt (∑' k, gDen φ n k) * ‖y (!b)‖ := by
  have hrepr : ∀ g : SpectralScalarL2, ‖(fourierBasis (T := (2 : ℝ))).repr g‖ = ‖g‖ :=
    fun g => LinearIsometryEquiv.norm_map _ g
  cases b
  · -- lower frame: coefficient (q y)_false at n
    have h1 : inner ℂ (frame n false : H) (qOperator φ n z hz y) =
        ∑' m : ℤ, (fourierCoeff (naturalPhysicalCoverL2 (φ false)) (n - m) *
          complementaryResolventCoeff n z (-m)) *
            (fourierBasis (T := (2 : ℝ))).repr (y true) m := by
      rw [frame_coe]
      simp only [kstPnFrame, Bool.false_eq_true, if_false]
      unfold kstPnLower
      rw [inner_single_left, ← spectralBasis_repr_inner, qOperator_lower_coeff]
      exact tsum_congr (fun m => by ring)
    rw [h1]
    have hg : Summable (fun m : ℤ => gDen φ n (-m)) :=
      (gDen_summable φ n).comp_injective neg_injective
    have := tsum_mul_cs (fun m : ℤ => fourierCoeff (naturalPhysicalCoverL2 (φ false)) (n - m) *
          complementaryResolventCoeff n z (-m)) (fun m => gDen φ n (-m)) hg ?_
      ((fourierBasis (T := (2 : ℝ))).repr (y true))
    · have e : ∑' m : ℤ, gDen φ n (-m) = ∑' k, gDen φ n k :=
        (Equiv.neg ℤ).tsum_eq (gDen φ n)
      rw [e, hrepr] at this
      simpa using this
    · intro m
      by_cases hm : -m = n
      · have : complementaryResolventCoeff n z (-m) = 0 := by rw [hm]; simp
        simp [this, gDen, hm]
      · have hc := complementaryResolventCoeff_bound n (-m) z hz
        have hf : ‖fourierCoeff (naturalPhysicalCoverL2 (φ false)) (n - m)‖ ≤
            majorantCoeff φ (n + -m) := by
          have := potentialCoeff_norm_le_majorant φ false (n - m)
          simpa [potentialCoeff, sub_eq_add_neg] using this
        have hd : (1 : ℝ) ≤ (Int.natAbs (-m - n) : ℝ) := by
          have : 0 < Int.natAbs (-m - n) := Int.natAbs_pos.mpr (sub_ne_zero.mpr hm)
          exact_mod_cast this
        rw [norm_mul, mul_pow]
        have h2 : ‖complementaryResolventCoeff n z (-m)‖ ^ 2 ≤ (1 / (Int.natAbs (-m - n) : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hc 2
        have h3 : ‖fourierCoeff (naturalPhysicalCoverL2 (φ false)) (n - m)‖ ^ 2 ≤
            majorantCoeff φ (n + -m) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hf 2
        have e : gDen φ n (-m) = majorantCoeff φ (n + -m) ^ 2 / (Int.natAbs (-m - n) : ℝ) ^ 2 := by
          simp only [gDen, hm, if_false]
          rw [natAbs_sq_eq]
          congr 1
          push_cast
          ring
        rw [one_div_pow] at h2
        rw [e, div_eq_mul_one_div]
        exact mul_le_mul h3 h2 (sq_nonneg _) (sq_nonneg _)
  · -- upper frame: coefficient (q y)_true at -n
    have h1 : inner ℂ (frame n true : H) (qOperator φ n z hz y) =
        ∑' m : ℤ, (fourierCoeff (naturalPhysicalCoverL2 (φ true)) (-n - m) *
          complementaryResolventCoeff n z m) *
            (fourierBasis (T := (2 : ℝ))).repr (y false) m := by
      rw [frame_coe]
      simp only [kstPnFrame, if_true]
      unfold kstPnUpper
      rw [inner_single_left, ← spectralBasis_repr_inner, qOperator_upper_coeff]
      exact tsum_congr (fun m => by ring)
    rw [h1]
    have := tsum_mul_cs (fun m : ℤ => fourierCoeff (naturalPhysicalCoverL2 (φ true)) (-n - m) *
          complementaryResolventCoeff n z m) (fun m => gDen φ n m) (gDen_summable φ n) ?_
      ((fourierBasis (T := (2 : ℝ))).repr (y false))
    · rw [hrepr] at this
      simpa using this
    · intro m
      by_cases hm : m = n
      · have : complementaryResolventCoeff n z m = 0 := by rw [hm]; simp
        simp [this, gDen, hm]
      · have hc := complementaryResolventCoeff_bound n m z hz
        have hf : ‖fourierCoeff (naturalPhysicalCoverL2 (φ true)) (-n - m)‖ ≤
            majorantCoeff φ (n + m) := by
          have h0 := potentialCoeff_norm_le_majorant φ true (-n - m)
          have h5 : majorantCoeff φ (-n - m) = majorantCoeff φ (n + m) := by
            have := majorant_even φ (n + m)
            rw [← this]; congr 1; ring
          simpa [potentialCoeff, h5] using h0
        rw [norm_mul, mul_pow]
        have h2 : ‖complementaryResolventCoeff n z m‖ ^ 2 ≤ (1 / (Int.natAbs (m - n) : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hc 2
        have h3 : ‖fourierCoeff (naturalPhysicalCoverL2 (φ true)) (-n - m)‖ ^ 2 ≤
            majorantCoeff φ (n + m) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hf 2
        have e : gDen φ n m = majorantCoeff φ (n + m) ^ 2 / (Int.natAbs (m - n) : ℝ) ^ 2 := by
          simp only [gDen, hm, if_false]
          rw [natAbs_sq_eq]
          congr 1
          push_cast
          ring
        rw [one_div_pow] at h2
        rw [e, div_eq_mul_one_div]
        exact mul_le_mul h3 h2 (sq_nonneg _) (sq_nonneg _)

/-! ### Section D: components of q and of the potential vectors -/

theorem norm_pair_sq {E : Type*} [NormedAddCommGroup E] (f : PiLp 2 (fun _ : Bool => E)) :
    ‖f‖ ^ 2 = ‖f true‖ ^ 2 + ‖f false‖ ^ 2 := by
  have h := PiLp.norm_sq_eq_of_L2 (fun _ : Bool => E) f
  simpa only [Fintype.sum_bool] using h

theorem q_comp_le (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) (c : Bool) (u : H) :
    ‖(qOperator φ n z hz u) c‖ ≤ 2 * ‖φ c‖ * ‖u (!c)‖ := by
  let ψ : Potential := WithLp.toLp 2 (fun b : Bool => if b = c then φ b else 0)
  let u' : H := WithLp.toLp 2 (fun b : Bool => if b = !c then u b else 0)
  have hψ : ‖ψ‖ = ‖φ c‖ := by
    have h := norm_pair_sq ψ
    cases c
    · have h2 : ‖ψ‖ ^ 2 = ‖φ false‖ ^ 2 := by simpa [ψ] using h
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2
    · have h2 : ‖ψ‖ ^ 2 = ‖φ true‖ ^ 2 := by simpa [ψ] using h
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2
  have hu' : ‖u'‖ = ‖u (!c)‖ := by
    have h := norm_pair_sq u'
    cases c
    · have h2 : ‖u'‖ ^ 2 = ‖u true‖ ^ 2 := by simpa [u'] using h
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2
    · have h2 : ‖u'‖ ^ 2 = ‖u false‖ ^ 2 := by simpa [u'] using h
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2
  have hcomp : (qOperator ψ n z hz u') c = (qOperator φ n z hz u) c := by
    apply (fourierBasis (T := (2 : ℝ))).repr.injective
    apply lp.ext
    funext l
    cases c
    · rw [qOperator_lower_coeff, qOperator_lower_coeff]
      simp [ψ, u']
    · rw [qOperator_upper_coeff, qOperator_upper_coeff]
      simp [ψ, u']
  calc ‖(qOperator φ n z hz u) c‖ = ‖(qOperator ψ n z hz u') c‖ := by rw [hcomp]
    _ ≤ ‖qOperator ψ n z hz u'‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖qOperator ψ n z hz‖ * ‖u'‖ := (qOperator ψ n z hz).le_opNorm _
    _ ≤ (2 * ‖ψ‖) * ‖u'‖ := by gcongr; exact norm_qOperator_le ψ n z hz
    _ = 2 * ‖φ c‖ * ‖u (!c)‖ := by rw [hψ, hu']

theorem phi_frame_false (φ : Potential) (n : ℤ) :
    potentialOnPn φ n (frame n false : H) =
      (PiLp.single 2 true (NlsGge.Schur.fourierMultiplier n
        (naturalPhysicalCoverL2 (φ true))) : H) := by
  rw [pot_apply, frame_coe]
  have h := orthonormal_iff_ite.mp (kstPnFrame_orthonormal n)
  have hll : inner ℂ (kstPnLower n) (kstPnLower n) = 1 := by simpa [kstPnFrame] using h false false
  have hul : inner ℂ (kstPnUpper n) (kstPnLower n) = 0 := by simpa [kstPnFrame] using h true false
  simp only [kstPnFrame, Bool.false_eq_true, if_false, hll, hul, one_smul, zero_smul, add_zero]

theorem phi_frame_true (φ : Potential) (n : ℤ) :
    potentialOnPn φ n (frame n true : H) =
      (PiLp.single 2 false (NlsGge.Schur.fourierMultiplier (-n)
        (naturalPhysicalCoverL2 (φ false))) : H) := by
  rw [pot_apply, frame_coe]
  have h := orthonormal_iff_ite.mp (kstPnFrame_orthonormal n)
  have huu : inner ℂ (kstPnUpper n) (kstPnUpper n) = 1 := by simpa [kstPnFrame] using h true true
  have hlu : inner ℂ (kstPnLower n) (kstPnUpper n) = 0 := by simpa [kstPnFrame] using h false true
  simp only [kstPnFrame, if_true, huu, hlu, one_smul, zero_smul, zero_add]

theorem phi_frame_false_norm (φ : Potential) (n : ℤ) :
    ‖potentialOnPn φ n (frame n false : H)‖ ≤ ‖majorantSequence φ‖ := by
  rw [phi_frame_false, PiLp.norm_single, NlsGge.Schur.fourierMultiplier_norm_apply,
    naturalPhysicalCoverL2_norm]
  exact comp_norm_le_A φ true

theorem phi_frame_true_norm (φ : Potential) (n : ℤ) :
    ‖potentialOnPn φ n (frame n true : H)‖ ≤ ‖majorantSequence φ‖ := by
  rw [phi_frame_true, PiLp.norm_single, NlsGge.Schur.fourierMultiplier_norm_apply,
    naturalPhysicalCoverL2_norm]
  exact comp_norm_le_A φ false

theorem phi_frame_false_channel (φ : Potential) (n : ℤ) :
    InChannel true (potentialOnPn φ n (frame n false : H)) := by
  have := potentialOnPn_flips φ n false _ (frame_inChannel n false)
  simpa using this

theorem phi_frame_true_channel (φ : Potential) (n : ℤ) :
    InChannel false (potentialOnPn φ n (frame n true : H)) := by
  have := potentialOnPn_flips φ n true _ (frame_inChannel n true)
  simpa using this

/-! ### Section E: the operator S = (1 - q^2)^{-1} -/

def Sinv (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) : EndH :=
  Ring.inverse (1 - qOperator φ n z hz ^ 2)

theorem Sinv_hasSum (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n)
    (hq : ‖qOperator φ n z hz ^ 2‖ < 1) :
    HasSum (fun k : ℕ => (qOperator φ n z hz ^ 2) ^ k) (Sinv φ n z hz) :=
  hasSum_geom_series_inverse _ hq

theorem Sinv_norm (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n)
    (hq : ‖qOperator φ n z hz ^ 2‖ ≤ 1 / 2) : ‖Sinv φ n z hz‖ ≤ 2 := by
  have hlt : ‖qOperator φ n z hz ^ 2‖ < 1 := lt_of_le_of_lt hq (by norm_num)
  have hs := Sinv_hasSum φ n z hz hlt
  have hg : HasSum (fun k : ℕ => (1 / 2 : ℝ) ^ k) 2 := by
    have := hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    convert this using 1
    norm_num
  refine hs.norm_le_of_bounded hg (fun k => ?_)
  have hpow : ‖(qOperator φ n z hz ^ 2) ^ k‖ ≤ ‖qOperator φ n z hz ^ 2‖ ^ k := by
    cases k with
    | zero => rw [pow_zero, pow_zero]; exact ContinuousLinearMap.norm_id_le
    | succ k => exact norm_pow_le' _ (Nat.succ_pos k)
  exact hpow.trans (pow_le_pow_left₀ (norm_nonneg _) hq k)

theorem Sinv_apply_norm (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n)
    (hq : ‖qOperator φ n z hz ^ 2‖ ≤ 1 / 2) (w : H) : ‖Sinv φ n z hz w‖ ≤ 2 * ‖w‖ :=
  calc ‖Sinv φ n z hz w‖ ≤ ‖Sinv φ n z hz‖ * ‖w‖ := (Sinv φ n z hz).le_opNorm _
    _ ≤ 2 * ‖w‖ := by gcongr; exact Sinv_norm φ n z hz hq

theorem Sinv_channel (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n)
    (hq : ‖qOperator φ n z hz ^ 2‖ < 1) (s : Bool) (w : H) (hw : InChannel s w) :
    InChannel s (Sinv φ n z hz w) := by
  intro c hc
  have hs := Sinv_hasSum φ n z hz hq
  let L : EndH →L[ℂ] SpectralScalarL2 :=
    (PiLp.proj 2 (fun _ : Bool => SpectralScalarL2) c).comp
      (ContinuousLinearMap.apply ℂ H w)
  have h1 := hs.mapL L
  have h2 : ∀ k : ℕ, L ((qOperator φ n z hz ^ 2) ^ k) = 0 := by
    intro k
    have := qOperator_pow_even φ n z hz k s w hw
    rw [pow_mul] at this
    exact this c hc
  have h3 : HasSum (fun k : ℕ => L ((qOperator φ n z hz ^ 2) ^ k)) 0 := by
    simp only [h2]
    exact hasSum_zero
  exact h1.unique h3

theorem Sinv_eq (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n)
    (hq : ‖qOperator φ n z hz ^ 2‖ < 1) (w : H) :
    Sinv φ n z hz w = w + qOperator φ n z hz (qOperator φ n z hz (Sinv φ n z hz w)) := by
  have hu : IsUnit (1 - qOperator φ n z hz ^ 2) := (Units.oneSub _ hq).isUnit
  have h := Ring.mul_inverse_cancel _ hu
  have h' : Sinv φ n z hz w - qOperator φ n z hz (qOperator φ n z hz (Sinv φ n z hz w)) = w := by
    have := congrArg (fun T : EndH => T w) h
    simpa [Sinv, pow_two, ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply] using this
  exact sub_eq_iff_eq_add.mp h'

theorem R_apply (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n)
    (hq : ‖qOperator φ n z hz ^ 2‖ < 1) (w : H) :
    Ring.inverse (1 - qOperator φ n z hz) w =
      Sinv φ n z hz w + qOperator φ n z hz (Sinv φ n z hz w) := by
  obtain ⟨_, hform, -, -⟩ := NlsGge.Atomic.KST012.inverse_one_sub_of_sq_norm_lt (qOperator φ n z hz) hq
  rw [hform]
  simp [Sinv, add_mul, ContinuousLinearMap.add_apply]

theorem reduced_inner_eq (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) (i j : Bool) :
    inner ℂ (frame n i : H) (correction φ n z hz (frame n j : H)) =
      inner ℂ (frame n i : H)
        (Ring.inverse (1 - qOperator φ n z hz) (potentialOnPn φ n (frame n j : H))) := by
  change inner ℂ (frame n i : H) (spectralPn n
    (Ring.inverse (1 - qOperator φ n z hz) (potentialOnPn φ n (frame n j : H)))) = _
  rw [frame_coe, inner_frame_Pn]


/-! ### Section F: the three coefficient bounds -/

theorem reducedA_bound (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n)
    (hq : ‖qOperator φ n z hz ^ 2‖ ≤ 1 / 2) :
    ‖reducedA φ n z hz‖ ≤ 2 * ‖majorantSequence φ‖ * Real.sqrt (∑' k, gDen φ n k) := by
  have hlt : ‖qOperator φ n z hz ^ 2‖ < 1 := lt_of_le_of_lt hq (by norm_num)
  set w : H := potentialOnPn φ n (frame n false : H) with hw
  have hA := (entries_correction φ n z hz).1
  have h0 : inner ℂ (frame n false : H) (Sinv φ n z hz w) = 0 := by
    apply inner_frame_of_channel
    simpa using Sinv_channel φ n z hz hlt true w (phi_frame_false_channel φ n)
  have hmain : reducedA φ n z hz =
      inner ℂ (frame n false : H) (qOperator φ n z hz (Sinv φ n z hz w)) := by
    rw [hA, reduced_inner_eq, R_apply φ n z hz hlt, inner_add_right, h0, zero_add]
  rw [hmain]
  have h1 := frame_inner_q_le φ n z hz false (Sinv φ n z hz w)
  have h2 : ‖(Sinv φ n z hz w) (!false)‖ ≤ ‖Sinv φ n z hz w‖ := PiLp.norm_apply_le _ _
  have h3 := Sinv_apply_norm φ n z hz hq w
  have h4 := phi_frame_false_norm φ n
  have hρ : 0 ≤ Real.sqrt (∑' k, gDen φ n k) := Real.sqrt_nonneg _
  have h5 : ‖(Sinv φ n z hz w) (!false)‖ ≤ 2 * ‖majorantSequence φ‖ :=
    h2.trans (h3.trans (by gcongr))
  calc ‖inner ℂ (frame n false : H) (qOperator φ n z hz (Sinv φ n z hz w))‖
      ≤ Real.sqrt (∑' k, gDen φ n k) * ‖(Sinv φ n z hz w) (!false)‖ := h1
    _ ≤ Real.sqrt (∑' k, gDen φ n k) * (2 * ‖majorantSequence φ‖) := by gcongr
    _ = _ := by ring

theorem reducedB_bound (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n)
    (hq : ‖qOperator φ n z hz ^ 2‖ ≤ 1 / 2) :
    ‖reducedB φ n z hz - coveredCoeff φ false (2 * n)‖ ≤
      4 * ‖majorantSequence φ‖ ^ 2 * Real.sqrt (∑' k, gDen φ n k) := by
  have hlt : ‖qOperator φ n z hz ^ 2‖ < 1 := lt_of_le_of_lt hq (by norm_num)
  set w : H := potentialOnPn φ n (frame n true : H) with hw
  have hB := (entries_correction φ n z hz).2.1
  have hz0 := (zeroth_offDiagonal_path φ n z hz).1
  have hz0' : inner ℂ (frame n false : H) w = coveredCoeff φ false (2 * n) := by
    simpa [pathTerm, hw] using hz0
  have hwch : InChannel false w := phi_frame_true_channel φ n
  have hSch : InChannel false (Sinv φ n z hz w) := Sinv_channel φ n z hz hlt false w hwch
  have hqS : InChannel true (qOperator φ n z hz (Sinv φ n z hz w)) := by
    simpa using qOperator_flips φ n z hz false _ hSch
  have h0 : inner ℂ (frame n false : H) (qOperator φ n z hz (Sinv φ n z hz w)) = 0 :=
    inner_frame_of_channel n false _ (by simpa using hqS)
  have key : inner ℂ (frame n false : H) (Sinv φ n z hz w) =
      coveredCoeff φ false (2 * n) + inner ℂ (frame n false : H)
        (qOperator φ n z hz (qOperator φ n z hz (Sinv φ n z hz w))) := by
    have := congrArg (inner ℂ (frame n false : H)) (Sinv_eq φ n z hz hlt w)
    rw [inner_add_right, hz0'] at this
    exact this
  have hmain : reducedB φ n z hz - coveredCoeff φ false (2 * n) =
      inner ℂ (frame n false : H) (qOperator φ n z hz
        (qOperator φ n z hz (Sinv φ n z hz w))) := by
    rw [hB, reduced_inner_eq, R_apply φ n z hz hlt, inner_add_right, h0, add_zero, key]
    ring
  rw [hmain]
  have h1 := frame_inner_q_le φ n z hz false (qOperator φ n z hz (Sinv φ n z hz w))
  have h2 := q_comp_le φ n z hz true (Sinv φ n z hz w)
  have h3 : ‖(Sinv φ n z hz w) (!true)‖ ≤ ‖Sinv φ n z hz w‖ := PiLp.norm_apply_le _ _
  have h4 := Sinv_apply_norm φ n z hz hq w
  have h5 := phi_frame_true_norm φ n
  have h6 := comp_norm_le_A φ true
  have hA0 : 0 ≤ ‖majorantSequence φ‖ := norm_nonneg _
  have hρ : 0 ≤ Real.sqrt (∑' k, gDen φ n k) := Real.sqrt_nonneg _
  have h7 : ‖(Sinv φ n z hz w) (!true)‖ ≤ 2 * ‖majorantSequence φ‖ :=
    h3.trans (h4.trans (by gcongr))
  have h8 : ‖(qOperator φ n z hz (Sinv φ n z hz w)) true‖ ≤ 4 * ‖majorantSequence φ‖ ^ 2 := by
    calc ‖(qOperator φ n z hz (Sinv φ n z hz w)) true‖
        ≤ 2 * ‖φ true‖ * ‖(Sinv φ n z hz w) (!true)‖ := h2
      _ ≤ 2 * ‖majorantSequence φ‖ * (2 * ‖majorantSequence φ‖) := by gcongr
      _ = 4 * ‖majorantSequence φ‖ ^ 2 := by ring
  calc ‖inner ℂ (frame n false : H) (qOperator φ n z hz (qOperator φ n z hz (Sinv φ n z hz w)))‖
      ≤ Real.sqrt (∑' k, gDen φ n k) *
          ‖(qOperator φ n z hz (Sinv φ n z hz w)) (!false)‖ := h1
    _ ≤ Real.sqrt (∑' k, gDen φ n k) * (4 * ‖majorantSequence φ‖ ^ 2) := by
        gcongr
        simpa using h8
    _ = _ := by ring

theorem reducedC_bound (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n)
    (hq : ‖qOperator φ n z hz ^ 2‖ ≤ 1 / 2) :
    ‖reducedC φ n z hz - coveredCoeff φ true (-2 * n)‖ ≤
      4 * ‖majorantSequence φ‖ ^ 2 * Real.sqrt (∑' k, gDen φ n k) := by
  have hlt : ‖qOperator φ n z hz ^ 2‖ < 1 := lt_of_le_of_lt hq (by norm_num)
  set w : H := potentialOnPn φ n (frame n false : H) with hw
  have hC := (entries_correction φ n z hz).2.2
  have hz0 := (zeroth_offDiagonal_path φ n z hz).2
  have hz0' : inner ℂ (frame n true : H) w = coveredCoeff φ true (-2 * n) := by
    simpa [pathTerm, hw] using hz0
  have hwch : InChannel true w := phi_frame_false_channel φ n
  have hSch : InChannel true (Sinv φ n z hz w) := Sinv_channel φ n z hz hlt true w hwch
  have hqS : InChannel false (qOperator φ n z hz (Sinv φ n z hz w)) := by
    simpa using qOperator_flips φ n z hz true _ hSch
  have h0 : inner ℂ (frame n true : H) (qOperator φ n z hz (Sinv φ n z hz w)) = 0 :=
    inner_frame_of_channel n true _ (by simpa using hqS)
  have key : inner ℂ (frame n true : H) (Sinv φ n z hz w) =
      coveredCoeff φ true (-2 * n) + inner ℂ (frame n true : H)
        (qOperator φ n z hz (qOperator φ n z hz (Sinv φ n z hz w))) := by
    have := congrArg (inner ℂ (frame n true : H)) (Sinv_eq φ n z hz hlt w)
    rw [inner_add_right, hz0'] at this
    exact this
  have hmain : reducedC φ n z hz - coveredCoeff φ true (-2 * n) =
      inner ℂ (frame n true : H) (qOperator φ n z hz
        (qOperator φ n z hz (Sinv φ n z hz w))) := by
    rw [hC, reduced_inner_eq, R_apply φ n z hz hlt, inner_add_right, h0, add_zero, key]
    ring
  rw [hmain]
  have h1 := frame_inner_q_le φ n z hz true (qOperator φ n z hz (Sinv φ n z hz w))
  have h2 := q_comp_le φ n z hz false (Sinv φ n z hz w)
  have h3 : ‖(Sinv φ n z hz w) (!false)‖ ≤ ‖Sinv φ n z hz w‖ := PiLp.norm_apply_le _ _
  have h4 := Sinv_apply_norm φ n z hz hq w
  have h5 := phi_frame_false_norm φ n
  have h6 := comp_norm_le_A φ false
  have hA0 : 0 ≤ ‖majorantSequence φ‖ := norm_nonneg _
  have hρ : 0 ≤ Real.sqrt (∑' k, gDen φ n k) := Real.sqrt_nonneg _
  have h7 : ‖(Sinv φ n z hz w) (!false)‖ ≤ 2 * ‖majorantSequence φ‖ :=
    h3.trans (h4.trans (by gcongr))
  have h8 : ‖(qOperator φ n z hz (Sinv φ n z hz w)) false‖ ≤ 4 * ‖majorantSequence φ‖ ^ 2 := by
    calc ‖(qOperator φ n z hz (Sinv φ n z hz w)) false‖
        ≤ 2 * ‖φ false‖ * ‖(Sinv φ n z hz w) (!false)‖ := h2
      _ ≤ 2 * ‖majorantSequence φ‖ * (2 * ‖majorantSequence φ‖) := by gcongr
      _ = 4 * ‖majorantSequence φ‖ ^ 2 := by ring
  calc ‖inner ℂ (frame n true : H) (qOperator φ n z hz (qOperator φ n z hz (Sinv φ n z hz w)))‖
      ≤ Real.sqrt (∑' k, gDen φ n k) *
          ‖(qOperator φ n z hz (Sinv φ n z hz w)) (!true)‖ := h1
    _ ≤ Real.sqrt (∑' k, gDen φ n k) * (4 * ‖majorantSequence φ‖ ^ 2) := by
        gcongr
        simpa using h8
    _ = _ := by ring


/-! ### Section G: source scalar norms and the final statement -/

def scalarEnergy (w A : ℤ → ℝ) : ℝ≥0∞ :=
  ∑' j : ℤ, ENNReal.ofReal (w j ^ 2 * A j ^ 2)

def scalarTailEnergy (w A : ℤ → ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∑' j : ℤ, if N ≤ j.natAbs then
    ENNReal.ofReal (w j ^ 2 * A j ^ 2) else 0

def sourceScalarNorm (A : ℤ → ℝ) : ℝ :=
  Real.sqrt (scalarEnergy (fun _ => 1) A).toReal

def sourceScalarTailNorm (A : ℤ → ℝ) (N : ℕ) : ℝ :=
  Real.sqrt (scalarTailEnergy (fun _ => 1) A N).toReal

def tailSum (φ : Potential) (N : ℕ) : ℝ :=
  ∑' j : ℤ, if N ≤ j.natAbs then majorantCoeff φ j ^ 2 else 0

theorem tailTerm_summable (φ : Potential) (N : ℕ) :
    Summable (fun j : ℤ => if N ≤ j.natAbs then majorantCoeff φ j ^ 2 else 0) := by
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) (majorant_sq_summable' φ)
  · split_ifs <;> positivity
  · split_ifs <;> first | exact le_rfl | positivity

theorem tailSum_nonneg (φ : Potential) (N : ℕ) : 0 ≤ tailSum φ N :=
  tsum_nonneg (fun j => by split_ifs <;> positivity)

theorem sourceScalarNorm_eq (φ : Potential) :
    sourceScalarNorm (majorantCoeff φ) = ‖majorantSequence φ‖ := by
  have hs := majorant_sq_summable' φ
  have h1 : (scalarEnergy (fun _ => 1) (majorantCoeff φ)).toReal =
      ∑' j : ℤ, majorantCoeff φ j ^ 2 := by
    unfold scalarEnergy
    have := ENNReal.ofReal_tsum_of_nonneg (f := fun j : ℤ => (1 : ℝ) ^ 2 * majorantCoeff φ j ^ 2)
      (fun j => by positivity) (by simpa using hs)
    rw [← this, ENNReal.toReal_ofReal (tsum_nonneg (fun j => by positivity))]
    simp
  have h2 : ∑' j : ℤ, majorantCoeff φ j ^ 2 = ‖majorantSequence φ‖ ^ 2 := by
    have h := (lpR_hasSum_sq (majorantSequence φ)).tsum_eq
    rw [← h]
    exact tsum_congr (fun k => by
      simp [majorantSequence_apply, Real.norm_eq_abs, abs_of_nonneg (majorant_nonneg φ _)])
  unfold sourceScalarNorm
  rw [h1, h2, Real.sqrt_sq (norm_nonneg _)]

theorem sourceScalarTailNorm_eq (φ : Potential) (N : ℕ) :
    sourceScalarTailNorm (majorantCoeff φ) N = Real.sqrt (tailSum φ N) := by
  have hs := tailTerm_summable φ N
  unfold sourceScalarTailNorm scalarTailEnergy tailSum
  congr 1
  have e : ∀ j : ℤ, (if N ≤ j.natAbs then ENNReal.ofReal ((1 : ℝ) ^ 2 * majorantCoeff φ j ^ 2)
      else 0) = ENNReal.ofReal (if N ≤ j.natAbs then majorantCoeff φ j ^ 2 else 0) := by
    intro j
    split_ifs <;> simp
  simp only [e]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by split_ifs <;> positivity) hs,
    ENNReal.toReal_ofReal (tsum_nonneg (fun j => by split_ifs <;> positivity))]

theorem tailSum_tendsto (φ : Potential) : Tendsto (fun N : ℕ => tailSum φ N) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence
    (𝓕 := (atTop : Filter ℕ))
    (f := fun (N : ℕ) (j : ℤ) => if N ≤ j.natAbs then majorantCoeff φ j ^ 2 else 0)
    (g := fun _ => (0 : ℝ)) (bound := fun j => majorantCoeff φ j ^ 2)
    (majorant_sq_summable' φ) ?_ ?_
  · simpa [tailSum] using h
  · intro j
    refine tendsto_atTop_of_eventually_const (i₀ := j.natAbs + 1) (fun N hN => ?_)
    have : ¬ N ≤ j.natAbs := by omega
    simp [this]
  · refine Eventually.of_forall (fun N j => ?_)
    split_ifs
    · simp
    · simp; positivity

theorem rho_le (φ : Potential) (n : ℤ) (hn : n ≠ 0) :
    Real.sqrt (∑' k, gDen φ n k) ≤
      ‖majorantSequence φ‖ / (n.natAbs : ℝ) + Real.sqrt (tailSum φ n.natAbs) := by
  have h1 := gDen_tsum_le φ n hn
  have hnabs : ((n : ℝ)) ^ 2 = (n.natAbs : ℝ) ^ 2 := by
    rw [natAbs_sq_eq]
  have hT : (∑' j : ℤ, if n.natAbs ≤ j.natAbs then majorantSequence φ j ^ 2 else (0 : ℝ)) =
      tailSum φ n.natAbs := by
    unfold tailSum
    exact tsum_congr (fun j => by simp [majorantSequence_apply])
  rw [hT, hnabs] at h1
  have hNpos : (0 : ℝ) < (n.natAbs : ℝ) := by
    have : 0 < n.natAbs := Int.natAbs_pos.mpr hn
    exact_mod_cast this
  have hs := norm_nonneg (majorantSequence φ)
  have hT0 := tailSum_nonneg φ n.natAbs
  set s := ‖majorantSequence φ‖
  set N : ℝ := (n.natAbs : ℝ)
  set T := tailSum φ n.natAbs
  have hy : 0 ≤ s / N + Real.sqrt T := by positivity
  refine Real.sqrt_le_iff.mpr ⟨hy, ?_⟩
  have h2 : (s / N + Real.sqrt T) ^ 2 = (s / N) ^ 2 + 2 * (s / N) * Real.sqrt T + T := by
    rw [add_sq, Real.sq_sqrt hT0]
  have h3 : 0 ≤ 2 * (s / N) * Real.sqrt T := by positivity
  have h4 : s ^ 2 / N ^ 2 = (s / N) ^ 2 := by rw [div_pow]
  rw [h2]
  linarith

theorem cov_le (φ : Potential) (n : ℤ) (b : Bool) (k : ℤ) (hk : n.natAbs ≤ k.natAbs) :
    ‖coveredCoeff φ b k‖ ≤ Real.sqrt (tailSum φ n.natAbs) := by
  have h1 : ‖coveredCoeff φ b k‖ ≤ majorantCoeff φ k := potentialCoeff_norm_le_majorant φ b k
  have h2 : majorantCoeff φ k ^ 2 ≤ tailSum φ n.natAbs := by
    have := (tailTerm_summable φ n.natAbs).le_tsum k (fun j _ => by split_ifs <;> positivity)
    rw [if_pos hk] at this
    exact this
  exact h1.trans (by
    have := Real.abs_le_sqrt h2
    rwa [abs_of_nonneg (majorant_nonneg φ k)] at this)

theorem kst018 (φ : Potential) :
  let A := majorantCoeff φ
  ∃ N₀ : ℕ, 5 ≤ N₀ ∧
    (∀ n : ℤ, N₀ ≤ n.natAbs → ∀ z : ℂ, z ∈ spectralStrip n →
      ‖a φ n z‖ ≤
        2 * sourceScalarNorm A *
          (sourceScalarNorm A / (n.natAbs : ℝ) + sourceScalarTailNorm A n.natAbs) ∧
      ‖b φ n z - coveredCoeff φ false (2*n)‖ ≤
        4 * sourceScalarNorm A ^ 2 *
          (sourceScalarNorm A / (n.natAbs : ℝ) + sourceScalarTailNorm A n.natAbs) ∧
      ‖c φ n z - coveredCoeff φ true (-2*n)‖ ≤
        4 * sourceScalarNorm A ^ 2 *
          (sourceScalarNorm A / (n.natAbs : ℝ) + sourceScalarTailNorm A n.natAbs)) ∧
    ∃ N₁ : ℕ, N₀ ≤ N₁ ∧ ∀ n : ℤ, N₁ ≤ n.natAbs →
      ∀ z : ℂ, z ∈ spectralStrip n →
        ‖a φ n z‖ ≤ Real.pi/48 ∧
        ‖b φ n z‖ ≤ Real.pi/48 ∧
        ‖c φ n z‖ ≤ Real.pi/48 := by
  dsimp only
  obtain ⟨ε, hε, N₀, hN₀, hloc⟩ := reducedBC_uniform_local φ
  have hq : ∀ n : ℤ, N₀ ≤ n.natAbs → ∀ (z : ℂ) (hz : z ∈ spectralStrip n),
      ‖qOperator φ n z hz ^ 2‖ ≤ 1 / 2 := fun n hn z hz =>
    (hloc φ (by simpa using hε) n hn z hz).1
  have hn0 : ∀ n : ℤ, N₀ ≤ n.natAbs → n ≠ 0 := by
    intro n hn h
    subst h
    simp at hn
    omega
  have hbound : ∀ n : ℤ, N₀ ≤ n.natAbs → ∀ z : ℂ, z ∈ spectralStrip n →
      ‖a φ n z‖ ≤ 2 * ‖majorantSequence φ‖ *
          (‖majorantSequence φ‖ / (n.natAbs : ℝ) + Real.sqrt (tailSum φ n.natAbs)) ∧
      ‖b φ n z - coveredCoeff φ false (2*n)‖ ≤ 4 * ‖majorantSequence φ‖ ^ 2 *
          (‖majorantSequence φ‖ / (n.natAbs : ℝ) + Real.sqrt (tailSum φ n.natAbs)) ∧
      ‖c φ n z - coveredCoeff φ true (-2*n)‖ ≤ 4 * ‖majorantSequence φ‖ ^ 2 *
          (‖majorantSequence φ‖ / (n.natAbs : ℝ) + Real.sqrt (tailSum φ n.natAbs)) := by
    intro n hn z hz
    have habc := abc_eq_reduced φ n z hz
    have ha : a φ n z = reducedA φ n z hz := by unfold a; rw [habc]
    have hb : b φ n z = reducedB φ n z hz := by unfold b; rw [habc]
    have hc : c φ n z = reducedC φ n z hz := by unfold c; rw [habc]
    have hρ := rho_le φ n (hn0 n hn)
    have hs := norm_nonneg (majorantSequence φ)
    rw [ha, hb, hc]
    refine ⟨(reducedA_bound φ n z hz (hq n hn z hz)).trans ?_,
      (reducedB_bound φ n z hz (hq n hn z hz)).trans ?_,
      (reducedC_bound φ n z hz (hq n hn z hz)).trans ?_⟩ <;> gcongr
  refine ⟨N₀, hN₀, ?_, ?_⟩
  · intro n hn z hz
    rw [sourceScalarNorm_eq, sourceScalarTailNorm_eq]
    exact hbound n hn z hz
  · set s := ‖majorantSequence φ‖ with hsdef
    have hs0 : 0 ≤ s := norm_nonneg _
    set K : ℝ := 2 * s + 1 + 4 * s ^ 2 with hK
    have hKpos : 0 < K := by positivity
    set δ : ℝ := Real.pi / (48 * K) with hδ
    have hδpos : 0 < δ := by positivity
    have ht : Tendsto (fun N : ℕ => Real.sqrt (tailSum φ N)) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp (tailSum_tendsto φ)
      rw [Real.sqrt_zero] at this
      exact this
    obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp
      (ht.eventually (gt_mem_nhds (show (0 : ℝ) < δ / 2 by positivity)))
    obtain ⟨N₃, hN₃⟩ := exists_nat_gt (2 * s / δ)
    refine ⟨max N₀ (max N₂ N₃), le_max_left _ _, ?_⟩
    intro n hn z hz
    have hn₀ : N₀ ≤ n.natAbs := le_trans (le_max_left _ _) hn
    have hn₂ : N₂ ≤ n.natAbs := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
    have hn₃ : N₃ ≤ n.natAbs := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
    obtain ⟨hA, hB, hC⟩ := hbound n hn₀ z hz
    have htail : Real.sqrt (tailSum φ n.natAbs) < δ / 2 := hN₂ _ hn₂
    have hNpos : (0 : ℝ) < (n.natAbs : ℝ) := by
      have : 0 < n.natAbs := Int.natAbs_pos.mpr (hn0 n hn₀)
      exact_mod_cast this
    have hsN : s / (n.natAbs : ℝ) ≤ δ / 2 := by
      rw [div_le_iff₀ hNpos]
      have h3 : (N₃ : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast hn₃
      have h4 : 2 * s / δ < (n.natAbs : ℝ) := lt_of_lt_of_le hN₃ h3
      rw [div_lt_iff₀ hδpos] at h4
      nlinarith
    have hρ : s / (n.natAbs : ℝ) + Real.sqrt (tailSum φ n.natAbs) ≤ δ := by linarith
    have hρ0 : 0 ≤ s / (n.natAbs : ℝ) + Real.sqrt (tailSum φ n.natAbs) := by positivity
    have hKδ : K * δ = Real.pi / 48 := by
      rw [hδ]; field_simp
    have hcb := cov_le φ n false (2 * n) (by omega)
    have hcc := cov_le φ n true (-2 * n) (by omega)
    have habc := abc_eq_reduced φ n z hz
    refine ⟨?_, ?_, ?_⟩
    · calc ‖a φ n z‖ ≤ 2 * s * (s / (n.natAbs : ℝ) + Real.sqrt (tailSum φ n.natAbs)) := hA
        _ ≤ K * δ := by
          have : 2 * s * (s / (n.natAbs : ℝ) + Real.sqrt (tailSum φ n.natAbs)) ≤ K * δ := by
            calc _ ≤ K * (s / (n.natAbs : ℝ) + Real.sqrt (tailSum φ n.natAbs)) := by
                  rw [hK]; nlinarith [sq_nonneg s]
              _ ≤ K * δ := by gcongr
          exact this
        _ = _ := hKδ
    · calc ‖b φ n z‖ = ‖(b φ n z - coveredCoeff φ false (2 * n)) + coveredCoeff φ false (2 * n)‖ := by
            congr 1; ring
        _ ≤ ‖b φ n z - coveredCoeff φ false (2 * n)‖ + ‖coveredCoeff φ false (2 * n)‖ := norm_add_le _ _
        _ ≤ 4 * s ^ 2 * δ + δ / 2 := by
            have h1 : 4 * s ^ 2 * (s / (n.natAbs : ℝ) + Real.sqrt (tailSum φ n.natAbs)) ≤ 4 * s ^ 2 * δ := by
              gcongr
            linarith
        _ ≤ K * δ := by rw [hK]; nlinarith [mul_pos hδpos hδpos, hδpos]
        _ = _ := hKδ
    · calc ‖c φ n z‖ = ‖(c φ n z - coveredCoeff φ true (-2 * n)) + coveredCoeff φ true (-2 * n)‖ := by
            congr 1; ring
        _ ≤ ‖c φ n z - coveredCoeff φ true (-2 * n)‖ + ‖coveredCoeff φ true (-2 * n)‖ := norm_add_le _ _
        _ ≤ 4 * s ^ 2 * δ + δ / 2 := by
            have h1 : 4 * s ^ 2 * (s / (n.natAbs : ℝ) + Real.sqrt (tailSum φ n.natAbs)) ≤ 4 * s ^ 2 * δ := by
              gcongr
            linarith
        _ ≤ K * δ := by rw [hK]; nlinarith [mul_pos hδpos hδpos, hδpos]
        _ = _ := hKδ

end NlsGge.ThirdConsultation.KST
