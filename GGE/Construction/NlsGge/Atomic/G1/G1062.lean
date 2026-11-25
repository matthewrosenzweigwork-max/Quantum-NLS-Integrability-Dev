import Mathlib
import NlsGge.Atomic.G1.G1061
import NlsGge.Atomic.G1.G1049
import NlsGge.Atomic.G1.G1021
import NlsGge.Spectral.ActualH1ACRepresentativeUniformBox38V1
import NlsGge.GK38.DirichletL2
import NlsGge.Atomic.G1.G1087

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open NlsGge.Pilot NlsGge.Schur NlsGge.GK38 NlsGge.Analysis NlsGge.SpectralFoundations

open scoped Matrix.Norms.L2Operator

namespace NlsGge.Atomic.G1062S2

open NlsGge.GK38.GradEigen38 NlsGge.Atomic.G1061S1 NlsGge.Atomic.Volterra

noncomputable section

/-- component lemma: the continuous `H¹` representative with its `L²` derivative. -/
theorem comp_rep (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ∃ f f' : ℝ → ℂ, Function.Periodic f 1 ∧
      AbsolutelyContinuousOnInterval f 0 1 ∧
      (∀ᵐ t ∂(volume : Measure ℝ), t ∈ uIcc (0 : ℝ) 1 → HasDerivAt f (f' t) t) ∧
      IntervalIntegrable (fun s : ℝ => ‖f' s‖ ^ 2) volume 0 1 ∧
      (∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioc (0 : ℝ) 1 → coverRep38 u s = f s) ∧
      (∫ s in (0 : ℝ)..1, ‖f' s‖ ^ 2) ≤ (2 * Real.pi * ‖physicalSobolevL2 1 u hu‖) ^ 2 ∧
      (∫ s in (0 : ℝ)..1, ‖f s‖ ^ 2) ≤ ‖physicalSobolevL2 1 u hu‖ ^ 2 := by
  let F := physicalH1Continuous u hu
  let f : ℝ → ℂ := fun t => F (t : PhysicalCircle)
  let w : SourceIntervalL2 := actualPhysicalL2SourcePotential (uA_deriv u hu)
  let g : ℝ → ℂ := fun x => w x
  have hI : IntervalIntegrable g volume 0 1 := uA_deriv_intervalIntegrable _
  have hprim : ∀ t ∈ Icc (0 : ℝ) 1, f t = f 0 + ∫ s in (0 : ℝ)..t, g s := by
    intro t ht
    have h := uA_integral_deriv u hu t ht
    simp only [f, g, w]
    rw [h]; ring
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioc (0 : ℝ) 1 → coverRep38 u s = f s := by
    have h := uA_continuous_rep_ae u hu
    have h' := (ae_restrict_iff' measurableSet_Ioc).1 h
    filter_upwards [h'] with s hs hmem
    exact (hs hmem).symm
  have hint2 : IntervalIntegrable (fun s : ℝ => ‖g s‖ ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact (Lp.memLp w).norm.integrable_sq
  refine ⟨f, g, ?_, ?_, ?_, hint2, hae, ?_, ?_⟩
  · intro s
    show F ((s + 1 : ℝ) : PhysicalCircle) = F (s : PhysicalCircle)
    rw [AddCircle.coe_add_period]
  · have hp := complex_intervalIntegral_primitive_absolutelyContinuousV2 hI
      (left_mem_uIcc : (0 : ℝ) ∈ uIcc (0 : ℝ) 1)
    have hs := (uA_const_absolutelyContinuous (f 0)).add hp
    refine hs.congr ?_
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact (hprim t ht).symm
  · have h0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by simp [ae_iff, measure_singleton]
    have h1 : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by simp [ae_iff, measure_singleton]
    filter_upwards [hI.ae_hasDerivAt_integral, h0, h1] with x hx hx0 hx1 hmem
    have hd := (hx hmem 0 (left_mem_uIcc : (0 : ℝ) ∈ uIcc (0 : ℝ) 1)).const_add (f 0)
    refine hd.congr_of_eventuallyEq ?_
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hmem
    have hmem' : x ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hmem.1 (Ne.symm hx0), lt_of_le_of_ne hmem.2 hx1⟩
    filter_upwards [Ioo_mem_nhds hmem'.1 hmem'.2] with y hy
    exact hprim y ⟨hy.1.le, hy.2.le⟩
  · have e : (∫ s in (0 : ℝ)..1, ‖g s‖ ^ 2) = ‖w‖ ^ 2 := by
      rw [sourceInterval_norm_sq w, intervalIntegral.integral_of_le zero_le_one]
    rw [e, actualPhysicalL2SourcePotential_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (uA_deriv_norm_le u hu) 2
  · have e : (∫ s in (0 : ℝ)..1, ‖f s‖ ^ 2) = ‖u‖ ^ 2 := by
      rw [← integral_sq_coverRep38_one]
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hae] with s hs hmem
      rw [uIoc_of_le zero_le_one] at hmem
      rw [hs hmem]
    rw [e, physicalSobolevL2_norm_sq]
    have hsum : Summable (fun n : ℤ => ‖physicalFourier u n‖ ^ 2) := (hasSum_physicalFourier_sq u).summable
    have hu2 : ‖u‖ ^ 2 = ∑' n : ℤ, ‖physicalFourier u n‖ ^ 2 := (hasSum_physicalFourier_sq u).tsum_eq.symm
    rw [hu2]
    refine hsum.tsum_le_tsum (fun n => ?_) hu
    have : (1 : ℝ) ≤ Real.rpow (japaneseBracket n) (2 * 1) := by
      rw [japaneseBracket_h1_weight]
      nlinarith [sq_nonneg (n : ℝ)]
    nlinarith [sq_nonneg ‖physicalFourier u n‖]


open NlsGge.Atomic.Volterra in
theorem term_congr (a b : ℝ → ℂ) (a' b' : ℝ → ℂ)
    (hA : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioc (0 : ℝ) 1 → a s = a' s)
    (hB : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioc (0 : ℝ) 1 → b s = b' s) (z : ℂ) (n : ℕ) :
    ∀ t ∈ Icc (0 : ℝ) 1, freeKernelVolterraTerm38 a b z n t = freeKernelVolterraTerm38 a' b' z n t := by
  induction n with
  | zero => intro t _; rfl
  | succ n ih =>
    intro t ht
    funext i j
    simp only [freeKernelVolterraTerm38]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hA, hB] with s hsA hsB hs
    have hs' : s ∈ Ioc (0 : ℝ) 1 := by
      rw [uIoc_of_le ht.1] at hs
      exact ⟨hs.1, hs.2.trans ht.2⟩
    have ihs := ih s ⟨hs'.1.le, hs'.2⟩
    have hraw : rawPotCoeff38 a b s = rawPotCoeff38 a' b' s := by
      simp only [rawPotCoeff38, hsA hs', hsB hs']
    rw [hraw, ihs]

open NlsGge.Atomic.Volterra in
theorem pair_rep (φ : PotPair) (h1 : SobolevSquareSummable 1 (physicalFourier φ.1))
    (h2 : SobolevSquareSummable 1 (physicalFourier φ.2)) :
    ∃ a b : ℝ → ℂ, (∀ s : ℝ, a (s + 1) = a s) ∧ (∀ s : ℝ, b (s + 1) = b s) ∧
      AbsolutelyContinuousOnInterval a 0 1 ∧ AbsolutelyContinuousOnInterval b 0 1 ∧
      IntervalIntegrable (fun s : ℝ => ‖deriv a s‖ ^ 2 + ‖deriv b s‖ ^ 2) volume 0 1 ∧
      (∫ s in (0 : ℝ)..1, (‖a s‖ ^ 2 + ‖deriv a s‖ ^ 2 + ‖b s‖ ^ 2 + ‖deriv b s‖ ^ 2)) ≤
        (1 + (2 * Real.pi) ^ 2) *
          (‖physicalSobolevL2 1 φ.1 h1‖ ^ 2 + ‖physicalSobolevL2 1 φ.2 h2‖ ^ 2) ∧
      ∀ (z : ℂ) (n : ℕ), ∀ t ∈ Icc (0 : ℝ) 1,
        freeKernelVolterraTerm38 a b z n t = potentialVolterraTerm38 φ z n t := by
  obtain ⟨a, a', hpa, hAa, hda, hia, hca, hna', hna⟩ := comp_rep φ.1 h1
  obtain ⟨b, b', hpb, hAb, hdb, hib, hcb, hnb', hnb⟩ := comp_rep φ.2 h2
  have hderA : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ uIcc (0 : ℝ) 1 → deriv a t = a' t := by
    filter_upwards [hda] with t ht hm using (ht hm).deriv
  have hderB : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ uIcc (0 : ℝ) 1 → deriv b t = b' t := by
    filter_upwards [hdb] with t ht hm using (ht hm).deriv
  have hI : Set.uIoc (0 : ℝ) 1 ⊆ uIcc (0 : ℝ) 1 := uIoc_subset_uIcc
  have hdA2 : IntervalIntegrable (fun s : ℝ => ‖deriv a s‖ ^ 2) volume 0 1 := by
    refine hia.congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hderA] with t ht hm
    rw [ht (hI hm)]
  have hdB2 : IntervalIntegrable (fun s : ℝ => ‖deriv b s‖ ^ 2) volume 0 1 := by
    refine hib.congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hderB] with t ht hm
    rw [ht (hI hm)]
  have hcontA : ContinuousOn a (Icc (0 : ℝ) 1) := by
    simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using hAa.continuousOn
  have hcontB : ContinuousOn b (Icc (0 : ℝ) 1) := by
    simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using hAb.continuousOn
  have haA : IntervalIntegrable (fun s : ℝ => ‖a s‖ ^ 2) volume 0 1 :=
    ((hcontA.norm).pow 2).intervalIntegrable_of_Icc zero_le_one
  have haB : IntervalIntegrable (fun s : ℝ => ‖b s‖ ^ 2) volume 0 1 :=
    ((hcontB.norm).pow 2).intervalIntegrable_of_Icc zero_le_one
  have eA : (∫ s in (0 : ℝ)..1, ‖deriv a s‖ ^ 2) = ∫ s in (0 : ℝ)..1, ‖a' s‖ ^ 2 := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hderA] with t ht hm
    rw [ht (hI hm)]
  have eB : (∫ s in (0 : ℝ)..1, ‖deriv b s‖ ^ 2) = ∫ s in (0 : ℝ)..1, ‖b' s‖ ^ 2 := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hderB] with t ht hm
    rw [ht (hI hm)]
  refine ⟨a, b, hpa, hpb, hAa, hAb, hdA2.add hdB2, ?_, ?_⟩
  · rw [intervalIntegral.integral_add (haA.add hdA2 |>.add haB) hdB2,
      intervalIntegral.integral_add (haA.add hdA2) haB, intervalIntegral.integral_add haA hdA2, eA, eB]
    rw [mul_pow] at hna' hnb'
    nlinarith [hna, hna', hnb, hnb']
  · intro z n t ht
    unfold potentialVolterraTerm38
    refine term_congr a b (potRepFst38 φ) (potRepSnd38 φ) ?_ ?_ z n t ht
    · filter_upwards [hca] with s hs hm using (hs hm).symm
    · filter_upwards [hcb] with s hs hm using (hs hm).symm

/-- bounded `H¹` hypothesis, exactly as in the landed G1-049 statement -/
def H1B (B : ℝ) (φ : PotPair) : Prop :=
  Summable (fun n : ℤ => japaneseBracket n ^ 2 *
      (‖physicalFourier (φ.1 : PhysicalCircle → ℂ) n‖ ^ 2 +
        ‖physicalFourier (φ.2 : PhysicalCircle → ℂ) n‖ ^ 2)) ∧
    Real.sqrt (∑' n : ℤ, japaneseBracket n ^ 2 *
      (‖physicalFourier (φ.1 : PhysicalCircle → ℂ) n‖ ^ 2 +
        ‖physicalFourier (φ.2 : PhysicalCircle → ℂ) n‖ ^ 2)) ≤ B

theorem physicalFourier_neg (u : PhysicalL2) (n : ℤ) :
    physicalFourier (-u : PhysicalL2) n = - physicalFourier u n := by
  rw [← physicalFourierL2_apply, ← physicalFourierL2_apply, map_neg]
  rfl

theorem H1B_neg {B : ℝ} {φ : PotPair} (h : H1B B φ) : H1B B (-φ) := by
  have e : ∀ n : ℤ, ‖physicalFourier (((-φ).1 : PhysicalL2) : PhysicalCircle → ℂ) n‖ =
      ‖physicalFourier (φ.1 : PhysicalCircle → ℂ) n‖ ∧
      ‖physicalFourier (((-φ).2 : PhysicalL2) : PhysicalCircle → ℂ) n‖ =
      ‖physicalFourier (φ.2 : PhysicalCircle → ℂ) n‖ := by
    intro n
    refine ⟨?_, ?_⟩
    · show ‖physicalFourier (-(φ.1) : PhysicalL2) n‖ = _
      rw [physicalFourier_neg, norm_neg]
    · show ‖physicalFourier (-(φ.2) : PhysicalL2) n‖ = _
      rw [physicalFourier_neg, norm_neg]
  unfold H1B
  simp only [(e _).1, (e _).2]
  exact h

theorem H1B_sob {B : ℝ} {φ : PotPair} (h : H1B B φ) :
    ∃ (h1 : SobolevSquareSummable 1 (physicalFourier φ.1))
      (h2 : SobolevSquareSummable 1 (physicalFourier φ.2)),
      ‖physicalSobolevL2 1 φ.1 h1‖ ^ 2 + ‖physicalSobolevL2 1 φ.2 h2‖ ^ 2 ≤ B ^ 2 := by
  obtain ⟨hs, hle⟩ := h
  have hw : ∀ n : ℤ, Real.rpow (japaneseBracket n) (2 * (1 : ℝ)) = japaneseBracket n ^ 2 := by
    intro n
    rw [japaneseBracket_h1_weight, NlsGge.Atomic.G1049S1.japaneseBracket_sq]
  have hb0 : ∀ n : ℤ, 0 ≤ japaneseBracket n ^ 2 := fun n => by positivity
  have h1 : SobolevSquareSummable 1 (physicalFourier φ.1) := by
    unfold SobolevSquareSummable
    refine Summable.of_nonneg_of_le (fun n => by rw [hw n]; positivity) (fun n => ?_) hs
    rw [hw n]
    have := mul_nonneg (hb0 n) (sq_nonneg ‖physicalFourier (φ.2 : PhysicalCircle → ℂ) n‖)
    nlinarith
  have h2 : SobolevSquareSummable 1 (physicalFourier φ.2) := by
    unfold SobolevSquareSummable
    refine Summable.of_nonneg_of_le (fun n => by rw [hw n]; positivity) (fun n => ?_) hs
    rw [hw n]
    have := mul_nonneg (hb0 n) (sq_nonneg ‖physicalFourier (φ.1 : PhysicalCircle → ℂ) n‖)
    nlinarith
  refine ⟨h1, h2, ?_⟩
  rw [physicalSobolevL2_norm_sq, physicalSobolevL2_norm_sq]
  simp only [hw]
  have hs1 : Summable (fun n : ℤ => japaneseBracket n ^ 2 * ‖physicalFourier (φ.1 : PhysicalCircle → ℂ) n‖ ^ 2) := by
    have h1' := h1
    unfold SobolevSquareSummable at h1'
    simpa only [hw] using h1'
  have hs2 : Summable (fun n : ℤ => japaneseBracket n ^ 2 * ‖physicalFourier (φ.2 : PhysicalCircle → ℂ) n‖ ^ 2) := by
    have h2' := h2
    unfold SobolevSquareSummable at h2'
    simpa only [hw] using h2'
  rw [← hs1.tsum_add hs2]
  have : (∑' n : ℤ, (japaneseBracket n ^ 2 * ‖physicalFourier (φ.1 : PhysicalCircle → ℂ) n‖ ^ 2 +
      japaneseBracket n ^ 2 * ‖physicalFourier (φ.2 : PhysicalCircle → ℂ) n‖ ^ 2)) =
      ∑' n : ℤ, japaneseBracket n ^ 2 *
        (‖physicalFourier (φ.1 : PhysicalCircle → ℂ) n‖ ^ 2 + ‖physicalFourier (φ.2 : PhysicalCircle → ℂ) n‖ ^ 2) := by
    refine tsum_congr fun n => ?_
    ring
  rw [this]
  exact (Real.sqrt_le_iff.1 hle).2

theorem unif_l2 (B : ℝ) (hB : 0 ≤ B) :
    ∃ R2 : ℝ, ∀ φ ∈ NlsGge.Atomic.G1049S1.Cset B,
      Summable (fun n : ℤ => ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ∧
        (∑' n : ℤ, ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ≤ R2 := by
  choose U hU c hc using fun φ₀ : PotPair => NlsGge.GK38.muSeq_l2 φ₀
  obtain ⟨t, -, hcov⟩ := (NlsGge.Atomic.G1049S1.isCompact_Cset hB).elim_nhds_subcover U (fun x _ => hU x)
  refine ⟨∑ x ∈ t, |c x|, fun φ hφ => ?_⟩
  obtain ⟨x, hx, hφx⟩ := Set.mem_iUnion₂.1 (hcov hφ)
  obtain ⟨hs, hle⟩ := hc x φ hφx
  refine ⟨hs, hle.trans ((le_abs_self _).trans ?_)⟩
  exact Finset.single_le_sum (f := fun x => |c x|) (fun _ _ => abs_nonneg _) hx

theorem unif_Q (B : ℝ) (hB : 0 ≤ B) :
    ∃ N : ℕ, ∀ φ ∈ NlsGge.Atomic.G1049S1.Cset B, ∀ n : ℤ, N < n.natAbs →
      ‖Q (state φ (muSeq φ n) (![1, 1] : PairVec38)) - 2‖ ≤ 1 / 2 := by
  choose V hV N hN using fun φ₀ : PotPair => NlsGge.Atomic.G1087S2.Uniform.Q_small φ₀ (1 / 2) (by norm_num)
  obtain ⟨t, -, hcov⟩ := (NlsGge.Atomic.G1049S1.isCompact_Cset hB).elim_nhds_subcover V (fun x _ => hV x)
  refine ⟨∑ x ∈ t, N x, fun φ hφ n hn => ?_⟩
  obtain ⟨x, hx, hφx⟩ := Set.mem_iUnion₂.1 (hcov hφ)
  refine hN x φ hφx n (lt_of_le_of_lt ?_ hn)
  exact Finset.single_le_sum (f := fun x => N x) (fun _ _ => Nat.zero_le _) hx


theorem g_err_le (φ : PotPair) (n : ℤ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {s : ℝ}
    (h : ‖Mser φ (muSeq φ n) t - freeZsFundamentalComplex ((n : ℂ) * (Real.pi : ℂ)) t‖ ≤ s) :
    ‖pairKernelExt38 (state φ (muSeq φ n) (![1, 1] : PairVec38)) t 0 -
        Complex.exp (-(Real.pi * n * t * Complex.I))‖ ≤ 2 * s ∧
    ‖pairKernelExt38 (state φ (muSeq φ n) (![1, 1] : PairVec38)) t 1 -
        Complex.exp (Real.pi * n * t * Complex.I)‖ ≤ 2 * s := by
  set M := Mser φ (muSeq φ n) t with hM
  set E := freeZsFundamentalComplex ((n : ℂ) * (Real.pi : ℂ)) t with hE
  have e00 : E 0 0 = Complex.exp (-(Real.pi * n * t * Complex.I)) := by
    rw [hE, freeZs_00]; congr 1; ring
  have e11 : E 1 1 = Complex.exp (Real.pi * n * t * Complex.I) := by
    rw [hE, freeZs_11]; congr 1; ring
  have e01 : E 0 1 = 0 := freeZs_01 _ _
  have e10 : E 1 0 = 0 := freeZs_10 _ _
  have hent : ∀ i j : Fin 2, ‖M i j - E i j‖ ≤ s := by
    intro i j
    have := norm_entry_le_l2 (M - E) i j
    simp only [Matrix.sub_apply] at this
    exact this.trans h
  refine ⟨?_, ?_⟩
  · rw [gcomp_eq φ _ ht, ← e00]
    have : M 0 0 + M 0 1 - E 0 0 = (M 0 0 - E 0 0) + (M 0 1 - E 0 1) := by rw [e01]; ring
    rw [this]
    calc _ ≤ ‖M 0 0 - E 0 0‖ + ‖M 0 1 - E 0 1‖ := norm_add_le _ _
      _ ≤ 2 * s := by linarith [hent 0 0, hent 0 1]
  · rw [gcomp_eq φ _ ht, ← e11]
    have : M 1 0 + M 1 1 - E 1 1 = (M 1 0 - E 1 0) + (M 1 1 - E 1 1) := by rw [e10]; ring
    rw [this]
    calc _ ≤ ‖M 1 0 - E 1 0‖ + ‖M 1 1 - E 1 1‖ := norm_add_le _ _
      _ ≤ 2 * s := by linarith [hent 1 0, hent 1 1]

theorem sup_core (B : ℝ) (hB : 0 ≤ B) :
    ∃ N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ φ : PotPair, H1B B φ →
      (∀ n : ℤ, N ≤ n.natAbs → ‖Q (state φ (muSeq φ n) (![1, 1] : PairVec38)) - 2‖ ≤ 1 / 2) ∧
      ∃ S : ℤ → ℝ, (∀ n, 0 ≤ S n) ∧ Summable (fun n : ℤ => S n ^ 2) ∧ (∑' n : ℤ, S n ^ 2) ≤ C ∧
        ∀ n : ℤ, ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
          ‖pairKernelExt38 (state φ (muSeq φ n) (![1, 1] : PairVec38)) t 0 -
            Complex.exp (-(Real.pi * n * t * Complex.I))‖ ≤ S n ∧
          ‖pairKernelExt38 (state φ (muSeq φ n) (![1, 1] : PairVec38)) t 1 -
            Complex.exp (Real.pi * n * t * Complex.I)‖ ≤ S n := by
  obtain ⟨R2c, hR2c⟩ := unif_l2 B hB
  obtain ⟨N0, hN0⟩ := unif_Q B hB
  set R0 : ℝ := Real.sqrt (1 + (2 * Real.pi) ^ 2) * B with hR0
  set R2 : ℝ := Real.sqrt (|R2c|) with hR2
  obtain ⟨CG, hCG⟩ := (NlsGge.Atomic.G1021S2.G1021_whole).2 R0 R2
  refine ⟨N0 + 1, 4 * |CG| + 1, by positivity, fun φ hφ => ?_⟩
  have hK : φ ∈ NlsGge.Atomic.G1049S1.Cset B := NlsGge.Atomic.G1049S1.mem_Cset φ hφ.1 hφ.2
  refine ⟨fun n hn => hN0 φ hK n (by omega), ?_⟩
  obtain ⟨h1, h2, hsob⟩ := H1B_sob hφ
  obtain ⟨a, b, hpa, hpb, hAa, hAb, hint, hH1, hterm⟩ := pair_rep φ h1 h2
  obtain ⟨hsum, hle⟩ := hR2c φ hK
  have hH1R : Real.sqrt (∫ s in (0 : ℝ)..1,
      (‖a s‖ ^ 2 + ‖deriv a s‖ ^ 2 + ‖b s‖ ^ 2 + ‖deriv b s‖ ^ 2)) ≤ R0 := by
    rw [hR0]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    calc _ ≤ (1 + (2 * Real.pi) ^ 2) * (‖physicalSobolevL2 1 φ.1 h1‖ ^ 2 + ‖physicalSobolevL2 1 φ.2 h2‖ ^ 2) := hH1
      _ ≤ (1 + (2 * Real.pi) ^ 2) * B ^ 2 :=
        mul_le_mul_of_nonneg_left hsob (by positivity)
  have hξ : Summable (fun n : ℤ => ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ∧
      Real.sqrt (∑' n : ℤ, ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ≤ R2 := by
    refine ⟨hsum, ?_⟩
    rw [hR2]
    exact Real.sqrt_le_sqrt (hle.trans (le_abs_self _))
  obtain ⟨S, hSs, hSC, hSb⟩ := (hCG a b hpa hpb hAa hAb hint hH1R (muSeq φ) hξ).1
  have hsq : ∀ n : ℤ, (2 * |S n|) ^ 2 = 4 * S n ^ 2 := fun n => by rw [mul_pow, sq_abs]; norm_num
  have hsum4 : Summable (fun n : ℤ => (2 * |S n|) ^ 2) := by
    simp only [hsq]; exact hSs.mul_left 4
  refine ⟨fun n => 2 * |S n|, fun n => by positivity, hsum4, ?_, ?_⟩
  · have : (∑' n : ℤ, (2 * |S n|) ^ 2) = 4 * ∑' n : ℤ, S n ^ 2 := by
      simp only [hsq]; exact tsum_mul_left
    rw [this]
    have := le_abs_self CG
    nlinarith [abs_nonneg CG]
  · intro n t ht
    have hb := hSb n t ht.1 ht.2
    have hM : (∑' m : ℕ, freeKernelVolterraTerm38 a b (muSeq φ n) m t) = Mser φ (muSeq φ n) t := by
      unfold Mser
      exact tsum_congr fun m => hterm (muSeq φ n) m t ht
    rw [hM] at hb
    have hg := g_err_le φ n ht hb
    refine ⟨hg.1.trans ?_, hg.2.trans ?_⟩ <;> nlinarith [le_abs_self (S n)]

theorem vec_norm_le (v : PairVec38) {b : ℝ} (hb : 0 ≤ b) (h0 : ‖v 0‖ ≤ b) (h1 : ‖v 1‖ ≤ b) :
    ‖v‖ ≤ b := by
  refine (pi_norm_le_iff_of_nonneg hb).2 (fun i => ?_)
  fin_cases i <;> assumption

theorem grad_lin {Q s f : ℂ} (hQ : ‖Q - 2‖ ≤ 1 / 2) (hf : ‖f‖ = 1) :
    ‖Q⁻¹ * s - (1 / 2 : ℂ) * f‖ ≤ ‖s - f‖ + ‖Q - 2‖ / 2 := by
  have hQn : (3 / 2 : ℝ) ≤ ‖Q‖ := by
    have h := norm_sub_norm_le (2 : ℂ) Q
    rw [norm_sub_rev] at h
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    linarith
  have e : Q⁻¹ * s - (1 / 2 : ℂ) * f = Q⁻¹ * (s - f) + (Q⁻¹ - 1 / 2) * f := by
    have hQ0 : Q ≠ 0 := by intro h; rw [h] at hQn; norm_num at hQn
    ring
  have h1 : ‖Q⁻¹‖ ≤ 1 := by
    rw [norm_inv]; exact inv_le_one_of_one_le₀ (by linarith)
  have h2 : ‖Q⁻¹ - 1 / 2‖ ≤ ‖Q - 2‖ / 2 := by
    have hQ0 : Q ≠ 0 := by intro h; rw [h] at hQn; norm_num at hQn
    have e2 : Q⁻¹ - 1 / 2 = (2 - Q) / (2 * Q) := by field_simp
    rw [e2, norm_div, norm_mul, norm_sub_rev]
    have h3 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h3]
    have hpos : 0 ≤ ‖Q - 2‖ := norm_nonneg _
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
    nlinarith
  rw [e]
  calc ‖Q⁻¹ * (s - f) + (Q⁻¹ - 1 / 2) * f‖ ≤ ‖Q⁻¹ * (s - f)‖ + ‖(Q⁻¹ - 1 / 2) * f‖ := norm_add_le _ _
    _ ≤ ‖s - f‖ + ‖Q - 2‖ / 2 := by
        rw [norm_mul, norm_mul, hf, mul_one]
        have := mul_le_mul h1 (le_refl ‖s - f‖) (norm_nonneg _) zero_le_one
        linarith

theorem sq_err (w : PairKernelCont38) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {n : ℤ} {s c : ℝ}
    (hs0 : 0 ≤ s) (hsc : s ≤ c)
    (h0 : ‖pairKernelExt38 w t 0 - Complex.exp (-(Real.pi * n * t * Complex.I))‖ ≤ s)
    (h1 : ‖pairKernelExt38 w t 1 - Complex.exp (Real.pi * n * t * Complex.I)‖ ≤ s) :
    ‖pairKernelExt38 (square w) t 0 - Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)‖ ≤ (2 + c) * s ∧
    ‖pairKernelExt38 (square w) t 1 - Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ ≤ (2 + c) * s := by
  obtain ⟨q0, q1⟩ := square_ext w ht
  rw [q0, q1, ← e1_sq n t, ← e0_sq n t]
  have a1 := sq_diff_le (g := pairKernelExt38 w t 1) (norm_e1 n t) h1
  have a0 := sq_diff_le (g := pairKernelExt38 w t 0) (norm_e0 n t) h0
  have a1' : ‖pairKernelExt38 w t 1 * pairKernelExt38 w t 1 - Complex.exp (Real.pi * n * t * Complex.I) ^ 2‖ ≤ (2 + s) * ‖pairKernelExt38 w t 1 - Complex.exp (Real.pi * n * t * Complex.I)‖ := by
    rw [← pow_two]; exact a1
  have a0' : ‖pairKernelExt38 w t 0 * pairKernelExt38 w t 0 - Complex.exp (-(Real.pi * n * t * Complex.I)) ^ 2‖ ≤ (2 + s) * ‖pairKernelExt38 w t 0 - Complex.exp (-(Real.pi * n * t * Complex.I))‖ := by
    rw [← pow_two]; exact a0
  refine ⟨?_, ?_⟩
  · refine a1'.trans ?_
    nlinarith [norm_nonneg (pairKernelExt38 w t 1 - Complex.exp (Real.pi * n * t * Complex.I))]
  · refine a0'.trans ?_
    nlinarith [norm_nonneg (pairKernelExt38 w t 0 - Complex.exp (-(Real.pi * n * t * Complex.I)))]

theorem Q_err (w : PairKernelCont38) {n : ℤ} {s : ℝ} (hs0 : 0 ≤ s)
    (h0 : ∀ t ∈ Icc (0 : ℝ) 1, ‖pairKernelExt38 w t 0 - Complex.exp (-(Real.pi * n * t * Complex.I))‖ ≤ s)
    (h1 : ∀ t ∈ Icc (0 : ℝ) 1, ‖pairKernelExt38 w t 1 - Complex.exp (Real.pi * n * t * Complex.I)‖ ≤ s) :
    ‖Q w - 2‖ ≤ 2 * (s * (2 + s)) := by
  have hc : Continuous (fun x : ℝ => pairKernelExt38 w x 0 * pairKernelExt38 w x 1) :=
    ((continuous_apply 0).comp (continuous_pairKernelExt38 w)).mul
      ((continuous_apply 1).comp (continuous_pairKernelExt38 w))
  have hpt : ∀ x ∈ Set.uIoc (0 : ℝ) 1,
      ‖pairKernelExt38 w x 0 * pairKernelExt38 w x 1 - 1‖ ≤ s * (2 + s) := by
    intro x hx
    rw [Set.uIoc_of_le zero_le_one] at hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
    have e : pairKernelExt38 w x 0 * pairKernelExt38 w x 1 - 1 =
        (pairKernelExt38 w x 0 - Complex.exp (-(Real.pi * n * x * Complex.I))) * pairKernelExt38 w x 1 +
        Complex.exp (-(Real.pi * n * x * Complex.I)) *
          (pairKernelExt38 w x 1 - Complex.exp (Real.pi * n * x * Complex.I)) := by
      have := e0_mul_e1 n x
      linear_combination this
    rw [e]
    have hw1 : ‖pairKernelExt38 w x 1‖ ≤ 1 + s := by
      have : pairKernelExt38 w x 1 = (pairKernelExt38 w x 1 - Complex.exp (Real.pi * n * x * Complex.I)) +
          Complex.exp (Real.pi * n * x * Complex.I) := by ring
      rw [this]
      calc _ ≤ ‖pairKernelExt38 w x 1 - Complex.exp (Real.pi * n * x * Complex.I)‖ +
            ‖Complex.exp (Real.pi * n * x * Complex.I)‖ := norm_add_le _ _
        _ ≤ 1 + s := by rw [norm_e1]; linarith [h1 x hx']
    calc _ ≤ ‖(pairKernelExt38 w x 0 - Complex.exp (-(Real.pi * n * x * Complex.I))) * pairKernelExt38 w x 1‖ +
          ‖Complex.exp (-(Real.pi * n * x * Complex.I)) *
            (pairKernelExt38 w x 1 - Complex.exp (Real.pi * n * x * Complex.I))‖ := norm_add_le _ _
      _ ≤ s * (1 + s) + 1 * s := by
          rw [norm_mul, norm_mul, norm_e0]
          have a := h0 x hx'
          have b := h1 x hx'
          have c1 := mul_le_mul a hw1 (norm_nonneg _) hs0
          linarith
      _ = s * (2 + s) := by ring
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  have hI : (∫ x in (0 : ℝ)..1, (pairKernelExt38 w x 0 * pairKernelExt38 w x 1 - 1)) =
      (∫ x in (0 : ℝ)..1, pairKernelExt38 w x 0 * pairKernelExt38 w x 1) - 1 := by
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const]
    simp
  rw [hI] at hint
  have hQ : Q w - 2 = 2 * ((∫ x in (0 : ℝ)..1, pairKernelExt38 w x 0 * pairKernelExt38 w x 1) - 1) := by
    unfold Q; ring
  rw [hQ, norm_mul]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  simp only [sub_zero, abs_one, mul_one] at hint
  linarith

end

end NlsGge.Atomic.G1062S2

/-! ===================== Pro's definitions (verbatim) and the G1_062 assembly ===================== -/

namespace NlsGge.GKDefinitionDesign

noncomputable section

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonMixed38
open NlsGge.GK38.PoissonDirichlet38 NlsGge.GK38.PoissonSpectral38
open NlsGge.Atomic.G1062S2 NlsGge.Atomic.G1061S1

def simpleDirichlet (φ : PotPair) (z : ℂ) : Prop :=
  dirichletChar φ z = 0 ∧ deriv (dirichletChar φ) z ≠ 0

def gkNeumannCharacteristic (φ : PotPair) (z : ℂ) : ℂ :=
  -neumannChar38 φ z

def physicalSobolev (r : ℝ) (u : PhysicalL2) : Prop :=
  SobolevSquareSummable r (reflectedFourierL2 u)

def pairSobolev (r : ℝ) (φ : PotPair) : Prop :=
  physicalSobolev r φ.1 ∧ physicalSobolev r φ.2

def physicalSobolevNorm (r : ℝ) (u : PhysicalL2) : ℝ :=
  Real.sqrt (∑' n : ℤ,
    Real.rpow (japaneseBracket n) (2*r) * ‖reflectedFourierL2 u n‖^2)

def pairSobolevNorm (r : ℝ) (φ : PotPair) : ℝ :=
  Real.sqrt (physicalSobolevNorm r φ.1 ^ 2 + physicalSobolevNorm r φ.2 ^ 2)

def freeG (n : ℤ) (t : Time) : PairVec38 :=
  ![Complex.exp (-(Real.pi : ℂ)*Complex.I*(n : ℂ)*(t.1 : ℂ)),
    Complex.exp ((Real.pi : ℂ)*Complex.I*(n : ℂ)*(t.1 : ℂ))]

def freeH (n : ℤ) (t : Time) : PairVec38 :=
  ![Complex.I * freeG n t 0, -Complex.I * freeG n t 1]

def ePlus (n : ℤ) (t : Time) : PairVec38 :=
  ![0,Complex.exp (-2*(Real.pi : ℂ)*Complex.I*(n : ℂ)*(t.1 : ℂ))]

def eMinus (n : ℤ) (t : Time) : PairVec38 :=
  ![Complex.exp (2*(Real.pi : ℂ)*Complex.I*(n : ℂ)*(t.1 : ℂ)),0]

def complexDirState (φ : PotPair) (n : ℤ) : PairKernelCont38 :=
  state φ (muSeq φ n) ![1,1]

def complexNeuState (φ : PotPair) (n : ℤ) : PairKernelCont38 :=
  state φ (nuSeq38 φ n) ![Complex.I,-Complex.I]

def canonicalError (φ : PotPair) (n : ℤ) (j : Fin 6) (t : Time) : PairVec38 :=
  ![complexDirState φ n t - freeG n t,
    complexNeuState φ n t - freeH n t,
    square (complexDirState φ n) t - (ePlus n t + eMinus n t),
    square (complexNeuState φ n) t + (ePlus n t + eMinus n t),
    dirEigenKernel38 φ (muSeq φ n) t - (1/2 : ℂ) • (ePlus n t + eMinus n t),
    (Q (complexNeuState φ n))⁻¹ • square (complexNeuState φ n) t +
      (1/2 : ℂ) • (ePlus n t + eMinus n t)] j

def canonicalTail (N : ℕ) (φ : PotPair) (n : ℤ) (j : Fin 6)
    (t : Time) : PairVec38 :=
  if j.val < 4 ∨ N ≤ n.natAbs then canonicalError φ n j t else 0

def kernelSup (f : Time → PairVec38) : ℝ := sSup (Set.range (fun t => ‖f t‖))

theorem time_ext (w : PairKernelCont38) (t : Time) : w t = pairKernelExt38 w t.1 :=
  (pairKernelExt38_of_mem w t.2).symm

theorem kernelSup_le_of (f : Time → PairVec38) {b : ℝ} (hb : 0 ≤ b) (h : ∀ t, ‖f t‖ ≤ b) :
    BddAbove (Set.range (fun t => ‖f t‖)) ∧ 0 ≤ kernelSup f ∧ kernelSup f ≤ b := by
  refine ⟨⟨b, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩; exact h t
  · exact Real.sSup_nonneg (by rintro _ ⟨t, rfl⟩; exact norm_nonneg _)
  · exact csSup_le ⟨_, ⟨t0, rfl⟩⟩ (by rintro _ ⟨t, rfl⟩; exact h t)

theorem Q_ne_zero_of {Q : ℂ} (h : ‖Q - 2‖ ≤ 1 / 2) : Q ≠ 0 := by
  intro h0
  rw [h0] at h
  norm_num at h

theorem norm_exp2 (n : ℤ) (t : ℝ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)‖ = 1 ∧
    ‖Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ = 1 := by
  constructor
  · have : Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I) =
        Complex.exp (((2 * Real.pi * n * t : ℝ) : ℂ) * Complex.I) := by
      congr 1; push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  · have : Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)) =
        Complex.exp (((-(2 * Real.pi * n * t) : ℝ) : ℂ) * Complex.I) := by
      congr 1; push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]

/-- Dirichlet-form data: the three derived sup bounds. -/
theorem dir_bounds (ψ : PotPair) (n : ℤ) {s c : ℝ} (hs0 : 0 ≤ s) (hsc : s ≤ c)
    (h0 : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖pairKernelExt38 (state ψ (muSeq ψ n) (![1, 1] : PairVec38)) t 0 -
        Complex.exp (-(Real.pi * n * t * Complex.I))‖ ≤ s)
    (h1 : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖pairKernelExt38 (state ψ (muSeq ψ n) (![1, 1] : PairVec38)) t 1 -
        Complex.exp (Real.pi * n * t * Complex.I)‖ ≤ s) :
    (∀ t : Time, ‖complexDirState ψ n t - freeG n t‖ ≤ s) ∧
    (∀ t : Time, ‖square (complexDirState ψ n) t - (ePlus n t + eMinus n t)‖ ≤ (2 + c) * s) ∧
    (‖Q (complexDirState ψ n) - 2‖ ≤ 1 / 2 →
      ∀ t : Time, ‖(Q (complexDirState ψ n))⁻¹ • square (complexDirState ψ n) t -
        (1 / 2 : ℂ) • (ePlus n t + eMinus n t)‖ ≤ 2 * ((2 + c) * s)) := by
  have hc : 0 ≤ c := hs0.trans hsc
  have hsc2 : 0 ≤ (2 + c) * s := mul_nonneg (by linarith) hs0
  refine ⟨fun t => ?_, fun t => ?_, fun hQ t => ?_⟩
  · rw [time_ext]
    refine vec_norm_le _ hs0 ?_ ?_
    · have e : freeG n t 0 = Complex.exp (-(Real.pi * n * t.1 * Complex.I)) := by
        simp [freeG] <;> (congr 1; ring)
      simp only [Pi.sub_apply, complexDirState, e]
      exact h0 t.1 t.2
    · have e : freeG n t 1 = Complex.exp (Real.pi * n * t.1 * Complex.I) := by
        simp [freeG] <;> (congr 1; ring)
      simp only [Pi.sub_apply, complexDirState, e]
      exact h1 t.1 t.2
  · have hsq := sq_err (state ψ (muSeq ψ n) (![1, 1] : PairVec38)) t.2 (n := n) hs0 hsc (h0 t.1 t.2) (h1 t.1 t.2)
    rw [time_ext]
    refine vec_norm_le _ hsc2 ?_ ?_
    · have e : (ePlus n t + eMinus n t) 0 =
          Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t.1 : ℂ) * Complex.I) := by
        simp [ePlus, eMinus] <;> (congr 1; ring)
      simp only [Pi.sub_apply, complexDirState, e]
      exact hsq.1
    · have e : (ePlus n t + eMinus n t) 1 =
          Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t.1 : ℂ) * Complex.I)) := by
        simp [ePlus, eMinus] <;> (congr 1; ring)
      simp only [Pi.sub_apply, complexDirState, e]
      exact hsq.2
  · have hsq := sq_err (state ψ (muSeq ψ n) (![1, 1] : PairVec38)) t.2 (n := n) hs0 hsc (h0 t.1 t.2) (h1 t.1 t.2)
    have hQe := Q_err (state ψ (muSeq ψ n) (![1, 1] : PairVec38)) (n := n) hs0 h0 h1
    have hQ' : ‖Q (state ψ (muSeq ψ n) (![1, 1] : PairVec38)) - 2‖ ≤ 2 * (s * (2 + s)) := hQe
    have hQc : ‖Q (state ψ (muSeq ψ n) (![1, 1] : PairVec38)) - 2‖ ≤ 2 * ((2 + c) * s) := by
      refine hQ'.trans ?_
      nlinarith
    have hb : 0 ≤ 2 * ((2 + c) * s) := by linarith
    rw [time_ext]
    simp only [complexDirState] at hQ ⊢
    have hn0 : ‖Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t.1 : ℂ) * Complex.I)‖ = 1 := (norm_exp2 n t.1).1
    have hn1 : ‖Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t.1 : ℂ) * Complex.I))‖ = 1 := (norm_exp2 n t.1).2
    refine vec_norm_le _ hb ?_ ?_
    · have e : (ePlus n t + eMinus n t) 0 =
          Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t.1 : ℂ) * Complex.I) := by
        simp [ePlus, eMinus] <;> (congr 1; ring)
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e]
      have := grad_lin (Q := Q (state ψ (muSeq ψ n) (![1, 1] : PairVec38)))
        (s := pairKernelExt38 (square (state ψ (muSeq ψ n) (![1, 1] : PairVec38))) t.1 0) hQ hn0
      refine this.trans ?_
      linarith [hsq.1]
    · have e : (ePlus n t + eMinus n t) 1 =
          Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t.1 : ℂ) * Complex.I)) := by
        simp [ePlus, eMinus] <;> (congr 1; ring)
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e]
      have := grad_lin (Q := Q (state ψ (muSeq ψ n) (![1, 1] : PairVec38)))
        (s := pairKernelExt38 (square (state ψ (muSeq ψ n) (![1, 1] : PairVec38))) t.1 1) hQ hn1
      refine this.trans ?_
      linarith [hsq.2]


theorem refl_term (u : PhysicalL2) (n : ℤ) :
    Real.rpow (japaneseBracket n) (2 * (1 : ℝ)) * ‖reflectedFourierL2 u n‖ ^ 2 =
      japaneseBracket (-n) ^ 2 * ‖physicalFourier (u : PhysicalCircle → ℂ) (-n)‖ ^ 2 := by
  rw [reflectedFourierL2_apply]
  unfold reflectedFourier
  rw [norm_neg, japaneseBracket_neg, japaneseBracket_h1_weight,
    NlsGge.Atomic.G1049S1.japaneseBracket_sq]

theorem refl_summable (u : PhysicalL2) (h : physicalSobolev 1 u) :
    Summable (fun n : ℤ => japaneseBracket n ^ 2 * ‖physicalFourier (u : PhysicalCircle → ℂ) n‖ ^ 2) := by
  have h' : Summable (fun n : ℤ => Real.rpow (japaneseBracket n) (2 * (1 : ℝ)) *
      ‖reflectedFourierL2 u n‖ ^ 2) := h
  have h2 : Summable (fun n : ℤ => japaneseBracket (-n) ^ 2 *
      ‖physicalFourier (u : PhysicalCircle → ℂ) (-n)‖ ^ 2) := h'.congr (refl_term u)
  exact (Equiv.neg ℤ).summable_iff.mp h2

theorem refl_tsum (u : PhysicalL2) :
    ∑' n : ℤ, Real.rpow (japaneseBracket n) (2 * (1 : ℝ)) * ‖reflectedFourierL2 u n‖ ^ 2 =
      ∑' n : ℤ, japaneseBracket n ^ 2 * ‖physicalFourier (u : PhysicalCircle → ℂ) n‖ ^ 2 := by
  calc _ = ∑' n : ℤ, japaneseBracket (-n) ^ 2 * ‖physicalFourier (u : PhysicalCircle → ℂ) (-n)‖ ^ 2 :=
        tsum_congr (refl_term u)
    _ = _ := (Equiv.neg ℤ).tsum_eq (fun n : ℤ => japaneseBracket n ^ 2 *
        ‖physicalFourier (u : PhysicalCircle → ℂ) n‖ ^ 2)

theorem pro_to_H1B (B : ℝ) (φ : PotPair) (hs : pairSobolev 1 φ) (hn : pairSobolevNorm 1 φ ≤ B) :
    H1B B φ := by
  obtain ⟨h1, h2⟩ := hs
  have s1 := refl_summable φ.1 h1
  have s2 := refl_summable φ.2 h2
  have T1 : 0 ≤ ∑' n : ℤ, Real.rpow (japaneseBracket n) (2 * (1 : ℝ)) * ‖reflectedFourierL2 φ.1 n‖ ^ 2 :=
    tsum_nonneg (fun n => mul_nonneg (Real.rpow_nonneg (japaneseBracket_pos n).le _) (sq_nonneg _))
  have T2 : 0 ≤ ∑' n : ℤ, Real.rpow (japaneseBracket n) (2 * (1 : ℝ)) * ‖reflectedFourierL2 φ.2 n‖ ^ 2 :=
    tsum_nonneg (fun n => mul_nonneg (Real.rpow_nonneg (japaneseBracket_pos n).le _) (sq_nonneg _))
  refine ⟨(s1.add s2).congr (fun n => by ring), ?_⟩
  have e : (∑' n : ℤ, japaneseBracket n ^ 2 *
      (‖physicalFourier (φ.1 : PhysicalCircle → ℂ) n‖ ^ 2 + ‖physicalFourier (φ.2 : PhysicalCircle → ℂ) n‖ ^ 2)) =
      (∑' n : ℤ, japaneseBracket n ^ 2 * ‖physicalFourier (φ.1 : PhysicalCircle → ℂ) n‖ ^ 2) +
        ∑' n : ℤ, japaneseBracket n ^ 2 * ‖physicalFourier (φ.2 : PhysicalCircle → ℂ) n‖ ^ 2 := by
    rw [← s1.tsum_add s2]
    exact tsum_congr (fun n => by ring)
  rw [e, ← refl_tsum φ.1, ← refl_tsum φ.2]
  unfold pairSobolevNorm physicalSobolevNorm at hn
  rwa [Real.sq_sqrt T1, Real.sq_sqrt T2] at hn


theorem finish_j (f : ℤ → Time → PairVec38) {c K C0 : ℝ} (S : ℤ → ℝ) (hc : 0 ≤ c) (hcK : c ≤ 2 * K)
    (hS0 : ∀ n, 0 ≤ S n) (hSs : Summable (fun n : ℤ => S n ^ 2)) (hSC : ∑' n : ℤ, S n ^ 2 ≤ C0)
    (hb : ∀ (n : ℤ) (t : Time), ‖f n t‖ ≤ c * S n) :
    (∀ n : ℤ, BddAbove (Set.range (fun t : Time => ‖f n t‖))) ∧
    Summable (fun n : ℤ => (kernelSup (f n)) ^ 2) ∧
    (∑' n : ℤ, (kernelSup (f n)) ^ 2) ≤ 4 * K ^ 2 * C0 + 1 := by
  have hbn : ∀ n, 0 ≤ c * S n := fun n => mul_nonneg hc (hS0 n)
  have hk : ∀ n, BddAbove (Set.range (fun t : Time => ‖f n t‖)) ∧ 0 ≤ kernelSup (f n) ∧
      kernelSup (f n) ≤ c * S n := fun n => kernelSup_le_of (f n) (hbn n) (hb n)
  have hsq : Summable (fun n : ℤ => c ^ 2 * S n ^ 2) := hSs.mul_left _
  have hle : ∀ n : ℤ, (kernelSup (f n)) ^ 2 ≤ c ^ 2 * S n ^ 2 := fun n => by
    have := pow_le_pow_left₀ (hk n).2.1 (hk n).2.2 2
    rw [mul_pow] at this
    exact this
  have hsum : Summable (fun n : ℤ => (kernelSup (f n)) ^ 2) :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) hle hsq
  refine ⟨fun n => (hk n).1, hsum, ?_⟩
  calc (∑' n : ℤ, (kernelSup (f n)) ^ 2) ≤ ∑' n : ℤ, c ^ 2 * S n ^ 2 := hsum.tsum_le_tsum hle hsq
    _ = c ^ 2 * ∑' n : ℤ, S n ^ 2 := tsum_mul_left
    _ ≤ (2 * K) ^ 2 * C0 := by
        have h0 : 0 ≤ ∑' n : ℤ, S n ^ 2 := tsum_nonneg (fun n => sq_nonneg _)
        have h1 : c ^ 2 ≤ (2 * K) ^ 2 := pow_le_pow_left₀ hc hcK 2
        calc c ^ 2 * ∑' n : ℤ, S n ^ 2 ≤ (2 * K) ^ 2 * ∑' n : ℤ, S n ^ 2 :=
              mul_le_mul_of_nonneg_right h1 h0
          _ ≤ (2 * K) ^ 2 * C0 := mul_le_mul_of_nonneg_left hSC (by positivity)
    _ ≤ 4 * K ^ 2 * C0 + 1 := by nlinarith [sq_nonneg K]

theorem G1_062 (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ φ : PotPair,
      pairSobolev 1 φ → pairSobolevNorm 1 φ ≤ B →
      (∀ n : ℤ, N ≤ n.natAbs →
        simpleDirichlet φ (muSeq φ n) ∧
        gkNeumannCharacteristic φ (nuSeq38 φ n) = 0 ∧
        deriv (gkNeumannCharacteristic φ) (nuSeq38 φ n) ≠ 0 ∧
        Q (complexDirState φ n) ≠ 0 ∧ Q (complexNeuState φ n) ≠ 0) ∧
      (∀ j : Fin 6,
        (∀ n : ℤ,
          BddAbove (Set.range (fun t : Time => ‖canonicalTail N φ n j t‖))) ∧
        Summable (fun n : ℤ => (kernelSup (canonicalTail N φ n j))^2) ∧
        (∑' n : ℤ, (kernelSup (canonicalTail N φ n j))^2) ≤ C) := by
  obtain ⟨N0, C0, hC0, hcore⟩ := sup_core B hB
  have hroot0 : 0 ≤ Real.sqrt C0 := Real.sqrt_nonneg _
  set K : ℝ := 2 + Real.sqrt C0 with hK
  have hK2 : 2 ≤ K := by linarith
  refine ⟨4 * K ^ 2 * C0 + 1, by positivity, N0, ?_⟩
  intro φ hs hn
  have hH : H1B B φ := pro_to_H1B B φ hs hn
  obtain ⟨hQ, S, hS0, hSs, hSC, hSb⟩ := hcore φ hH
  obtain ⟨hQ', S', hS0', hSs', hSC', hSb'⟩ := hcore (-φ) (H1B_neg hH)
  have hSle : ∀ n, S n ≤ Real.sqrt C0 := fun n => by
    have h : S n ^ 2 ≤ C0 := (hSs.le_tsum n (fun m _ => sq_nonneg _)).trans hSC
    exact le_trans (le_abs_self _) (Real.abs_le_sqrt h)
  have hSle' : ∀ n, S' n ≤ Real.sqrt C0 := fun n => by
    have h : S' n ^ 2 ≤ C0 := (hSs'.le_tsum n (fun m _ => sq_nonneg _)).trans hSC'
    exact le_trans (le_abs_self _) (Real.abs_le_sqrt h)
  have hDir := fun n => dir_bounds φ n (hS0 n) (hSle n) (fun t ht => (hSb n t ht).1) (fun t ht => (hSb n t ht).2)
  have hDir' := fun n => dir_bounds (-φ) n (hS0' n) (hSle' n) (fun t ht => (hSb' n t ht).1) (fun t ht => (hSb' n t ht).2)
  refine ⟨?_, ?_⟩
  · intro n hn0
    have hQn := hQ n hn0
    have hQn' := hQ' n hn0
    have hQd : Q (complexDirState φ n) ≠ 0 := Q_ne_zero_of hQn
    have hQN : Q (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38)) ≠ 0 := by
      rw [neu_Q]; exact Q_ne_zero_of hQn'
    have hsd := NlsGge.Atomic.G1061S1.muSeq_simple_of_Q_ne_zero φ n hQd
    have hsn := NlsGge.Atomic.G1061S1.nuSeq_simple_of_Q_ne_zero φ n hQN
    obtain ⟨hr1, hd1⟩ := (NlsGge.GK38.SimpleBoundary38.simple_boundary_iff
      NlsGge.GK38.SimpleBoundary38.dirichletProblem φ (muSeq φ n)).mp hsd
    obtain ⟨hr2, hd2⟩ := (NlsGge.GK38.SimpleBoundary38.simple_boundary_iff
      NlsGge.GK38.SimpleBoundary38.neumannProblem φ (nuSeq38 φ n)).mp hsn
    have hneg : deriv (gkNeumannCharacteristic φ) (nuSeq38 φ n) =
        - deriv (neumannChar38 φ) (nuSeq38 φ n) := by
      unfold gkNeumannCharacteristic
      exact deriv.neg
    refine ⟨by unfold simpleDirichlet; exact ⟨hr1, hd1⟩, ?_, ?_, hQd, hQN⟩
    · unfold gkNeumannCharacteristic
      have : neumannChar38 φ (nuSeq38 φ n) = 0 := hr2
      rw [this]; simp
    · rw [hneg]
      exact neg_ne_zero.mpr hd2
  · have hK0 : 0 ≤ K := by linarith
    have hc1 : (1 : ℝ) ≤ 2 * K := by linarith
    have hKc : K ≤ 2 * K := by linarith
    -- the six tail bounds
    have t0 : ∀ (n : ℤ) (t : Time), ‖canonicalTail N0 φ n 0 t‖ ≤ 1 * S n := fun n t => by
      have e : canonicalTail N0 φ n 0 t = canonicalError φ n 0 t := if_pos (Or.inl (by decide))
      rw [e, one_mul]
      exact (hDir n).1 t
    have t2 : ∀ (n : ℤ) (t : Time), ‖canonicalTail N0 φ n 2 t‖ ≤ K * S n := fun n t => by
      have e : canonicalTail N0 φ n 2 t = canonicalError φ n 2 t := if_pos (Or.inl (by decide))
      rw [e]
      have := (hDir n).2.1 t
      have e2 : canonicalError φ n 2 t = square (complexDirState φ n) t - (ePlus n t + eMinus n t) := rfl
      rw [e2]
      calc _ ≤ (2 + Real.sqrt C0) * S n := this
        _ = K * S n := by rw [hK]
    have t4 : ∀ (n : ℤ) (t : Time), ‖canonicalTail N0 φ n 4 t‖ ≤ (2 * K) * S n := fun n t => by
      by_cases hnn : N0 ≤ n.natAbs
      · have e : canonicalTail N0 φ n 4 t = canonicalError φ n 4 t := if_pos (Or.inr hnn)
        rw [e]
        have e4 : canonicalError φ n 4 t = (Q (complexDirState φ n))⁻¹ • square (complexDirState φ n) t -
            (1 / 2 : ℂ) • (ePlus n t + eMinus n t) := rfl
        rw [e4]
        have := (hDir n).2.2 (hQ n hnn) t
        calc _ ≤ 2 * ((2 + Real.sqrt C0) * S n) := this
          _ = (2 * K) * S n := by rw [hK]; ring
      · have e : canonicalTail N0 φ n 4 t = 0 := if_neg (by
          rintro (h | h)
          · exact absurd h (by decide)
          · exact hnn h)
        rw [e, norm_zero]
        exact mul_nonneg (by linarith) (hS0 n)
    -- Neumann side, through `-φ`
    have key0 : ∀ (n : ℤ) (t : Time), (complexNeuState φ n t) 0 = Complex.I * (complexDirState (-φ) n t) 0 := by
      intro n t
      rw [time_ext (complexNeuState φ n) t, time_ext (complexDirState (-φ) n) t]
      exact (neu_comp φ (nuSeq38 φ n) t.2).1
    have key1 : ∀ (n : ℤ) (t : Time), (complexNeuState φ n t) 1 = -Complex.I * (complexDirState (-φ) n t) 1 := by
      intro n t
      rw [time_ext (complexNeuState φ n) t, time_ext (complexDirState (-φ) n) t]
      exact (neu_comp φ (nuSeq38 φ n) t.2).2
    have t1 : ∀ (n : ℤ) (t : Time), ‖canonicalTail N0 φ n 1 t‖ ≤ 1 * S' n := fun n t => by
      have e : canonicalTail N0 φ n 1 t = canonicalError φ n 1 t := if_pos (Or.inl (by decide))
      rw [e, one_mul]
      have e1 : canonicalError φ n 1 t = complexNeuState φ n t - freeH n t := rfl
      rw [e1]
      have hd := (hDir' n).1 t
      refine vec_norm_le _ (hS0' n) ?_ ?_
      · show ‖(complexNeuState φ n t) 0 - Complex.I * freeG n t 0‖ ≤ S' n
        rw [key0 n t]
        have h' : Complex.I * (complexDirState (-φ) n t) 0 - Complex.I * freeG n t 0 =
            Complex.I * ((complexDirState (-φ) n t - freeG n t) 0) := by
          simp only [Pi.sub_apply]; ring
        rw [h', norm_mul, Complex.norm_I, one_mul]
        exact (norm_le_pi_norm (complexDirState (-φ) n t - freeG n t) 0).trans hd
      · show ‖(complexNeuState φ n t) 1 - (-Complex.I) * freeG n t 1‖ ≤ S' n
        rw [key1 n t]
        have h' : -Complex.I * (complexDirState (-φ) n t) 1 - (-Complex.I) * freeG n t 1 =
            -Complex.I * ((complexDirState (-φ) n t - freeG n t) 1) := by
          simp only [Pi.sub_apply]; ring
        rw [h', norm_mul, norm_neg, Complex.norm_I, one_mul]
        exact (norm_le_pi_norm (complexDirState (-φ) n t - freeG n t) 1).trans hd
    have hsqneg : ∀ (n : ℤ) (t : Time),
        square (complexNeuState φ n) t = - square (complexDirState (-φ) n) t := by
      intro n t
      rw [time_ext (square (complexNeuState φ n)) t, time_ext (square (complexDirState (-φ) n)) t]
      funext i
      exact neu_square φ (nuSeq38 φ n) t.2 i
    have t3 : ∀ (n : ℤ) (t : Time), ‖canonicalTail N0 φ n 3 t‖ ≤ K * S' n := fun n t => by
      have e : canonicalTail N0 φ n 3 t = canonicalError φ n 3 t := if_pos (Or.inl (by decide))
      rw [e]
      have e3 : canonicalError φ n 3 t = square (complexNeuState φ n) t + (ePlus n t + eMinus n t) := rfl
      rw [e3, hsqneg n t]
      have : -square (complexDirState (-φ) n) t + (ePlus n t + eMinus n t) =
          -(square (complexDirState (-φ) n) t - (ePlus n t + eMinus n t)) := by abel
      rw [this, norm_neg]
      calc _ ≤ (2 + Real.sqrt C0) * S' n := (hDir' n).2.1 t
        _ = K * S' n := by rw [hK]
    have t5 : ∀ (n : ℤ) (t : Time), ‖canonicalTail N0 φ n 5 t‖ ≤ (2 * K) * S' n := fun n t => by
      by_cases hnn : N0 ≤ n.natAbs
      · have e : canonicalTail N0 φ n 5 t = canonicalError φ n 5 t := if_pos (Or.inr hnn)
        rw [e]
        have e5 : canonicalError φ n 5 t = (Q (complexNeuState φ n))⁻¹ • square (complexNeuState φ n) t +
            (1 / 2 : ℂ) • (ePlus n t + eMinus n t) := rfl
        have hQeq : Q (complexNeuState φ n) = Q (complexDirState (-φ) n) := neu_Q φ (nuSeq38 φ n)
        rw [e5, hsqneg n t, hQeq]
        have : (Q (complexDirState (-φ) n))⁻¹ • -square (complexDirState (-φ) n) t +
            (1 / 2 : ℂ) • (ePlus n t + eMinus n t) =
            -((Q (complexDirState (-φ) n))⁻¹ • square (complexDirState (-φ) n) t -
              (1 / 2 : ℂ) • (ePlus n t + eMinus n t)) := by
          rw [smul_neg]; abel
        rw [this, norm_neg]
        calc _ ≤ 2 * ((2 + Real.sqrt C0) * S' n) := (hDir' n).2.2 (hQ' n hnn) t
          _ = (2 * K) * S' n := by rw [hK]; ring
      · have e : canonicalTail N0 φ n 5 t = 0 := if_neg (by
          rintro (h | h)
          · exact absurd h (by decide)
          · exact hnn h)
        rw [e, norm_zero]
        exact mul_nonneg (by linarith) (hS0' n)
    intro j
    fin_cases j
    · exact finish_j (fun n => canonicalTail N0 φ n 0) S (by norm_num) hc1 hS0 hSs hSC t0
    · exact finish_j (fun n => canonicalTail N0 φ n 1) S' (by norm_num) hc1 hS0' hSs' hSC' t1
    · exact finish_j (fun n => canonicalTail N0 φ n 2) S hK0 hKc hS0 hSs hSC t2
    · exact finish_j (fun n => canonicalTail N0 φ n 3) S' hK0 hKc hS0' hSs' hSC' t3
    · exact finish_j (fun n => canonicalTail N0 φ n 4) S (by linarith) le_rfl hS0 hSs hSC t4
    · exact finish_j (fun n => canonicalTail N0 φ n 5) S' (by linarith) le_rfl hS0' hSs' hSC' t5

end

end NlsGge.GKDefinitionDesign
