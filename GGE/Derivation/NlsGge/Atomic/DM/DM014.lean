/- DM-014 PRODUCTION01 (proof development review kit; HELD for landing). Source: proof development/DM014_P06.lean (author proof development, request 15b73e19),
   byte-identical except this header and the removed top-level  line.
   Target NlsGge/Atomic/DM/DM014.lean, namespace NlsGge.ThirdConsultation.DM. -/
import NlsGge.Atomic.DM.DM002
import NlsGge.Atomic.DM.DM011
import NlsGge.Atomic.DM.DM001
import NlsGge.Atomic.LIB.LIB031

set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology
open NlsGge.Atomic.DM001 NlsGge.Atomic.DM002

namespace NlsGge.ThirdConsultation.DM
noncomputable section

abbrev RawPair := Bool → ℤ → ℂ

def rawPiFourier (v : PiPairL2) : RawPair :=
  fun b k => piCoeff (v b) k

def fourierTailNorm (v : RawPair) (N : ℕ) : ℝ :=
  Real.sqrt ((∑' k : ℤ, if N ≤ k.natAbs then
    ENNReal.ofReal (‖v true k‖^2 + ‖v false k‖^2) else 0) : ℝ≥0∞).toReal

theorem piCoeff_hasSum (f : PiL2) :
    HasSum (fun k : ℤ => ‖piCoeff f k‖ ^ 2) (‖f‖ ^ 2) := by
  have e : (fun k : ℤ => ‖piCoeff f k‖ ^ 2) =
      fun k : ℤ => ‖unitCoeff (unitaryRescale f) k‖ ^ 2 :=
    funext fun k => by rw [piCoeff_rescale]
  rw [e]
  set g := unitaryRescale f with hg
  have hL : MemLp (g : ℝ → ℂ) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := Lp.memLp g
  have h := hasSum_sq_fourierCoeffOn (a := 0) (b := 1) zero_lt_one hL
  have hn : ‖g‖ = ‖f‖ := LinearIsometryEquiv.norm_map _ _
  rw [← hn, ← NlsGge.Atomic.LIB031.integral_norm_sq g]
  simpa [unitCoeff] using h

theorem piCoeff_sub (f g : PiL2) (k : ℤ) :
    piCoeff (f - g) k = piCoeff f k - piCoeff g k := by
  rw [piCoeff_integral, piCoeff_integral, piCoeff_integral, ← mul_sub,
    ← intervalIntegral.integral_sub (piCoeff_integrable f k) (piCoeff_integrable g k)]
  congr 1
  rw [intervalIntegral.integral_of_le Real.pi_pos.le, intervalIntegral.integral_of_le Real.pi_pos.le]
  apply integral_congr_ae
  have hae : ((f - g : PiL2) : ℝ → ℂ) =ᵐ[NlsGge.Atomic.PeriodPi.normalizedMeasure]
      (f : ℝ → ℂ) - (g : ℝ → ℂ) := Lp.coeFn_sub f g
  have hne : ENNReal.ofReal (Real.pi⁻¹) ≠ 0 := by
    simpa using Real.pi_pos
  have hae' : ∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) Real.pi)),
      ((f - g : PiL2) : ℝ → ℂ) x = ((f : ℝ → ℂ) - (g : ℝ → ℂ)) x := by
    have : ∀ᵐ x ∂(ENNReal.ofReal (Real.pi⁻¹) • volume.restrict (Set.Ioc (0 : ℝ) Real.pi)),
        ((f - g : PiL2) : ℝ → ℂ) x = ((f : ℝ → ℂ) - (g : ℝ → ℂ)) x := hae
    have h2 := ae_iff.1 this
    rw [Measure.smul_apply, smul_eq_mul, mul_eq_zero] at h2
    exact ae_iff.2 (h2.resolve_left hne)
  filter_upwards [hae'] with x hx
  have hx' : ((f - g : PiL2) : ℝ → ℂ) x = (f : ℝ → ℂ) x - (g : ℝ → ℂ) x := hx
  simp only [hx', mul_sub]

theorem norm_piCoeff_le (f : PiL2) (k : ℤ) : ‖piCoeff f k‖ ≤ ‖f‖ := by
  have h := le_hasSum (piCoeff_hasSum f) k (fun j _ => sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem continuous_piCoeff_comp (b : Bool) (k : ℤ) :
    Continuous (fun v : PiPairL2 => piCoeff (v b) k) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun v w => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, ← piCoeff_sub]
  calc ‖piCoeff (v b - w b) k‖ ≤ ‖v b - w b‖ := norm_piCoeff_le _ _
    _ = ‖(v - w) b‖ := rfl
    _ ≤ ‖v - w‖ := PiLp.norm_apply_le _ _
    _ = 1 * ‖v - w‖ := by simp

def pa (v : PiPairL2) (k : ℤ) : ℝ := ‖piCoeff (v true) k‖ ^ 2 + ‖piCoeff (v false) k‖ ^ 2

theorem pa_nonneg (v : PiPairL2) (k : ℤ) : 0 ≤ pa v k := by unfold pa; positivity

theorem pa_hasSum (v : PiPairL2) : HasSum (pa v) (‖v‖ ^ 2) := by
  have h := (piCoeff_hasSum (v true)).add (piCoeff_hasSum (v false))
  have hn : ‖v‖ ^ 2 = ‖v true‖ ^ 2 + ‖v false‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]; simp [Fintype.sum_bool]
  rw [hn]; exact h

def tailR (v : PiPairL2) (N : ℕ) : ℝ := ∑' k : ℤ, if N ≤ k.natAbs then pa v k else 0

theorem tail_summable (v : PiPairL2) (N : ℕ) :
    Summable (fun k : ℤ => if N ≤ k.natAbs then pa v k else 0) :=
  (pa_hasSum v).summable.of_nonneg_of_le (fun k => by split_ifs <;> simp [pa_nonneg v k])
    (fun k => by split_ifs <;> simp [pa_nonneg v k])

theorem tailR_nonneg (v : PiPairL2) (N : ℕ) : 0 ≤ tailR v N :=
  tsum_nonneg fun k => by split_ifs <;> simp [pa_nonneg v k]

theorem tailR_antitone (v : PiPairL2) {N N' : ℕ} (h : N ≤ N') : tailR v N' ≤ tailR v N :=
  (tail_summable v N').tsum_le_tsum (fun k => by
    by_cases h1 : N' ≤ k.natAbs
    · have : N ≤ k.natAbs := le_trans h h1
      simp [h1, this]
    · simp only [h1, if_false]
      split_ifs <;> simp [pa_nonneg v k]) (tail_summable v N)

def sN (N : ℕ) : Finset ℤ := Finset.Ioo (-(N : ℤ)) N

theorem mem_sN (N : ℕ) (k : ℤ) : k ∈ sN N ↔ k.natAbs < N := by
  simp only [sN, Finset.mem_Ioo]; omega

theorem tailR_eq (v : PiPairL2) (N : ℕ) : tailR v N = ‖v‖ ^ 2 - ∑ k ∈ sN N, pa v k := by
  have hlo : HasSum (fun k : ℤ => if N ≤ k.natAbs then 0 else pa v k)
      (∑ k ∈ sN N, (if N ≤ k.natAbs then 0 else pa v k)) :=
    hasSum_sum_of_ne_finset_zero (fun k hk => by
      have : ¬ k.natAbs < N := fun h => hk ((mem_sN N k).2 h)
      simp [show N ≤ k.natAbs by omega])
  have hs : ∑ k ∈ sN N, (if N ≤ k.natAbs then (0 : ℝ) else pa v k) = ∑ k ∈ sN N, pa v k :=
    Finset.sum_congr rfl fun k hk => by
      have := (mem_sN N k).1 hk
      simp [show ¬ N ≤ k.natAbs by omega]
  rw [hs] at hlo
  have hhi := (pa_hasSum v).sub hlo
  have e : (fun k : ℤ => pa v k - (if N ≤ k.natAbs then 0 else pa v k)) =
      fun k => if N ≤ k.natAbs then pa v k else 0 := by
    funext k; split_ifs <;> simp
  rw [e] at hhi
  exact hhi.tsum_eq

theorem continuous_tailR (N : ℕ) : Continuous (fun v : PiPairL2 => tailR v N) := by
  have : (fun v : PiPairL2 => tailR v N) =
      fun v => ‖v‖ ^ 2 - ∑ k ∈ sN N, pa v k := funext fun v => tailR_eq v N
  rw [this]
  refine (continuous_norm.pow 2).sub (continuous_finset_sum _ fun k _ => ?_)
  unfold pa
  exact ((continuous_piCoeff_comp true k).norm.pow 2).add
    ((continuous_piCoeff_comp false k).norm.pow 2)

theorem tailR_tendsto (v : PiPairL2) : Tendsto (fun N : ℕ => tailR v N) atTop (𝓝 0) := by
  have hm : Monotone sN := fun N N' h => by
    intro k hk
    rw [mem_sN] at hk ⊢
    exact lt_of_lt_of_le hk h
  have hf : Tendsto sN atTop atTop :=
    tendsto_atTop_finset_of_monotone hm (fun k => ⟨k.natAbs + 1, (mem_sN _ _).2 (Nat.lt_succ_self _)⟩)
  have h2 : Tendsto (fun N : ℕ => ∑ k ∈ sN N, pa v k) atTop (𝓝 (‖v‖ ^ 2)) :=
    (pa_hasSum v).comp hf
  have h3 := (tendsto_const_nhds (x := ‖v‖ ^ 2)).sub h2
  simp only [sub_self] at h3
  refine h3.congr fun N => ?_
  rw [tailR_eq]

theorem tail_eq_sqrt (v : PiPairL2) (N : ℕ) :
    fourierTailNorm (rawPiFourier v) N = Real.sqrt (tailR v N) := by
  unfold fourierTailNorm
  congr 1
  have e : (fun k : ℤ => if N ≤ k.natAbs then
      ENNReal.ofReal (‖rawPiFourier v true k‖ ^ 2 + ‖rawPiFourier v false k‖ ^ 2) else 0) =
      fun k : ℤ => ENNReal.ofReal (if N ≤ k.natAbs then pa v k else 0) := by
    funext k
    by_cases h : N ≤ k.natAbs <;> simp [h, pa, rawPiFourier]
  rw [e, ← ENNReal.ofReal_tsum_of_nonneg (fun k => by split_ifs <;> simp [pa_nonneg v k])
    (tail_summable v N)]
  exact ENNReal.toReal_ofReal (tailR_nonneg v N)

theorem compact_uniform_fourier_tail
    (K : Set PiPairL2) (hK : IsCompact K) :
  Tendsto (fun N : ℕ =>
    sSup {r : ℝ | ∃ v ∈ K, r = fourierTailNorm (rawPiFourier v) N})
    atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set F : ℕ → PiPairL2 → ℝ := fun N v => Real.sqrt (tailR v N) with hF
  have hFc : ∀ N, Continuous (F N) := fun N => (continuous_tailR N).sqrt
  have hFa : ∀ v, ∀ {N N' : ℕ}, N ≤ N' → F N' v ≤ F N v := fun v N N' h =>
    Real.sqrt_le_sqrt (tailR_antitone v h)
  let U : ℕ → Set PiPairL2 := fun N => {v | F N v < ε / 2}
  have hUo : ∀ N, IsOpen (U N) := fun N => isOpen_lt (hFc N) continuous_const
  have hUm : Monotone U := fun N N' h v hv => lt_of_le_of_lt (hFa v h) hv
  have hcov : K ⊆ ⋃ N, U N := by
    intro v _
    have h0 : Tendsto (fun N : ℕ => F N v) atTop (𝓝 0) := by
      have := (tailR_tendsto v).sqrt
      simpa [hF] using this
    obtain ⟨N, hN⟩ := (h0.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))).exists
    exact mem_iUnion.2 ⟨N, hN⟩
  obtain ⟨N₀, hN₀⟩ := hK.elim_directed_cover U hUo hcov hUm.directed_le
  refine ⟨N₀, fun N hN => ?_⟩
  have hbd : ∀ r ∈ {r : ℝ | ∃ v ∈ K, r = fourierTailNorm (rawPiFourier v) N},
      0 ≤ r ∧ r ≤ ε / 2 := by
    rintro r ⟨v, hv, rfl⟩
    rw [tail_eq_sqrt]
    exact ⟨Real.sqrt_nonneg _, (lt_of_le_of_lt (hFa v hN) (hN₀ hv)).le⟩
  have h0 : 0 ≤ sSup {r : ℝ | ∃ v ∈ K, r = fourierTailNorm (rawPiFourier v) N} :=
    Real.sSup_nonneg fun r hr => (hbd r hr).1
  have h1 : sSup {r : ℝ | ∃ v ∈ K, r = fourierTailNorm (rawPiFourier v) N} ≤ ε / 2 :=
    Real.sSup_le (fun r hr => (hbd r hr).2) (by positivity)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  linarith


end
end NlsGge.ThirdConsultation.DM
-- v6
