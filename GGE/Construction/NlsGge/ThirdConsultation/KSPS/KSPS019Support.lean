import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS019Host
import NlsGge.Atomic.KSPS.KSPS018
import NlsGge.ThirdConsultation.KSPS.KSPS006Support
import NlsGge.Atomic.G1.G1049
import NlsGge.Atomic.G1.G1050
import NlsGge.Atomic.G1.G1061
import NlsGge.Analysis.PhysicalH1Bounds
import NlsGge.GK38.DirichletCounting
import NlsGge.GK38.DirichletLabels
import NlsGge.GK38.PeriodicLabellingCanonical

                                                                                                                    
                                                      
                                                                                                               
                                                                                                                        
                                                                   
                                                                      
                                                                                                               
set_option autoImplicit false
noncomputable section

open Filter Topology Set Metric
open scoped Matrix.Norms.L2Operator

namespace NlsGge.ThirdConsultation.KSPS019Support

open NlsGge.GK38
open NlsGge.ThirdConsultation.KSPS

/-! ### Part A -/

theorem norm_le_five_mul_norm_sin {w : ℂ} (hw : ‖w‖ < Real.pi / 4) :
    ‖w‖ ≤ 5 * ‖Complex.sin w‖ := by
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hw1 : ‖w‖ ≤ 1 := by linarith
  have h1 : ‖Complex.exp (-w * Complex.I) - 1 - (-w * Complex.I)‖ ≤ ‖w‖ ^ 2 := by
    have := Complex.norm_exp_sub_one_sub_id_le (x := -w * Complex.I) (by simpa using hw1)
    simpa using this
  have h2 : ‖Complex.exp (w * Complex.I) - 1 - (w * Complex.I)‖ ≤ ‖w‖ ^ 2 := by
    have := Complex.norm_exp_sub_one_sub_id_le (x := w * Complex.I) (by simpa using hw1)
    simpa using this
  have key : (2 : ℂ) * Complex.sin w - 2 * w =
      ((Complex.exp (-w * Complex.I) - 1 - (-w * Complex.I)) -
        (Complex.exp (w * Complex.I) - 1 - (w * Complex.I))) * Complex.I := by
    rw [Complex.two_sin]
    linear_combination (-2 * w) * Complex.I_sq
  have h3 : ‖(2 : ℂ) * Complex.sin w - 2 * w‖ ≤ 2 * ‖w‖ ^ 2 := by
    rw [key, norm_mul, Complex.norm_I, mul_one]
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have h4 : ‖(2 : ℂ) * w‖ ≤ ‖(2 : ℂ) * Complex.sin w‖ + ‖(2 : ℂ) * Complex.sin w - 2 * w‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub (2 * w) (2 * Complex.sin w) 0
    have h5 := norm_sub_norm_le ((2 : ℂ) * Complex.sin w) (2 * w)
    have h6 : ‖(2 : ℂ) * w‖ ≤ ‖(2 : ℂ) * Complex.sin w‖ + ‖(2 : ℂ) * w - 2 * Complex.sin w‖ := by
      calc ‖(2 : ℂ) * w‖ = ‖(2 * Complex.sin w) + (2 * w - 2 * Complex.sin w)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    rwa [norm_sub_rev] at h6
  rw [norm_mul, norm_mul, Complex.norm_ofNat] at h4
  nlinarith [norm_nonneg w]

/-! ### Part B: uniform asymptotics and counting on `Cset B` -/

section PartB

open NlsGge.Atomic.G1049S1

theorem unif_dirichlet_asymp {B : ℝ} (hB : 0 ≤ B) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ φ ∈ Cset B, ∀ z : ℂ, R ≤ ‖z‖ →
      ‖dirichletChar φ z - Complex.sin z‖ ≤ ε * Real.exp |z.im| := by
  choose U hU R hR using fun φ₀ : PotPair => dirichletChar_asymp φ₀ ε hε
  obtain ⟨t, -, hcov⟩ := (isCompact_Cset hB).elim_nhds_subcover U (fun x _ => hU x)
  refine ⟨∑ x ∈ t, |R x|, fun φ hφ z hz => ?_⟩
  obtain ⟨x, hx, hφx⟩ := Set.mem_iUnion₂.1 (hcov hφ)
  refine hR x φ hφx z ?_
  exact le_trans (le_trans (le_abs_self _)
    (Finset.single_le_sum (f := fun x => |R x|) (fun _ _ => abs_nonneg _) hx)) hz

theorem unif_critical_asymp {B : ℝ} (hB : 0 ≤ B) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ φ ∈ Cset B, ∀ z : ℂ, R ≤ ‖z‖ →
      ‖deriv (discrim φ) z - (-2 * Complex.sin z)‖ ≤ ε * Real.exp |z.im| := by
  choose U hU R hR using fun φ₀ : PotPair => discrimDeriv_asymp φ₀ ε hε
  obtain ⟨t, -, hcov⟩ := (isCompact_Cset hB).elim_nhds_subcover U (fun x _ => hU x)
  refine ⟨∑ x ∈ t, |R x|, fun φ hφ z hz => ?_⟩
  obtain ⟨x, hx, hφx⟩ := Set.mem_iUnion₂.1 (hcov hφ)
  refine hR x φ hφx z ?_
  exact le_trans (le_trans (le_abs_self _)
    (Finset.single_le_sum (f := fun x => |R x|) (fun _ _ => abs_nonneg _) hx)) hz

theorem unif_counting {B : ℝ} (hB : 0 ≤ B) :
    ∃ N : ℕ, 0 < N ∧ ∀ φ ∈ Cset B,
      RootCountingAt38 (dirichletChar φ) 1 N ∧ RootCountingAt38 (deriv (discrim φ)) 1 N := by
  obtain ⟨R₁, hR₁⟩ := unif_dirichlet_asymp hB (1 / (2 * sineOffDiscsConstant38))
    (one_div_pos.mpr (mul_pos (by norm_num) sineOffDiscsConstant38_pos))
  obtain ⟨R₂, hR₂⟩ := unif_critical_asymp hB (1 / sineOffDiscsConstant38)
    (one_div_pos.mpr sineOffDiscsConstant38_pos)
  obtain ⟨K, hK⟩ := exists_nat_gt (max R₁ R₂ / Real.pi)
  let N : ℕ := K + 1
  have hN : 0 < N := Nat.succ_pos K
  have hRN : max R₁ R₂ ≤ countingRadius38 N := by
    have h := (div_lt_iff₀ Real.pi_pos).mp hK
    unfold countingRadius38 N
    push_cast
    linarith [Real.pi_pos]
  refine ⟨N, hN, fun φ hφ => ⟨?_, ?_⟩⟩
  · exact dirichlet_counting_at38 φ N hN (fun z hz hsep =>
      dirichlet_strict_comparison38 (hR₁ φ hφ z ((le_max_left _ _).trans (hRN.trans hz))) hsep)
  · have hcmp : ∀ z : ℂ, countingRadius38 N ≤ ‖z‖ →
        (∀ n : ℤ, Real.pi / 4 ≤ ‖z - countingCenter38 n‖) →
        ‖deriv (discrim φ) z - deriv (NlsGge.GK38.discrim 0) z‖ < ‖deriv (NlsGge.GK38.discrim 0) z‖ := by
      intro z hz hsep
      exact critical_strict_comparison38
        (hR₂ φ hφ z ((le_max_right _ _).trans (hRN.trans hz))) hsep
    obtain ⟨hs₂, hc₂, he₂⟩ := critical_counting_at38 φ N hcmp
    have hsphere := counting_radius_mem_sphere38 N
    have hnorm : countingRadius38 N ≤ ‖(countingRadius38 N : ℂ)‖ := by
      simp [Complex.norm_real, abs_of_pos (countingRadius_pos38 N)]
    have hsep := counting_central_sphere_separated38 N hsphere
    refine ⟨hN, analyticOnNhd_discrimDeriv38 φ,
      ⟨_, critical_ne_zero_of_comparison38 (hcmp _ hnorm hsep)⟩,
      critical_zeroMult_support_finite38 φ, hs₂, ?_, he₂⟩
    simpa only [one_mul] using hc₂

theorem natAbs_lt_iff {N : ℕ} {n : ℤ} : N < n.natAbs ↔ (N : ℤ) < |n| := by
  rw [← Int.natCast_natAbs]
  exact Nat.cast_lt.symm

theorem small_mem {f : ℂ → ℂ} {N : ℕ} (h : RootCountingAt38 f 1 N) {n : ℤ} (hn : (N : ℤ) < |n|) :
    criticalCandidate38 f N n ∈ ball (countingCenter38 n) (Real.pi / 4) := by
  have hm := criticalCandidate_small_multiset38 h hn
  have hmem : criticalCandidate38 f N n ∈
      Lib.zeroMultiset f (ball (countingCenter38 n) (Real.pi / 4)) := by
    rw [← hm]; exact Multiset.mem_singleton_self _
  exact ((Lib.mem_zeroMultiset_ball (h.2.1.mono (subset_univ _))).1 hmem).1

theorem unif_localization {B : ℝ} (hB : 0 ≤ B) :
    ∃ N : ℕ, 0 < N ∧ ∀ φ ∈ Cset B, ∀ n : ℤ, N < n.natAbs →
      ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 4 ∧ dirichletChar φ (muSeq φ n) = 0 ∧
      ‖lamDot φ n - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 4 ∧ deriv (discrim φ) (lamDot φ n) = 0 := by
  obtain ⟨N, hN, h⟩ := unif_counting hB
  refine ⟨N, hN, fun φ hφ n hn => ?_⟩
  have hn' := natAbs_lt_iff.1 hn
  obtain ⟨hD, hC⟩ := h φ hφ
  refine ⟨?_, muSeq_root38 φ n, ?_, (lamDot_enumeration38 φ).1 n⟩
  · have := small_mem hD hn'
    rw [← muSeq_eq_candidate38 φ hD, Metric.mem_ball, dist_eq_norm] at this
    exact this
  · have := small_mem hC hn'
    rw [← lamDot_eq_candidate38 φ hC, Metric.mem_ball, dist_eq_norm] at this
    exact this

end PartB

/-! ### Part C: the H1 ball of `SobolevC 1` lies in `Cset B` -/

section PartC

open NlsGge.Atomic.G1049S1
open NlsGge.Pilot NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

theorem fourier_embed (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) (n : ℤ) :
    physicalFourier (physicalSobolevEmbed 1 u) n =
      -carrierCoe38 ((1 : ℕ) : ℝ) (physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ) u) (-n) := by
  have h1 := fourierSeq38_apply (physicalSobolevEmbed 1 u) (-n)
  rw [neg_neg, physicalSobolevEmbed_fourier] at h1
  rw [h1]; ring

theorem partial_sum_le (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) (F : Finset ℤ) :
    ∑ n ∈ F, (1 + (n : ℝ) ^ 2) * ‖physicalFourier (physicalSobolevEmbed 1 u) n‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  set z := physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ) u with hz
  have hu : ‖u‖ = ‖z‖ := ((physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ)).norm_map u).symm
  have hw : ∀ n : ℤ, sobolevModeWeight ((1 : ℕ) : ℝ) n = 1 + (n : ℝ) ^ 2 := fun n => by
    have := NlsGge.Analysis.japaneseBracket_h1_weight n
    simpa [sobolevModeWeight] using this
  have hs : HasSum (fun n : ℤ => sobolevModeWeight ((1 : ℕ) : ℝ) n *
      ‖carrierCoe38 ((1 : ℕ) : ℝ) z n‖ ^ 2) (‖z‖ ^ 2) :=
    weightedHilbert_hasSum (sobolevModeWeight ((1 : ℕ) : ℝ))
      (show WeightedHilbert (sobolevModeWeight ((1 : ℕ) : ℝ)) from z)
  rw [hu]
  have hsum : ∑ n ∈ F, (1 + (n : ℝ) ^ 2) * ‖physicalFourier (physicalSobolevEmbed 1 u) n‖ ^ 2 =
      ∑ m ∈ F.image Neg.neg, sobolevModeWeight ((1 : ℕ) : ℝ) m *
        ‖carrierCoe38 ((1 : ℕ) : ℝ) z m‖ ^ 2 := by
    rw [Finset.sum_image (fun x _ y _ h => neg_injective h)]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    have hneg : (((-n : ℤ) : ℝ)) ^ 2 = (n : ℝ) ^ 2 := by push_cast; ring
    rw [fourier_embed, norm_neg, hw, hneg]
  rw [hsum]
  have hle := hs.summable.sum_le_tsum (F.image Neg.neg) (fun m _ => by
    rw [hw m]; positivity)
  rwa [hs.tsum_eq] at hle

theorem embed_mem_image (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) {B : ℝ} (hu : ‖u‖ ≤ B) :
    physicalSobolevEmbed 1 u ∈ physicalFourierL2.symm '' ellipsoid B := by
  refine ⟨physicalFourierL2 (physicalSobolevEmbed 1 u), ?_, by simp⟩
  intro F
  simp only [physicalFourierL2_apply]
  exact (partial_sum_le u F).trans (pow_le_pow_left₀ (norm_nonneg _) hu 2)

theorem toPotPair_mem_Cset (φ : SobolevC 1) {B : ℝ} (h : sobolevNorm 1 φ ≤ B) :
    toPotPair φ ∈ Cset B :=
  ⟨embed_mem_image φ.1 (le_trans (NlsGge.ThirdConsultation.KSPS018Support.norm_fst_le φ) h),
   embed_mem_image φ.2 (le_trans (NlsGge.ThirdConsultation.KSPS018Support.norm_snd_le φ) h)⟩

end PartC

/-! ### Part D: bridges and the two sine inequalities -/

section PartD

open NlsGge.ThirdConsultation.KSPSVolterra (fundamental)

theorem freeE_eq_freePropagator (z : ℂ) (t : ℝ) : freeE z t = freePropagator t z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [freeE, freePropagator]

theorem monodromy_eq (φ : SobolevC 1) (lam : ℂ) :
    monodromyPair (toPotPair φ) lam = fundamental φ 1 lam := by
  rw [NlsGge.ThirdConsultation.KSPS018Support.fundamental_eq_tsum φ zero_le_one lam,
    monodromyPair_eq_fundPair]
  exact (NlsGge.Atomic.G1061S1.Mser_eq_fundPair (toPotPair φ) lam (s := 1)
    ⟨zero_le_one, le_rfl⟩).symm

theorem sin_le_of_dirichlet_root (φ : SobolevC 1) (lam : ℂ)
    (h : dirichletChar (toPotPair φ) lam = 0) :
    ‖Complex.sin lam‖ ≤ 2 * ‖fundamental φ 1 lam - freePropagator 1 lam‖ := by
  have h1 := dirichlet_residual_eq38 (toPotPair φ) lam
  have hD : monodromyPair (toPotPair φ) lam - freeE lam 1 =
      fundamental φ 1 lam - freePropagator 1 lam := by
    rw [monodromy_eq, freeE_eq_freePropagator]
  rw [hD, h, zero_sub] at h1
  set D := fundamental φ 1 lam - freePropagator 1 lam with hDdef
  have e : ‖Complex.sin lam‖ = ‖D 1 0 + D 1 1 - D 0 0 - D 0 1‖ / 2 := by
    rw [← norm_neg, h1, norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
  rw [e]
  have h10 := NlsGge.ThirdConsultation.KSPS006Support.norm_entry_le_l2 D 1 0
  have h11 := NlsGge.ThirdConsultation.KSPS006Support.norm_entry_le_l2 D 1 1
  have h00 := NlsGge.ThirdConsultation.KSPS006Support.norm_entry_le_l2 D 0 0
  have h01 := NlsGge.ThirdConsultation.KSPS006Support.norm_entry_le_l2 D 0 1
  have hn : ‖D 1 0 + D 1 1 - D 0 0 - D 0 1‖ ≤ 4 * ‖D‖ := by
    have hh := norm_sub_le (D 1 0 + D 1 1 - D 0 0) (D 0 1)
    have hh' := norm_sub_le (D 1 0 + D 1 1) (D 0 0)
    have hh'' := norm_add_le (D 1 0) (D 1 1)
    linarith
  linarith

theorem sin_le_of_critical_root (φ : SobolevC 1) (lam : ℂ)
    (h : deriv (discrim (toPotPair φ)) lam = 0) :
    ‖Complex.sin lam‖ ≤
      ‖deriv (fun l : ℂ => fundamental φ 1 l) lam - deriv (fun l : ℂ => freePropagator 1 l) lam‖ := by
  have hfun : (fun w : ℂ => ∑' m : ℕ, NlsGge.Atomic.Volterra.potentialVolterraTerm38
      (toPotPair φ) w m 1) = fun w : ℂ => fundamental φ 1 w :=
    funext fun w => (NlsGge.ThirdConsultation.KSPS018Support.fundamental_eq_tsum φ zero_le_one w).symm
  have hfree : (fun w : ℂ => NlsGge.SpectralFoundations.freeZsFundamentalComplex w 1) =
      fun w : ℂ => freePropagator 1 w :=
    funext fun w => by
      rw [← NlsGge.ThirdConsultation.KSPS018Support.E_eq_freeZs]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [NlsGge.ThirdConsultation.KSPSVolterra.E, freePropagator]
  have hd : DifferentiableAt ℂ (fun w : ℂ => ∑' m : ℕ, NlsGge.Atomic.Volterra.potentialVolterraTerm38
      (toPotPair φ) w m 1) lam := by
    rw [hfun]
    exact ((NlsGge.ThirdConsultation.KSPS018Support.analyticOnNhd_fundamental φ zero_le_one)
      lam (Set.mem_univ _)).differentiableAt
  have key := NlsGge.Atomic.G1050S2.deriv_discrim_add_two_sin (toPotPair φ) lam hd
  rw [hfun, hfree, h, zero_add] at key
  set D := deriv (fun l : ℂ => fundamental φ 1 l) lam - deriv (fun l : ℂ => freePropagator 1 l) lam
    with hDdef
  have h00 := NlsGge.ThirdConsultation.KSPS006Support.norm_entry_le_l2 D 0 0
  have h11 := NlsGge.ThirdConsultation.KSPS006Support.norm_entry_le_l2 D 1 1
  have e : ‖Complex.sin lam‖ = ‖D 0 0 + D 1 1‖ / 2 := by
    rw [Matrix.trace_fin_two] at key
    rw [← key, norm_mul, Complex.norm_ofNat]
    ring
  rw [e]
  have := norm_add_le (D 0 0) (D 1 1)
  linarith

end PartD

/-- From a sine bound `|sin z| <= K/|z|` on a root `z` of the quarter disc about `n pi`
to `|z - n pi| <= 5 K / (2 |n|)`. -/
theorem close_of_sin {z : ℂ} {n : ℤ} {K : ℝ} (hz : ‖z - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 4)
    (hn : 1 ≤ n.natAbs) (hK : 0 ≤ K) (hsin : ‖Complex.sin z‖ ≤ K / ‖z‖) :
    ‖z - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 5 * (K / (2 * (n.natAbs : ℝ))) := by
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi' : 3.14 < Real.pi := Real.pi_gt_d2
  have hm : ‖(n : ℂ)‖ = (n.natAbs : ℝ) := by
    rw [Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs]
  have hn1 : (1 : ℝ) ≤ n.natAbs := by exact_mod_cast hn
  have hnz : ‖(n : ℂ) * (Real.pi : ℂ)‖ = (n.natAbs : ℝ) * Real.pi := by
    rw [norm_mul, hm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hzn : (2 : ℝ) * n.natAbs ≤ ‖z‖ := by
    have h1 := norm_sub_norm_le ((n : ℂ) * (Real.pi : ℂ)) z
    rw [norm_sub_rev, hnz] at h1
    have hmpi : 3.14 * (n.natAbs : ℝ) ≤ (n.natAbs : ℝ) * Real.pi := by nlinarith
    linarith
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (by positivity) hzn
  have hcos : ‖Complex.cos ((n : ℂ) * (Real.pi : ℂ))‖ = 1 := by
    have h := Complex.sin_sq_add_cos_sq ((n : ℂ) * (Real.pi : ℂ))
    rw [Complex.sin_int_mul_pi] at h
    have h2 : Complex.cos ((n : ℂ) * (Real.pi : ℂ)) ^ 2 = 1 := by simpa using h
    have h3 : ‖Complex.cos ((n : ℂ) * (Real.pi : ℂ))‖ ^ 2 = 1 := by
      rw [← norm_pow, h2, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3
  have hnorm : ‖Complex.sin (z - (n : ℂ) * (Real.pi : ℂ))‖ = ‖Complex.sin z‖ := by
    rw [Complex.sin_sub, Complex.sin_int_mul_pi, mul_zero, sub_zero, norm_mul, hcos, mul_one]
  have h5 := norm_le_five_mul_norm_sin hz
  rw [hnorm] at h5
  refine h5.trans ?_
  have : K / ‖z‖ ≤ K / (2 * (n.natAbs : ℝ)) :=
    div_le_div_of_nonneg_left hK (by positivity) hzn
  linarith

end NlsGge.ThirdConsultation.KSPS019Support
