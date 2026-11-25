import Mathlib
import NlsGge.Atomic.G1.G1004
import NlsGge.Atomic.G1.G1040
import NlsGge.Atomic.Volterra
import NlsGge.GK38.PairPotential
import NlsGge.GK38.PairVolterra
import NlsGge.GK38.PairVolterraProbe
import NlsGge.GK38.PeriodicLabellingCounting
import NlsGge.GK38.CountingLemma
import NlsGge.Sobolev.PeriodicBridge
import NlsGge.Atomic.G1.G1047
import NlsGge.Atomic.G1.G1048

/- G1-049 production: the G1-047 and G1-048 private copies of the reviewed candidate (namespaces G1047S2, G1048S3, verbatim) are replaced by `import NlsGge.Atomic.G1.G1047` and `import NlsGge.Atomic.G1.G1048`. -/

set_option autoImplicit false

open MeasureTheory Filter Topology Set NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations
  NlsGge.Atomic.G1004GenT
open scoped Matrix.Norms.L2Operator
-- file-level opens that sat between the removed G1047S2 blocks in the reviewed candidate (kept: the remaining code was compiled with them active)
open NlsGge.Atomic.G1047S2.K17.K16
open NlsGge.Pilot



                                                                                
                                                                                                                                
                                                                                                                                
                                                                                                                                                                                                               
                                                                                                                                
                                                                                                                          
                                                                                                                     
                                                                                                                                                            

open scoped ENNReal

namespace NlsGge.Atomic.G1049S1

noncomputable section

/-- The Hilbert space `ℓ²(ℤ; ℂ)`. -/
abbrev L2Seq : Type := lp (fun _ : ℤ => ℂ) 2

/-- The `H¹`-ellipsoid of radius `B`: every finite weighted partial sum is at most `B²`. -/
def ellipsoid (B : ℝ) : Set L2Seq :=
  {x | ∀ F : Finset ℤ, ∑ n ∈ F, (1 + (n : ℝ) ^ 2) * ‖x n‖ ^ 2 ≤ B ^ 2}

theorem continuous_coord (n : ℤ) : Continuous (fun x : L2Seq => x n) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun x y => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  have := lp.norm_apply_le_norm (p := (2 : ℝ≥0∞)) (by norm_num) (x - y) n
  simpa using this

theorem isClosed_ellipsoid (B : ℝ) : IsClosed (ellipsoid B) := by
  have : ellipsoid B = ⋂ F : Finset ℤ, {x : L2Seq | ∑ n ∈ F, (1 + (n : ℝ) ^ 2) * ‖x n‖ ^ 2 ≤ B ^ 2} := by
    ext x; simp [ellipsoid]
  rw [this]
  refine isClosed_iInter fun F => isClosed_le ?_ continuous_const
  exact continuous_finset_sum _ fun n _ => continuous_const.mul ((continuous_coord n).norm.pow 2)

theorem sq_norm_hasSum (x : L2Seq) : HasSum (fun n : ℤ => ‖x n‖ ^ 2) (‖x‖ ^ 2) := by
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) x
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

theorem norm_le_of_mem_ellipsoid {B : ℝ} (hB : 0 ≤ B) {x : L2Seq} (hx : x ∈ ellipsoid B) :
    ‖x‖ ≤ B := by
  have h1 : ‖x‖ ^ 2 ≤ B ^ 2 := by
    refine hasSum_le_of_sum_le (sq_norm_hasSum x) fun F => ?_
    refine le_trans (Finset.sum_le_sum fun n _ => ?_) (hx F)
    have : (0 : ℝ) ≤ ‖x n‖ ^ 2 := sq_nonneg _
    nlinarith [sq_nonneg (n : ℝ)]
  by_contra h
  push_neg at h
  nlinarith [norm_nonneg x]

/-- Coordinate truncation to a finite set of modes. -/
def proj (S : Finset ℤ) (x : L2Seq) : L2Seq := ∑ n ∈ S, x n • lp.single 2 n (1 : ℂ)

theorem proj_apply (S : Finset ℤ) (x : L2Seq) (m : ℤ) :
    proj S x m = if m ∈ S then x m else 0 := by
  unfold proj
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.coeFn_smul, Pi.smul_apply, lp.single_apply, Pi.single_apply, smul_eq_mul]
  simp [Finset.sum_ite_eq]

theorem totallyBounded_ellipsoid {B : ℝ} (hB : 0 ≤ B) : TotallyBounded (ellipsoid B) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * B / ε)
  set S : Finset ℤ := Finset.Icc (-(M : ℤ)) M with hS
  let V : Submodule ℂ L2Seq :=
    Submodule.span ℂ (Set.range fun n : S => lp.single (E := fun _ : ℤ => ℂ) 2 (n : ℤ) (1 : ℂ))
  haveI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  haveI : ProperSpace V := FiniteDimensional.proper_rclike ℂ V
  have hmem : ∀ x, proj S x ∈ V := by
    intro x
    unfold proj
    refine Submodule.sum_mem _ fun n hn => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨n, hn⟩, rfl⟩)
  let C : Set L2Seq := ((↑) : V → L2Seq) '' Metric.closedBall (0 : V) (B + ε / 2)
  have hC : IsCompact C := (isCompact_closedBall _ _).image continuous_subtype_val
  obtain ⟨t, htfin, htcov⟩ := Metric.totallyBounded_iff.1 hC.totallyBounded (ε / 2) (by positivity)
  refine ⟨t, htfin, fun x hx => ?_⟩
  -- tail estimate
  have htail : ‖x - proj S x‖ ^ 2 * ((M : ℝ) + 1) ^ 2 ≤ B ^ 2 := by
    have hs := (sq_norm_hasSum (x - proj S x)).mul_right (((M : ℝ) + 1) ^ 2)
    refine hasSum_le_of_sum_le hs fun F => ?_
    refine le_trans (Finset.sum_le_sum fun n _ => ?_) (hx F)
    have hc : (x - proj S x) n = if n ∈ S then 0 else x n := by
      rw [lp.coeFn_sub, Pi.sub_apply, proj_apply]
      split_ifs <;> simp
    rw [hc]
    by_cases hn : n ∈ S
    · simp only [hn, if_true, norm_zero]
      have : (0 : ℝ) ≤ (1 + (n : ℝ) ^ 2) * ‖x n‖ ^ 2 := by positivity
      simpa using this
    · simp only [hn, if_false]
      have hn' : ¬ (-(M : ℤ) ≤ n ∧ n ≤ M) := by simpa [hS] using hn
      have habs : (M : ℝ) + 1 ≤ |(n : ℝ)| := by
        have : (M : ℤ) + 1 ≤ |n| := by
          rw [not_and_or] at hn'
          rcases hn' with h | h
          · rw [abs_of_neg (by omega)]; omega
          · rw [abs_of_pos (by omega)]; omega
        exact_mod_cast this
      have hsq : ((M : ℝ) + 1) ^ 2 ≤ (n : ℝ) ^ 2 := by
        rw [← sq_abs (n : ℝ)]
        exact pow_le_pow_left₀ (by positivity) habs 2
      have : ((M : ℝ) + 1) ^ 2 ≤ 1 + (n : ℝ) ^ 2 := by linarith
      calc ‖x n‖ ^ 2 * ((M : ℝ) + 1) ^ 2 ≤ ‖x n‖ ^ 2 * (1 + (n : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left this (sq_nonneg _)
        _ = _ := by ring
  have hxB : ‖x‖ ≤ B := norm_le_of_mem_ellipsoid hB hx
  have hsmall : ‖x - proj S x‖ < ε / 2 := by
    by_contra hcon
    push_neg at hcon
    have hM1 : 2 * B / ε < (M : ℝ) + 1 := by linarith
    have h2 : 2 * B < ((M : ℝ) + 1) * ε := by
      have := (div_lt_iff₀ hε).1 hM1
      linarith
    have h3 : ((M : ℝ) + 1) * (ε / 2) ≤ ((M : ℝ) + 1) * ‖x - proj S x‖ :=
      mul_le_mul_of_nonneg_left hcon (by positivity)
    have h4 : (((M : ℝ) + 1) * ‖x - proj S x‖) ^ 2 ≤ B ^ 2 := by
      calc _ = ‖x - proj S x‖ ^ 2 * ((M : ℝ) + 1) ^ 2 := by ring
        _ ≤ _ := htail
    have h5 : ((M : ℝ) + 1) * ‖x - proj S x‖ ≤ B := by
      by_contra h; push_neg at h
      nlinarith [norm_nonneg (x - proj S x)]
    nlinarith
  have hPx : proj S x ∈ C := by
    refine ⟨⟨proj S x, hmem x⟩, ?_, rfl⟩
    rw [mem_closedBall_zero_iff]
    show ‖proj S x‖ ≤ B + ε / 2
    have : proj S x = x - (x - proj S x) := by abel
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    linarith
  obtain ⟨y, hy, hdist⟩ := Set.mem_iUnion₂.1 (htcov hPx)
  refine Set.mem_iUnion₂.2 ⟨y, hy, ?_⟩
  rw [Metric.mem_ball] at hdist ⊢
  calc dist x y ≤ dist x (proj S x) + dist (proj S x) y := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
        rw [dist_eq_norm]
        exact add_lt_add hsmall hdist
    _ = ε := by ring

theorem isCompact_ellipsoid {B : ℝ} (hB : 0 ≤ B) : IsCompact (ellipsoid B) :=
  isCompact_iff_totallyBounded_isComplete.2 ⟨totallyBounded_ellipsoid hB, (isClosed_ellipsoid B).isComplete⟩


end

end NlsGge.Atomic.G1049S1

namespace NlsGge.Atomic.G1049S1

open Filter Topology Set Metric NlsGge.GK38

noncomputable section

/-- The compact `L² × L²` set containing the `H¹` ball. -/
def Cset (B : ℝ) : Set PotPair :=
  (NlsGge.Pilot.physicalFourierL2.symm '' ellipsoid B) ×ˢ (NlsGge.Pilot.physicalFourierL2.symm '' ellipsoid B)

theorem isCompact_Cset {B : ℝ} (hB : 0 ≤ B) : IsCompact (Cset B) :=
  ((isCompact_ellipsoid hB).image NlsGge.Pilot.physicalFourierL2.symm.continuous).prod
    ((isCompact_ellipsoid hB).image NlsGge.Pilot.physicalFourierL2.symm.continuous)

theorem japaneseBracket_sq (n : ℤ) : NlsGge.Pilot.japaneseBracket n ^ 2 = 1 + (n : ℝ) ^ 2 := by
  unfold NlsGge.Pilot.japaneseBracket
  rw [Real.sq_sqrt (by positivity)]

theorem mem_Cset {B : ℝ} (φ : PotPair)
    (hsum : Summable (fun n : ℤ => NlsGge.Pilot.japaneseBracket n ^ 2 *
        (‖NlsGge.Pilot.physicalFourier (φ.1 : NlsGge.Pilot.PhysicalCircle → ℂ) n‖ ^ 2 +
          ‖NlsGge.Pilot.physicalFourier (φ.2 : NlsGge.Pilot.PhysicalCircle → ℂ) n‖ ^ 2)))
    (hle : Real.sqrt (∑' n : ℤ, NlsGge.Pilot.japaneseBracket n ^ 2 *
        (‖NlsGge.Pilot.physicalFourier (φ.1 : NlsGge.Pilot.PhysicalCircle → ℂ) n‖ ^ 2 +
          ‖NlsGge.Pilot.physicalFourier (φ.2 : NlsGge.Pilot.PhysicalCircle → ℂ) n‖ ^ 2)) ≤ B) :
    φ ∈ Cset B := by
  have hts : (∑' n : ℤ, NlsGge.Pilot.japaneseBracket n ^ 2 *
        (‖NlsGge.Pilot.physicalFourier (φ.1 : NlsGge.Pilot.PhysicalCircle → ℂ) n‖ ^ 2 +
          ‖NlsGge.Pilot.physicalFourier (φ.2 : NlsGge.Pilot.PhysicalCircle → ℂ) n‖ ^ 2)) ≤ B ^ 2 :=
    ((Real.sqrt_le_iff.1 hle).2)
  have hF : ∀ F : Finset ℤ, ∑ n ∈ F, NlsGge.Pilot.japaneseBracket n ^ 2 *
        (‖NlsGge.Pilot.physicalFourier (φ.1 : NlsGge.Pilot.PhysicalCircle → ℂ) n‖ ^ 2 +
          ‖NlsGge.Pilot.physicalFourier (φ.2 : NlsGge.Pilot.PhysicalCircle → ℂ) n‖ ^ 2) ≤ B ^ 2 :=
    fun F => (hsum.sum_le_tsum F (fun n _ => by positivity)).trans hts
  refine ⟨⟨NlsGge.Pilot.physicalFourierL2 φ.1, ?_, by simp⟩, ⟨NlsGge.Pilot.physicalFourierL2 φ.2, ?_, by simp⟩⟩
  · intro F
    refine le_trans (Finset.sum_le_sum fun n _ => ?_) (hF F)
    rw [NlsGge.Pilot.physicalFourierL2_apply, japaneseBracket_sq]
    have := sq_nonneg ‖NlsGge.Pilot.physicalFourier (φ.2 : NlsGge.Pilot.PhysicalCircle → ℂ) n‖
    have h0 : (0 : ℝ) ≤ 1 + (n : ℝ) ^ 2 := by positivity
    nlinarith [mul_nonneg h0 this]
  · intro F
    refine le_trans (Finset.sum_le_sum fun n _ => ?_) (hF F)
    rw [NlsGge.Pilot.physicalFourierL2_apply, japaneseBracket_sq]
    have := sq_nonneg ‖NlsGge.Pilot.physicalFourier (φ.1 : NlsGge.Pilot.PhysicalCircle → ℂ) n‖
    have h0 : (0 : ℝ) ≤ 1 + (n : ℝ) ^ 2 := by positivity
    nlinarith [mul_nonneg h0 this]

theorem uniform_cmp (K : Set PotPair) (hK : IsCompact K) :
    ∃ R : ℝ, ∀ φ ∈ K, ∀ z : ℂ, R ≤ ‖z‖ →
      (∀ n : ℤ, Real.pi / 4 ≤ ‖z - countingCenter38 n‖) →
      ‖perChar φ z - perChar 0 z‖ < ‖perChar 0 z‖ := by
  choose U hU R hR using fun φ₀ : PotPair => NlsGge.Atomic.G1048S3.perChar_cmp_s3 φ₀
  obtain ⟨t, -, hcov⟩ := hK.elim_nhds_subcover U (fun x _ => hU x)
  refine ⟨∑ x ∈ t, |R x|, fun φ hφ z hz hsep => ?_⟩
  obtain ⟨x, hx, hφx⟩ := Set.mem_iUnion₂.1 (hcov hφ)
  refine hR x φ hφx z ?_ hsep
  exact le_trans (le_trans (le_abs_self _)
    (Finset.single_le_sum (f := fun x => |R x|) (fun _ _ => abs_nonneg _) hx)) hz

theorem G1049_whole : ((
  ∀ B : ℝ, 0 ≤ B →
  ∃ N : ℕ, 0 < N ∧
  ∀ φ : PotPair,
    (Summable (fun n : ℤ => NlsGge.Pilot.japaneseBracket n ^ 2 *
        (‖NlsGge.Pilot.physicalFourier (φ.1 : NlsGge.Pilot.PhysicalCircle → ℂ) n‖ ^ 2 +
          ‖NlsGge.Pilot.physicalFourier (φ.2 : NlsGge.Pilot.PhysicalCircle → ℂ) n‖ ^ 2)) ∧
      Real.sqrt (∑' n : ℤ, NlsGge.Pilot.japaneseBracket n ^ 2 *
        (‖NlsGge.Pilot.physicalFourier (φ.1 : NlsGge.Pilot.PhysicalCircle → ℂ) n‖ ^ 2 +
          ‖NlsGge.Pilot.physicalFourier (φ.2 : NlsGge.Pilot.PhysicalCircle → ℂ) n‖ ^ 2)) ≤ B) →
    ((∀ n : ℤ, N < n.natAbs →
        Multiset.card (Lib.zeroMultiset (fun w : ℂ => perChar φ w)
          (Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4))) = 2) ∧
      Multiset.card (Lib.zeroMultiset (fun w : ℂ => perChar φ w)
        (Metric.ball (0 : ℂ) ((N : ℝ) * Real.pi + Real.pi / 4))) = 4 * N + 2 ∧
      (∀ w : ℂ, perChar φ w = 0 →
        w ∈ Metric.ball (0 : ℂ) ((N : ℝ) * Real.pi + Real.pi / 4) ∨
        ∃ n : ℤ, N < n.natAbs ∧ w ∈ Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4)))
  : Prop)) := by
  intro B hB
  obtain ⟨R, hR⟩ := uniform_cmp (Cset B) (isCompact_Cset hB)
  obtain ⟨K, hK⟩ := exists_nat_gt (R / Real.pi)
  let N : ℕ := K + 1
  have hNpos : 0 < N := Nat.succ_pos K
  have hRN : R ≤ countingRadius38 N := by
    have h := (div_lt_iff₀ Real.pi_pos).mp hK
    unfold countingRadius38 N
    push_cast
    linarith [Real.pi_pos]
  refine ⟨N, hNpos, fun φ hφ => ?_⟩
  obtain ⟨h1, h2, h3⟩ := periodic_counting_at38 φ N
    (fun z hz hsep => hR φ (mem_Cset φ hφ.1 hφ.2) z (hRN.trans hz) hsep)
  refine ⟨fun n hn => h1 n (NlsGge.Atomic.G1048S3.natAbs_iff.1 hn), h2, fun w hw => ?_⟩
  rcases h3 w hw with h4 | ⟨n, hn, h5⟩
  · exact Or.inl h4
  · exact Or.inr ⟨n, NlsGge.Atomic.G1048S3.natAbs_iff.2 hn, h5⟩

end

end NlsGge.Atomic.G1049S1
