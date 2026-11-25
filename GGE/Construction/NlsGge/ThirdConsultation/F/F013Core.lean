import Mathlib
import NlsGge.Hierarchy.RiccatiSmoothDenseSobolev38
import NlsGge.Hierarchy.RiccatiLocalRemainderPaperForm38
import NlsGge.Birkhoff.F05Identity38
import NlsGge.Atomic.F.F011

                                                                                                            
                                                                                                              
                                                                                                                       
                                                                                                                  
                                                                                                                
                                                                                                       
                                                                                     
                                                                                                             
                                                                                                                     
set_option autoImplicit false
open MeasureTheory Filter Topology
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core

namespace NlsGge.ThirdConsultation.F013X
noncomputable section

/-- Coefficients of a Sobolev element (the body of `F.sobolevCoe`). -/
abbrev co (r : ℝ) (y : SobolevHilbert r) : ℤ → ℂ :=
  fun n => (show WeightedHilbert (sobolevModeWeight r) from y) n

/-- The weighted quadratic form (the body of `F.finiteA` after unfolding `sobolevCoe`). -/
abbrev qA (m : ℕ) (β : ℕ → ℝ) (x : Hm1 m) : ℝ :=
  ∑' n : ℤ, finiteHierarchyRate38 m β n * ‖co _ x n‖ ^ 2

/-! ### Pure pieces -/

theorem rate_nonneg (m : ℕ) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j) (n : ℤ) :
    0 ≤ finiteHierarchyRate38 m β n := by
  unfold finiteHierarchyRate38 finiteHierarchyW38
  refine Finset.sum_nonneg (fun j hj => mul_nonneg (hβ j (by have := Finset.mem_range.1 hj; omega)).le ?_)
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg _) _

theorem sobolevModeWeight_nat (k : ℕ) (n : ℤ) :
    sobolevModeWeight (k : ℝ) n = (1 + (n : ℝ) ^ 2) ^ k := by
  unfold sobolevModeWeight japaneseBracket
  show Real.sqrt (1 + (n : ℝ) ^ 2) ^ (2 * (k : ℝ)) = _
  rw [show (2 * (k : ℝ)) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, pow_mul,
    Real.sq_sqrt (by positivity)]

/-- Σ a_{m,n} |v_n|² ≤ C ‖v‖²_{H^m}, with summability. -/
theorem rate_tsum_le (m : ℕ) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SobolevHilbert (m : ℝ),
      Summable (fun n : ℤ => finiteHierarchyRate38 m β n * ‖co _ v n‖ ^ 2) ∧
      ∑' n : ℤ, finiteHierarchyRate38 m β n * ‖co _ v n‖ ^ 2 ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨C, hC, hrate⟩ := NlsGge.Atomic.F011.rate_upper_comparison m β (fun i hi => (hβ i hi).le)
  refine ⟨C, hC, fun v => ?_⟩
  have hs := weightedHilbert_hasSum (sobolevModeWeight (m : ℝ))
    (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from v)
  have hle : ∀ n : ℤ, finiteHierarchyRate38 m β n * ‖co _ v n‖ ^ 2 ≤
      C * (sobolevModeWeight (m : ℝ) n * ‖co _ v n‖ ^ 2) := by
    intro n
    rw [← mul_assoc, sobolevModeWeight_nat]
    exact mul_le_mul_of_nonneg_right (hrate n) (sq_nonneg _)
  have hnn : ∀ n : ℤ, 0 ≤ finiteHierarchyRate38 m β n * ‖co _ v n‖ ^ 2 :=
    fun n => mul_nonneg (rate_nonneg m β hβ n) (sq_nonneg _)
  have hmaj := hs.summable.mul_left C
  have hsum := Summable.of_nonneg_of_le hnn hle hmaj
  refine ⟨hsum, ?_⟩
  calc _ ≤ ∑' n : ℤ, C * (sobolevModeWeight (m : ℝ) n * ‖co _ v n‖ ^ 2) :=
        hsum.tsum_le_tsum hle hmaj
    _ = C * ‖v‖ ^ 2 := by rw [tsum_mul_left, hs.tsum_eq]; rfl

/-- Pythagoras under truncation: p supported in [−N, N]. -/
theorem split_trunc (a : ℤ → ℝ) (N : ℕ) (p q : ℤ → ℂ)
    (hp : ∀ n ∉ Finset.Icc (-(N : ℤ)) N, p n = 0)
    (hq : Summable (fun n => a n * ‖q n‖ ^ 2)) (ha : ∀ n, 0 ≤ a n) :
    Summable (fun n => a n * ‖p n + truncCoeff38 N q n‖ ^ 2) ∧
    Summable (fun n => a n * ‖q n - truncCoeff38 N q n‖ ^ 2) ∧
    ∑' n, a n * ‖p n + q n‖ ^ 2 =
      ∑' n, a n * ‖p n + truncCoeff38 N q n‖ ^ 2 + ∑' n, a n * ‖q n - truncCoeff38 N q n‖ ^ 2 := by
  have h1 : Summable (fun n => a n * ‖p n + truncCoeff38 N q n‖ ^ 2) := by
    apply summable_of_ne_finset_zero (s := Finset.Icc (-(N : ℤ)) N)
    intro n hn
    simp [truncCoeff38, hn, hp n hn]
  have h2 : Summable (fun n => a n * ‖q n - truncCoeff38 N q n‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (ha n) (sq_nonneg _)) (fun n => ?_) hq
    unfold truncCoeff38
    split_ifs <;> simp [mul_nonneg (ha n) (sq_nonneg _)]
  have hpt : ∀ n, a n * ‖p n + q n‖ ^ 2 =
      a n * ‖p n + truncCoeff38 N q n‖ ^ 2 + a n * ‖q n - truncCoeff38 N q n‖ ^ 2 := by
    intro n
    unfold truncCoeff38
    by_cases hn : n ∈ Finset.Icc (-(N : ℤ)) N
    · simp [hn]
    · simp [hn, hp n hn]
  refine ⟨h1, h2, ?_⟩
  rw [← (h1.tsum_add h2)]
  exact tsum_congr hpt

/-- ‖y − P_N y‖ ≤ ‖y‖. -/
theorem norm_sub_trunc_le (r : ℝ) (N : ℕ) (y : SobolevHilbert r) :
    ‖y - truncSobolev38 r N y‖ ≤ ‖y‖ := by
  have h := truncW38_norm_sq (sobolevModeWeight r) N (show WeightedHilbert (sobolevModeWeight r) from y)
  have hS : 0 ≤ ∑ n ∈ Finset.Icc (-(N : ℤ)) N, sobolevModeWeight r n *
      ‖((show WeightedHilbert (sobolevModeWeight r) from y) : ℤ → ℂ) n‖ ^ 2 :=
    Finset.sum_nonneg (fun n _ => mul_nonneg (sobolevModeWeight_pos r n).le (sq_nonneg _))
  have h2 : ‖y - truncSobolev38 r N y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    change ‖(show WeightedHilbert (sobolevModeWeight r) from y) -
        truncW38 (sobolevModeWeight r) N (show WeightedHilbert (sobolevModeWeight r) from y)‖ ^ 2 ≤
      ‖(show WeightedHilbert (sobolevModeWeight r) from y)‖ ^ 2
    rw [h]; linarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

theorem trunc_sub (r : ℝ) (N : ℕ) (y z : SobolevHilbert r) :
    truncSobolev38 r N (y - z) = truncSobolev38 r N y - truncSobolev38 r N z := by
  refine carrierExt38 (r := r) (funext fun n => ?_)
  change (if n ∈ Finset.Icc (-(N : ℤ)) N then co r y n - co r z n else 0) =
    (if n ∈ Finset.Icc (-(N : ℤ)) N then co r y n else 0) -
      (if n ∈ Finset.Icc (-(N : ℤ)) N then co r z n else 0)
  split_ifs <;> simp

/-- For a convergent sequence, ‖v_N − P_N v_N‖ → 0. -/
theorem tendsto_sub_trunc (r : ℝ) (v : ℕ → SobolevHilbert r) (v0 : SobolevHilbert r)
    (hv : Tendsto v atTop (𝓝 v0)) :
    Tendsto (fun N => ‖v N - truncSobolev38 r N (v N)‖) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N => ‖v N - v0‖) atTop (𝓝 0) := by
    have := (hv.sub_const v0).norm
    simpa using this
  have h2 : Tendsto (fun N => ‖v0 - truncSobolev38 r N v0‖) atTop (𝓝 0) := by
    have := ((tendsto_truncSobolev38 r v0).const_sub v0).norm
    simpa using this
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) (by simpa using h1.add h2)
  have e : v N - truncSobolev38 r N (v N) =
      ((v N - v0) - truncSobolev38 r N (v N - v0)) + (v0 - truncSobolev38 r N v0) := by
    rw [trunc_sub]; abel
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add (norm_sub_trunc_le r N _) le_rfl)

/-! ### The core -/

theorem core (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j)
    (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
    (L : SobolevHilbert (m : ℝ) → Hm1 m) (hL : ∀ y n, co _ (L y) n = co _ y n)
    (T : Hm1 m → Hm1 m) (hT : ∀ x n, co _ (T x) n = B.T (co _ x) n)
    (D : Hm1 m → ℝ) (hDc : Continuous D)
    (hDid : ∀ h : SobolevHilbert (m : ℝ),
      Summable (fun n : ℤ => finiteHierarchyRate38 m β n * ‖co _ (L h) n‖ ^ 2) ∧
      D (L h) = qA m β (T (L h)) - qA m β (L h)) :
    ∃ K : Hm1 m → SobolevHilbert (m : ℝ),
      Continuous K ∧
      (∀ x : Hm1 m, L (K x) = T x - x) ∧
      ∀ x : Hm1 m,
        Tendsto (fun N => K (truncSobolev38 _ N x)) atTop (nhds (K x)) ∧
        (∀ N : ℕ,
          Summable (fun n : ℤ => finiteHierarchyRate38 m β n *
            ‖co _ (L (K (truncSobolev38 _ N x)) -
              truncSobolev38 _ N (L (K (truncSobolev38 _ N x)))) n‖ ^ 2) ∧
          qA m β (truncSobolev38 _ N (T (truncSobolev38 _ N x))) -
            qA m β (truncSobolev38 _ N x) =
          D (truncSobolev38 _ N x) -
            qA m β (L (K (truncSobolev38 _ N x)) -
              truncSobolev38 _ N (L (K (truncSobolev38 _ N x))))) ∧
        Tendsto (fun N => qA m β
          (L (K (truncSobolev38 _ N x)) -
            truncSobolev38 _ N (L (K (truncSobolev38 _ N x)))))
          atTop (nhds 0) ∧
        Tendsto (fun N =>
          qA m β (truncSobolev38 _ N (T (truncSobolev38 _ N x))) -
            qA m β (truncSobolev38 _ N x)) atTop (nhds (D x)) := by
  have hk : 1 ≤ m - 1 := by omega
  have hcast : (m : ℝ) ≤ (((m - 1 + 1 : ℕ)) : ℝ) := by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
  let Kc : SobolevCarrier38 ((m - 1 : ℕ) : ℝ) → SobolevCarrier38 (((m - 1 + 1 : ℕ)) : ℝ) :=
    carrierMap38 ((m - 1 : ℕ) : ℝ) (((m - 1 + 1 : ℕ)) : ℝ) (fun z => B.T z - z) (O.smooth_T (m - 1) hk)
  have hKc : Continuous Kc := continuousOn_univ.1 (O.analytic_smooth_T (m - 1) hk).continuousOn
  let K : Hm1 m → SobolevHilbert (m : ℝ) := fun x =>
    ofCarrier38 (m : ℝ) (carrierIncl38 hcast (Kc (toCarrier38 _ x)))
  have hKcont : Continuous K :=
    (continuous_ofCarrier38 _).comp ((carrierIncl38 hcast).continuous.comp
      (hKc.comp (continuous_toCarrier38 _)))
  have hKco : ∀ x n, co _ (K x) n = B.T (co _ x) n - co _ x n := by
    intro x n
    show carrierCoe38 (m : ℝ) (carrierIncl38 hcast (Kc (toCarrier38 _ x))) n = _
    rw [carrierCoe38_incl38]
    rfl
  have hLK : ∀ x, L (K x) = T x - x := by
    intro x
    apply carrierExt38
    funext n
    change co _ (L (K x)) n = co _ (T x - x) n
    rw [hL, hKco]
    change _ = co _ (T x) n - co _ x n
    rw [hT]
  obtain ⟨C, hC, hrate⟩ := rate_tsum_le m β hβ
  refine ⟨K, hKcont, hLK, fun x => ?_⟩
  set xN : ℕ → Hm1 m := fun N => truncSobolev38 _ N x with hxN
  have hxt : Tendsto xN atTop (𝓝 x) := tendsto_truncSobolev38 _ x
  -- finite identity at each N
  have hfin : ∀ N : ℕ,
      Summable (fun n : ℤ => finiteHierarchyRate38 m β n *
        ‖co _ (L (K (xN N)) - truncSobolev38 _ N (L (K (xN N)))) n‖ ^ 2) ∧
      qA m β (truncSobolev38 _ N (T (xN N))) - qA m β (xN N) =
        D (xN N) - qA m β (L (K (xN N)) - truncSobolev38 _ N (L (K (xN N)))) := by
    intro N
    -- lift of the truncation to H^m
    have hsupp : ∀ n ∉ Finset.Icc (-(N : ℤ)) N, co _ (xN N) n = 0 := by
      intro n hn
      show (if n ∈ Finset.Icc (-(N : ℤ)) N then _ else 0) = 0
      rw [if_neg hn]
    have hmem : co _ (xN N) ∈ seqSobolev38 (m : ℝ) := by
      rw [mem_seqSobolev38_iff]
      unfold SobolevSquareSummable
      apply summable_of_ne_finset_zero (s := Finset.Icc (-(N : ℤ)) N)
      intro n hn
      simp [hsupp n hn]
    let hN : SobolevHilbert (m : ℝ) := ofCarrier38 _ (carrierMk38 (m : ℝ) (co _ (xN N)) hmem)
    have hLh : L hN = xN N := by
      apply carrierExt38
      funext n
      change co _ (L hN) n = co _ (xN N) n
      rw [hL]
      rfl
    obtain ⟨-, hD⟩ := hDid hN
    rw [hLh] at hD
    obtain ⟨hsK, -⟩ := hDid (K (xN N))
    -- coefficients of T (xN N)
    have hTco : ∀ n, co _ (T (xN N)) n = co _ (xN N) n + co _ (L (K (xN N))) n := by
      intro n
      rw [hLK]
      change _ = co _ (xN N) n + (co _ (T (xN N)) n - co _ (xN N) n)
      ring
    obtain ⟨hs1, hs2, hsplit⟩ := split_trunc (finiteHierarchyRate38 m β) N (co _ (xN N))
      (co _ (L (K (xN N)))) hsupp hsK (rate_nonneg m β hβ)
    have hA1 : qA m β (T (xN N)) = ∑' n, finiteHierarchyRate38 m β n *
        ‖co _ (xN N) n + co _ (L (K (xN N))) n‖ ^ 2 := by
      unfold qA
      exact tsum_congr (fun n => by rw [hTco])
    have hEq : ∀ n, co _ (truncSobolev38 _ N (T (xN N))) n =
        co _ (xN N) n + truncCoeff38 N (co _ (L (K (xN N)))) n := by
      intro n
      change (if n ∈ Finset.Icc (-(N : ℤ)) N then co _ (T (xN N)) n else 0) = _
      rw [hTco]
      unfold truncCoeff38
      by_cases hn : n ∈ Finset.Icc (-(N : ℤ)) N
      · simp [hn]
      · simp [hn, hsupp n hn]
    have hA2 : qA m β (truncSobolev38 _ N (T (xN N))) = ∑' n, finiteHierarchyRate38 m β n *
        ‖co _ (xN N) n + truncCoeff38 N (co _ (L (K (xN N)))) n‖ ^ 2 := by
      unfold qA
      exact tsum_congr (fun n => by rw [hEq])
    have hA3 : qA m β (L (K (xN N)) - truncSobolev38 _ N (L (K (xN N)))) =
        ∑' n, finiteHierarchyRate38 m β n *
          ‖co _ (L (K (xN N))) n - truncCoeff38 N (co _ (L (K (xN N)))) n‖ ^ 2 := rfl
    refine ⟨hs2, ?_⟩
    rw [hA2, hA3, hD, hA1, hsplit]
    ring
  -- vanishing tail
  have htail : Tendsto (fun N => qA m β (L (K (xN N)) - truncSobolev38 _ N (L (K (xN N)))))
      atTop (𝓝 0) := by
    have hv : Tendsto (fun N => K (xN N)) atTop (𝓝 (K x)) := (hKcont.tendsto x).comp hxt
    have hsq := (tendsto_sub_trunc (m : ℝ) (fun N => K (xN N)) (K x) hv).pow 2
    rw [zero_pow two_ne_zero] at hsq
    refine squeeze_zero (fun N => tsum_nonneg (fun n => mul_nonneg (rate_nonneg m β hβ n)
      (sq_nonneg _))) (fun N => ?_) (by simpa using hsq.const_mul C)
    have hco : ∀ n, co _ (L (K (xN N)) - truncSobolev38 _ N (L (K (xN N)))) n =
        co _ (K (xN N) - truncSobolev38 _ N (K (xN N))) n := by
      intro n
      change co _ (L (K (xN N))) n - (if n ∈ Finset.Icc (-(N : ℤ)) N then co _ (L (K (xN N))) n else 0) =
        co _ (K (xN N)) n - (if n ∈ Finset.Icc (-(N : ℤ)) N then co _ (K (xN N)) n else 0)
      rw [hL]
    have e : qA m β (L (K (xN N)) - truncSobolev38 _ N (L (K (xN N)))) =
        ∑' n : ℤ, finiteHierarchyRate38 m β n *
          ‖co _ (K (xN N) - truncSobolev38 _ N (K (xN N))) n‖ ^ 2 := by
      unfold qA
      exact tsum_congr (fun n => by rw [hco])
    rw [e]
    exact (hrate _).2
  refine ⟨(hKcont.tendsto x).comp hxt, hfin, htail, ?_⟩
  have hD := (hDc.tendsto x).comp hxt
  have hlim := hD.sub htail
  rw [sub_zero] at hlim
  refine hlim.congr (fun N => ?_)
  exact ((hfin N).2).symm

end
end NlsGge.ThirdConsultation.F013X
