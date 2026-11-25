import Mathlib
import NlsGge.Sobolev.PeriodicBridge
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST029Support
import NlsGge.Atomic.KST.KST029

/- KST031Support PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/ThirdConsultation/KST/KST031Support.lean.
   SUPPORTING module (no packet increment).  Route (Pro rounds 7-8 section 25, "Dependency ruling"): the w-weighted
   componentwise ball is contained in a compact subset of the Euclidean L2 pair space (weighted ellipsoid in l2 compact
   because w -> infinity; adapted from the landed G1-049 ellipsoid argument with a general weight); the local
   statements (KST-029 and the KST-011/KST-018 smallness `uniform_small_abc`) are covered by finitely many L2 balls.
   Namespace NlsGge.ThirdConsultation.KST.KST031S. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ENNReal

namespace NlsGge.ThirdConsultation.KST.KST031S

/-! ### Weighted ellipsoids in `ℓ²(ℤ)` are compact when the weight tends to infinity -/

abbrev L2Seq : Type := lp (fun _ : ℤ => ℂ) 2

/-- Weighted ellipsoid: every finite weighted partial sum is at most `B²`. -/
def wEllipsoid (W : ℤ → ℝ) (B : ℝ) : Set L2Seq :=
  {x | ∀ F : Finset ℤ, ∑ n ∈ F, W n ^ 2 * ‖x n‖ ^ 2 ≤ B ^ 2}

theorem continuous_coord (n : ℤ) : Continuous (fun x : L2Seq => x n) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun x y => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  have := lp.norm_apply_le_norm (p := (2 : ℝ≥0∞)) (by norm_num) (x - y) n
  simpa using this

theorem isClosed_wEllipsoid (W : ℤ → ℝ) (B : ℝ) : IsClosed (wEllipsoid W B) := by
  have : wEllipsoid W B = ⋂ F : Finset ℤ, {x : L2Seq | ∑ n ∈ F, W n ^ 2 * ‖x n‖ ^ 2 ≤ B ^ 2} := by
    ext x; simp [wEllipsoid]
  rw [this]
  refine isClosed_iInter fun F => isClosed_le ?_ continuous_const
  exact continuous_finset_sum _ fun n _ => continuous_const.mul ((continuous_coord n).norm.pow 2)

theorem sq_norm_hasSum (x : L2Seq) : HasSum (fun n : ℤ => ‖x n‖ ^ 2) (‖x‖ ^ 2) := by
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) x
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

theorem norm_le_of_mem_wEllipsoid {W : ℤ → ℝ} (hW1 : ∀ n, 1 ≤ W n) {B : ℝ} (hB : 0 ≤ B)
    {x : L2Seq} (hx : x ∈ wEllipsoid W B) : ‖x‖ ≤ B := by
  have h1 : ‖x‖ ^ 2 ≤ B ^ 2 := by
    refine hasSum_le_of_sum_le (sq_norm_hasSum x) fun F => ?_
    refine le_trans (Finset.sum_le_sum fun n _ => ?_) (hx F)
    have h2 : (1 : ℝ) ≤ W n ^ 2 := by nlinarith [hW1 n]
    calc ‖x n‖ ^ 2 = 1 * ‖x n‖ ^ 2 := (one_mul _).symm
      _ ≤ W n ^ 2 * ‖x n‖ ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
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

theorem totallyBounded_wEllipsoid {W : ℤ → ℝ} (hW1 : ∀ n, 1 ≤ W n)
    (hW : ∀ K : ℝ, ∃ M : ℕ, ∀ n : ℤ, M < n.natAbs → K ≤ W n) {B : ℝ} (hB : 0 ≤ B) :
    TotallyBounded (wEllipsoid W B) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  set K : ℝ := 2 * B / ε + 1 with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hKε : K * ε = 2 * B + ε := by rw [hKdef]; field_simp
  obtain ⟨M, hM⟩ := hW K
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
  have htail : ‖x - proj S x‖ ^ 2 * K ^ 2 ≤ B ^ 2 := by
    have hs := (sq_norm_hasSum (x - proj S x)).mul_right (K ^ 2)
    refine hasSum_le_of_sum_le hs fun F => ?_
    refine le_trans (Finset.sum_le_sum fun n _ => ?_) (hx F)
    have hc : (x - proj S x) n = if n ∈ S then 0 else x n := by
      rw [lp.coeFn_sub, Pi.sub_apply, proj_apply]
      split_ifs <;> simp
    rw [hc]
    by_cases hn : n ∈ S
    · simp only [hn, if_true, norm_zero]
      have : (0 : ℝ) ≤ W n ^ 2 * ‖x n‖ ^ 2 := by positivity
      simpa using this
    · simp only [hn, if_false]
      have hMn : M < n.natAbs := by
        rw [hS, Finset.mem_Icc] at hn
        omega
      have hKn : K ^ 2 ≤ W n ^ 2 := pow_le_pow_left₀ hK0 (hM n hMn) 2
      calc ‖x n‖ ^ 2 * K ^ 2 ≤ ‖x n‖ ^ 2 * W n ^ 2 :=
            mul_le_mul_of_nonneg_left hKn (sq_nonneg _)
        _ = _ := by ring
  have hxB : ‖x‖ ≤ B := norm_le_of_mem_wEllipsoid hW1 hB hx
  have hsmall : ‖x - proj S x‖ < ε / 2 := by
    by_contra hcon
    push_neg at hcon
    have h3 : K * (ε / 2) ≤ K * ‖x - proj S x‖ :=
      mul_le_mul_of_nonneg_left hcon hK0
    have h4 : (K * ‖x - proj S x‖) ^ 2 ≤ B ^ 2 := by
      calc _ = ‖x - proj S x‖ ^ 2 * K ^ 2 := by ring
        _ ≤ _ := htail
    have h5 : K * ‖x - proj S x‖ ≤ B := by
      by_contra h; push_neg at h
      nlinarith [norm_nonneg (x - proj S x), mul_nonneg hK0 (norm_nonneg (x - proj S x))]
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

theorem isCompact_wEllipsoid {W : ℤ → ℝ} (hW1 : ∀ n, 1 ≤ W n)
    (hW : ∀ K : ℝ, ∃ M : ℕ, ∀ n : ℤ, M < n.natAbs → K ≤ W n) {B : ℝ} (hB : 0 ≤ B) :
    IsCompact (wEllipsoid W B) :=
  isCompact_iff_totallyBounded_isComplete.2
    ⟨totallyBounded_wEllipsoid hW1 hW hB, (isClosed_wEllipsoid W B).isComplete⟩


/-! ### The weighted ball lies in a compact subset of the Euclidean pair space -/

theorem w_eq_natAbs (w : ℤ → ℝ) (hw : ∀ k, w (-k) = w k) (k : ℤ) : w k = w (k.natAbs : ℤ) := by
  rcases le_total 0 k with h | h
  · rw [Int.natAbs_of_nonneg h]
  · rw [Int.ofNat_natAbs_of_nonpos h, hw]

theorem ball_subset_compact (w : ℤ → ℝ) (hw : UnboundedWeight w) (M : ℝ) :
    ∃ K : Set Potential, IsCompact K ∧ physicalComponentBall w (2 * M) ⊆ K := by
  obtain ⟨⟨h1, h2, -⟩, hlim⟩ := hw
  set W : ℤ → ℝ := fun m => w (2 * m) with hWdef
  have hW1 : ∀ n, 1 ≤ W n := fun n => h1 _
  have hW : ∀ K : ℝ, ∃ M : ℕ, ∀ n : ℤ, M < n.natAbs → K ≤ W n := by
    intro K
    obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.1 (hlim.eventually_ge_atTop K)
    refine ⟨n0, fun n hn => ?_⟩
    have hWn : W n = w ((2 * n).natAbs : ℤ) := w_eq_natAbs w h2 (2 * n)
    rw [hWn]
    exact hn0 _ (by omega)
  set R : ℝ := |2 * M| with hRdef
  have hR : 0 ≤ R := abs_nonneg _
  have hEc := isCompact_wEllipsoid hW1 hW hR
  refine ⟨(WithLp.toLp 2) '' Set.pi Set.univ
    (fun _ : Bool => NlsGge.Pilot.physicalFourierL2.symm '' wEllipsoid W R), ?_, ?_⟩
  · exact IsCompact.image
      (isCompact_univ_pi fun _ => hEc.image NlsGge.Pilot.physicalFourierL2.symm.continuous)
      (PiLp.continuous_toLp 2 _)
  · intro φ hφ
    refine ⟨fun ch => φ ch, fun ch _ => ⟨NlsGge.Pilot.physicalFourierL2 (φ ch), ?_, by simp⟩, rfl⟩
    intro F
    have h := hφ ch
    simp only [NlsGge.Pilot.physicalFourierL2_apply]
    have hnn : ∀ m, 0 ≤ W m ^ 2 * ‖NlsGge.Pilot.physicalFourier (φ ch) m‖ ^ 2 :=
      fun m => by positivity
    have h2' : ENNReal.ofReal (∑ n ∈ F, W n ^ 2 * ‖NlsGge.Pilot.physicalFourier (φ ch) n‖ ^ 2) ≤
        ENNReal.ofReal ((2 * M) ^ 2) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun m _ => hnn m)]
      exact (ENNReal.sum_le_tsum F).trans h
    have h3 := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).1 h2'
    calc _ ≤ (2 * M) ^ 2 := h3
      _ = R ^ 2 := (sq_abs _).symm

/-! ### Finite cover of local statements -/

theorem cover_of_local {K : Set Potential} (hK : IsCompact K) (Q : Potential → ℤ → Prop)
    (hloc : ∀ φ0 : Potential, ∃ e : ℝ, 0 < e ∧ ∃ N : ℕ, 5 ≤ N ∧
      ∀ φ : Potential, ‖φ - φ0‖ < e → ∀ n : ℤ, N ≤ n.natAbs → Q φ n) :
    ∃ N : ℕ, 5 ≤ N ∧ ∀ φ ∈ K, ∀ n : ℤ, N ≤ n.natAbs → Q φ n := by
  choose e he N hN5 hN using hloc
  obtain ⟨t, -, hcov⟩ := hK.elim_nhds_subcover (fun x => Metric.ball x (e x))
    (fun x _ => Metric.ball_mem_nhds x (he x))
  refine ⟨max 5 (t.sup N), le_max_left _ _, fun φ hφ n hn => ?_⟩
  obtain ⟨x, hxt, hφx⟩ := Set.mem_iUnion₂.1 (hcov hφ)
  rw [Metric.mem_ball, dist_eq_norm] at hφx
  exact hN x φ hφx n (le_trans ((Finset.le_sup hxt).trans (le_max_right _ _)) hn)


/-! ### Local reduced bounds near every potential, and the uniform cutoff on the weighted ball -/

section Reduced

open NlsGge.Atomic.KST004 NlsGge.Atomic.KST006 NlsGge.GK38

/-- The three clauses of `uniformReducedBounds` for one potential and one index. -/
def ReducedClauses (φ : Potential) (n : ℤ) : Prop :=
  SmallCoefficients n (a φ n) (b φ n) (c φ n) ∧
  (∀ (z : ℂ) (hz : z ∈ spectralStrip n),
    ‖qOperator φ n z hz ^ 2‖ ≤ (1/2 : ℝ) ∧ IsUnit (1-qOperator φ n z hz)) ∧
  Lib.zeroMultiset (determinant n (a φ n) (b φ n) (c φ n))
    (Metric.ball (center n) (Real.pi/3)) =
    {lamMinus (periodicPair φ) n, lamPlus (periodicPair φ) n}

/-- Local form: KST-029 (smallness and root identification) together with the KST-011/018 bound
`‖q²‖ ≤ 1/2` (`uniform_small_abc`), and invertibility of `1 - q` from `‖q²‖ < 1`. -/
theorem local_reduced (φ0 : Potential) :
    ∃ e : ℝ, 0 < e ∧ ∃ N : ℕ, 5 ≤ N ∧
      ∀ φ : Potential, ‖φ - φ0‖ < e → ∀ n : ℤ, N ≤ n.natAbs → ReducedClauses φ n := by
  obtain ⟨e1, he1, N1, hN1, h1⟩ := kst029 φ0
  obtain ⟨e2, he2, N2, hN2, h2⟩ := uniform_small_abc φ0
  refine ⟨min e1 e2, lt_min he1 he2, max N1 N2, le_trans hN1 (le_max_left _ _),
    fun φ hφ n hn => ?_⟩
  obtain ⟨hs, hz, -⟩ := h1 φ (lt_of_lt_of_le hφ (min_le_left _ _)) n
    (le_trans (le_max_left _ _) hn)
  obtain ⟨hq, -⟩ := h2 φ (lt_of_lt_of_le hφ (min_le_right _ _)) n
    (le_trans (le_max_right _ _) hn)
  refine ⟨hs, fun z hz' => ⟨hq z hz', ?_⟩, hz⟩
  exact (NlsGge.Atomic.KST012.inverse_one_sub_of_sq_norm_lt _
    (lt_of_le_of_lt (hq z hz') (by norm_num))).1

/-- The cutoff exists: `uniformReducedBounds w M N₄` for some `N₄`. -/
theorem exists_uniformReducedBounds (w : ℤ → ℝ) (hw : UnboundedWeight w) (M : ℝ) :
    ∃ N₄ : ℕ, uniformReducedBounds w M N₄ := by
  obtain ⟨K, hK, hsub⟩ := ball_subset_compact w hw M
  obtain ⟨N, hN5, hN⟩ := cover_of_local hK ReducedClauses local_reduced
  exact ⟨N, hN5, fun φ hφ n hn => hN φ (hsub hφ) n hn⟩

end Reduced

/-! ### Transfer to the product weight -/

theorem ball_productWeight_subset (w v : ℤ → ℝ) (hw : ∀ k, 1 ≤ w k) (hv : ∀ k, 1 ≤ v k)
    (R : ℝ) : physicalComponentBall (productWeight w v) R ⊆ physicalComponentBall w R := by
  intro φ hφ ch
  refine le_trans (ENNReal.tsum_le_tsum fun m => ENNReal.ofReal_le_ofReal ?_) (hφ ch)
  have hw1 := hw (2 * m)
  have hv1 := hv (2 * m)
  have h : w (2 * m) ^ 2 ≤ (productWeight w v (2 * m)) ^ 2 := by
    show w (2 * m) ^ 2 ≤ (w (2 * m) * v (2 * m)) ^ 2
    have h0 : 0 ≤ w (2 * m) := by linarith
    have h1 : w (2 * m) ≤ w (2 * m) * v (2 * m) := by nlinarith
    exact pow_le_pow_left₀ h0 h1 2
  exact mul_le_mul_of_nonneg_right h (sq_nonneg _)

theorem uniformReducedBounds_of_ball_subset (w w' : ℤ → ℝ) (M : ℝ) (N : ℕ)
    (h : physicalComponentBall w' (2 * M) ⊆ physicalComponentBall w (2 * M))
    (hu : uniformReducedBounds w M N) : uniformReducedBounds w' M N :=
  ⟨hu.1, fun φ hφ n hn => hu.2 φ (h hφ) n hn⟩

end NlsGge.ThirdConsultation.KST.KST031S
end
