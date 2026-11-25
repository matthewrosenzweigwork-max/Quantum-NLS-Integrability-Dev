import Mathlib
import QuantumNLS.Fidelity
import QuantumNLS.ExactDensity
import QuantumNLS.UniformStaticR31m

/-!
# UniformProjR01Compact: compactness of `𝒰_R` and uniform tails (R-98833BEE, first paragraph of the proof)

Source: `source-text/chapters/core/projective_reconstruction.tex` (sha256
`bc1188a07b52d3a19c337ef5ba61fb006d940f5d079d0defe2730801e679a60d`), proof of `thm:uniform-projective`,
lines 378-382:

"The set `𝒰_R` is compact in `L²`. Indeed, for the physical Fourier projection `Π_M` onto `|n| ≤ M`,
`sup_{u∈𝒰_R} ‖(1-Π_M)u‖₂² ≤ R²/(1+(2π(M+1)/L)²)`. Each projected set is bounded in finite dimension, so this
bound proves total boundedness. The unit-mass condition is closed in `L²`, and the `H¹` norm bound is closed by
lower semicontinuity of its Fourier sum. Thus `𝒰_R` is compact. The quantum-derived continuous map
`w : L² → ℓ²` has compact image on this class. Coordinate projections converge uniformly to the identity on that
image: take a finite norm net, control its finitely many tails, and use contractivity. This proves
`eq:target-tightness` with parameter set `𝒰_R`."

Objects.  `𝒰_R` is `UniformStaticR31m.unitBall R = {u ∈ L²(𝕋_L) : ‖u‖ = 1, ∃ v ∈ H¹ (DEF-002), v = u, ‖v‖_{H¹} ≤ R}`,
the same class as in the R-D2F4CE8F input.  The `H¹` norm is the DEF-002 one,
`Σ_n (1+|2πn/L|)² |û(n)|²` (`definitions.tex:15`); the printed tail bound `R²/(1+(2π(M+1)/L)²)` holds for it because
`(1+|x|)² ≥ 1+x²` (`tail_bound`).  `Π_M = 𝓕⁻¹ P_{[-M,M]} 𝓕` with `𝓕 = Fourier.fourierL2 L` (`physProj`), and
`P_F = Fidelity.coordProj F` is the coordinate projection of the accepted R-849FDB99 module.

Main results: `isCompact_unitBall` (every `R`), `exists_uniform_tail` (finite net + tails + contractivity),
`tight_of_compact` (`inf_F sup_t ‖(1-P_F)z(t)‖ = 0`, the literal hypothesis of `Fidelity.uniform_upgrade`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate ENNReal
open Filter Topology Metric

noncomputable section

namespace QuantumNLS.UniformProjR01Compact

open QuantumNLS.Fidelity (L2Z ev coordProj inner_ev_left inner_ev_coordProj norm_coordProj_le
  stdBasis stdBasis_apply)
open QuantumNLS.PhysicalTensor (L2T)

/-! ### Coordinates of `P_F` and its elementary properties -/

theorem coordProj_apply (F : Finset ℤ) (z : L2Z) (n : ℤ) :
    coordProj F z n = if n ∈ F then z n else 0 := by
  rw [coordProj, lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.coeFn_smul, Pi.smul_apply, ev, lp.single_apply, Pi.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]

theorem coordProj_sub (F : Finset ℤ) (y z : L2Z) :
    coordProj F y - coordProj F z = coordProj F (y - z) := by
  simp only [coordProj, lp.coeFn_sub, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

theorem continuous_eval (b : ℤ) : Continuous (fun x : L2Z => x b) := by
  have h : (fun x : L2Z => x b) = fun x => ⟪ev b, x⟫_ℂ := funext fun x => (inner_ev_left b x).symm
  rw [h]
  exact continuous_const.inner continuous_id

/-- For one vector, `P_F y → y` along finite sets. -/
theorem tendsto_coordProj (y : L2Z) : Tendsto (fun F : Finset ℤ => coordProj F y) atTop (𝓝 y) := by
  have h := stdBasis.hasSum_repr y
  have e : (fun i => stdBasis.repr y i • stdBasis i) = fun i => y i • ev i := by
    funext i
    rw [HilbertBasis.repr_apply_apply, stdBasis_apply, inner_ev_left]
  rw [e] at h
  exact h

/-- **Uniform tails on a compact set** (finite norm net, finitely many tails, contractivity of `P_F`). -/
theorem exists_uniform_tail {S : Set L2Z} (hS : IsCompact S) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset ℤ, ∀ z ∈ S, ‖z - coordProj F z‖ ≤ ε := by
  obtain ⟨t, -, htfin, hcover⟩ := hS.finite_cover_balls (e := ε / 3) (by positivity)
  have htail : ∀ y : L2Z, ∃ F₀ : Finset ℤ, ∀ F, F₀ ≤ F → ‖y - coordProj F y‖ ≤ ε / 3 := by
    intro y
    have h := (tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_coordProj y)).eventually
      (ge_mem_nhds (show (0 : ℝ) < ε / 3 by positivity))
    obtain ⟨F₀, hF₀⟩ := eventually_atTop.1 h
    exact ⟨F₀, fun F hF => by rw [norm_sub_rev]; exact hF₀ F hF⟩
  choose F₀ hF₀ using htail
  refine ⟨htfin.toFinset.biUnion F₀, fun z hz => ?_⟩
  obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.1 (hcover hz)
  rw [mem_ball, dist_eq_norm] at hzy
  have hsub : F₀ y ≤ htfin.toFinset.biUnion F₀ :=
    Finset.subset_biUnion_of_mem F₀ (htfin.mem_toFinset.2 hy)
  have h1 := hF₀ y _ hsub
  have h2 : ‖coordProj (htfin.toFinset.biUnion F₀) y - coordProj (htfin.toFinset.biUnion F₀) z‖ ≤
      ‖y - z‖ := by
    rw [coordProj_sub]
    exact norm_coordProj_le _ _
  have e : z - coordProj (htfin.toFinset.biUnion F₀) z =
      (z - y) + (y - coordProj (htfin.toFinset.biUnion F₀) y) +
        (coordProj (htfin.toFinset.biUnion F₀) y - coordProj (htfin.toFinset.biUnion F₀) z) := by
    abel
  rw [e]
  have h3 := norm_add_le (z - y + (y - coordProj (htfin.toFinset.biUnion F₀) y))
    (coordProj (htfin.toFinset.biUnion F₀) y - coordProj (htfin.toFinset.biUnion F₀) z)
  have h4 := norm_add_le (z - y) (y - coordProj (htfin.toFinset.biUnion F₀) y)
  rw [norm_sub_rev y z] at h2
  linarith

/-- **`eq:target-tightness`** for any family with values in a compact set:
`inf_F sup_t ‖(1-P_F) z(t)‖ = 0` (real infimum and supremum, as in `Fidelity.uniform_upgrade`). -/
theorem tight_of_compact {T : Type*} (z : T → L2Z) {S : Set L2Z} (hS : IsCompact S)
    (hz : ∀ t, z t ∈ S) : ⨅ F : Finset ℤ, ⨆ t, ‖z t - coordProj F (z t)‖ = 0 := by
  apply le_antisymm
  · refine le_of_forall_gt_imp_ge_of_dense fun ε hε => ?_
    obtain ⟨F, hF⟩ := exists_uniform_tail hS hε
    refine (ciInf_le ⟨0, ?_⟩ F).trans ?_
    · rintro _ ⟨G, rfl⟩
      exact Real.iSup_nonneg fun _ => norm_nonneg _
    · exact Real.iSup_le (fun t => hF _ (hz t)) hε.le
  · exact le_ciInf fun F => Real.iSup_nonneg fun _ => norm_nonneg _

/-! ### The DEF-002 `H¹` weight and the weighted ball in Fourier coordinates -/

variable {L : ℝ} [Fact (0 < L)]

/-- The DEF-002 `H¹` weight `(1+|2πn/L|)²`. -/
abbrev W (L : ℝ) (n : ℤ) : ℝ := Fourier.sobolevWeight L 1 n

theorem W_eq (n : ℤ) : W L n = (1 + |2 * Real.pi * (n : ℝ) / L|) ^ 2 := by
  show (1 + |2 * Real.pi * (n : ℝ) / L|) ^ ((2 : ℝ) * 1) = _
  rw [mul_one, Real.rpow_two]

theorem one_add_sq_le_W (n : ℤ) : 1 + (2 * Real.pi * (n : ℝ) / L) ^ 2 ≤ W L n := by
  rw [W_eq]
  nlinarith [abs_nonneg (2 * Real.pi * (n : ℝ) / L), sq_abs (2 * Real.pi * (n : ℝ) / L)]

theorem one_le_W (n : ℤ) : 1 ≤ W L n :=
  le_trans (by nlinarith [sq_nonneg (2 * Real.pi * (n : ℝ) / L)]) (one_add_sq_le_W (L := L) n)

/-- The tail weight: for `|n| > M`, `W n ≥ 1 + (2π(M+1)/L)²`. -/
theorem W_tail (M : ℕ) (n : ℤ) (hn : n ∉ Finset.Icc (-(M : ℤ)) M) :
    1 + (2 * Real.pi * ((M : ℝ) + 1) / L) ^ 2 ≤ W L n := by
  refine le_trans ?_ (one_add_sq_le_W (L := L) n)
  have hL : 0 < L := Fact.out
  have hn' : ((M : ℝ) + 1) ≤ |(n : ℝ)| := by
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    have : ((M : ℤ) + 1 ≤ |n|) := by
      rcases hn with h | h
      · rw [abs_of_neg (by omega)]; omega
      · rw [abs_of_pos (by omega)]; omega
    have := (Int.cast_le (R := ℝ)).2 this
    push_cast at this
    exact this
  have h3 : ((M : ℝ) + 1) ^ 2 ≤ (n : ℝ) ^ 2 :=
    sq_le_sq.2 (by rwa [abs_of_pos (by positivity : (0 : ℝ) < (M : ℝ) + 1)])
  have h4 : (2 * Real.pi * ((M : ℝ) + 1) / L) ^ 2 ≤ (2 * Real.pi * (n : ℝ) / L) ^ 2 := by
    calc (2 * Real.pi * ((M : ℝ) + 1) / L) ^ 2 = (2 * Real.pi / L) ^ 2 * ((M : ℝ) + 1) ^ 2 := by ring
      _ ≤ (2 * Real.pi / L) ^ 2 * (n : ℝ) ^ 2 := by gcongr
      _ = (2 * Real.pi * (n : ℝ) / L) ^ 2 := by ring
  linarith

/-- The weighted ball `{x ∈ ℓ² : ∀ G finite, Σ_{n∈G} W(n)|x_n|² ≤ R²}`. -/
def ball (L R : ℝ) : Set L2Z := {x | ∀ G : Finset ℤ, ∑ n ∈ G, W L n * ‖x n‖ ^ 2 ≤ R ^ 2}

theorem isClosed_ball (R : ℝ) : IsClosed (ball L R) := by
  simp only [ball, Set.ofPred_forall]
  refine isClosed_iInter fun G => isClosed_le ?_ continuous_const
  exact continuous_finsetSum _ fun n _ =>
    continuous_const.mul ((continuous_norm.comp (continuous_eval n)).pow 2)

theorem coord_sq_le {R : ℝ} {x : L2Z} (hx : x ∈ ball L R) (n : ℤ) : ‖x n‖ ≤ |R| := by
  have h := hx {n}
  rw [Finset.sum_singleton] at h
  have h2 : ‖x n‖ ^ 2 ≤ |R| ^ 2 := by
    rw [sq_abs]
    nlinarith [one_le_W (L := L) n, sq_nonneg ‖x n‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (abs_nonneg R) two_ne_zero).1 h2

/-- The tail estimate on the weighted ball: if `W ≥ c > 0` off `F`, then `‖(1-P_F)x‖² ≤ R²/c`. -/
theorem tail_le {R c : ℝ} (hc : 0 < c) {F : Finset ℤ} (hF : ∀ n, n ∉ F → c ≤ W L n)
    {x : L2Z} (hx : x ∈ ball L R) : ‖x - coordProj F x‖ ^ 2 ≤ R ^ 2 / c := by
  have hs := ExactDensity.lp_sq_hasSum (x - coordProj F x)
  rw [← hs.tsum_eq]
  have hval : ∀ n, ‖(x - coordProj F x) n‖ ^ 2 = if n ∈ F then 0 else ‖x n‖ ^ 2 := by
    intro n
    rw [lp.coeFn_sub, Pi.sub_apply, coordProj_apply]
    split_ifs <;> simp
  refine Real.tsum_le_of_sum_le (fun n => sq_nonneg _) fun G => ?_
  calc ∑ n ∈ G, ‖(x - coordProj F x) n‖ ^ 2
      ≤ ∑ n ∈ G, W L n * ‖x n‖ ^ 2 / c := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [hval n]
        split_ifs with hn
        · have := one_le_W (L := L) n
          positivity
        · rw [le_div_iff₀ hc]
          have := hF n hn
          nlinarith [sq_nonneg ‖x n‖]
    _ = (∑ n ∈ G, W L n * ‖x n‖ ^ 2) / c := by rw [Finset.sum_div]
    _ ≤ R ^ 2 / c := by gcongr; exact hx G

/-- **The printed tail bound** in Fourier coordinates: for `F = [-M, M]`,
`‖(1-P_F)x‖² ≤ R²/(1+(2π(M+1)/L)²)`. -/
theorem tail_bound {R : ℝ} (M : ℕ) {x : L2Z} (hx : x ∈ ball L R) :
    ‖x - coordProj (Finset.Icc (-(M : ℤ)) M) x‖ ^ 2 ≤
      R ^ 2 / (1 + (2 * Real.pi * ((M : ℝ) + 1) / L) ^ 2) :=
  tail_le (by positivity) (fun n hn => W_tail M n hn) hx

theorem tendsto_tail_bound (R : ℝ) :
    Tendsto (fun M : ℕ => R ^ 2 / (1 + (2 * Real.pi * ((M : ℝ) + 1) / L) ^ 2)) atTop (𝓝 0) := by
  have hL : 0 < L := Fact.out
  have h1 : Tendsto (fun M : ℕ => 2 * Real.pi * ((M : ℝ) + 1) / L) atTop atTop := by
    have : Tendsto (fun M : ℕ => ((M : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h := this.const_mul_atTop (show (0 : ℝ) < 2 * Real.pi / L by positivity)
    refine h.congr fun M => ?_
    ring
  have h2 : Tendsto (fun M : ℕ => 1 + (2 * Real.pi * ((M : ℝ) + 1) / L) ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 ((tendsto_pow_atTop two_ne_zero).comp h1)
  exact tendsto_const_nhds.div_atTop h2

/-- Each projected set is bounded in finite dimension; with the uniform tail this gives total boundedness. -/
theorem totallyBounded_ball (R : ℝ) : TotallyBounded (ball L R) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨M, hM⟩ := ((tendsto_tail_bound (L := L) R).eventually
    (gt_mem_nhds (show (0 : ℝ) < (ε / 2) ^ 2 by positivity))).exists
  set F : Finset ℤ := Finset.Icc (-(M : ℤ)) M with hFdef
  let φ : (F → ℂ) → L2Z := fun v => ∑ a : F, v a • ev a
  have hφ : Continuous φ :=
    continuous_finsetSum _ fun a _ => (continuous_apply a).smul continuous_const
  have hK : IsCompact (φ '' closedBall (0 : F → ℂ) |R|) := (isCompact_closedBall _ _).image hφ
  obtain ⟨t, htfin, hcov⟩ := Metric.totallyBounded_iff.1 hK.totallyBounded (ε / 2) (by positivity)
  refine ⟨t, htfin, fun x hx => ?_⟩
  have hPx : coordProj F x ∈ φ '' closedBall (0 : F → ℂ) |R| := by
    refine ⟨fun a => x a, ?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (abs_nonneg R)]
      exact fun a => coord_sq_le hx a
    · show ∑ a : F, x a • ev a = ∑ a ∈ F, x a • ev a
      exact Finset.sum_coe_sort F (fun a => x a • ev a)
  obtain ⟨y, hy, hdy⟩ := Set.mem_iUnion₂.1 (hcov hPx)
  refine Set.mem_iUnion₂.2 ⟨y, hy, ?_⟩
  rw [mem_ball] at hdy ⊢
  have htail : ‖x - coordProj F x‖ < ε / 2 := by
    have h := (tail_bound M hx).trans_lt hM
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h
  calc dist x y ≤ dist x (coordProj F x) + dist (coordProj F x) y := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by rw [dist_eq_norm]; exact add_lt_add htail hdy
    _ = ε := by ring

theorem isCompact_ball (R : ℝ) : IsCompact (ball L R) :=
  (totallyBounded_ball R).isCompact_of_isClosed (isClosed_ball R)

/-! ### `𝒰_R` in Fourier coordinates, and its compactness -/

/-- `𝒰_R = UniformStaticR31m.unitBall R`. -/
abbrev UR (L : ℝ) [Fact (0 < L)] (R : ℝ) : Set (L2T L) := UniformStaticR31m.unitBall (L := L) R

theorem mem_UR_iff {R : ℝ} (hR : 0 ≤ R) (u : L2T L) :
    u ∈ UR L R ↔ ‖u‖ = 1 ∧ Fourier.fourierL2 L u ∈ ball L R := by
  constructor
  · rintro ⟨hu, v, rfl, hvR⟩
    refine ⟨hu, fun G => ?_⟩
    have hsum := v.summable
    have hn := Sobolev.WField.norm_sq_eq_tsum L v
    calc ∑ n ∈ G, W L n * ‖Fourier.fourierL2 L v.val n‖ ^ 2
        ≤ ∑' n, W L n * ‖Fourier.fourierL2 L v.val n‖ ^ 2 :=
          hsum.sum_le_tsum G fun n _ => mul_nonneg (le_trans zero_le_one (one_le_W (L := L) n)) (sq_nonneg _)
      _ = ‖v‖ ^ 2 := hn.symm
      _ ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hvR 2
  · rintro ⟨hu, hx⟩
    have hnn : 0 ≤ fun n => W L n * ‖Fourier.fourierL2 L u n‖ ^ 2 :=
      fun n => mul_nonneg (le_trans zero_le_one (one_le_W (L := L) n)) (sq_nonneg _)
    have hsum := summable_of_sum_le hnn hx
    refine ⟨hu, Sobolev.WField.mk (W := Sobolev.def002 L 1) u hsum, rfl, ?_⟩
    have hn := Sobolev.WField.norm_sq_eq_tsum L (Sobolev.WField.mk (W := Sobolev.def002 L 1) u hsum)
    have h2 : ‖Sobolev.WField.mk (W := Sobolev.def002 L 1) u hsum‖ ^ 2 ≤ R ^ 2 := by
      rw [hn]
      exact Real.tsum_le_of_sum_le hnn hx
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).1 h2

theorem UR_subset_ball (R : ℝ) {u : L2T L} (hu : u ∈ UR L R) : Fourier.fourierL2 L u ∈ ball L R := by
  obtain ⟨hu1, v, hv, hvR⟩ := hu
  have hR : 0 ≤ R := (norm_nonneg v).trans hvR
  exact ((mem_UR_iff hR u).1 ⟨hu1, v, hv, hvR⟩).2

theorem UR_mono {R R' : ℝ} (h : R ≤ R') {u : L2T L} (hu : u ∈ UR L R) : u ∈ UR L R' := by
  obtain ⟨hu1, v, hv, hvR⟩ := hu
  exact ⟨hu1, v, hv, hvR.trans h⟩

theorem norm_of_mem_UR {R : ℝ} {u : L2T L} (hu : u ∈ UR L R) : ‖u‖ = 1 := hu.1

/-- The physical Fourier projection `Π_M` onto `|n| ≤ M`. -/
def physProj (L : ℝ) [Fact (0 < L)] (M : ℕ) (u : L2T L) : L2T L :=
  (Fourier.fourierL2 L).symm (coordProj (Finset.Icc (-(M : ℤ)) M) (Fourier.fourierL2 L u))

/-- **The printed bound** `sup_{u∈𝒰_R} ‖(1-Π_M)u‖₂² ≤ R²/(1+(2π(M+1)/L)²)`. -/
theorem physical_tail_bound {R : ℝ} (M : ℕ) {u : L2T L} (hu : u ∈ UR L R) :
    ‖u - physProj L M u‖ ^ 2 ≤ R ^ 2 / (1 + (2 * Real.pi * ((M : ℝ) + 1) / L) ^ 2) := by
  have e : ‖u - physProj L M u‖ =
      ‖Fourier.fourierL2 L u - coordProj (Finset.Icc (-(M : ℤ)) M) (Fourier.fourierL2 L u)‖ := by
    rw [← (Fourier.fourierL2 L).norm_map, map_sub, physProj, LinearIsometryEquiv.apply_symm_apply]
  rw [e]
  exact tail_bound M (UR_subset_ball R hu)

/-- **`𝒰_R` is compact in `L²`** (closed: unit mass and the `H¹` bound via its finite Fourier sums; contained in
the compact preimage of the weighted ball). -/
theorem isCompact_UR (R : ℝ) : IsCompact (UR L R) := by
  by_cases hR : 0 ≤ R
  · have hset : UR L R = sphere (0 : L2T L) 1 ∩ (Fourier.fourierL2 L) ⁻¹' ball L R := by
      ext u
      rw [mem_UR_iff hR, Set.mem_inter_iff, mem_sphere_zero_iff_norm, Set.mem_preimage]
    have hcl : IsClosed (UR L R) := by
      rw [hset]
      exact isClosed_sphere.inter ((isClosed_ball R).preimage (Fourier.fourierL2 L).continuous)
    have hK : IsCompact ((Fourier.fourierL2 L) ⁻¹' ball L R) :=
      (Fourier.fourierL2 L).toHomeomorph.isCompact_preimage.2 (isCompact_ball R)
    exact hK.of_isClosed_subset hcl (fun u hu => (hset ▸ hu).2)
  · have hempty : UR L R = ∅ := by
      ext u
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, v, -, hvR⟩
      exact hR ((norm_nonneg v).trans hvR)
    rw [hempty]
    exact isCompact_empty

end QuantumNLS.UniformProjR01Compact

#print axioms QuantumNLS.UniformProjR01Compact.exists_uniform_tail
#print axioms QuantumNLS.UniformProjR01Compact.tight_of_compact
#print axioms QuantumNLS.UniformProjR01Compact.tail_bound
#print axioms QuantumNLS.UniformProjR01Compact.physical_tail_bound
#print axioms QuantumNLS.UniformProjR01Compact.isCompact_ball
#print axioms QuantumNLS.UniformProjR01Compact.mem_UR_iff
#print axioms QuantumNLS.UniformProjR01Compact.isCompact_UR

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.UniformProjR01Compact." ||
        n.toString.startsWith "_private.QuantumNLS.UniformProjR01Compact." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          n.components.any (fun c => c.toString == "RegularCut") then
        throwError "Held dependency: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"UniformProjR01Compact aggregate audit PASS: {own} own constants; {seen.size} transitive constants; standard axioms only; no held identifiers."
