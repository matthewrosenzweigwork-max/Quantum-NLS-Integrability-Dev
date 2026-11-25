import NlsGge.Ramer.General.TruncatedFieldConvergenceG
import NlsGge.Ramer.TruncatedDerivConvergence

/-!
# Truncated-derivative convergence on the general source law (GB2)

Generalization of `NlsGge/Ramer/TruncatedDerivConvergence.lean` to a `RamerSetting S`.
`i = S.incl`, `H = S.H`, `E = S.E`; the Hilbert-Schmidt bound uses `S.incl_hs_hasSum`.
The generic helpers `headIndex`, `mem_headIndex`, `hsNormSq_eq_sum_norm_sq` are reused from
the old file.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer

variable (S : NlsGge.Ramer.General.RamerSetting)

/-! ### The truncation acts on the coordinate basis by `0` or the identity -/

theorem hcoord_basis_of_ne (p : ℤ × Fin 2) (n : ℤ) (hn : n ≠ p.1) :
    S.hcoord (weightedRealHilbertBasis S.cmWeight p) n = 0 := by
  rw [S.hcoord_basis]
  simp [hn]

theorem cmTrunc_basis_of_mem (N : ℕ) (p : ℤ × Fin 2) (hp : p.1 ∈ symmetricModes N) :
    ((S.cmTrunc N (weightedRealHilbertBasis S.cmWeight p) : S.head N) : S.H) =
      weightedRealHilbertBasis S.cmWeight p := by
  apply S.hcoord_ext
  intro n
  rw [S.hcoord_cmTrunc]
  split_ifs with hn
  · rfl
  · have hne : n ≠ p.1 := fun h => hn (h ▸ hp)
    rw [S.hcoord_basis_of_ne p n hne]

theorem cmTrunc_basis_of_not_mem (N : ℕ) (p : ℤ × Fin 2) (hp : p.1 ∉ symmetricModes N) :
    ((S.cmTrunc N (weightedRealHilbertBasis S.cmWeight p) : S.head N) : S.H) = 0 := by
  apply S.hcoord_ext
  intro n
  rw [S.hcoord_cmTrunc]
  split_ifs with hn
  · have hne : n ≠ p.1 := fun h => hp (h ▸ hn)
    rw [S.hcoord_basis_of_ne p n hne]
    rfl
  · rfl

theorem eventually_cmTrunc_basis_eq (p : ℤ × Fin 2) :
    ∀ᶠ N : ℕ in atTop,
      ((S.cmTrunc N (weightedRealHilbertBasis S.cmWeight p) : S.head N) : S.H) =
        weightedRealHilbertBasis S.cmWeight p := by
  filter_upwards [eventually_ge_atTop p.1.natAbs] with N hN
  refine S.cmTrunc_basis_of_mem N p ?_
  simp only [symmetricModes, Finset.mem_Icc]
  omega

theorem norm_map_cmTrunc_basis_le (N : ℕ) (p : ℤ × Fin 2) {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (T : S.H →L[ℝ] F) :
    ‖T ((S.cmTrunc N (weightedRealHilbertBasis S.cmWeight p) : S.head N) : S.H)‖ ≤
      ‖T (weightedRealHilbertBasis S.cmWeight p)‖ := by
  by_cases hp : p.1 ∈ symmetricModes N
  · rw [S.cmTrunc_basis_of_mem N p hp]
  · rw [S.cmTrunc_basis_of_not_mem N p hp, map_zero, norm_zero]
    exact norm_nonneg _

theorem tendsto_truncatedDeriv_apply_basis
    (G : S.E → S.H) (hG : ContDiff ℝ 1 G)
    (z : ℤ → ℂ) (hz : ∀ n : ℤ, S.coord n (S.R z) = z n) (p : ℤ × Fin 2) :
    Tendsto (fun N : ℕ =>
        ((S.cmTrunc N (fderiv ℝ G (S.headToE N (S.headPt N z))
            (S.incl ((S.cmTrunc N (weightedRealHilbertBasis S.cmWeight p) : S.head N) :
              S.H))) : S.head N) : S.H))
      atTop (𝓝 (fderiv ℝ G (S.R z)
        (S.incl (weightedRealHilbertBasis S.cmWeight p)))) := by
  have hD : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  have hcont : Continuous (fun x : S.E =>
      fderiv ℝ G x (S.incl (weightedRealHilbertBasis S.cmWeight p))) :=
    hD.clm_apply continuous_const
  have h1 := S.tendsto_cmTrunc_comp
    (fun x => fderiv ℝ G x (S.incl (weightedRealHilbertBasis S.cmWeight p))) hcont _ _
    (S.tendsto_headToE_headPt z hz)
  refine h1.congr' ?_
  filter_upwards [S.eventually_cmTrunc_basis_eq p] with N hN
  rw [hN]


/-- **Truncated-derivative convergence in Hilbert-Schmidt norm** (v2 ~l.579), general `S`. -/
theorem tendsto_lintegral_hs_truncatedDeriv
    (G : S.E → S.H) (hG : ContDiff ℝ 1 G) (B : ℝ)
    (hB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) :
    Tendsto (fun N : ℕ => ∫⁻ z, ∑' p : ℤ × Fin 2, ENNReal.ofReal (‖
        ((S.cmTrunc N (fderiv ℝ G (S.headToE N (S.headPt N z))
            (S.incl ((S.cmTrunc N (weightedRealHilbertBasis S.cmWeight p) :
                S.head N) : S.H))) : S.head N) : S.H)
        - fderiv ℝ G (S.R z) (S.incl (weightedRealHilbertBasis S.cmWeight p))‖ ^ 2)
      ∂S.γ) atTop (𝓝 0) := by
  set γ := S.γ with hγ
  let _ : MeasurableSpace S.H := borel _
  have _ : BorelSpace S.H := ⟨rfl⟩
  set R := S.R with hR
  have hRm : Measurable R := S.measurable_R
  set b := weightedRealHilbertBasis S.cmWeight with hb
  set i := S.incl with hi
  have hD : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  let f : ℕ → (ℤ → ℂ) → ℤ × Fin 2 → ℝ := fun N z p => ‖
        ((S.cmTrunc N (fderiv ℝ G (S.headToE N (S.headPt N z))
            (i ((S.cmTrunc N (b p) : S.head N) : S.H))) : S.head N) : S.H)
          - fderiv ℝ G (R z) (i (b p))‖ ^ 2
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  let σ : ℤ × Fin 2 → ℝ := fun p => ‖i (b p)‖ ^ 2
  have hσ : Summable σ := S.incl_hs b
  have hbd : ∀ N z p, f N z p ≤ 4 * B ^ 2 * σ p := by
    intro N z p
    have h1 : ‖((S.cmTrunc N (fderiv ℝ G (S.headToE N (S.headPt N z))
            (i ((S.cmTrunc N (b p) : S.head N) : S.H))) : S.head N) : S.H)‖
          ≤ B * ‖i (b p)‖ := by
      exact (S.norm_cmTrunc_le N _).trans (((fderiv ℝ G _).le_opNorm _).trans
        (mul_le_mul (hB _) (S.norm_map_cmTrunc_basis_le N p i) (norm_nonneg _) hB0))
    have h2 : ‖fderiv ℝ G (R z) (i (b p))‖ ≤ B * ‖i (b p)‖ :=
      ((fderiv ℝ G _).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _))
    have h3 : ‖((S.cmTrunc N (fderiv ℝ G (S.headToE N (S.headPt N z))
            (i ((S.cmTrunc N (b p) : S.head N) : S.H))) : S.head N) : S.H)
          - fderiv ℝ G (R z) (i (b p))‖ ≤ 2 * B * ‖i (b p)‖ := by
      refine (norm_sub_le _ _).trans ?_
      linarith
    calc f N z p ≤ (2 * B * ‖i (b p)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
      _ = 4 * B ^ 2 * σ p := by simp only [σ]; ring
  have hsumm : ∀ N z, Summable (f N z) := fun N z =>
    Summable.of_nonneg_of_le (fun p => sq_nonneg _) (hbd N z) (hσ.mul_left _)
  have hfm : ∀ N p, Measurable (fun z => f N z p) := by
    intro N p
    have hc : Continuous (fun v : S.head N =>
        ((S.cmTrunc N (fderiv ℝ G (S.headToE N v)
            (i ((S.cmTrunc N (b p) : S.head N) : S.H))) : S.head N) : S.H)) :=
      continuous_subtype_val.comp ((S.cmTrunc N).continuous.comp
        ((hD.comp (S.headToE N).continuous).clm_apply continuous_const))
    have h1 := hc.measurable.comp (S.measurable_headPt N)
    have hc2 : Continuous (fun x : S.E => fderiv ℝ G x (i (b p))) :=
      hD.clm_apply continuous_const
    have h2 := hc2.measurable.comp hRm
    exact (h1.sub h2).norm.pow_const 2
  set F : ℕ → (ℤ → ℂ) → ℝ≥0∞ := fun N z => ∑' p : ℤ × Fin 2, ENNReal.ofReal (f N z p) with hF
  have hFm : ∀ N, Measurable (F N) := fun N =>
    Measurable.tsum (fun p => ENNReal.measurable_ofReal.comp (hfm N p))
  have hae := S.coord_R_ae
  have hlim : ∀ᵐ z ∂γ, Tendsto (fun N => F N z) atTop (𝓝 ((fun _ => (0:ℝ≥0∞)) z)) := by
    filter_upwards [hae] with z hz
    have hr : Tendsto (fun N => ∑' p, f N z p) atTop (𝓝 (∑' p : ℤ × Fin 2, (0:ℝ))) := by
      refine tendsto_tsum_of_dominated_convergence (hσ.mul_left (4 * B ^ 2)) ?_
        (Eventually.of_forall fun N p => ?_)
      · intro p
        have h1 := S.tendsto_truncatedDeriv_apply_basis G hG z hz p
        have h2 := (tendsto_iff_norm_sub_tendsto_zero.1 h1).pow 2
        simpa using h2
      · rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact hbd N z p
    rw [tsum_zero] at hr
    have h := ENNReal.tendsto_ofReal hr
    rw [ENNReal.ofReal_zero] at h
    refine h.congr (fun N => ?_)
    rw [hF]
    exact (ENNReal.ofReal_tsum_of_nonneg (fun p => sq_nonneg _) (hsumm N z))
  have hFle : ∀ N z, F N z ≤ ENNReal.ofReal (∑' p, 4 * B ^ 2 * σ p) := by
    intro N z
    rw [hF]
    dsimp only
    rw [← ENNReal.ofReal_tsum_of_nonneg (f := f N z) (fun p => sq_nonneg _) (hsumm N z)]
    exact ENNReal.ofReal_le_ofReal
      ((hsumm N z).tsum_le_tsum (hbd N z) (hσ.mul_left _))
  show Tendsto (fun N => ∫⁻ z, F N z ∂γ) atTop (𝓝 0)
  have := tendsto_lintegral_of_dominated_convergence (μ := γ)
    (F := F) (f := fun _ => 0)
    (fun _ => ENNReal.ofReal (∑' p, 4 * B ^ 2 * σ p)) hFm
    (fun N => Eventually.of_forall fun z => hFle N z)
    (by
      rw [lintegral_const, measure_univ, mul_one]
      exact ENNReal.ofReal_ne_top)
    hlim
  simpa using this

/-! ### Hilbert-Schmidt norm of the finite head in the coordinate basis -/

theorem basis_mem_head (N : ℕ) (p : ℤ × Fin 2) (hp : p.1 ∈ symmetricModes N) :
    weightedRealHilbertBasis S.cmWeight p ∈ S.head N :=
  fun n hn => S.hcoord_basis_of_ne p n (fun h => hn (h ▸ hp))

theorem repr_basis_eq_zero_of_mem_head (N : ℕ) (v : S.H) (hv : v ∈ S.head N) (p : ℤ × Fin 2)
    (hp : p.1 ∉ symmetricModes N) :
    (weightedRealHilbertBasis S.cmWeight).repr v p = 0 := by
  rw [HilbertBasis.repr_apply_apply, weightedRealHilbertBasis_apply,
    weightedRealBasisVector_inner]
  have h0 : (show WeightedHilbert S.cmWeight from v) p.1 = 0 := hv p.1 hp
  have : (weightedIsometry S.cmWeight) (show WeightedHilbert S.cmWeight from v) p.1
      = 0 := by
    rw [weightedIsometry_apply]
    simp [weightedCoordinates, h0]
  rw [this]
  simp

/-- The coordinate basis vectors `b_p`, `p.1 ∈ {-N..N}`, form an orthonormal basis of the head. -/
def headBasis (N : ℕ) : OrthonormalBasis (headIndex N) ℝ (S.head N) :=
  OrthonormalBasis.mk (v := fun p : headIndex N =>
      (⟨weightedRealHilbertBasis S.cmWeight p.1,
        S.basis_mem_head N p.1 (mem_headIndex.1 p.2)⟩ : S.head N))
    (by
      have h := ((weightedRealHilbertBasis S.cmWeight).orthonormal.comp
        (fun p : headIndex N => p.1) Subtype.val_injective)
      exact Orthonormal.codRestrict h (S.head N)
        (fun p => S.basis_mem_head N p.1 (mem_headIndex.1 p.2)))
    (by
      intro x _
      set b := weightedRealHilbertBasis S.cmWeight with hb
      have hsum : HasSum (fun p : ℤ × Fin 2 => b.repr (x : S.H) p • b p)
          (x : S.H) := b.hasSum_repr _
      have hfin : HasSum (fun p : ℤ × Fin 2 => b.repr (x : S.H) p • b p)
          (∑ p ∈ headIndex N, b.repr (x : S.H) p • b p) :=
        hasSum_sum_of_ne_finset_zero (fun p hp => by
          rw [S.repr_basis_eq_zero_of_mem_head N _ x.2 p (fun h => hp (mem_headIndex.2 h)),
            zero_smul])
      have heq : (x : S.H) = ∑ p ∈ headIndex N, b.repr (x : S.H) p • b p :=
        hsum.unique hfin
      have hx : x = ∑ p : headIndex N, b.repr (x : S.H) p.1 •
          (⟨b p.1, S.basis_mem_head N p.1 (mem_headIndex.1 p.2)⟩ : S.head N) := by
        apply Subtype.ext
        refine heq.trans ?_
        rw [Submodule.coe_sum]
        exact (Finset.sum_coe_sort (headIndex N)
          (fun p => b.repr (x : S.H) p • b p)).symm
      rw [hx]
      exact Submodule.sum_mem _ (fun p _ => Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self p))))

theorem headToE_basis (N : ℕ) (p : ℤ × Fin 2) (hp : p.1 ∈ symmetricModes N) :
    S.headToE N ⟨weightedRealHilbertBasis S.cmWeight p, S.basis_mem_head N p hp⟩ =
      S.incl (weightedRealHilbertBasis S.cmWeight p) := rfl

/-- **Hilbert-Schmidt norm on the head.** -/
theorem hsNormSq_fderiv_truncatedField
    (G : S.E → S.H) (hG : Differentiable ℝ G)
    (N : ℕ) (v : S.head N) :
    hsNormSq (fderiv ℝ (fun w : S.head N => S.cmTrunc N (G (S.headToE N w))) v) =
      ∑' p : ℤ × Fin 2, ‖S.cmTrunc N (fderiv ℝ G (S.headToE N v)
        (S.incl ((S.cmTrunc N (weightedRealHilbertBasis S.cmWeight p) :
            S.head N) : S.H)))‖ ^ 2 := by
  have hA : HasFDerivAt (fun w : S.head N => S.cmTrunc N (G (S.headToE N w)))
      ((S.cmTrunc N).comp ((fderiv ℝ G (S.headToE N v)).comp (S.headToE N))) v :=
    (S.cmTrunc N).hasFDerivAt.comp v
      ((hG (S.headToE N v)).hasFDerivAt.comp v (S.headToE N).hasFDerivAt)
  rw [hA.fderiv, hsNormSq_eq_sum_norm_sq (S.headBasis N)]
  rw [tsum_eq_sum (s := headIndex N)]
  · rw [← Finset.sum_coe_sort (headIndex N)]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hq := mem_headIndex.1 q.2
    have hb : (S.headBasis N q : S.head N) =
        ⟨weightedRealHilbertBasis S.cmWeight q.1, S.basis_mem_head N q.1 hq⟩ := by
      exact congrFun (OrthonormalBasis.coe_mk _ _) q
    rw [hb]
    change ‖S.cmTrunc N (fderiv ℝ G (S.headToE N v) (S.headToE N
      ⟨weightedRealHilbertBasis S.cmWeight q.1, S.basis_mem_head N q.1 hq⟩))‖ ^ 2 = _
    rw [S.headToE_basis N q.1 hq, S.cmTrunc_basis_of_mem N q.1 hq]
  · intro p hp
    rw [S.cmTrunc_basis_of_not_mem N p (fun h => hp (mem_headIndex.2 h)),
      S.incl.map_zero, (fderiv ℝ G (S.headToE N v)).map_zero,
      (S.cmTrunc N).map_zero]
    simp

end NlsGge.Ramer.General.RamerSetting
