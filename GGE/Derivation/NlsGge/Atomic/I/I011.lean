import Mathlib
import NlsGge.Spectral.ActualGapHeightHolderE02_38
import NlsGge.Spectral.ActualQuasimomentumBoundaryFunctionE02_38
import NlsGge.Herglotz38.TruncatedSymmetrizationE02_38

/- I-011 PROOF01 (proof development). Main statement verbatim from the supplemental design (section I-011, node I011.main).
   House reuse: truncKernelE02_38 with truncKernelE02_38_swap and measurable_truncKernelE02_38 (TruncatedSymmetrizationE02_38.lean),
   continuous_actualGapHeightE02_38, continuous_actualQuasimomentumRealPartE02_38, actualGapHeight_support_finiteGap_E02_38.
   Route: v = actualGapHeightE02_38 u is continuous with compact support (zero outside [-A,A]); the kernel K is measurable and
   bounded by sup|v|^2/eps with support in the compact square; phi is continuous. Integrability by domination, Fubini for the
   iterated identity, swap antisymmetry for the symmetrized identity. Interface adaptation: none. -/

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff
open NlsGge.Pilot NlsGge.Schur NlsGge.Analysis
open NlsGge.SpectralFoundations

/-- Pointwise identity: the truncated kernel times a weight in the first variable is a product of
    the weight and the indicator of the inner set (split out to keep the main proof within heartbeats). -/
theorem I011_pt (v : ℝ → ℝ) (ε x t c : ℝ) :
    c * truncKernelE02_38 v ε (x, t) =
      (c * v x) * {t : ℝ | ε < |t-x|}.indicator (fun t => v t / (x-t)) t := by
  unfold truncKernelE02_38
  by_cases h : ε < |t - x|
  · have h' : ε < |(x, t).2 - (x, t).1| := h
    rw [Set.indicator_of_mem (show (x, t) ∈ {q : ℝ × ℝ | ε < |q.2 - q.1|} from h'),
      Set.indicator_of_mem (show t ∈ {t : ℝ | ε < |t - x|} from h)]
    simp only
    ring
  · have h' : ¬ ε < |(x, t).2 - (x, t).1| := h
    rw [Set.indicator_of_notMem (show (x, t) ∉ {q : ℝ × ℝ | ε < |q.2 - q.1|} from h'),
      Set.indicator_of_notMem (show t ∉ {t : ℝ | ε < |t - x|} from h)]
    ring


/-- Swap antisymmetry of the weighted truncated kernel (top-level, explicit functions). -/
theorem I011_swap (v φ : ℝ → ℝ) (ε : ℝ) (hint : Integrable (fun q : ℝ × ℝ => φ q.1 * truncKernelE02_38 v ε q)) :
    ∫ q : ℝ × ℝ, φ q.2 * truncKernelE02_38 v ε q = -∫ q : ℝ × ℝ, φ q.1 * truncKernelE02_38 v ε q := by
  have hK : ∀ q : ℝ × ℝ, truncKernelE02_38 v ε q.swap = -truncKernelE02_38 v ε q :=
    fun q => truncKernelE02_38_swap _ _ q
  have hmp : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume :=
    Measure.measurePreserving_swap
  have hkey : ∫ q : ℝ × ℝ, φ q.swap.1 * truncKernelE02_38 v ε q.swap =
      ∫ q : ℝ × ℝ, φ q.1 * truncKernelE02_38 v ε q :=
    integral_prod_swap (μ := volume) (ν := volume) (fun q : ℝ × ℝ => φ q.1 * truncKernelE02_38 v ε q)
  have hfun : (fun q : ℝ × ℝ => φ q.2 * truncKernelE02_38 v ε q) =
      fun q : ℝ × ℝ => -(φ q.swap.1 * truncKernelE02_38 v ε q.swap) := by
    funext q
    rw [hK q, Prod.fst_swap]
    ring
  rw [hfun, integral_neg, hkey]

/-- Fubini for the weighted truncated kernel (top-level, explicit functions). -/
theorem I011_fubini (v φ : ℝ → ℝ) (ε : ℝ)
    (hint : Integrable (fun q : ℝ × ℝ => φ q.1 * truncKernelE02_38 v ε q)) :
    ∫ q : ℝ × ℝ, φ q.1 * truncKernelE02_38 v ε q =
      ∫ x : ℝ, φ x * v x * ∫ t in {t : ℝ | ε < |t-x|}, v t / (x-t) := by
  have hfub0 : ∫ q : ℝ × ℝ, φ q.1 * truncKernelE02_38 v ε q =
      ∫ x : ℝ, ∫ t : ℝ, φ x * truncKernelE02_38 v ε (x, t) :=
    integral_prod (μ := volume) (ν := volume) (fun q : ℝ × ℝ => φ q.1 * truncKernelE02_38 v ε q) hint
  rw [hfub0]
  congr 1
  funext x
  have hpt : ∀ t : ℝ, φ x * truncKernelE02_38 v ε (x, t) =
      (φ x * v x) * {t : ℝ | ε < |t-x|}.indicator (fun t => v t / (x-t)) t :=
    fun t => I011_pt v ε x t (φ x)
  simp_rw [hpt]
  rw [integral_const_mul]
  congr 1
  exact integral_indicator (measurableSet_lt measurable_const
    ((continuous_id.sub continuous_const).abs.measurable))

namespace NlsGge.Atomic.I011

theorem truncatedHilbert_symmetrization
    (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (hfin : {n : ℤ |
      actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n}.Finite)
    (W : ℝ → ℝ) (hW : ContDiff ℝ 2 W)
    (hconv : ConvexOn ℝ Set.univ W) (ε : ℝ) (hε : 0 < ε) :
    let φ : ℝ → ℝ := fun x =>
      deriv (fun y : ℝ => W (2*y)) (actualQuasimomentumRealPartE02_38 u x)
    let K := truncKernelE02_38 (actualGapHeightE02_38 u) ε
    Integrable (fun q : ℝ × ℝ => φ q.1 * K q) ∧
    Integrable (fun q : ℝ × ℝ => (φ q.1 - φ q.2) * K q) ∧
    2 * (∫ x : ℝ, φ x * actualGapHeightE02_38 u x *
      ∫ t in {t : ℝ | ε < |t-x|}, actualGapHeightE02_38 u t / (x-t)) =
        ∫ q : ℝ × ℝ, (φ q.1 - φ q.2) * K q := by
  intro φ K
  -- continuity and compact support of the gap height
  have hv : Continuous (actualGapHeightE02_38 u) := continuous_actualGapHeightE02_38 u
  obtain ⟨-, A, hA⟩ := actualGapHeight_support_finiteGap_E02_38 u hfin
  have hvcs : HasCompactSupport (actualGapHeightE02_38 u) :=
    HasCompactSupport.intro (isCompact_Icc (a := -A) (b := A)) (fun x hx =>
      hA x (lt_of_not_ge fun h => hx ⟨(abs_le.mp h).1, (abs_le.mp h).2⟩))
  -- continuity of phi
  have hp : Continuous (actualQuasimomentumRealPartE02_38 u) := continuous_actualQuasimomentumRealPartE02_38 u
  have hd : Continuous (fun y : ℝ => deriv (fun z : ℝ => W (2*z)) y) := by
    have hfun : (fun y : ℝ => deriv (fun z : ℝ => W (2*z)) y) = fun y => 2 * deriv W (2*y) := by
      funext y
      rw [deriv_comp_mul_left]
      ring
    rw [hfun]
    exact continuous_const.mul ((hW.continuous_deriv (by norm_num)).comp (continuous_const.mul continuous_id))
  have hφ : Continuous φ := hd.comp hp
  -- kernel bounds and support
  obtain ⟨M, hM⟩ := hv.bounded_above_of_compact_support hvcs
  set S : Set (ℝ × ℝ) := Icc (-A) A ×ˢ Icc (-A) A with hSdef
  have hS_meas : MeasurableSet S := (isCompact_Icc.prod isCompact_Icc).isClosed.measurableSet
  have hS_fin : volume S ≠ ⊤ := ((isCompact_Icc.prod isCompact_Icc).measure_lt_top).ne
  have hK_supp : ∀ q : ℝ × ℝ, K q ≠ 0 → q ∈ S := by
    intro q hq
    simp only [K, truncKernelE02_38, Set.indicator_apply] at hq
    split_ifs at hq with hmem
    · have hv1 : actualGapHeightE02_38 u q.1 ≠ 0 := fun h => by simp [h] at hq
      have hv2 : actualGapHeightE02_38 u q.2 ≠ 0 := fun h => by simp [h] at hq
      have h1 : q.1 ∈ Icc (-A) A := abs_le.mp (by
        by_contra hc; exact hv1 (hA q.1 (not_le.mp hc)))
      have h2 : q.2 ∈ Icc (-A) A := abs_le.mp (by
        by_contra hc; exact hv2 (hA q.2 (not_le.mp hc)))
      exact ⟨h1, h2⟩
    · exact absurd rfl hq
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hK_bound : ∀ q : ℝ × ℝ, ‖K q‖ ≤ M * M / ε := by
    intro q
    simp only [K, truncKernelE02_38, Set.indicator_apply]
    split_ifs with hmem
    · have hd : ε ≤ ‖q.1 - q.2‖ := by
        rw [Real.norm_eq_abs, abs_sub_comm]; exact hmem.le
      rw [norm_div, norm_mul]
      exact div_le_div₀ (mul_nonneg hM0 hM0)
        (mul_le_mul (hM q.1) (hM q.2) (norm_nonneg _) hM0) hε hd
    · simp only [norm_zero]
      exact div_nonneg (mul_nonneg hM0 hM0) hε.le
  have hgen : ∀ F : ℝ × ℝ → ℝ, Continuous F → ∀ C : ℝ, (∀ q ∈ S, ‖F q‖ ≤ C) →
      Integrable (fun q : ℝ × ℝ => F q * K q) := by
    intro F hF C hC
    refine Integrable.mono' (g := S.indicator (fun _ => C * (M * M / ε))) ?_ ?_ ?_
    · exact (integrable_indicator_iff hS_meas).2 (integrableOn_const hS_fin)
    · exact (hF.measurable.mul (measurable_truncKernelE02_38 _ hv ε)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun q => ?_)
      by_cases hq : q ∈ S
      · rw [indicator_of_mem hq, norm_mul]
        exact mul_le_mul (hC q hq) (hK_bound q) (norm_nonneg _) (le_trans (norm_nonneg _) (hC q hq))
      · have hK0 : K q = 0 := by
          by_contra h; exact hq (hK_supp q h)
        simp [hK0, indicator_of_notMem hq]
  obtain ⟨Φ, hΦ⟩ := (isCompact_Icc (a := -A) (b := A)).exists_bound_of_continuousOn hφ.continuousOn
  have hφS1 : ∀ q ∈ S, ‖φ q.1‖ ≤ Φ := fun q hq => hΦ q.1 hq.1
  have hφS2 : ∀ q ∈ S, ‖φ q.2‖ ≤ Φ := fun q hq => hΦ q.2 hq.2
  have hint1 : Integrable (fun q : ℝ × ℝ => φ q.1 * K q) :=
    hgen (fun q => φ q.1) (hφ.comp continuous_fst) Φ hφS1
  have hint2 : Integrable (fun q : ℝ × ℝ => φ q.2 * K q) :=
    hgen (fun q => φ q.2) (hφ.comp continuous_snd) Φ hφS2
  have hint3 : Integrable (fun q : ℝ × ℝ => (φ q.1 - φ q.2) * K q) :=
    hgen (fun q => φ q.1 - φ q.2) ((hφ.comp continuous_fst).sub (hφ.comp continuous_snd)) (Φ + Φ)
      (fun q hq => (norm_sub_le _ _).trans (add_le_add (hφS1 q hq) (hφS2 q hq)))
  have hswap := I011_swap (actualGapHeightE02_38 u) φ ε hint1
  have hfub := I011_fubini (actualGapHeightE02_38 u) φ ε hint1
  -- conclusion
  have hsplit : (fun q : ℝ × ℝ => (φ q.1 - φ q.2) * K q) =
      fun q : ℝ × ℝ => φ q.1 * K q - φ q.2 * K q := funext fun q => by ring
  refine ⟨hint1, hint3, ?_⟩
  rw [hsplit, integral_sub hint1 hint2, hswap, hfub, sub_neg_eq_add, two_mul]

end NlsGge.Atomic.I011
