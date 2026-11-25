import Mathlib
import NlsGge.Atomic.G1.G1066
import NlsGge.Atomic.G1.G1084
import NlsGge.Atomic.G5.G5029Host
import NlsGge.Atomic.G5.G5029Sup1
import NlsGge.Atomic.G5.G5029Sup2
import NlsGge.GK38.EigenvalueCompactnessStrong
import NlsGge.GK38.DirichletRealContinuity
import NlsGge.GK38.GradEigenRealPeriodicLabels

/- G5-029 SUPPORT 3 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5029Sup3.lean, namespace NlsGge.GKDefinitionDesign.
   Head `allDirichletLeft_openGaps_approximation` VERBATIM from PRO_DEFINITION_RESPONSE_FP80_14.md "G5029: all-left density".
   Route (Pro steps 1-5): G1-066 gives all-gap-open base potentials b_j -> u; G1-084 gives w_j in Iso(b_j) with signed datum
   (lower endpoint, 0) at every gap (endpoint antidiscriminant zero), so w_j is all-left with all gaps open; any subsequence has a
   further subsequence converging strongly (Sup1) to an isospectral limit that is all-left (continuity of gkMu and of the lower endpoints),
   hence equals u (Sup2); tendsto_of_subseq_tendsto. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem left_datum_mem_gapCircle (b : PhysicalL2) (n : ℤ)
    (h : actualGapLowerAllE02_38 b n < actualGapUpperAllE02_38 b n) :
    ((actualGapLowerAllE02_38 b n, (0 : ℝ)) : ℝ × ℝ) ∈ gapCircle b n := by
  refine ⟨le_rfl, h.le, ?_⟩
  have hd := (NlsGge.GK38.gap_discrim_endpoint_values38 b n).1
  rw [hd]
  have hs : Real.sin ((n : ℝ) * Real.pi) = 0 := Real.sin_int_mul_pi n
  have h1 := Real.sin_sq_add_cos_sq ((n : ℝ) * Real.pi)
  rw [hs] at h1
  have hre : (2 * (Real.cos ((n : ℝ) * Real.pi) : ℂ)) =
      (((2 * Real.cos ((n : ℝ) * Real.pi)) : ℝ) : ℂ) := by push_cast; ring
  rw [hre, Complex.ofReal_re]
  nlinarith [h1]

theorem allDirichletLeft_openGaps_approximation
    (u : PhysicalL2) (hu : AllDirichletLeft u) (F : Finset ℤ) :
  ∃ v : ℕ → PhysicalL2, Tendsto v atTop (𝓝 u) ∧
    (∀ j : ℕ, AllDirichletLeft (v j)) ∧
    ∀ (j : ℕ) (n : ℤ), n ∈ F → gamma2 (realSlice (v j)) n ≠ 0 := by
  -- base potentials with every gap open
  have hdense := (NlsGge.Atomic.G1066.G1_066).1
  have hb : ∀ j : ℕ, ∃ y ∈ {u : PhysicalL2 | ∀ n : ℤ,
      actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n},
      dist u y < 1 / ((j : ℝ) + 1) := fun j =>
    hdense.exists_dist_lt u (by positivity)
  choose b hbS hbd using hb
  have hbt : Tendsto b atTop (𝓝 u) := by
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg)
      (fun j => ?_) tendsto_one_div_add_atTop_nhds_zero_nat)
    rw [dist_comm]; exact (hbd j).le
  -- left-endpoint isospectral companions
  have hex : ∀ j : ℕ, ∃ w : PhysicalL2, w ∈ isospectralSet (b j) ∧
      signedDirichletData w = fun n => (actualGapLowerAllE02_38 (b j) n, (0 : ℝ)) := by
    intro j
    have hp : (fun n : ℤ => ((actualGapLowerAllE02_38 (b j) n, (0 : ℝ)) : ℝ × ℝ)) ∈
        gapCircleProduct (b j) := fun n => left_datum_mem_gapCircle (b j) n (hbS j n)
    exact (G1_084 (b j)).2.2 hp
  choose w hwiso hwdat using hex
  have hwleft : ∀ j : ℕ, AllDirichletLeft (w j) := by
    intro j n
    have h1 : gkMu (w j) n = actualGapLowerAllE02_38 (b j) n := by
      have := congrFun (hwdat j) n
      exact congrArg Prod.fst this
    rw [h1]
    exact (isospectral_gapLower_eq (hwiso j) n).symm
  have hwgap : ∀ j : ℕ, ∀ n : ℤ, gamma2 (realSlice (w j)) n ≠ 0 := by
    intro j n
    have hl : actualGapLowerAllE02_38 (w j) n < actualGapUpperAllE02_38 (w j) n := by
      rw [isospectral_gapLower_eq (hwiso j) n, isospectral_gapUpper_eq (hwiso j) n]
      exact hbS j n
    obtain ⟨hP, hM⟩ := lamPlus_real (w j) n
    rw [gamma2_value38 _ (realSlice_mem_gkW (w j)) n, hP, hM, ← Complex.ofReal_sub]
    exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hl.ne'))
  refine ⟨w, ?_, hwleft, fun j n _ => hwgap j n⟩
  refine tendsto_of_subseq_tendsto (fun ns hns => ?_)
  obtain ⟨s, wl, hs, hwl, hisol⟩ := isospectral_subsequence_of_base_tendsto u (b ∘ ns) (w ∘ ns)
    (hbt.comp hns) (fun j => hwiso (ns j))
  have hleft : AllDirichletLeft wl := by
    intro n
    have h1 : Tendsto (fun k => gkMu ((w ∘ ns) (s k)) n) atTop (𝓝 (gkMu wl n)) :=
      ((continuous_gkMu38 n).tendsto wl).comp hwl
    have h2 : Tendsto (fun k => actualGapLowerAllE02_38 ((w ∘ ns) (s k)) n) atTop
        (𝓝 (actualGapLowerAllE02_38 wl n)) :=
      (((gapEndpoints_L2_continuous38 n).1).tendsto wl).comp hwl
    have h3 : (fun k => gkMu ((w ∘ ns) (s k)) n) =
        fun k => actualGapLowerAllE02_38 ((w ∘ ns) (s k)) n :=
      funext fun k => hwleft (ns (s k)) n
    rw [h3] at h1
    exact tendsto_nhds_unique h1 h2
  have hEq : u = wl := allDirichletLeft_isospectral_unique u wl hu hleft hisol
  refine ⟨s, ?_⟩
  rw [← hEq] at hwl
  exact hwl

end
end NlsGge.GKDefinitionDesign
