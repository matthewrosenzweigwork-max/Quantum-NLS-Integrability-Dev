import NlsGge.Atomic.AL.AL086
import NlsGge.Hierarchy.ALCorrector38
import NlsGge.ThirdConsultation.T.ECarrier98
import NlsGge.Atomic.R.R111
import NlsGge.Atomic.F.F027
import NlsGge.Birkhoff.F08Bare38d
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.MutuallySingular

/- G10/G11 AUTHOR candidate 02, proof development. Awaiting root round-2 compilation.
   Round 1 checked G10; the full probe failed on alias/rewrite diagnostics.
   This revision changes proof terms only. Independent review remains pending.
   Baseline: 16f37e1a1f0f50ed32a1e513759984d6bb9275d9.
   G10 reuses the landed actual lattice law and compact escape in AL.al086.
   G11 concerns the actual Lebesgue Fourier-plane laws, with the concrete PDE
   providers. Finite-gap singularity I.i027 is a separate statement.
   Root owns every compiler invocation; this text is not an acceptance receipt. -/

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators
open NlsGge.Pilot NlsGge.Measure NlsGge.Birkhoff NlsGge.Sobolev38
open NlsGge.HierarchyRiccati.Core NlsGge.AblowitzLadik

namespace NlsGge.ThirdConsultation.Narrative

/-- Every tail of the existing uncorrected lattice laws escapes compact sets,
so it fails the standard Mathlib tightness predicate. -/
theorem grouped_lattice_reference_tail_not_tight {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ) (N0 : ℕ) :
    ¬ IsTightMeasureSet
      (Set.range (fun n : ℕ => AL.alCriticalLaw c s (N0 + n))) := by
  obtain ⟨hreal, -, hcompact, -⟩ := AL.al086 lo up c s
  intro ht
  obtain ⟨K, hKc, hK⟩ :=
    (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 ht)
      (ENNReal.ofReal (1 / 2)) (ENNReal.ofReal_pos.2 (by norm_num))
  have hshift : Tendsto (fun n : ℕ => N0 + n) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat N0
  have hKT : Tendsto (fun n : ℕ => AL.alCriticalLaw c s (N0 + n) K)
      atTop (𝓝 0) := (hcompact K hKc).comp hshift
  obtain ⟨n, hn⟩ := (hKT.eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.2 (by norm_num : (0 : ℝ) < 1 / 4)))).exists
  haveI : IsProbabilityMeasure (AL.alCriticalLaw c s (N0 + n)) := by
    unfold AL.alCriticalLaw
    refine ⟨?_⟩
    rw [Measure.map_apply (hreal (N0 + n)).1 MeasurableSet.univ, Set.preimage_univ]
    exact measure_univ
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 2) := by
    calc
      (1 : ℝ≥0∞) = AL.alCriticalLaw c s (N0 + n) K +
          AL.alCriticalLaw c s (N0 + n) Kᶜ := by
        rw [measure_add_measure_compl hKc.isClosed.measurableSet]
        exact (measure_univ : AL.alCriticalLaw c s (N0 + n) Set.univ = 1).symm
      _ ≤ _ := add_le_add hn.le (hK _ ⟨n, rfl⟩)
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num), ENNReal.one_le_ofReal] at h1
  norm_num at h1

/-- v2:2235–2239, with the positive-rate tail produced from the source coefficient
class. `AL.alCriticalLaw` is the existing measurable pushforward of the actual
coupled field `g_k / sqrt(a_{h,k})` into the completed `E_s` carrier. -/
theorem grouped_lattice_reference_not_tight {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ) :
    ∃ N0 : ℕ,
      (∀ N ≥ N0, ∀ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        0 < alRateFree38 c.val N k) ∧
      ¬ IsTightMeasureSet
        (Set.range (fun n : ℕ => AL.alCriticalLaw c s (N0 + n))) := by
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1
    (alRateFree_pos_eventually38 (AL.al080Aux.admissible c))
  refine ⟨N0, ?_, grouped_lattice_reference_tail_not_tight c s N0⟩
  intro N hN k hk
  exact hN0 N hN k (abs_le.2 (Finset.mem_Icc.1 hk))

/-- A proper complex Gaussian with positive rate gives every singleton mass zero. -/
theorem grouped_complexGaussian_singleton_zero (a : ℝ) (ha : 0 < a) (z : ℂ) :
    complexGaussian a {z} = 0 := by
  rw [complexGaussian_density a ha]
  exact withDensity_absolutelyContinuous _ _ (measure_singleton z)

/-- Actual marginal of a reflected Fourier coefficient of the full physical Gaussian.
The reflection and phase are retained by `fourierSeq38`, `physFW06_38`, and `coordE`. -/
theorem grouped_full_fourier_gaussian_map_coeff {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ) (hs : (1 : ℝ) / 2 < s) (n : ℤ) :
    (R.actualFourierGaussian c s).map (fun u : PhysicalL2 => fourierSeq38 u n) =
      complexGaussian (fullWeightRate c.val n) := by
  have hm : Measurable (fun u : PhysicalL2 => fourierSeq38 u n) :=
    (measurable_pi_apply n).comp measurable_fourierSeq38
  unfold R.actualFourierGaussian
  rw [Measure.map_map hm (continuous_physFW06_38 c s).measurable]
  have hcomp : (fun u : PhysicalL2 => fourierSeq38 u n) ∘ physFW06_38 c s =
      (fun z : ℤ → ℂ => z n) ∘ NlsGge.Ramer.coordE c s := by
    funext x
    change fourierSeq38 (physOfE38 c s x) n = NlsGge.Ramer.coordE c s x n
    exact congrFun (fourierSeq38_physOfE38 c s
      (show ECarrier38 c s from x)) n
  rw [hcomp, ← Measure.map_map (measurable_pi_apply n) (NlsGge.Ramer.measurable_coordE c s),
    (NlsGge.Ramer.measurePreserving_coordE c s hs).map_eq]
  exact fullWeightSequenceGaussian_map_eval c.val n

/-- The actual full limiting Gibbs law assigns zero mass to a zero Fourier coefficient. -/
theorem grouped_full_limit_zero_coeff_null {lo up : ℝ}
    (c : BoundedCoefficients lo up) (n : ℤ) :
    PDE.actualBirkhoffTop38.muW38 c.val {u : PhysicalL2 | fourierSeq38 u n = 0} = 0 := by
  have hm : Measurable (fun u : PhysicalL2 => fourierSeq38 u n) :=
    (measurable_pi_apply n).comp measurable_fourierSeq38
  have hzero : R.actualFourierGaussian c (5 / 8)
      {u : PhysicalL2 | fourierSeq38 u n = 0} = 0 := by
    change R.actualFourierGaussian c (5 / 8)
      ((fun u : PhysicalL2 => fourierSeq38 u n) ⁻¹' ({0} : Set ℂ)) = 0
    rw [← Measure.map_apply hm (measurableSet_singleton (0 : ℂ)),
      grouped_full_fourier_gaussian_map_coeff c (5 / 8) (by norm_num)]
    exact grouped_complexGaussian_singleton_zero _ (sourceRate_pos c n) 0
  exact (R.actual_mutually_absolutelyContinuous c (5 / 8)
    (by norm_num) (by norm_num)).1 hzero

/-- The first omitted reflected Fourier coefficient vanishes on the actual spatial plane. -/
theorem grouped_planeL2_high_coefficient_zero (N : ℕ) (z : FourierPlane N) :
    fourierSeq38 (planeL2 N z) ((N : ℤ) + 1) = 0 := by
  rw [fourierSeq38_apply, physicalFourier_planeL2,
    physicalFourier_planeField_outside N z (-((N : ℤ) + 1)) (Or.inl (by omega)), neg_zero]

/-- The actual finite spatial Fourier plane is a null set for the full limiting law. -/
theorem grouped_full_limit_fourier_plane_null {lo up : ℝ}
    (c : BoundedCoefficients lo up) (N : ℕ) :
    PDE.actualBirkhoffTop38.muW38 c.val (Set.range (planeL2 N)) = 0 := by
  refine measure_mono_null ?_ (grouped_full_limit_zero_coeff_null c ((N : ℤ) + 1))
  rintro u ⟨z, rfl⟩
  exact grouped_planeL2_high_coefficient_zero N z

/-- v2:1796–1798. Actual full-energy Lebesgue Fourier-plane field laws are mutually
singular with the actual infinite-dimensional full limiting field law. -/
theorem grouped_fourier_field_singular {lo up : ℝ}
    (c : BoundedCoefficients lo up) (N : ℕ) :
    (nuWN38 c N).MutuallySingular (PDE.actualBirkhoffTop38.muW38 c.val) := by
  let A : Set PhysicalL2 := {u | fourierSeq38 u ((N : ℤ) + 1) = 0}
  have hA : MeasurableSet A :=
    ((measurable_pi_apply ((N : ℤ) + 1)).comp measurable_fourierSeq38)
      (measurableSet_singleton (0 : ℂ))
  refine ⟨Aᶜ, hA.compl, ?_, ?_⟩
  · unfold nuWN38
    rw [Measure.smul_apply, Measure.map_apply (continuous_planeL2 N).measurable hA.compl]
    have hpre : planeL2 N ⁻¹' Aᶜ = ∅ := by
      ext z
      simp [A, grouped_planeL2_high_coefficient_zero]
    rw [hpre, measure_empty, smul_eq_mul, mul_zero]
  · simpa only [compl_compl] using grouped_full_limit_zero_coeff_null c ((N : ℤ) + 1)

/-- Actual one-coordinate marginal of the finite-order physical Fourier Gaussian.
The almost-everywhere realization theorem discharges the off-domain fallback. -/
theorem grouped_finite_order_gaussian_map_coeff (m : ℕ) (hm : 2 ≤ m)
    (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j) (n : ℤ) :
    (gammaFM38 m β).map (fun u : Hm1 m => F.sobolevCoe _ u n) =
      complexGaussian (finiteHierarchyRate38 m β n) := by
  have hcoord : Measurable (fun u : Hm1 m => F.sobolevCoe _ u n) :=
    (F.continuous_sobolevCoe_apply _ n).measurable
  rw [gammaFM38_eq_realization,
    Measure.map_map hcoord measurable_gaussianRealization38]
  calc
    (gammaM38 m β).map ((fun u : Hm1 m => F.sobolevCoe _ u n) ∘
        gaussianRealization38 m) = (gammaM38 m β).map (fun z : ℤ → ℂ => z n) := by
      apply Measure.map_congr
      filter_upwards [ae_gaussianRealization_apply38 hm (fun j hj => (hβ j hj).le)
        (hβ 0 (Nat.zero_le _)) (hβ m le_rfl)] with z hz
      exact hz n
    _ = _ := countableComplexGaussian_map_eval (finiteHierarchyRate38 m β) n

/-- The actual finite-order limiting Gibbs law has no atom at a zero Fourier coefficient. -/
theorem grouped_finite_order_limit_zero_coeff_null (m : ℕ) (hm : 2 ≤ m)
    (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j) (n : ℤ) :
    muM38 PDE.actualBirkhoffInput38 m β {u : Hm1 m | F.sobolevCoe _ u n = 0} = 0 := by
  have hcoord : Measurable (fun u : Hm1 m => F.sobolevCoe _ u n) :=
    (F.continuous_sobolevCoe_apply _ n).measurable
  have hzero : gammaFM38 m β {u : Hm1 m | F.sobolevCoe _ u n = 0} = 0 := by
    change gammaFM38 m β
      ((fun u : Hm1 m => F.sobolevCoe _ u n) ⁻¹' ({0} : Set ℂ)) = 0
    rw [← Measure.map_apply hcoord (measurableSet_singleton (0 : ℂ)),
      grouped_finite_order_gaussian_map_coeff m hm β hβ]
    exact grouped_complexGaussian_singleton_zero _
      (rate_pos38 m β (by omega) (fun j hj => (hβ j hj).le)
        (hβ 0 (Nat.zero_le _)) (hβ m le_rfl) n) 0
  rw [muM38_eq05 PDE.actualBirkhoffInput38 PDE.actualOneSmoothingInput38 hm hβ]
  exact withDensity_absolutelyContinuous _ _ hzero

/-- The first omitted ordinary Fourier coefficient vanishes in every Sobolev plane. -/
theorem grouped_planeElement_high_coefficient_zero (r : ℝ) (N : ℕ) (z : FourierPlane N) :
    F.sobolevCoe r (planeElement38 r N z) ((N : ℤ) + 1) = 0 := by
  change (show WeightedHilbert (sobolevModeWeight r) from
    planeElement38 r N z) ((N : ℤ) + 1) = 0
  rw [planeElement_coeff38]
  apply finiteSeq_zero_off38 N z
  intro hn
  obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hn
  have hib := (modeIndex_bounds N i).2
  omega

/-- The actual finite Fourier plane in `H^(m-1)` is null for the limiting law. -/
theorem grouped_finite_order_limit_fourier_plane_null (m : ℕ) (hm : 2 ≤ m)
    (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j) (N : ℕ) :
    muM38 PDE.actualBirkhoffInput38 m β
      (Set.range (planeElement38 ((m - 1 : ℕ) : ℝ) N)) = 0 := by
  refine measure_mono_null ?_
    (grouped_finite_order_limit_zero_coeff_null m hm β hβ ((N : ℤ) + 1))
  rintro u ⟨z, rfl⟩
  exact grouped_planeElement_high_coefficient_zero _ N z

/-- v2:854–856. Actual finite-hierarchy Lebesgue Fourier-plane laws and their
infinite-dimensional limits are mutually singular on the existing `H^(m-1)` carrier. -/
theorem grouped_finite_order_fourier_field_singular (m : ℕ) (hm : 2 ≤ m)
    (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j) (N : ℕ) :
    (nuBare38 m β N).MutuallySingular (muM38 PDE.actualBirkhoffInput38 m β) := by
  let A : Set (Hm1 m) := {u | F.sobolevCoe _ u ((N : ℤ) + 1) = 0}
  have hA : MeasurableSet A :=
    (F.continuous_sobolevCoe_apply ((m - 1 : ℕ) : ℝ) ((N : ℤ) + 1)).measurable
      (measurableSet_singleton (0 : ℂ))
  refine ⟨Aᶜ, hA.compl, ?_, ?_⟩
  · have hplane : Measurable (planeElement38 ((m - 1 : ℕ) : ℝ) N) :=
      measurable_finiteElement38 ((m - 1 : ℕ) : ℝ) (modeIndex N)
    unfold nuBare38
    rw [Measure.map_apply hplane hA.compl]
    have hpre : planeElement38 ((m - 1 : ℕ) : ℝ) N ⁻¹' Aᶜ = ∅ := by
      ext z
      simp [A, grouped_planeElement_high_coefficient_zero]
    rw [hpre, measure_empty]
  · simpa only [compl_compl] using
      grouped_finite_order_limit_zero_coeff_null m hm β hβ ((N : ℤ) + 1)

end NlsGge.ThirdConsultation.Narrative
