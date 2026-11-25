import Mathlib
import NlsGge.Atomic.R.R021
import NlsGge.Atomic.R.R022
import NlsGge.Ramer.TruncLimitClosedDiv

                                                                                                 
                                                                                      
                                                                               
                                                                                                 
                                                                                                 
                                                                                                         
                                                                                          
                                                                                                                 
set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section

/-- Closed divergence on the actual carriers: `G` is in `L²(μ)`, `d` is in `L²(μ)`, and there are
finite `C²` L² cylindrical cores whose `H`-valued fields and scalar divergences converge in `L²(μ)`
to `G` and `d` (Pro round 6, section 3). -/
def IsClosedDiv
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (G : RamerE c s → RamerH c) (d : RamerE c s → ℝ) : Prop :=
  MemLp G 2 (ramerGaussian c s) ∧
    MemLp d 2 (ramerGaussian c s) ∧
    ∃ (N : ℕ → ℕ)
      (f : ∀ k : ℕ, NlsGge.Ramer.actualCMHead c (N k) →
        NlsGge.Ramer.actualCMHead c (N k)),
      (∀ k : ℕ, GaussianL2CylindricalCore c (N k) (f k)) ∧
      Tendsto
        (fun k : ℕ => eLpNorm
          (fun x : RamerE c s => cylFieldE c s (N k) (f k) x - G x)
          2 (ramerGaussian c s))
        atTop (𝓝 0) ∧
      Tendsto
        (fun k : ℕ => eLpNorm
          (fun x : RamerE c s => cylDivE c s (N k) (f k) x - d x)
          2 (ramerGaussian c s))
        atTop (𝓝 0)

/-- Finite Gaussian L² membership of a `C²` field and its divergence from polynomial bounds. -/
theorem r025_finite_core {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (F : V → V) (hF : ContDiff ℝ 2 F) (A : ℝ) (hA : 0 ≤ A) (k : ℕ)
    (hb : ∀ x, ‖F x‖ ≤ A * (1 + ‖x‖) ^ k)
    (hd : ∀ x, ‖fderiv ℝ F x‖ ≤ A * (1 + ‖x‖) ^ k) :
    MemLp F 2 (NlsGge.Ramer.finiteStdGaussian V) ∧
      MemLp (NlsGge.Ramer.finiteGaussianDivergence F) 2
        (NlsGge.Ramer.finiteStdGaussian V) := by
  have hFc : Continuous F := hF.continuous
  have hdc : Continuous (NlsGge.Ramer.finiteGaussianDivergence F) :=
    (NlsGge.Ramer.contDiff_finiteGaussianDivergence hF).continuous
  constructor
  · rw [memLp_two_iff_integrable_sq_norm hFc.aestronglyMeasurable]
    refine NlsGge.Ramer.integrable_of_le_poly (V := V) (g := fun x => ‖F x‖ ^ 2)
      ((hFc.norm.pow 2).aestronglyMeasurable) (A ^ 2) (k * 2) ?_
    intro x
    try dsimp only
    have h0 : 0 ≤ ‖F x‖ := norm_nonneg _
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc ‖F x‖ ^ 2 ≤ (A * (1 + ‖x‖) ^ k) ^ 2 := pow_le_pow_left₀ h0 (hb x) 2
      _ = A ^ 2 * (1 + ‖x‖) ^ (k * 2) := by rw [mul_pow, ← pow_mul]
  · rw [memLp_two_iff_integrable_sq hdc.aestronglyMeasurable]
    refine NlsGge.Ramer.integrable_of_le_poly (V := V)
      (g := fun x => NlsGge.Ramer.finiteGaussianDivergence F x ^ 2)
      (hdc.pow 2).aestronglyMeasurable
      ((A + (Module.finrank ℝ V : ℝ) * A) ^ 2) ((k + 1) * 2) ?_
    intro x
    try dsimp only
    have h1 := NlsGge.Ramer.abs_finiteGaussianDivergence_le_poly hA hA x (hb x) (hd x)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc NlsGge.Ramer.finiteGaussianDivergence F x ^ 2
        = |NlsGge.Ramer.finiteGaussianDivergence F x| ^ 2 := (sq_abs _).symm
      _ ≤ ((A + (Module.finrank ℝ V : ℝ) * A) * (1 + ‖x‖) ^ (k + 1)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = (A + (Module.finrank ℝ V : ℝ) * A) ^ 2 * (1 + ‖x‖) ^ ((k + 1) * 2) := by
          rw [mul_pow, ← pow_mul]

/-- The Gaussian L² core is stable under subtraction at a common level. -/
theorem r025_core_sub {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (N : ℕ)
    (F G : NlsGge.Ramer.actualCMHead c N → NlsGge.Ramer.actualCMHead c N)
    (hF : GaussianL2CylindricalCore c N F) (hG : GaussianL2CylindricalCore c N G) :
    GaussianL2CylindricalCore c N (fun v => F v - G v) := by
  unfold GaussianL2CylindricalCore at hF hG ⊢
  obtain ⟨hFc, hFL, hFD⟩ := hF
  obtain ⟨hGc, hGL, hGD⟩ := hG
  have hFd : ∀ x, DifferentiableAt ℝ F x := fun x => (hFc.differentiable (by norm_num)) x
  have hGd : ∀ x, DifferentiableAt ℝ G x := fun x => (hGc.differentiable (by norm_num)) x
  have hdiv : NlsGge.Ramer.finiteGaussianDivergence (fun v => F v - G v) =
      fun x => NlsGge.Ramer.finiteGaussianDivergence F x -
        NlsGge.Ramer.finiteGaussianDivergence G x :=
    funext fun x => NlsGge.Ramer.finiteGaussianDivergence_sub F G x (hFd x) (hGd x)
  refine ⟨hFc.sub hGc, hFL.sub hGL, ?_⟩
  rw [hdiv]
  exact hFD.sub hGD

/-- The cylinder field of a difference is the difference of the cylinder fields. -/
theorem r025_cylField_sub {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (N : ℕ)
    (F G : NlsGge.Ramer.actualCMHead c N → NlsGge.Ramer.actualCMHead c N) (z : ℤ → ℂ) :
    NlsGge.Ramer.cylField c N (fun v => F v - G v) z =
      NlsGge.Ramer.cylField c N F z - NlsGge.Ramer.cylField c N G z := by
  unfold NlsGge.Ramer.cylField
  first
    | rfl
    | simp

/-- The cylinder divergence of a difference is the difference of the cylinder divergences. -/
theorem r025_cylDiv_sub {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (N : ℕ)
    (F G : NlsGge.Ramer.actualCMHead c N → NlsGge.Ramer.actualCMHead c N)
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (z : ℤ → ℂ) :
    NlsGge.Ramer.cylDiv c N (fun v => F v - G v) z =
      NlsGge.Ramer.cylDiv c N F z - NlsGge.Ramer.cylDiv c N G z := by
  unfold NlsGge.Ramer.cylDiv
  exact NlsGge.Ramer.finiteGaussianDivergence_sub F G _ (hF _) (hG _)

/-- Transport of an `L²` seminorm from `E_s` to the coordinate law along the realization. -/
theorem r025_eLpNorm_transport {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (φ : RamerE c s → ℝ) (hφ : AEStronglyMeasurable φ (ramerGaussian c s)) :
    eLpNorm φ 2 (ramerGaussian c s) =
      eLpNorm (fun z => φ (NlsGge.Measure.fullWeightedSequenceRealization c s z)) 2
        (NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
  have hR : Measurable (NlsGge.Measure.fullWeightedSequenceRealization c s) :=
    NlsGge.Measure.measurable_fullWeightedSequenceRealization c s
  have hmap : ramerGaussian c s =
      (NlsGge.Measure.fullWeightSequenceGaussian c.val).map
        (NlsGge.Measure.fullWeightedSequenceRealization c s) := rfl
  rw [hmap] at hφ ⊢
  exact eLpNorm_map_measure hφ hR.aemeasurable

/-- The realized coordinates of a raw sample are the sample, almost surely. -/
theorem r025_ae_coord {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s) :
    ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      NlsGge.Ramer.coordE c s (NlsGge.Measure.fullWeightedSequenceRealization c s z) = z := by
  filter_upwards [NlsGge.Measure.ae_fullWeightedSequenceRealization_apply c s hs] with z hz
  funext n
  exact hz n

/-- Existence of the closed divergence of a bounded `C²` field with bounded derivative. -/
theorem exists_isClosedDiv_of_bounded
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s)
    (G : RamerE c s → RamerH c)
    (hG : ContDiff ℝ 2 G)
    (hB : BoundedFieldAndDerivative G) :
    ∃ d : RamerE c s → ℝ, IsClosedDiv c s G d := by
  obtain ⟨C, hC⟩ := hB
  have hGb : ∀ x, ‖G x‖ ≤ C := fun x => (hC x).1
  have hDb : ∀ x, ‖fderiv ℝ G x‖ ≤ C := fun x => (hC x).2
  obtain ⟨η, hη⟩ := NlsGge.Ramer.exists_isClosedDiv_of_bounded c s hs G hG C hGb hDb
  obtain ⟨hηL, N, g, Cg, p, hgC, hgb, hgd, hF, hD⟩ := hη
  obtain ⟨η', hη'sm, hηae⟩ : ∃ η' : (ℤ → ℂ) → ℝ, StronglyMeasurable η' ∧
      η =ᵐ[NlsGge.Measure.fullWeightSequenceGaussian c.val] η' :=
    ⟨hηL.aestronglyMeasurable.mk η, hηL.aestronglyMeasurable.stronglyMeasurable_mk,
      hηL.aestronglyMeasurable.ae_eq_mk⟩
  have hη'L : MemLp η' 2 (NlsGge.Measure.fullWeightSequenceGaussian c.val) :=
    hηL.ae_eq hηae
  have hcoord : Continuous (NlsGge.Ramer.coordE c s) := r021_continuous_coordE c s
  have hR : Measurable (NlsGge.Measure.fullWeightedSequenceRealization c s) :=
    NlsGge.Measure.measurable_fullWeightedSequenceRealization c s
  have hae := r025_ae_coord c s hs
  have hdm : StronglyMeasurable (fun x : RamerE c s => η' (NlsGge.Ramer.coordE c s x)) :=
    hη'sm.comp_measurable hcoord.measurable
  haveI : IsProbabilityMeasure (ramerGaussian c s) := by
    unfold ramerGaussian; infer_instance
  -- finite cores of the production witnesses
  have hcore : ∀ k, GaussianL2CylindricalCore c (N k) (g k) := by
    intro k
    have hA : (0 : ℝ) ≤ |Cg k| := abs_nonneg _
    have hb : ∀ x, ‖g k x‖ ≤ |Cg k| * (1 + ‖x‖) ^ p k := fun x =>
      (hgb k x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    have hd : ∀ x, ‖fderiv ℝ (g k) x‖ ≤ |Cg k| * (1 + ‖x‖) ^ p k := fun x =>
      (hgd k x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    obtain ⟨h1, h2⟩ := r025_finite_core (g k) (hgC k) _ hA (p k) hb hd
    unfold GaussianL2CylindricalCore
    exact ⟨hgC k, h1, h2⟩
  -- the bounded field is in L²
  have hGL : MemLp G 2 (ramerGaussian c s) :=
    MemLp.of_bound hG.continuous.aestronglyMeasurable C (Eventually.of_forall hGb)
  -- the scalar limit on E_s
  have hdL : MemLp (fun x : RamerE c s => η' (NlsGge.Ramer.coordE c s x)) 2
      (ramerGaussian c s) := by
    have hmeas : AEStronglyMeasurable (fun x : RamerE c s => η' (NlsGge.Ramer.coordE c s x))
        (Measure.map (NlsGge.Measure.fullWeightedSequenceRealization c s)
          (NlsGge.Measure.fullWeightSequenceGaussian c.val)) :=
      hdm.aestronglyMeasurable
    have hμ : ramerGaussian c s = (NlsGge.Measure.fullWeightSequenceGaussian c.val).map
        (NlsGge.Measure.fullWeightedSequenceRealization c s) := rfl
    rw [hμ, memLp_map_measure_iff hmeas hR.aemeasurable]
    refine hη'L.ae_eq ?_
    filter_upwards [hae] with z hz
    show η' z = η' (NlsGge.Ramer.coordE c s (NlsGge.Measure.fullWeightedSequenceRealization c s z))
    rw [hz]
  -- the field limit on E_s
  have hFlim : Tendsto (fun k : ℕ => eLpNorm
      (fun x : RamerE c s => cylFieldE c s (N k) (g k) x - G x) 2 (ramerGaussian c s))
      atTop (𝓝 0) := by
    have hEq : ∀ k, eLpNorm (fun x : RamerE c s => cylFieldE c s (N k) (g k) x - G x) 2
        (ramerGaussian c s) = eLpNorm (fun z : ℤ → ℂ =>
          ‖NlsGge.Ramer.cylField c (N k) (g k) z -
            G (NlsGge.Measure.fullWeightedSequenceRealization c s z)‖) 2
          (NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
      intro k
      have hA : AEStronglyMeasurable (fun x : RamerE c s => cylFieldE c s (N k) (g k) x - G x)
          (ramerGaussian c s) :=
        (r021_aesm_cylFieldE c s (N k) (μ := ramerGaussian c s) (g k) (hgC k).continuous).sub
          hG.continuous.aestronglyMeasurable
      calc eLpNorm (fun x : RamerE c s => cylFieldE c s (N k) (g k) x - G x) 2
            (ramerGaussian c s)
          = eLpNorm (fun x : RamerE c s => ‖cylFieldE c s (N k) (g k) x - G x‖) 2
              (ramerGaussian c s) := (eLpNorm_norm _ hA).symm
        _ = eLpNorm (fun z : ℤ → ℂ =>
              ‖cylFieldE c s (N k) (g k)
                (NlsGge.Measure.fullWeightedSequenceRealization c s z) -
                G (NlsGge.Measure.fullWeightedSequenceRealization c s z)‖) 2
              (NlsGge.Measure.fullWeightSequenceGaussian c.val) :=
            r025_eLpNorm_transport c s (fun x => ‖cylFieldE c s (N k) (g k) x - G x‖) hA.norm
        _ = eLpNorm (fun z : ℤ → ℂ =>
              ‖NlsGge.Ramer.cylField c (N k) (g k) z -
                G (NlsGge.Measure.fullWeightedSequenceRealization c s z)‖) 2
              (NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
            refine eLpNorm_congr_ae ?_
            filter_upwards [hae] with z hz
            show ‖cylFieldE c s (N k) (g k)
                (NlsGge.Measure.fullWeightedSequenceRealization c s z) -
                G (NlsGge.Measure.fullWeightedSequenceRealization c s z)‖ =
              ‖NlsGge.Ramer.cylField c (N k) (g k) z -
                G (NlsGge.Measure.fullWeightedSequenceRealization c s z)‖
            unfold cylFieldE
            rw [hz]
    exact hF.congr (fun k => (hEq k).symm)
  -- the divergence limit on E_s
  have hDlim : Tendsto (fun k : ℕ => eLpNorm
      (fun x : RamerE c s => cylDivE c s (N k) (g k) x - η' (NlsGge.Ramer.coordE c s x)) 2
      (ramerGaussian c s)) atTop (𝓝 0) := by
    have hcongr : ∀ k, eLpNorm (fun z : ℤ → ℂ => NlsGge.Ramer.cylDiv c (N k) (g k) z - η z) 2
        (NlsGge.Measure.fullWeightSequenceGaussian c.val) =
        eLpNorm (fun z : ℤ → ℂ => NlsGge.Ramer.cylDiv c (N k) (g k) z - η' z) 2
          (NlsGge.Measure.fullWeightSequenceGaussian c.val) := fun k =>
      eLpNorm_congr_ae (by
        filter_upwards [hηae] with z hz
        simp only [hz])
    have hD' : Tendsto (fun k : ℕ => eLpNorm
        (fun z : ℤ → ℂ => NlsGge.Ramer.cylDiv c (N k) (g k) z - η' z) 2
        (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0) :=
      hD.congr (fun k => hcongr k)
    have hEq2 : ∀ k, eLpNorm (fun x : RamerE c s =>
          cylDivE c s (N k) (g k) x - η' (NlsGge.Ramer.coordE c s x)) 2 (ramerGaussian c s) =
        eLpNorm (fun z : ℤ → ℂ => NlsGge.Ramer.cylDiv c (N k) (g k) z - η' z) 2
          (NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
      intro k
      have hcd : Continuous (fun x : RamerE c s => cylDivE c s (N k) (g k) x) :=
        r021_continuous_cylDivE c s (N k) (g k) ((hgC k).of_le (by norm_num))
      have hA : AEStronglyMeasurable (fun x : RamerE c s =>
          cylDivE c s (N k) (g k) x - η' (NlsGge.Ramer.coordE c s x)) (ramerGaussian c s) :=
        hcd.aestronglyMeasurable.sub hdm.aestronglyMeasurable
      calc eLpNorm (fun x : RamerE c s =>
            cylDivE c s (N k) (g k) x - η' (NlsGge.Ramer.coordE c s x)) 2 (ramerGaussian c s)
          = eLpNorm (fun z : ℤ → ℂ =>
              cylDivE c s (N k) (g k) (NlsGge.Measure.fullWeightedSequenceRealization c s z) -
                η' (NlsGge.Ramer.coordE c s
                  (NlsGge.Measure.fullWeightedSequenceRealization c s z))) 2
              (NlsGge.Measure.fullWeightSequenceGaussian c.val) :=
            r025_eLpNorm_transport c s _ hA
        _ = eLpNorm (fun z : ℤ → ℂ => NlsGge.Ramer.cylDiv c (N k) (g k) z - η' z) 2
              (NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
            refine eLpNorm_congr_ae ?_
            filter_upwards [hae] with z hz
            show cylDivE c s (N k) (g k)
                (NlsGge.Measure.fullWeightedSequenceRealization c s z) -
                η' (NlsGge.Ramer.coordE c s
                  (NlsGge.Measure.fullWeightedSequenceRealization c s z)) =
              NlsGge.Ramer.cylDiv c (N k) (g k) z - η' z
            unfold cylDivE
            rw [hz]
    exact hD'.congr (fun k => (hEq2 k).symm)
  refine ⟨fun x => η' (NlsGge.Ramer.coordE c s x), ?_⟩
  unfold IsClosedDiv
  exact ⟨hGL, hdL, N, g, hcore, hFlim, hDlim⟩

/-- A cylindrical approximation of a difference of two closed-divergence witnesses, at the common level. -/
theorem r025_unique_ae_sub {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s)
    (G : RamerE c s → RamerH c) (d e : RamerE c s → ℝ)
    (N N' : ℕ → ℕ)
    (f : ∀ k : ℕ, NlsGge.Ramer.actualCMHead c (N k) → NlsGge.Ramer.actualCMHead c (N k))
    (f' : ∀ k : ℕ, NlsGge.Ramer.actualCMHead c (N' k) → NlsGge.Ramer.actualCMHead c (N' k))
    (hf : ∀ k : ℕ, GaussianL2CylindricalCore c (N k) (f k))
    (hf' : ∀ k : ℕ, GaussianL2CylindricalCore c (N' k) (f' k))
    (hdL : MemLp d 2 (ramerGaussian c s)) (heL : MemLp e 2 (ramerGaussian c s))
    (hFd : Tendsto (fun k : ℕ => eLpNorm
      (fun x : RamerE c s => cylFieldE c s (N k) (f k) x - G x) 2 (ramerGaussian c s))
      atTop (𝓝 0))
    (hFe : Tendsto (fun k : ℕ => eLpNorm
      (fun x : RamerE c s => cylFieldE c s (N' k) (f' k) x - G x) 2 (ramerGaussian c s))
      atTop (𝓝 0))
    (hDd : Tendsto (fun k : ℕ => eLpNorm
      (fun x : RamerE c s => cylDivE c s (N k) (f k) x - d x) 2 (ramerGaussian c s))
      atTop (𝓝 0))
    (hDe : Tendsto (fun k : ℕ => eLpNorm
      (fun x : RamerE c s => cylDivE c s (N' k) (f' k) x - e x) 2 (ramerGaussian c s))
      atTop (𝓝 0)) :
    (fun x => d x - e x) =ᵐ[ramerGaussian c s] 0 := by
  have hlD : ∀ k, Differentiable ℝ
      (NlsGge.Ramer.liftField c (le_max_left (N k) (N' k)) (f k)) := fun k =>
    (r021_core_contDiff (r021_lift_core c (le_max_left (N k) (N' k)) (f k) (hf k))).differentiable
      (by norm_num)
  have hlD' : ∀ k, Differentiable ℝ
      (NlsGge.Ramer.liftField c (le_max_right (N k) (N' k)) (f' k)) := fun k =>
    (r021_core_contDiff (r021_lift_core c (le_max_right (N k) (N' k)) (f' k) (hf' k))).differentiable
      (by norm_num)
  have hcoreD : ∀ k, GaussianL2CylindricalCore c (max (N k) (N' k))
      (fun v => NlsGge.Ramer.liftField c (le_max_left (N k) (N' k)) (f k) v -
        NlsGge.Ramer.liftField c (le_max_right (N k) (N' k)) (f' k) v) := fun k =>
    r025_core_sub c (max (N k) (N' k))
      (NlsGge.Ramer.liftField c (le_max_left (N k) (N' k)) (f k))
      (NlsGge.Ramer.liftField c (le_max_right (N k) (N' k)) (f' k))
      (r021_lift_core c (le_max_left (N k) (N' k)) (f k) (hf k))
      (r021_lift_core c (le_max_right (N k) (N' k)) (f' k) (hf' k))
  have hcylF : ∀ k x,
      cylFieldE c s (max (N k) (N' k))
        (fun v => NlsGge.Ramer.liftField c (le_max_left (N k) (N' k)) (f k) v -
          NlsGge.Ramer.liftField c (le_max_right (N k) (N' k)) (f' k) v) x =
        cylFieldE c s (N k) (f k) x - cylFieldE c s (N' k) (f' k) x := by
    intro k x
    unfold cylFieldE
    rw [r025_cylField_sub, NlsGge.Ramer.cylField_lift, NlsGge.Ramer.cylField_lift]
  have hcylD : ∀ k x,
      cylDivE c s (max (N k) (N' k))
        (fun v => NlsGge.Ramer.liftField c (le_max_left (N k) (N' k)) (f k) v -
          NlsGge.Ramer.liftField c (le_max_right (N k) (N' k)) (f' k) v) x =
        cylDivE c s (N k) (f k) x - cylDivE c s (N' k) (f' k) x := by
    intro k x
    unfold cylDivE
    rw [r025_cylDiv_sub c (max (N k) (N' k)) _ _ (hlD k) (hlD' k),
      NlsGge.Ramer.cylDiv_lift c (le_max_left (N k) (N' k)) (f k)
        ((r021_core_contDiff (hf k)).differentiable (by norm_num)),
      NlsGge.Ramer.cylDiv_lift c (le_max_right (N k) (N' k)) (f' k)
        ((r021_core_contDiff (hf' k)).differentiable (by norm_num))]
  have hFlim : Tendsto (fun k : ℕ => eLpNorm (fun x : RamerE c s =>
      cylFieldE c s (max (N k) (N' k))
        (fun v => NlsGge.Ramer.liftField c (le_max_left (N k) (N' k)) (f k) v -
          NlsGge.Ramer.liftField c (le_max_right (N k) (N' k)) (f' k) v) x) 2
      (ramerGaussian c s)) atTop (𝓝 0) := by
    have hsplit : ∀ k, eLpNorm (fun x : RamerE c s =>
        cylFieldE c s (max (N k) (N' k))
          (fun v => NlsGge.Ramer.liftField c (le_max_left (N k) (N' k)) (f k) v -
            NlsGge.Ramer.liftField c (le_max_right (N k) (N' k)) (f' k) v) x) 2
        (ramerGaussian c s) ≤
        eLpNorm (fun x : RamerE c s => cylFieldE c s (N k) (f k) x - G x) 2
          (ramerGaussian c s) +
        eLpNorm (fun x : RamerE c s => cylFieldE c s (N' k) (f' k) x - G x) 2
          (ramerGaussian c s) := by
      intro k
      have hfun : (fun x : RamerE c s =>
          cylFieldE c s (max (N k) (N' k))
            (fun v => NlsGge.Ramer.liftField c (le_max_left (N k) (N' k)) (f k) v -
              NlsGge.Ramer.liftField c (le_max_right (N k) (N' k)) (f' k) v) x) =
          (fun x : RamerE c s => cylFieldE c s (N k) (f k) x - G x) -
            (fun x : RamerE c s => cylFieldE c s (N' k) (f' k) x - G x) := by
        funext x
        rw [hcylF k x]
        simp only [Pi.sub_apply]
        abel
      rw [hfun]
      exact eLpNorm_sub_le one_le_two
    have h12 := hFd.add hFe
    rw [add_zero] at h12
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h12
      (fun _ => zero_le) hsplit
  have hDlim : Tendsto (fun k : ℕ => eLpNorm (fun x : RamerE c s =>
      cylDivE c s (max (N k) (N' k))
        (fun v => NlsGge.Ramer.liftField c (le_max_left (N k) (N' k)) (f k) v -
          NlsGge.Ramer.liftField c (le_max_right (N k) (N' k)) (f' k) v) x -
        (d x - e x)) 2 (ramerGaussian c s)) atTop (𝓝 0) := by
    have hsplit : ∀ k, eLpNorm (fun x : RamerE c s =>
        cylDivE c s (max (N k) (N' k))
          (fun v => NlsGge.Ramer.liftField c (le_max_left (N k) (N' k)) (f k) v -
            NlsGge.Ramer.liftField c (le_max_right (N k) (N' k)) (f' k) v) x -
          (d x - e x)) 2 (ramerGaussian c s) ≤
        eLpNorm (fun x : RamerE c s => cylDivE c s (N k) (f k) x - d x) 2
          (ramerGaussian c s) +
        eLpNorm (fun x : RamerE c s => cylDivE c s (N' k) (f' k) x - e x) 2
          (ramerGaussian c s) := by
      intro k
      have hfun : (fun x : RamerE c s =>
          cylDivE c s (max (N k) (N' k))
            (fun v => NlsGge.Ramer.liftField c (le_max_left (N k) (N' k)) (f k) v -
              NlsGge.Ramer.liftField c (le_max_right (N k) (N' k)) (f' k) v) x -
            (d x - e x)) =
          (fun x : RamerE c s => cylDivE c s (N k) (f k) x - d x) -
            (fun x : RamerE c s => cylDivE c s (N' k) (f' k) x - e x) := by
        funext x
        rw [hcylD k x]
        simp only [Pi.sub_apply]
        abel
      rw [hfun]
      exact eLpNorm_sub_le one_le_two
    have h12 := hDd.add hDe
    rw [add_zero] at h12
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h12
      (fun _ => zero_le) hsplit
  exact cylDiv_closable_E c s hs (fun k => max (N k) (N' k))
    (fun k v => NlsGge.Ramer.liftField c (le_max_left (N k) (N' k)) (f k) v -
      NlsGge.Ramer.liftField c (le_max_right (N k) (N' k)) (f' k) v)
    hcoreD (fun x => d x - e x) (hdL.sub heL) hFlim hDlim

/-- Uniqueness of the closed divergence, almost everywhere on the actual Gaussian. -/
theorem IsClosedDiv.unique
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s)
    (G : RamerE c s → RamerH c)
    (d e : RamerE c s → ℝ)
    (hd : IsClosedDiv c s G d)
    (he : IsClosedDiv c s G e) :
    d =ᵐ[ramerGaussian c s] e := by
  unfold IsClosedDiv at hd he
  obtain ⟨_, hdL, N, f, hf, hFd, hDd⟩ := hd
  obtain ⟨_, heL, N', f', hf', hFe, hDe⟩ := he
  filter_upwards [r025_unique_ae_sub c s hs G d e N N' f f' hf hf' hdL heL hFd hFe hDd hDe]
    with x hx
  simpa [sub_eq_zero] using hx

end
end NlsGge.ThirdConsultation.R
