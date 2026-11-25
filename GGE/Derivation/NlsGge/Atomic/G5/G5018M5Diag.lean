import Mathlib
import NlsGge.ThirdConsultation.G3.G3024Param
import NlsGge.Atomic.G5.G5018M5Id

/- G5-018 M5a SUPPORT `G5018M5Diag` (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5018M5Diag.lean, namespace NlsGge.GKDefinitionDesign.G5018M5Aux.
   Explicit diagonal local lift: from landed G3024Param.diag_local_data at phi0 in sourceW \ (collapsedSet n u endpointSet n)
   build the open V, labels a b, roots, bound C and the EXPLICIT lift e = int_0^1 G/sqrt t (analytic on V, copied from the
   argument of G3024Param.g3024_diag_package), shrink V so xiN38 n is analytic and nonzero, and prove
   angleDerivative n phi - fderiv (betaSum n) phi = fderiv e phi on V by G5018M5Id.angle_diff_eq.
   betaSum differentiability is the hypothesis `hβ : AnalyticOnNhd (betaSum n) sourceBetaW`, discharged in the head by landed
   betaSum_analyticOnNhd_sourceBetaW.  No sourceFamily.XY_analytic. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
namespace G5018M5Aux
noncomputable section

/-- The diagonal integrand of the local data. -/
def diagG (n : ℤ) (a rω : PotPair → ℂ) (rseg : PotPair → ℝ → ℂ) (φ : PotPair) (t : ℝ) : ℂ :=
  psi n φ (a φ + (t : ℂ) * (muSeq φ n - a φ)) * rω φ /
    (2 * Complex.I * rootProduct n (φ, a φ + (t : ℂ) * (muSeq φ n - a φ)) * rseg φ t)

/-- The explicit local lift. -/
def diagE (n : ℤ) (a rω : PotPair → ℂ) (rseg : PotPair → ℝ → ℂ) (φ : PotPair) : ℂ :=
  ∫ t in (0 : ℝ)..1, diagG n a rω rseg φ t / (Real.sqrt t : ℂ)

theorem diag_explicit (n : ℤ) (φ0 : PotPair)
    (hφ0 : φ0 ∈ sourceBetaW ∧ φ0 ∈ sourceW \ (collapsedSet n ∪ endpointSet n))
    (hξ : AnalyticAt ℂ (xiN38 n) φ0) (hξ0 : xiN38 n φ0 ≠ 0)
    (hβ : AnalyticOnNhd ℂ (betaSum n) sourceBetaW) :
    ∃ (V : Set PotPair) (a b rω : PotPair → ℂ) (rseg : PotPair → ℝ → ℂ) (C : ℝ),
      φ0 ∈ V ∧ V ⊆ sourceBetaW \ collapsedSet n ∧
      LocalEndpointSegmentSeparation n V a b ∧ AnalyticSegmentRoots n V a b rω rseg ∧ 0 < C ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, AnalyticOnNhd ℂ (fun φ => diagG n a rω rseg φ t) V) ∧
      (∀ φ ∈ V, ContinuousOn (diagG n a rω rseg φ) (Icc (0 : ℝ) 1) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ‖diagG n a rω rseg φ t‖ ≤ C) ∧
        IntervalIntegrable (fun t => diagG n a rω rseg φ t / (Real.sqrt t : ℂ)) volume 0 1) ∧
      AnalyticOnNhd ℂ (diagE n a rω rseg) V ∧
      (∀ φ ∈ V, ∃ s : ℂ, (s = 1 ∨ s = -1) ∧
        Complex.exp (Complex.I * diagE n a rω rseg φ) = s * etaExponential n φ) ∧
      ∀ φ ∈ V, angleDerivative n φ - fderiv ℂ (betaSum n) φ = fderiv ℂ (diagE n a rω rseg) φ := by
  obtain ⟨hφB, hφ0'⟩ := hφ0
  obtain ⟨V1, a, b, rω, rseg, C, hφV1, hsep, hroots, hC, hH⟩ :=
    G3024Param.diag_local_data n φ0 hφ0'
  obtain ⟨hHan, hHφ⟩ := hH
  have hV1o : IsOpen V1 := hsep.1
  have hHan' : ∀ t ∈ Ioo (0 : ℝ) 1, AnalyticOnNhd ℂ (fun φ => diagG n a rω rseg φ t) V1 := hHan
  have hHφ' : ∀ φ ∈ V1, ContinuousOn (diagG n a rω rseg φ) (Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ‖diagG n a rω rseg φ t‖ ≤ C) ∧
      IntervalIntegrable (fun t => diagG n a rω rseg φ t / (Real.sqrt t : ℂ)) volume 0 1 ∧
      gk16ActualScalarZPlus38 sourceF n φ = (b φ - a φ) *
        Complex.exp (Complex.I * diagE n a rω rseg φ) := fun φ hφ => hHφ φ hφ
  -- analyticity of the explicit lift on V1
  have hmain := NlsGge.Atomic.G4.analyticOn_integral_of_rpow_half_locally_dominated
    (E := PotPair) (F := ℂ) (U := V1)
    (a := fun (t : ℝ) (φ : PotPair) => diagG n a rω rseg φ t / (Real.sqrt t : ℂ)) C hC.le hV1o
    ((ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun t ht φ hφ =>
      (hHan' t ht φ hφ).div analyticAt_const
        (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 ht.1).ne')))
    (fun φ hφ => by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
      refine ((hHφ' φ hφ).1.mono Ioo_subset_Icc_self).div
        (Complex.continuous_ofReal.comp_continuousOn Real.continuous_sqrt.continuousOn) ?_
      intro t ht
      exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 ht.1).ne')
    (fun φ hφ => by
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hV1o φ hφ
      refine ⟨r, hr, hball, fun v hv => ?_⟩
      refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun t ht => ?_)
      have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht.1
      have hb := (hHφ' v (hball hv)).2.1 t ⟨ht.1.le, ht.2.le⟩
      have hr' : Real.rpow t (-1 / 2) = (Real.sqrt t)⁻¹ := by
        rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num]
        exact g3005_rpow_neg_half_eq ht.1
      rw [hr', norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right hb hs.le)
  have hEan : AnalyticOnNhd ℂ (diagE n a rω rseg) V1 := by
    intro φ hφ
    refine (hmain φ hφ).congr ?_
    filter_upwards [hV1o.mem_nhds hφ] with ψ hψ
    show _ = diagE n a rω rseg ψ
    unfold diagE
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  -- shrink: xi analytic and nonzero
  have hxev : ∀ᶠ φ in 𝓝 φ0, AnalyticAt ℂ (xiN38 n) φ ∧ xiN38 n φ ≠ 0 :=
    hξ.eventually_analyticAt.and (hξ.continuousAt.eventually_ne hξ0)
  obtain ⟨Wx, hWxsub, hWxo, hφWx⟩ := _root_.mem_nhds_iff.1 hxev
  set V : Set PotPair := V1 ∩ sourceBetaW ∩ Wx with hVdef
  have hVo : IsOpen V := (hV1o.inter sourceFamily.V_open).inter hWxo
  have hVV1 : V ⊆ V1 := fun φ hφ => hφ.1.1
  have hφV : φ0 ∈ V := ⟨⟨hφV1, hφB⟩, hφWx⟩
  obtain ⟨-, hV1sub, haA, hbA, hVp⟩ := hsep
  have hVsub : V ⊆ sourceW \ collapsedSet n := fun φ hφ =>
    ⟨(hV1sub (hVV1 hφ)).1, fun hc => (hV1sub (hVV1 hφ)).2 (Or.inl hc)⟩
  refine ⟨V, a, b, rω, rseg, C, hφV, fun φ hφ => ⟨hφ.1.2, (hVsub hφ).2⟩,
    ⟨hVo, fun φ hφ => hV1sub (hVV1 hφ), haA.mono hVV1, hbA.mono hVV1,
      fun φ hφ => hVp φ (hVV1 hφ)⟩,
    G3015Aux.roots_mono n hroots hVV1, hC,
    fun t ht => (hHan' t ht).mono hVV1,
    fun φ hφ => ⟨(hHφ' φ (hVV1 hφ)).1, (hHφ' φ (hVV1 hφ)).2.1, (hHφ' φ (hVV1 hφ)).2.2.1⟩,
    hEan.mono hVV1, ?_, ?_⟩
  · intro φ hφ
    have hφ1 := hVV1 hφ
    have hgam : lamPlus φ n - lamMinus φ n ≠ 0 :=
      G3015Aux.gap_ne_of_mem n φ (hV1sub hφ1)
    have hZφ := (hHφ' φ hφ1).2.2.2
    obtain ⟨hpair, -⟩ := hVp φ hφ1
    have hE : etaExponential n φ = gk16ActualScalarZPlus38 sourceF n φ / (lamPlus φ n - lamMinus φ n) :=
      rfl
    rcases Set.pair_eq_pair_iff.1 hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [h1, h2] at hZφ
      rw [hE, one_mul, hZφ]
      field_simp
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [h1, h2] at hZφ
      rw [hE, hZφ]
      field_simp
      ring
  · intro φ hφ
    have hφ1 := hVV1 hφ
    exact G5018M5Aux.angle_diff_eq n φ V hVo hφ hVsub a b (diagE n a rω rseg)
      (haA φ hφ1).differentiableAt (hbA φ hφ1).differentiableAt
      (hEan φ hφ1).differentiableAt
      (fun ψ hψ => (hVp ψ (hVV1 hψ)).1)
      (fun ψ hψ => (hHφ' ψ (hVV1 hψ)).2.2.2)
      (hWxsub hφ.2).1.differentiableAt (hWxsub hφ.2).2
      (hβ φ hφ.1.2).differentiableAt

end
end G5018M5Aux
end NlsGge.GKDefinitionDesign
