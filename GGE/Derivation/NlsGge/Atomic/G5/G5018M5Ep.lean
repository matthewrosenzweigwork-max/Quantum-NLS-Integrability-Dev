import Mathlib
import NlsGge.ThirdConsultation.G3.G3024Endpoint
import NlsGge.Atomic.G5.G5018M5Id

/- G5-018 M5a SUPPORT `G5018M5Ep` (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5018M5Ep.lean, namespace NlsGge.GKDefinitionDesign.G5018M5Aux.
   Endpoint-inclusive version of `G5018M5Diag.diag_explicit` for the M5a head, where only `gamma2 <> 0` (not an interior
   Dirichlet root) is available: re-runs the landed G3024Endpoint labels_any / roots_any / param_data / analyticity argument
   of `g3024_endpoint_package` (the package statement forgets analyticity of the labels a, b) at phi0 in sourceW \ collapsedSet n,
   with the explicit lift e = int_0^1 G / sqrt t, then shrinks V for xiN38 and applies `angle_diff_eq`.
   betaSum differentiability is the hypothesis hβ, discharged by landed betaSum_analyticOnNhd_sourceBetaW in the head.
   No sourceFamily.XY_analytic. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
namespace G5018M5Aux
noncomputable section
open G3024Endpoint

theorem ep_explicit (n : ℤ) (φ0 : PotPair)
    (hφ0 : φ0 ∈ sourceBetaW ∧ φ0 ∈ sourceW \ collapsedSet n)
    (hξ : AnalyticAt ℂ (xiN38 n) φ0) (hξ0 : xiN38 n φ0 ≠ 0)
    (hβ : AnalyticOnNhd ℂ (betaSum n) sourceBetaW) :
    ∃ (V : Set PotPair) (e : PotPair → ℂ),
      IsOpen V ∧ φ0 ∈ V ∧ V ⊆ sourceBetaW \ collapsedSet n ∧
      AnalyticOnNhd ℂ e V ∧
      (∀ φ ∈ V, ∃ s : ℂ, (s = 1 ∨ s = -1) ∧
        Complex.exp (Complex.I * e φ) = s * etaExponential n φ) ∧
      ∀ φ ∈ V, angleDerivative n φ - fderiv ℂ (betaSum n) φ = fderiv ℂ e φ := by
  obtain ⟨hφB, hφ0⟩ := hφ0
  obtain ⟨V1, a, b, hV1o, hφV1, hV1sub, haA, hbA, hVp⟩ := labels_any n φ0 hφ0
  obtain ⟨U, rω, rseg, hUo, hφU, hUV, hrωA, hrsegA, hrsegC, hroots⟩ :=
    roots_any n V1 a b hV1o hV1sub haA hbA hVp φ0 hφV1
  have hUsub : U ⊆ sourceW \ collapsedSet n := fun φ hφ => hV1sub (hUV hφ)
  obtain ⟨V, C, hVo, hφV, hVU, hC, hHan, hHφ⟩ :=
    param_data n φ0 U a b rω rseg hUo hφU hUsub (haA.mono hUV) (hbA.mono hUV)
      (fun φ hφ => (hVp φ (hUV hφ)).1) hrωA hrsegA hrsegC hroots
  obtain ⟨Gf, hGf⟩ : ∃ Gf : PotPair → ℝ → ℂ, Gf = fun (φ : PotPair) (t : ℝ) =>
      psi n φ (a φ + (t : ℂ) * (muSeq φ n - a φ)) * rω φ /
        (2 * Complex.I * rootProduct n (φ, a φ + (t : ℂ) * (muSeq φ n - a φ)) * rseg φ t) :=
    ⟨_, rfl⟩
  have hHan' : ∀ t ∈ Ioo (0 : ℝ) 1, AnalyticOnNhd ℂ (fun φ => Gf φ t) V := by
    subst hGf; exact hHan
  have hHφ' : ∀ φ ∈ V, ContinuousOn (Gf φ) (Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ‖Gf φ t‖ ≤ C) ∧
      IntervalIntegrable (fun t => Gf φ t / (Real.sqrt t : ℂ)) volume 0 1 ∧
      gk16ActualScalarZPlus38 sourceF n φ = (b φ - a φ) *
        Complex.exp (Complex.I * ∫ t in (0 : ℝ)..1, Gf φ t / (Real.sqrt t : ℂ)) := by
    subst hGf; exact hHφ
  have hmain := NlsGge.Atomic.G4.analyticOn_integral_of_rpow_half_locally_dominated
    (E := PotPair) (F := ℂ) (U := V)
    (a := fun (t : ℝ) (φ : PotPair) => Gf φ t / (Real.sqrt t : ℂ)) C hC.le hVo
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
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hVo φ hφ
      refine ⟨r, hr, hball, fun v hv => ?_⟩
      refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun t ht => ?_)
      have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht.1
      have hb := (hHφ' v (hball hv)).2.1 t ⟨ht.1.le, ht.2.le⟩
      have hr' : Real.rpow t (-1 / 2) = (Real.sqrt t)⁻¹ := by
        rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num]
        exact g3005_rpow_neg_half_eq ht.1
      rw [hr', norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right hb hs.le)
  -- explicit lift
  have hAn : AnalyticOnNhd ℂ (fun φ : PotPair => ∫ t in (0 : ℝ)..1, Gf φ t / (Real.sqrt t : ℂ)) V := by
    intro φ hφ
    refine (hmain φ hφ).congr ?_
    filter_upwards [hVo.mem_nhds hφ] with ψ hψ
    show _ = ∫ t in (0 : ℝ)..1, Gf ψ t / (Real.sqrt t : ℂ)
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have hVV1 : V ⊆ V1 := fun φ hφ => hUV (hVU hφ)
  have hxev : ∀ᶠ φ in 𝓝 φ0, AnalyticAt ℂ (xiN38 n) φ ∧ xiN38 n φ ≠ 0 :=
    hξ.eventually_analyticAt.and (hξ.continuousAt.eventually_ne hξ0)
  obtain ⟨Wx, hWxsub, hWxo, hφWx⟩ := _root_.mem_nhds_iff.1 hxev
  set V' : Set PotPair := V ∩ sourceBetaW ∩ Wx with hV'def
  have hV'o : IsOpen V' := (hVo.inter sourceFamily.V_open).inter hWxo
  have hV'V : V' ⊆ V := fun φ hφ => hφ.1.1
  refine ⟨V', fun φ : PotPair => ∫ t in (0 : ℝ)..1, Gf φ t / (Real.sqrt t : ℂ), hV'o,
    ⟨⟨hφV, hφB⟩, hφWx⟩, fun φ hφ => ⟨hφ.1.2, (hV1sub (hVV1 (hV'V hφ))).2⟩,
    hAn.mono hV'V, ?_, ?_⟩
  · intro φ hφ
    have hφ1 := hVV1 (hV'V hφ)
    have hgam : lamPlus φ n - lamMinus φ n ≠ 0 := gap_ne n φ (hV1sub hφ1)
    have hZφ := (hHφ' φ (hV'V hφ)).2.2.2
    have hE : etaExponential n φ = gk16ActualScalarZPlus38 sourceF n φ / (lamPlus φ n - lamMinus φ n) :=
      rfl
    rcases Set.pair_eq_pair_iff.1 ((hVp φ hφ1).1) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [h1, h2] at hZφ
      rw [hE, one_mul]
      show Complex.exp (Complex.I * ∫ t in (0 : ℝ)..1, Gf φ t / (Real.sqrt t : ℂ)) = _
      rw [hZφ]
      field_simp
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [h1, h2] at hZφ
      rw [hE]
      show Complex.exp (Complex.I * ∫ t in (0 : ℝ)..1, Gf φ t / (Real.sqrt t : ℂ)) = _
      rw [hZφ]
      field_simp
      ring
  · intro φ hφ
    have hφ1 := hVV1 (hV'V hφ)
    exact angle_diff_eq n φ V' hV'o hφ (fun ψ hψ => hV1sub (hVV1 (hV'V hψ))) a b
      (fun φ : PotPair => ∫ t in (0 : ℝ)..1, Gf φ t / (Real.sqrt t : ℂ))
      (haA φ hφ1).differentiableAt (hbA φ hφ1).differentiableAt
      (hAn φ (hV'V hφ)).differentiableAt
      (fun ψ hψ => (hVp ψ (hVV1 (hV'V hψ))).1)
      (fun ψ hψ => (hHφ' ψ (hV'V hψ)).2.2.2)
      (hWxsub hφ.2).1.differentiableAt (hWxsub hφ.2).2
      (hβ φ hφ.1.2).differentiableAt

end
end G5018M5Aux
noncomputable section

/-- M5a head with the landed analyticity of `betaSum` kept as the explicit hypothesis `hβ`. -/
theorem g5018_diagonal_local_lift_of_beta
    (u : PhysicalL2) (n : ℤ)
    (hn : gamma2 (realSlice u) n ≠ 0)
    (hβ : AnalyticOnNhd ℂ (betaSum n) sourceBetaW) :
    ∃ (V : Set PotPair) (e : PotPair → ℂ),
      IsOpen V ∧ realSlice u ∈ V ∧
      V ⊆ sourceBetaW \ collapsedSet n ∧
      AnalyticOnNhd ℂ e V ∧
      (∀ φ ∈ V, ∃ s : ℂ, (s = 1 ∨ s = -1) ∧
        Complex.exp (Complex.I * e φ) = s * etaExponential n φ) ∧
      ∀ φ ∈ V,
        angleDerivative n φ - fderiv ℂ (betaSum n) φ = fderiv ℂ e φ := by
  have hW : realSlice u ∈ sourceW := sourceFamily.W_real (Set.mem_range_self u)
  have hB : realSlice u ∈ sourceBetaW := sourceFamily.V_real (Set.mem_range_self u)
  have hgk : realSlice u ∈ gkW := sourceFamily.W_gk hW
  have hslit : xiSq38 n (realSlice u) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl (lt_of_lt_of_le one_pos (xiSq38_real_ge_one u n).2)
  have hξ : AnalyticAt ℂ (xiN38 n) (realSlice u) := xiN38_analytic n _ ⟨hgk, hslit⟩
  have hξ0 : xiN38 n (realSlice u) ≠ 0 := by
    intro h
    have := (xiN38_real_ge_one u n).2
    rw [h] at this
    simp at this
    linarith
  exact G5018M5Aux.ep_explicit n (realSlice u) ⟨hB, hW, fun h => hn h.2⟩ hξ hξ0 hβ

end
end NlsGge.GKDefinitionDesign
