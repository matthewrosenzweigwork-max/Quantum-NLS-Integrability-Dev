import NlsGge.Spectral.ActualComplexZsDysonIntegralEquationContinuousPotentialV6
import NlsGge.Spectral.ActualContinuousPotentialCompactNormBoundV2
import NlsGge.Spectral.ActualComplexZsDysonSeriesUniformOnDisksV10
import NlsGge.Spectral.ActualComplexZsFiniteDysonIteratesContinuousV9
import NlsGge.Spectral.ActualComplexZsFundamentalIccAssemblyV1
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.UniformSpace.UniformApproximation

open Filter MeasureTheory
open scoped Topology

set_option autoImplicit false

noncomputable section

namespace NlsGge.SpectralFoundations

local instance dysonODEMatrixNormedAddCommGroup :
    NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) :=
  instAnyInitialSourcePiNormedAddCommGroup

local instance dysonODEMatrixNormedSpace :
    NormedSpace ℝ (Matrix (Fin 2) (Fin 2) ℂ) :=
  instAnyInitialSourcePiNormedSpace

/-- The actual entrywise Dyson sum is continuous in time on the closed source
interval, by uniform convergence of the actual iterates on a bounded spectral
parameter set. -/
theorem continuousOn_actualComplexZsDysonTsum_entry_of_continuousOn
    (u : ℝ → ℂ) (z : ℂ)
    (hu : ContinuousOn u (Set.Icc (0 : ℝ) 2)) (i j : Fin 2) :
    ContinuousOn (fun t : ℝ => actualComplexZsDysonTsum u z t i j)
      (Set.Icc (0 : ℝ) 2) := by
  obtain ⟨C, hC, hU⟩ := exists_nonneg_actualPotential_norm_bound u hu
  let R : ℝ := ‖z‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hz : ‖z‖ ≤ R := by dsimp [R]; linarith
  let P : Set (ℂ × ℝ) :=
    {p | ‖p.1‖ ≤ R ∧ p.2 ∈ Set.Icc (0 : ℝ) 2}
  have hpair : HasSumUniformlyOn
      (fun n : ℕ => fun p : ℂ × ℝ =>
        actualComplexZsDysonTerm u p.1 n p.2 i j)
      (fun p => ∑' n : ℕ, actualComplexZsDysonTerm u p.1 n p.2 i j) P := by
    simpa [P] using hasSumUniformlyOn_actualComplexZsDysonSeries_entry
      u R C hR hC hU i j
  have hpairConv : TendstoUniformlyOn
      (fun s : Finset ℕ => fun p : ℂ × ℝ =>
        ∑ n ∈ s, actualComplexZsDysonTerm u p.1 n p.2 i j)
      (fun p => ∑' n : ℕ, actualComplexZsDysonTerm u p.1 n p.2 i j)
      atTop P :=
    (hasSumUniformlyOn_iff_tendstoUniformlyOn).mp hpair
  have hconv : TendstoUniformlyOn
      (fun s : Finset ℕ => fun t : ℝ =>
        ∑ n ∈ s, actualComplexZsDysonTerm u z n t i j)
      (fun t : ℝ => ∑' n : ℕ, actualComplexZsDysonTerm u z n t i j)
      atTop (Set.Icc (0 : ℝ) 2) := by
    intro U hU'
    filter_upwards [hpairConv U hU'] with s hs
    intro t ht
    exact hs (z, t) ⟨hz, ht⟩
  have hpartial : ∀ s : Finset ℕ,
      ContinuousOn
        (fun t : ℝ => ∑ n ∈ s, actualComplexZsDysonTerm u z n t i j)
        (Set.Icc (0 : ℝ) 2) := by
    intro s
    exact continuousOn_finsetSum s fun n hn =>
      continuousOn_actualComplexZsDysonTerm_entry u hu z n i j
  have hfreq : ∃ᶠ s : Finset ℕ in atTop,
      ContinuousOn
        (fun t : ℝ => ∑ n ∈ s, actualComplexZsDysonTerm u z n t i j)
        (Set.Icc (0 : ℝ) 2) :=
    (Filter.Eventually.of_forall hpartial).frequently
  have hcont := hconv.continuousOn hfreq
  simpa [actualComplexZsDysonTsum] using hcont

/-- The actual continuous-potential Dyson sum satisfies the normalized ZS
within-ODE on `[0,2]`. This uses the actual Volterra equation and the relative
interval FTC, including its one-sided endpoint filters. -/
theorem hasDerivWithinAt_actualComplexZsDysonTsum_of_continuousOn
    (u : ℝ → ℂ) (z : ℂ)
    (hu : ContinuousOn u (Set.Icc (0 : ℝ) 2))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 2) :
    HasDerivWithinAt (fun x : ℝ => actualComplexZsDysonTsum u z x)
      (zsCoefficientComplex u z t * actualComplexZsDysonTsum u z t)
      (Set.Icc (0 : ℝ) 2) t := by
  obtain ⟨C, hC, hU⟩ := exists_nonneg_actualPotential_norm_bound u hu
  let R : ℝ := ‖z‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hz : ‖z‖ ≤ R := by dsimp [R]; linarith
  have hFcont (i j : Fin 2) :
      ContinuousOn (fun x : ℝ => actualComplexZsDysonTsum u z x i j)
        (Set.Icc (0 : ℝ) 2) :=
    continuousOn_actualComplexZsDysonTsum_entry_of_continuousOn u z hu i j
  let A : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun s => zsCoefficientComplex u z s
  let F : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun s => actualComplexZsDysonTsum u z s
  have hprod (i j : Fin 2) :
      ContinuousOn (fun s : ℝ => (A s * F s) i j)
        (Set.Icc (0 : ℝ) 2) := by
    have h0 : ContinuousOn (fun s : ℝ => A s i 0 * F s 0 j)
        (Set.Icc (0 : ℝ) 2) := by
      exact (continuousOn_zsCoefficientComplex_entry u z 2 (by norm_num) hu i 0).mul
        (hFcont 0 j)
    have h1 : ContinuousOn (fun s : ℝ => A s i 1 * F s 1 j)
        (Set.Icc (0 : ℝ) 2) := by
      exact (continuousOn_zsCoefficientComplex_entry u z 2 (by norm_num) hu i 1).mul
        (hFcont 1 j)
    simpa only [A, F, Matrix.mul_apply, Fin.sum_univ_two, Pi.add_apply] using! h0.add h1
  have hentry (i j : Fin 2) :
      HasDerivWithinAt (fun x : ℝ => F x i j) ((A t * F t) i j)
        (Set.Icc (0 : ℝ) 2) t := by
    let g : ℝ → ℂ := fun s => (A s * F s) i j
    have hg : ContinuousOn g (Set.Icc (0 : ℝ) 2) := by
      simpa [g] using hprod i j
    have huIcc : Set.uIcc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) 2 := by
      rw [Set.uIcc_of_le ht.1]
      intro x hx
      exact ⟨hx.1, le_trans hx.2 ht.2⟩
    have hgIcc : ContinuousOn g (Set.uIcc (0 : ℝ) t) := hg.mono huIcc
    have hint : IntervalIntegrable g MeasureTheory.volume 0 t :=
      hgIcc.intervalIntegrable (μ := MeasureTheory.volume)
    letI : Fact (t ∈ Set.Icc (0 : ℝ) 2) := ⟨ht⟩
    have hmeas : StronglyMeasurableAtFilter g
        (𝓝[Set.Icc (0 : ℝ) 2] t) :=
      hg.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t
    have hftc := intervalIntegral.integral_hasDerivWithinAt_right
      (a := (0 : ℝ)) (b := t)
      (s := Set.Icc (0 : ℝ) 2) (t := Set.Icc (0 : ℝ) 2)
      hint hmeas (hg.continuousWithinAt ht)
    have hsumDeriv :
        HasDerivWithinAt
          (fun x : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ) i j +
            ∫ s in (0 : ℝ)..x, g s)
          (g t) (Set.Icc (0 : ℝ) 2) t := by
      have hsum' :=
        (hasDerivWithinAt_const t (Set.Icc (0 : ℝ) 2)
          ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j)).add hftc
      have hfun :
          (fun x : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ) i j +
            ∫ s in (0 : ℝ)..x, g s) =
          (fun x : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ) i j) +
            (fun x : ℝ => ∫ s in (0 : ℝ)..x, g s) := by
        funext x
        rfl
      rw [hfun]
      simpa only [zero_add] using hsum'
    have hEq : Set.EqOn
        (fun x : ℝ => F x i j)
        (fun x : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ) i j +
          ∫ s in (0 : ℝ)..x, g s)
        (Set.Icc (0 : ℝ) 2) := by
      intro x hx
      exact actualComplexZsDysonTsum_integral_equation_of_continuousOn
        u hu z R C hz hR hC hU x hx i j
    have hEqFilter := hEq.eventuallyEq_nhdsWithin (a := t)
    have hAt := hEq ht
    simpa [A, F, g] using
      hsumDeriv.congr_of_eventuallyEq hEqFilter hAt
  change HasDerivWithinAt
    (fun x : ℝ => fun i : Fin 2 => fun j : Fin 2 =>
      actualComplexZsDysonTsum u z x i j)
    (fun i : Fin 2 => fun j : Fin 2 =>
      (zsCoefficientComplex u z t * actualComplexZsDysonTsum u z t) i j)
    (Set.Icc (0 : ℝ) 2) t
  rw [hasDerivWithinAt_pi]
  intro i
  rw [hasDerivWithinAt_pi]
  intro j
  exact hentry i j

/-- The actual Dyson sum is the normalized fundamental matrix on `[0,2]`:
it is the unique solution with identity initial data, and its determinant is
one. The input is only the actual continuous-potential hypothesis. -/
theorem exists_normalized_actualComplexZsDysonFundamental_Icc
    (u : ℝ → ℂ) (z : ℂ)
    (hu : ContinuousOn u (Set.Icc (0 : ℝ) 2)) :
    ∃ G : ℝ → Matrix (Fin 2) (Fin 2) ℂ,
      G 0 = 1 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 2,
        HasDerivWithinAt G (zsCoefficientComplex u z t * G t)
          (Set.Icc (0 : ℝ) 2) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 2, Matrix.det (G t) = 1) ∧
      Set.EqOn G (fun t => actualComplexZsDysonTsum u z t)
        (Set.Icc (0 : ℝ) 2) := by
  obtain ⟨G, hG0, hG, hdet, hunique⟩ :=
    exists_actual_normalized_complexZs_fundamental_Icc_det_unique u z hu
  have hD0 : actualComplexZsDysonTsum u z 0 = 1 := by
    obtain ⟨C, hC, hU⟩ := exists_nonneg_actualPotential_norm_bound u hu
    let R : ℝ := ‖z‖ + 1
    have hR : 0 ≤ R := by dsimp [R]; positivity
    have hz : ‖z‖ ≤ R := by dsimp [R]; linarith
    ext i j
    have h := actualComplexZsDysonTsum_integral_equation_of_continuousOn
      u hu z R C hz hR hC hU 0 ⟨le_rfl, by norm_num⟩ i j
    simpa using h
  have hD : ∀ t ∈ Set.Icc (0 : ℝ) 2,
      HasDerivWithinAt (fun x : ℝ => actualComplexZsDysonTsum u z x)
        (zsCoefficientComplex u z t * actualComplexZsDysonTsum u z t)
        (Set.Icc (0 : ℝ) 2) t := by
    intro t ht
    exact hasDerivWithinAt_actualComplexZsDysonTsum_of_continuousOn u z hu t ht
  have hEq := hunique (fun t => actualComplexZsDysonTsum u z t) hD0 hD
  exact ⟨G, hG0, hG, hdet, hEq⟩

end NlsGge.SpectralFoundations

end
