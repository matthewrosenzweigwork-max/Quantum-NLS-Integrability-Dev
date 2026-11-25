import NlsGge.GK38.PairRealBridgeVC
import NlsGge.Spectral.ActualPhysicalL2ZsACFundamentalWellPosedV1
import NlsGge.Spectral.ActualPhysicalUnitDiscriminantNonrealZeroFree32V1

/-!
# F4: the discriminant `Δ`, its analyticity, and the identification with E02

Source: Grébert-Kappeler book, Chapter I, section 1 (Theorem 1.1: `M(1, λ, φ)` is analytic in
`(λ, φ)`; `Δ(λ, φ) = tr M(1, λ, φ)`, book normalization `Δ = 2 Δh`, `Δh(0, λ) = cos λ`).

## Contents

* `discrim φ z = tr M(1, z, φ)` (full trace), `perChar φ z = Δ² - 4` (`perCharOf` of X2);
* trace-level analyticity (F3 review N3): jointly on `PotPair × ℂ` (`analyticOnNhd_discrim`), in `z`
  for fixed `φ`, in `φ` for fixed `z`; real-analyticity on the real slice
  (`analyticOnNhd_discrim_real`, in `u : PhysicalL2` for fixed `z`, and jointly in `(u, z)`);
* the identification with E02, by the AMENDED ROUTE of F2 review N1: the E02 Dyson matrix `G` is an
  absolutely continuous a.e. solution (`actualPhysicalL2ZsDysonTsum_is_AC_fundamental`); with F1's
  `zsCoeffPot38_realSlice_ae` it is a solution of the book integral equation by variation of
  constants (`PairRealBridgeVC.lean`), hence equals F2's `fundPair` (`fundCont_unique`).
  `monodromyPair_realSlice`, `discrim_realSlice`, `discrim_zero`.
-/

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace NlsGge.GK38

noncomputable section

open NlsGge.Pilot NlsGge.Schur NlsGge.Analysis NlsGge.SpectralFoundations

/-! ### Definitions -/

/-- The full (unit-period) trace `Δ(φ, z) = tr M(1, z, φ)`; `Δh = Δ / 2` (book normalization). -/
def discrim (φ : PotPair) (z : ℂ) : ℂ := Matrix.trace (monodromyPair φ z)

/-- The periodic characteristic function `χ_p = Δ² - 4` (`perCharOf` is X2's generic form). -/
def perChar (φ : PotPair) (z : ℂ) : ℂ := perCharOf (discrim φ) z

theorem discrim_eq (φ : PotPair) (z : ℂ) :
    discrim φ z = monodromyPair φ z 0 0 + monodromyPair φ z 1 1 := by
  simp [discrim, Matrix.trace, Fin.sum_univ_two]

theorem perChar_eq (φ : PotPair) (z : ℂ) : perChar φ z = discrim φ z ^ 2 - 4 := rfl

/-! ### Analyticity of the trace (F3 review N3) -/

/-- `Δ(φ, z)` is analytic jointly in `(φ, z)` on all of `PotPair × ℂ` (book Thm 1.1). -/
theorem analyticOnNhd_discrim :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => discrim p.1 p.2) Set.univ := by
  have : (fun p : PotPair × ℂ => discrim p.1 p.2) =
      fun p => monodromyPair p.1 p.2 0 0 + monodromyPair p.1 p.2 1 1 :=
    funext fun p => discrim_eq p.1 p.2
  rw [this]
  exact (analyticOnNhd_monodromyPair 0 0).add (analyticOnNhd_monodromyPair 1 1)

/-- `Δ(φ, ·)` is entire. -/
theorem analyticOnNhd_discrim_z (φ : PotPair) :
    AnalyticOnNhd ℂ (discrim φ) Set.univ := fun z _ =>
  AnalyticAt.comp (g := fun p : PotPair × ℂ => discrim p.1 p.2) (f := fun z : ℂ => (φ, z))
    (analyticOnNhd_discrim (φ, z) (Set.mem_univ _)) ((analyticAt_const (v := φ)).prod analyticAt_id)

/-- `Δ(·, z)` is analytic on `PotPair`, for fixed `z`. -/
theorem analyticOnNhd_discrim_phi (z : ℂ) :
    AnalyticOnNhd ℂ (fun φ : PotPair => discrim φ z) Set.univ := fun φ _ =>
  AnalyticAt.comp (g := fun p : PotPair × ℂ => discrim p.1 p.2) (f := fun φ : PotPair => (φ, z))
    (analyticOnNhd_discrim (φ, z) (Set.mem_univ _)) (analyticAt_id.prod analyticAt_const)

/-- `χ_p(φ, ·)` is entire. -/
theorem analyticOnNhd_perChar_z (φ : PotPair) :
    AnalyticOnNhd ℂ (perChar φ) Set.univ := by
  have : perChar φ = fun z => discrim φ z ^ 2 - 4 := rfl
  rw [this]
  exact ((analyticOnNhd_discrim_z φ).pow 2).sub analyticOnNhd_const

/-- `Δ(realSlice u, z)` is real-analytic in `u ∈ L²_r` for every fixed `z` (restriction of scalars
and `analyticOnNhd_comp_realSlice`). -/
theorem analyticOnNhd_discrim_real (z : ℂ) :
    AnalyticOnNhd ℝ (fun u : PhysicalL2 => discrim (realSlice u) z) Set.univ :=
  analyticOnNhd_comp_realSlice (f := fun φ : PotPair => discrim φ z) (analyticOnNhd_discrim_phi z)

/-- Joint real-analyticity of `(u, z) ↦ Δ(realSlice u, z)` on `L²_r × ℂ`. -/
theorem analyticOnNhd_discrim_real_joint :
    AnalyticOnNhd ℝ (fun p : PhysicalL2 × ℂ => discrim (realSlice p.1) p.2) Set.univ := fun p _ =>
  AnalyticAt.comp (g := fun q : PotPair × ℂ => discrim q.1 q.2)
    (f := fun p : PhysicalL2 × ℂ => (realSlice p.1, p.2))
    ((analyticOnNhd_discrim (realSlice p.1, p.2) (Set.mem_univ _)).restrictScalars (𝕜 := ℝ))
    (((realSlice.analyticAt p.1).comp (analyticAt_fst (𝕜 := ℝ))).prod
      (analyticAt_snd (𝕜 := ℝ)))

/-! ### The identification with E02 (amended route) -/

/-- The E02 potential on the real line (`potRepFst38 (realSlice u)` by `rfl`, F1). -/
abbrev e02Pot38 (u : PhysicalL2) : ℝ → ℂ := fun t => naturalPhysicalCoverL2 u (t : SpectralCircle)

theorem potRepFst38_realSlice_eq (u : PhysicalL2) : potRepFst38 (realSlice u) = e02Pot38 u := rfl

/-- On `[0,1]`, F2's fundamental solution of the real-slice pair is E02's actual Dyson matrix. -/
theorem fundPair_realSlice (u : PhysicalL2) (z : ℂ) (t : Set.Icc (0 : ℝ) 1) :
    fundPair (realSlice u) z t = actualComplexZsDysonTsum (e02Pot38 u) z t := by
  obtain ⟨hinit, hAC, hODE⟩ := actualPhysicalL2ZsDysonTsum_is_AC_fundamental u z
  refine fundPair_eq_of_ac_ae_ode38 (realSlice u) z _ hinit hAC (fun i j => ?_) t
  filter_upwards [hODE i j, zsCoeffPot38_realSlice_ae u z] with x hx hcoef
  rw [hcoef]
  exact hx

/-- **F4 bridge.**  `M(1, z, (u, ū))` is E02's Dyson matrix at `t = 1` for the unit period. -/
theorem monodromyPair_realSlice (u : PhysicalL2) (z : ℂ) :
    monodromyPair (realSlice u) z =
      actualComplexZsDysonTsum (fun t => naturalPhysicalCoverL2 u (t : SpectralCircle)) z 1 := by
  rw [monodromyPair_eq_fundPair, fundPair_realSlice]

/-- `Δ(u, ū, z) = 2 Δh(u, z)`, with E02's half trace `actualPhysicalUnitHalfTrace32`. -/
theorem discrim_realSlice (u : PhysicalL2) (z : ℂ) :
    discrim (realSlice u) z = 2 * actualPhysicalUnitHalfTrace32 u z := by
  unfold discrim actualPhysicalUnitHalfTrace32
  rw [monodromyPair_realSlice]
  ring

/-- `Δ(0, z) = 2 cos z` (book Lemma 3.1 normalization `Δ = 2 Δh`). -/
theorem discrim_zero (z : ℂ) : discrim 0 z = 2 * Complex.cos z :=
  trace_monodromyPair_zero z

/-- `χ_p(φ = 0) = -4 sin² z`. -/
theorem perChar_zero (z : ℂ) : perChar 0 z = -4 * Complex.sin z ^ 2 := by
  unfold perChar
  have : discrim 0 = fun w => 2 * Complex.cos w := funext discrim_zero
  rw [this]
  exact perCharOf_free z

/-- On the real slice `χ_p = 4 (Δh² - 1)`: E02's branch radicand
`actualPhysicalUnitHalfTrace32 u z ^ 2 - 1` (times `4`). -/
theorem perChar_realSlice (u : PhysicalL2) (z : ℂ) :
    perChar (realSlice u) z = 4 * (actualPhysicalUnitHalfTrace32 u z ^ 2 - 1) := by
  rw [perChar_eq, discrim_realSlice]
  ring

end

end NlsGge.GK38
