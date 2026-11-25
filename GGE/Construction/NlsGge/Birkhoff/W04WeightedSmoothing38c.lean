import NlsGge.Birkhoff.W04WeightedSmoothing38b
import NlsGge.Sobolev.CMWeightComparison

/-! # W04 (`D:thm:weighted`), part 3: the orbit argument for an equivariant analytic one-smoothing

Source: `paper/v2.tex` l.1489-1494.  Birkhoff-free abstract core: let `F` be a map of sequences that
maps `h^ρ` into `h^ρ'` real analytically (as a map of the real Hilbert carriers) and commutes with
the rotations `S_θ`.  Apply W03 (`composition_analytic`) to the orbit `θ ↦ S_θ x` with the weight
`w_n = √a_n ⟨n⟩^{-s-1}`, `s = σ+ρ-1`.  The result: `F` maps `E_σ` into `E_τ`, `τ = σ + ρ - ρ'`, and is
real analytic there.  (v2 takes `ρ = 1`, `ρ' = 2`, `σ = s`, `τ = s - 1`.)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Composition MeasureTheory AddCircle
open scoped Real

section Core

variable {lower upper : ℝ}

/-- `F : h^ρ → h^ρ'` (as a map of complex Hilbert spaces `HC38`). -/
def hMap38 (ρ ρ' : ℝ) (F : (ℤ → ℂ) → (ℤ → ℂ)) (hmem : ∀ x ∈ seqSobolev38 ρ, F x ∈ seqSobolev38 ρ') :
    HC38 ρ → HC38 ρ' :=
  fun y => hMk38 ρ' (F (y : ℤ → ℂ)) (hmem _ y.2)

/-- Analyticity transfers from the coherent real carriers `SobolevCarrier38` to the complex
Hilbert spaces `HC38` (the two real structures agree definitionally). -/
theorem analytic_hMap38 (ρ ρ' : ℝ) (F : (ℤ → ℂ) → (ℤ → ℂ))
    (hmem : ∀ x ∈ seqSobolev38 ρ, F x ∈ seqSobolev38 ρ')
    (han : AnalyticOnNhd ℝ (carrierMap38 ρ ρ' F hmem) Set.univ) :
    AnalyticOnNhd ℝ (hMap38 ρ ρ' F hmem) Set.univ := han

/-- **Abstract orbit argument (W04.02-W04.05).**  Let `F` map `h^ρ → h^ρ'` real analytically and
commute with the rotations `S_θ` on `h^ρ`.  Then `F` maps `E_σ` into `E_τ` for
`τ = σ + ρ - ρ'`, and `F : E_σ → E_τ` is real analytic.  Moreover for every `y ∈ E_σ`, with
`w = √a_n ⟨n⟩^{-(σ+ρ)}` and `ι y` the weighted orbit vector, the orbit `θ ↦ F (S_θ x)` lies in
`A_w(h^ρ')` and has `A_w`-norm `‖F x‖_{E_τ}`. -/
theorem weighted_smoothing_core38 (c : BoundedCoefficients lower upper) (ρ ρ' σ τ : ℝ)
    (hτ : τ = σ + ρ - ρ') (F : (ℤ → ℂ) → (ℤ → ℂ))
    (hmem : ∀ x ∈ seqSobolev38 ρ, F x ∈ seqSobolev38 ρ')
    (han : AnalyticOnNhd ℝ (carrierMap38 ρ ρ' F hmem) Set.univ)
    (hequi : ∀ x ∈ seqSobolev38 ρ, ∀ θ : ℝ, F (rotSeq38 θ x) = rotSeq38 θ (F x)) :
    ∃ hF : ∀ x ∈ seqE38 c σ, F x ∈ seqE38 c τ,
      AnalyticOnNhd ℝ (eMap38 c σ τ F hF) Set.univ ∧
      ∀ y : ECarrier38 c σ,
        MemAw (orbitWeight38 c (σ + ρ - 1))
          (hMap38 ρ ρ' F hmem ∘ synth (orbitWeight38 c (σ + ρ - 1))
            (orbitCLM38 c (σ + ρ - 1) ρ σ (by ring) y)) ∧
        awNorm (orbitWeight38 c (σ + ρ - 1))
          (hMap38 ρ ρ' F hmem ∘ synth (orbitWeight38 c (σ + ρ - 1))
            (orbitCLM38 c (σ + ρ - 1) ρ σ (by ring) y)) = ‖eMap38 c σ τ F hF y‖ := by
  set s : ℝ := σ + ρ - 1 with hs
  have hσ : s + 1 - ρ = σ := by rw [hs]; ring
  have hτ' : s + 1 - ρ' = τ := by rw [hs, hτ]; ring
  have hw := orbitWeight38_admissible c s
  have hFh := analytic_hMap38 ρ ρ' F hmem han
  obtain ⟨-, hcomp, hsynth⟩ := composition_analytic hw (isOpen_univ) hFh
  have hrange : ∀ g : Model (HC38 ρ), g ∈ rangeSet (orbitWeight38 c s) (Set.univ : Set (HC38 ρ)) :=
    fun g θ => Set.mem_univ _
  -- the composite map
  set K : ECarrier38 c σ → ECarrier38 c τ := fun y =>
    modeCLM38 c s ρ' τ hτ' (compMap hw (hMap38 ρ ρ' F hmem) (orbitCLM38 c s ρ σ hσ y)) with hK
  have hKan : AnalyticOnNhd ℝ K Set.univ := by
    have h1 : AnalyticOnNhd ℝ (orbitCLM38 c s ρ σ hσ) Set.univ :=
      (orbitCLM38 c s ρ σ hσ).analyticOnNhd _
    have h2 : AnalyticOnNhd ℝ (modeCLM38 c s ρ' τ hτ') Set.univ :=
      (modeCLM38 c s ρ' τ hτ').analyticOnNhd _
    have h3 := hcomp.comp h1 (fun y _ => hrange _)
    exact h2.comp h3 (fun _ _ => Set.mem_univ _)
  -- key identity on each orbit
  have key : ∀ y : ECarrier38 c σ,
      (∀ t : ℝ, synth (orbitWeight38 c s)
        (compMap hw (hMap38 ρ ρ' F hmem) (orbitCLM38 c s ρ σ hσ y)) ((t : ℝ) : AddCircle (1 : ℝ)) =
        hMk38 ρ' (rotSeq38 (2 * π * t) (F (eCoe38 c σ y)))
          (rotSeq38_mem ρ' _ (hmem _ (seqE38_subset_seqSobolev38 c σ ρ (eCoe38_mem c σ y))))) := by
    intro y t
    have hx := eCoe38_mem c σ y
    have hxρ := seqE38_subset_seqSobolev38 c σ ρ hx
    obtain ⟨-, hs2⟩ := hsynth _ (hrange (orbitCLM38 c s ρ σ hσ y))
    have h1 := congrFun hs2 ((t : ℝ) : AddCircle (1 : ℝ))
    simp only [Function.comp_apply] at h1
    rw [h1, orbitCLM38_apply, synth_orbitMk38 c s ρ σ hσ _ hx t]
    refine hExt38 ρ' fun m => ?_
    change F (rotSeq38 (2 * π * t) (eCoe38 c σ y)) m = rotSeq38 (2 * π * t) (F (eCoe38 c σ y)) m
    rw [hequi _ hxρ]
  have hcoe : ∀ y : ECarrier38 c σ, eCoe38 c τ (K y) = F (eCoe38 c σ y) := fun y =>
    eCoe_modeCLM_of_orbit_synth38 c s ρ' τ hτ' _ _
      (hmem _ (seqE38_subset_seqSobolev38 c σ ρ (eCoe38_mem c σ y))) (key y)
  have hF : ∀ x ∈ seqE38 c σ, F x ∈ seqE38 c τ := by
    intro x hx
    have := eCoe38_mem c τ (K (eMk38 c σ x hx))
    rwa [hcoe, eCoe38_mk] at this
  have hKeq : eMap38 c σ τ F hF = K := by
    funext y
    refine eExt38 c τ ?_
    rw [eCoe38_eMap38, hcoe]
  refine ⟨hF, ?_, fun y => ?_⟩
  · rw [hKeq]; exact hKan
  · obtain ⟨hmemAw, -⟩ := hsynth _ (hrange (orbitCLM38 c s ρ σ hσ y))
    refine ⟨hmemAw, ?_⟩
    rw [hKeq]
    have hsyn := hsynth _ (hrange (orbitCLM38 c s ρ σ hσ y))
    rw [← hsyn.2, awNorm_synth hw]
    exact norm_eq_of_orbit_synth38 c s ρ' τ hτ' _ _
      (hmem _ (seqE38_subset_seqSobolev38 c σ ρ (eCoe38_mem c σ y))) (key y)

end Core

/-! ## Inclusions `E_s ⊆ E_{s'}` (`s ≤ s'`) and the Cameron-Martin space `E_0` -/

section Incl

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper)

theorem fullModeWeight_anti38 {s s' : ℝ} (h : s ≤ s') (n : ℤ) :
    fullModeWeight c s' n ≤ fullModeWeight c s n := by
  unfold fullModeWeight
  refine mul_le_mul_of_nonneg_left ?_ (sourceRate_pos c n).le
  exact Real.rpow_le_rpow_of_exponent_le (japaneseBracket_one_le n) (by linarith)

theorem seqE38_mono {s s' : ℝ} (h : s ≤ s') {x : ℤ → ℂ} (hx : x ∈ seqE38 c s) :
    x ∈ seqE38 c s' := by
  rw [mem_seqE38_iff] at hx ⊢
  exact Summable.of_nonneg_of_le (fun n => mul_nonneg (fullModeWeight_pos c s' n).le (sq_nonneg _))
    (fun n => mul_le_mul_of_nonneg_right (fullModeWeight_anti38 c h n) (sq_nonneg _)) hx

/-- The inclusion `E_s ↪ E_{s'}` is a contraction. -/
theorem norm_eIncl_le38 {s s' : ℝ} (h : s ≤ s') (y : ECarrier38 c s) :
    ‖eMap38 c s s' id (fun _ hx => seqE38_mono c h hx) y‖ ≤ ‖y‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [norm_sq_eCarrier38, norm_sq_eCarrier38]
  have e : ∀ n, eCoe38 c s' (eMap38 c s s' id (fun _ hx => seqE38_mono c h hx) y) n = eCoe38 c s y n := fun n => by
    rw [eCoe38_eMap38]; rfl
  simp only [e]
  have hy : Summable fun n : ℤ => fullModeWeight c s n * ‖eCoe38 c s y n‖ ^ 2 :=
    (mem_seqE38_iff c s _).1 (eCoe38_mem c s y)
  have hy' : Summable fun n : ℤ => fullModeWeight c s' n * ‖eCoe38 c s y n‖ ^ 2 :=
    (mem_seqE38_iff c s' _).1 (seqE38_mono c h (eCoe38_mem c s y))
  refine Summable.tsum_le_tsum (fun n => ?_) hy' hy
  exact mul_le_mul_of_nonneg_right (fullModeWeight_anti38 c h n) (sq_nonneg _)

/-- The inclusion `E_s ↪ E_{s'}` for `s ≤ s'`, a real-linear contraction. -/
def eInclCLM38 {s s' : ℝ} (h : s ≤ s') : ECarrier38 c s →L[ℝ] ECarrier38 c s' :=
  LinearMap.mkContinuous
    { toFun := eMap38 c s s' id (fun _ hx => seqE38_mono c h hx)
      map_add' := fun y z => eExt38 c s' (funext fun n => by
        rw [eCoe38_eMap38, eAdd_apply38 c s', eCoe38_eMap38, eCoe38_eMap38]
        exact eAdd_apply38 c s y z n)
      map_smul' := fun a y => eExt38 c s' (funext fun n => by
        show eCoe38 c s' (eMap38 c s s' id (fun _ hx => seqE38_mono c h hx) (a • y)) n =
          eCoe38 c s' (a • eMap38 c s s' id (fun _ hx => seqE38_mono c h hx) y) n
        rw [eCoe38_eMap38, eSmul_apply38 c s', eCoe38_eMap38]
        exact eSmul_apply38 c s a y n) }
    1 (fun y => by
      rw [one_mul]
      exact norm_eIncl_le38 c h y)

theorem eCoe38_eInclCLM38 {s s' : ℝ} (h : s ≤ s') (y : ECarrier38 c s) :
    eCoe38 c s' (eInclCLM38 c h y) = eCoe38 c s y := by
  funext n
  show eCoe38 c s' (eMap38 c s s' id (fun _ hx => seqE38_mono c h hx) y) n = _
  rw [eCoe38_eMap38]; rfl

/-- `E_0` is the Cameron-Martin sequence space: `x ∈ E_0 ↔ ∑ 2 a_n |x_n|² < ∞`
(`ActualCM c = WeightedRealHilbert (cmModeWeight c)`, `cmModeWeight c n = 2 a_n`; v2 `D:eq:CM`). -/
theorem mem_seqE38_zero_iff_cm (x : ℤ → ℂ) :
    x ∈ seqE38 c 0 ↔ x ∈ weightedSubmodule (cmModeWeight c) := by
  change x ∈ weightedSubmodule (fullModeWeight c 0) ↔ _
  change Memℓp (weightedCoordinates (fullModeWeight c 0) x) 2 ↔
    Memℓp (weightedCoordinates (cmModeWeight c) x) 2
  rw [weightedCoordinates_mem_l2_iff (fullModeWeight c 0) (fun n => (fullModeWeight_pos c 0 n).le),
    weightedCoordinates_mem_l2_iff (cmModeWeight c) (fun n => (cmModeWeight_pos c n).le)]
  have h : ∀ n : ℤ, cmModeWeight c n * ‖x n‖ ^ 2 = 2 * (fullModeWeight c 0 n * ‖x n‖ ^ 2) := by
    intro n
    unfold cmModeWeight fullModeWeight
    simp [Real.rpow_zero]
    ring
  simp_rw [h]
  exact (summable_mul_left_iff (by norm_num : (2 : ℝ) ≠ 0)).symm

end Incl

/-! ## W04: the Birkhoff application (conditional on `B : BirkhoffInput38`, `O : OneSmoothingInput38 B`)

`B` fields used: `T`, `Tinv`, `left_inv`, `right_inv` (via `Tinv_rotSeq38`, `T_rotSeq38_h1`, `T_rotSeq38`
from S01, which use `canonical`, `action`, `analytic_T`, `analytic_Tinv`, `mapsTo_T`, `mapsTo_Tinv`).
`O` fields used: `smooth_T 1`, `smooth_Tinv 1`, `analytic_smooth_T 1`, `analytic_smooth_Tinv 1`.
-/

namespace BirkhoffInput38

variable {lower upper : ℝ}

theorem rotSeq38_sub (θ : ℝ) (a b : ℤ → ℂ) :
    rotSeq38 θ (a - b) = rotSeq38 θ a - rotSeq38 θ b := by
  funext n; simp only [rotSeq38_apply, Pi.sub_apply, mul_sub]

/-- `K = T - Id` commutes with the rotations on `h¹` (v2: "translation equivariance identifies the
image under `K` with the orbit `S_θ K(x)`"; from S01 `T_rotSeq38`). -/
theorem K_equivariant38 (B : BirkhoffInput38) (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ))
    (θ : ℝ) :
    (fun y => B.T y - y) (rotSeq38 θ x) = rotSeq38 θ ((fun y => B.T y - y) x) := by
  show B.T (rotSeq38 θ x) - rotSeq38 θ x = rotSeq38 θ (B.T x - x)
  rw [rotSeq38_sub, B.T_rotSeq38 x (seqSobolev38_natCast_mono hx) θ]

/-- `T⁻¹ - Id` commutes with the rotations on `h¹` (S01 `Tinv_rotSeq38`). -/
theorem Kinv_equivariant38 (B : BirkhoffInput38) (x : ℤ → ℂ)
    (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) (θ : ℝ) :
    (fun y => B.Tinv y - y) (rotSeq38 θ x) = rotSeq38 θ ((fun y => B.Tinv y - y) x) := by
  show B.Tinv (rotSeq38 θ x) - rotSeq38 θ x = rotSeq38 θ (B.Tinv x - x)
  rw [rotSeq38_sub, B.Tinv_rotSeq38 x (seqSobolev38_natCast_mono hx) θ]

/-- **W04.04 (existence form).** `K = T - Id : E_s → E_{s-1}` is well defined and real analytic. -/
theorem weighted_K_exists38 (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
    (c : BoundedCoefficients lower upper) (s : ℝ) :
    ∃ hF : ∀ x ∈ seqE38 c s, B.T x - x ∈ seqE38 c (s - 1),
      AnalyticOnNhd ℝ (eMap38 c s (s - 1) (fun y => B.T y - y) hF) Set.univ := by
  obtain ⟨hF, han, -⟩ := weighted_smoothing_core38 c ((1 : ℕ) : ℝ) ((1 + 1 : ℕ) : ℝ) s (s - 1)
    (by push_cast; ring) (fun y => B.T y - y) (O.smooth_T 1 le_rfl) (O.analytic_smooth_T 1 le_rfl)
    (B.K_equivariant38)
  exact ⟨hF, han⟩

/-- **W04.06 (existence form).** `T⁻¹ - Id : E_s → E_{s-1}` is well defined and real analytic. -/
theorem weighted_Kinv_exists38 (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
    (c : BoundedCoefficients lower upper) (s : ℝ) :
    ∃ hF : ∀ x ∈ seqE38 c s, B.Tinv x - x ∈ seqE38 c (s - 1),
      AnalyticOnNhd ℝ (eMap38 c s (s - 1) (fun y => B.Tinv y - y) hF) Set.univ := by
  obtain ⟨hF, han, -⟩ := weighted_smoothing_core38 c ((1 : ℕ) : ℝ) ((1 + 1 : ℕ) : ℝ) s (s - 1)
    (by push_cast; ring) (fun y => B.Tinv y - y) (O.smooth_Tinv 1 le_rfl)
    (O.analytic_smooth_Tinv 1 le_rfl) (B.Kinv_equivariant38)
  exact ⟨hF, han⟩

/-- **W04 (i), membership.** `K x = T x - x ∈ E_{s-1}` for `x ∈ E_s`, every real `s`. -/
theorem K_mem_E38 (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
    (c : BoundedCoefficients lower upper) (s : ℝ) :
    ∀ x ∈ seqE38 c s, B.T x - x ∈ seqE38 c (s - 1) :=
  (B.weighted_K_exists38 O c s).choose

/-- **W04 (i), analyticity.** `K : E_s → E_{s-1}` is real analytic (on all of `E_s`), every real `s`. -/
theorem analytic_K_E38 (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
    (c : BoundedCoefficients lower upper) (s : ℝ) :
    AnalyticOnNhd ℝ (eMap38 c s (s - 1) (fun y => B.T y - y) (B.K_mem_E38 O c s)) Set.univ :=
  (B.weighted_K_exists38 O c s).choose_spec

/-- **W04 (ii), membership.** `T⁻¹ x - x ∈ E_{s-1}` for `x ∈ E_s`, every real `s`. -/
theorem Kinv_mem_E38 (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
    (c : BoundedCoefficients lower upper) (s : ℝ) :
    ∀ x ∈ seqE38 c s, B.Tinv x - x ∈ seqE38 c (s - 1) :=
  (B.weighted_Kinv_exists38 O c s).choose

/-- **W04 (ii), analyticity.** `T⁻¹ - Id : E_s → E_{s-1}` is real analytic, every real `s`. -/
theorem analytic_Kinv_E38 (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
    (c : BoundedCoefficients lower upper) (s : ℝ) :
    AnalyticOnNhd ℝ (eMap38 c s (s - 1) (fun y => B.Tinv y - y) (B.Kinv_mem_E38 O c s))
      Set.univ :=
  (B.weighted_Kinv_exists38 O c s).choose_spec

/-! ### `T` and `T⁻¹` preserve `E_s`; `T` is a global analytic diffeomorphism of `E_s` -/

theorem T_mem_E38 (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
    (c : BoundedCoefficients lower upper) (s : ℝ) : ∀ x ∈ seqE38 c s, B.T x ∈ seqE38 c s := by
  intro x hx
  have h1 := seqE38_mono c (by linarith : s - 1 ≤ s) (B.K_mem_E38 O c s x hx)
  have h2 : x + (B.T x - x) ∈ weightedSubmodule (fullModeWeight c s) :=
    Submodule.add_mem _ hx h1
  rwa [add_sub_cancel] at h2

theorem Tinv_mem_E38 (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
    (c : BoundedCoefficients lower upper) (s : ℝ) : ∀ x ∈ seqE38 c s, B.Tinv x ∈ seqE38 c s := by
  intro x hx
  have h1 := seqE38_mono c (by linarith : s - 1 ≤ s) (B.Kinv_mem_E38 O c s x hx)
  have h2 : x + (B.Tinv x - x) ∈ weightedSubmodule (fullModeWeight c s) :=
    Submodule.add_mem _ hx h1
  rwa [add_sub_cancel] at h2

theorem eMap_T_eq38 (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
    (c : BoundedCoefficients lower upper) (s : ℝ) :
    eMap38 c s s B.T (B.T_mem_E38 O c s) = fun y =>
      y + eInclCLM38 c (by linarith : s - 1 ≤ s)
        (eMap38 c s (s - 1) (fun z => B.T z - z) (B.K_mem_E38 O c s) y) := by
  funext y
  refine eExt38 c s (funext fun n => ?_)
  rw [eCoe38_eMap38, eAdd_apply38, eCoe38_eInclCLM38, eCoe38_eMap38]
  simp only [Pi.sub_apply]
  ring

theorem eMap_Tinv_eq38 (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
    (c : BoundedCoefficients lower upper) (s : ℝ) :
    eMap38 c s s B.Tinv (B.Tinv_mem_E38 O c s) = fun y =>
      y + eInclCLM38 c (by linarith : s - 1 ≤ s)
        (eMap38 c s (s - 1) (fun z => B.Tinv z - z) (B.Kinv_mem_E38 O c s) y) := by
  funext y
  refine eExt38 c s (funext fun n => ?_)
  rw [eCoe38_eMap38, eAdd_apply38, eCoe38_eInclCLM38, eCoe38_eMap38]
  simp only [Pi.sub_apply]
  ring

/-- `T : E_s → E_s` is real analytic. -/
theorem analytic_T_E38 (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
    (c : BoundedCoefficients lower upper) (s : ℝ) :
    AnalyticOnNhd ℝ (eMap38 c s s B.T (B.T_mem_E38 O c s)) Set.univ := by
  rw [B.eMap_T_eq38 O c s]
  exact analyticOnNhd_id.add (((eInclCLM38 c (by linarith : s - 1 ≤ s)).analyticOnNhd _).comp
    (B.analytic_K_E38 O c s) (fun _ _ => Set.mem_univ _))

/-- `T⁻¹ : E_s → E_s` is real analytic. -/
theorem analytic_Tinv_E38 (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
    (c : BoundedCoefficients lower upper) (s : ℝ) :
    AnalyticOnNhd ℝ (eMap38 c s s B.Tinv (B.Tinv_mem_E38 O c s)) Set.univ := by
  rw [B.eMap_Tinv_eq38 O c s]
  exact analyticOnNhd_id.add (((eInclCLM38 c (by linarith : s - 1 ≤ s)).analyticOnNhd _).comp
    (B.analytic_Kinv_E38 O c s) (fun _ _ => Set.mem_univ _))

/-- **W04.06.** The restrictions of `T` and `T⁻¹` to `E_s` are mutually inverse (already true on
`h⁰ ⊇ E_s`). -/
theorem Tinv_T_E38 (B : BirkhoffInput38) (c : BoundedCoefficients lower upper) (s : ℝ)
    {x : ℤ → ℂ} (hx : x ∈ seqE38 c s) : B.Tinv (B.T x) = x :=
  B.left_inv x (seqE38_subset_seqSobolev38 c s 0 hx)

theorem T_Tinv_E38 (B : BirkhoffInput38) (c : BoundedCoefficients lower upper) (s : ℝ)
    {x : ℤ → ℂ} (hx : x ∈ seqE38 c s) : B.T (B.Tinv x) = x :=
  B.right_inv x (seqE38_subset_seqSobolev38 c s 0 hx)

/-- **W04 (iii).** `T` is a global analytic diffeomorphism of `E_s` onto itself, for every real
`s`: a homeomorphism of `ECarrier38 c s` extending `T` on sequences (`weightedHomeoE38_apply`),
which is real analytic together with its inverse (`analytic_weightedHomeoE38`,
`analytic_weightedHomeoE38_symm`). -/
def weightedHomeoE38 (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
    (c : BoundedCoefficients lower upper) (s : ℝ) : ECarrier38 c s ≃ₜ ECarrier38 c s where
  toFun := eMap38 c s s B.T (B.T_mem_E38 O c s)
  invFun := eMap38 c s s B.Tinv (B.Tinv_mem_E38 O c s)
  left_inv := fun y => eExt38 c s (by
    rw [eCoe38_eMap38, eCoe38_eMap38]
    exact B.Tinv_T_E38 c s (eCoe38_mem c s y))
  right_inv := fun y => eExt38 c s (by
    rw [eCoe38_eMap38, eCoe38_eMap38]
    exact B.T_Tinv_E38 c s (eCoe38_mem c s y))
  continuous_toFun := (B.analytic_T_E38 O c s).continuous
  continuous_invFun := (B.analytic_Tinv_E38 O c s).continuous

theorem weightedHomeoE38_apply (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
    (c : BoundedCoefficients lower upper) (s : ℝ) (y : ECarrier38 c s) :
    eCoe38 c s (B.weightedHomeoE38 O c s y) = B.T (eCoe38 c s y) := by
  show eCoe38 c s (eMap38 c s s B.T (B.T_mem_E38 O c s) y) = _
  rw [eCoe38_eMap38]

theorem weightedHomeoE38_symm_apply (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
    (c : BoundedCoefficients lower upper) (s : ℝ) (y : ECarrier38 c s) :
    eCoe38 c s ((B.weightedHomeoE38 O c s).symm y) = B.Tinv (eCoe38 c s y) := by
  show eCoe38 c s (eMap38 c s s B.Tinv (B.Tinv_mem_E38 O c s) y) = _
  rw [eCoe38_eMap38]

theorem analytic_weightedHomeoE38 (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
    (c : BoundedCoefficients lower upper) (s : ℝ) :
    AnalyticOnNhd ℝ (B.weightedHomeoE38 O c s) Set.univ :=
  B.analytic_T_E38 O c s

theorem analytic_weightedHomeoE38_symm (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
    (c : BoundedCoefficients lower upper) (s : ℝ) :
    AnalyticOnNhd ℝ (B.weightedHomeoE38 O c s).symm Set.univ :=
  B.analytic_Tinv_E38 O c s

/-! ### W04.07: values in the Cameron-Martin space `E_0` for `s ≤ 1` (v2 range `1/2 < s < 3/4`) -/

/-- For `s ≤ 1` (in particular for v2's range `1/2 < s < 3/4`) both differences take values in the
Cameron-Martin space `E_0 = H` (`E_{s-1} ↪ E_0` since `s - 1 ≤ 0`). -/
theorem differences_mem_E0_38 (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
    (c : BoundedCoefficients lower upper) {s : ℝ} (hs : s ≤ 1) :
    (∀ x ∈ seqE38 c s, B.T x - x ∈ seqE38 c 0) ∧ (∀ x ∈ seqE38 c s, B.Tinv x - x ∈ seqE38 c 0) :=
  ⟨fun x hx => seqE38_mono c (by linarith : s - 1 ≤ 0) (B.K_mem_E38 O c s x hx),
   fun x hx => seqE38_mono c (by linarith : s - 1 ≤ 0) (B.Kinv_mem_E38 O c s x hx)⟩

/-- The same statement for the actual Cameron-Martin sequence space
`WeightedRealHilbert (cmModeWeight c)` (`ActualCM c`). -/
theorem differences_mem_CM_38 (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
    (c : BoundedCoefficients lower upper) {s : ℝ} (hs : s ≤ 1) :
    (∀ x ∈ seqE38 c s, B.T x - x ∈ weightedSubmodule (cmModeWeight c)) ∧
      (∀ x ∈ seqE38 c s, B.Tinv x - x ∈ weightedSubmodule (cmModeWeight c)) :=
  ⟨fun x hx => (mem_seqE38_zero_iff_cm c _).1 ((B.differences_mem_E0_38 O c hs).1 x hx),
   fun x hx => (mem_seqE38_zero_iff_cm c _).1 ((B.differences_mem_E0_38 O c hs).2 x hx)⟩

/-- Analyticity of the differences as maps `E_s → E_0 = H` (for `s ≤ 1`). -/
theorem analytic_differences_E0_38 (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
    (c : BoundedCoefficients lower upper) {s : ℝ} (hs : s ≤ 1) :
    AnalyticOnNhd ℝ (eMap38 c s 0 (fun y => B.T y - y) (B.differences_mem_E0_38 O c hs).1)
        Set.univ ∧
      AnalyticOnNhd ℝ (eMap38 c s 0 (fun y => B.Tinv y - y) (B.differences_mem_E0_38 O c hs).2)
        Set.univ := by
  have h : s - 1 ≤ 0 := by linarith
  constructor
  · have e : eMap38 c s 0 (fun y => B.T y - y) (B.differences_mem_E0_38 O c hs).1 =
        fun y => eInclCLM38 c h (eMap38 c s (s - 1) (fun z => B.T z - z) (B.K_mem_E38 O c s) y) := by
      funext y
      refine eExt38 c 0 (funext fun n => ?_)
      rw [eCoe38_eMap38, eCoe38_eInclCLM38, eCoe38_eMap38]
    rw [e]
    exact ((eInclCLM38 c h).analyticOnNhd _).comp (B.analytic_K_E38 O c s) (fun _ _ => Set.mem_univ _)
  · have e : eMap38 c s 0 (fun y => B.Tinv y - y) (B.differences_mem_E0_38 O c hs).2 =
        fun y => eInclCLM38 c h
          (eMap38 c s (s - 1) (fun z => B.Tinv z - z) (B.Kinv_mem_E38 O c s) y) := by
      funext y
      refine eExt38 c 0 (funext fun n => ?_)
      rw [eCoe38_eMap38, eCoe38_eInclCLM38, eCoe38_eMap38]
    rw [e]
    exact ((eInclCLM38 c h).analyticOnNhd _).comp (B.analytic_Kinv_E38 O c s)
      (fun _ _ => Set.mem_univ _)

end BirkhoffInput38

end NlsGge.Birkhoff
