import NlsGge.Composition.Bilinear
import NlsGge.Composition.Multilinear
import NlsGge.Composition.TaylorModel
import NlsGge.Composition.TrigApprox
import NlsGge.Composition.CompMap
import NlsGge.Composition.LocalBounds

/-!
# `D:lem:composition` (paper/v2.tex lines 1438-1480): analytic composition on `A_w`

Final assembly (W03.08).  Fix `g₀` whose synthesized function takes values in `O`.
1. `K = range (synth g₀)` is compact; uniform power-series data `δ, ρ, M` of `F` on the
   `δ`-thickening of `K` (W03.04, `exists_uniform_series_bounds`).
2. Only then choose a truncation `p` of `g₀` (W03.05) with `‖g₀ - p‖ < R/2` and
   `S_w ‖g₀ - p‖ < δ`, where `R` depends on `ρ, C_w, S_w` only.
3. Only after `p`, the decay rate `s` (W03.06) and the constant `D` (W03.07).
4. `P k = multCLM k (B_k)` is a power series of the composition map at `p` on the ball of
   radius `R`, which contains `g₀`; hence analyticity at `g₀` (W03.08).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace NlsGge.Composition

open AddCircle
open scoped ENNReal NNReal

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
variable {w : ℤ → ℝ}

/-- Local power series of the composition map around a trigonometric approximant, with a ball
containing the given point. -/
theorem exists_local_expansion (hw : AdmissibleWeight w) {F : X → Y} {O : Set X}
    (hO : IsOpen O) (hF : AnalyticOnNhd ℝ F O) {g₀ : Model X} (hg₀ : g₀ ∈ rangeSet w O) :
    ∃ (p : Model X) (P : FormalMultilinearSeries ℝ (Model X) (Model Y)) (A q R : ℝ),
      0 ≤ A ∧ 0 ≤ q ∧ 0 < R ∧ q * R ≤ 1 ∧ (∀ k, ‖P k‖ ≤ A * q ^ k) ∧
      (∀ r : Model X, ‖r‖ < R → ∀ θ : AddCircle (1 : ℝ),
        HasSum (fun k => synth w (P k (fun _ => r)) θ) (F (synth w (p + r) θ))) ∧
      ‖g₀ - p‖ < R := by
  classical
  -- Step 1: compact range and uniform data
  set K := Set.range (synth w g₀) with hKdef
  have hK : IsCompact K := isCompact_range_synth hw g₀
  have hKO : K ⊆ O := by rintro _ ⟨θ, rfl⟩; exact hg₀ θ
  obtain ⟨δ, ρ, M, hδ, hρ, hM, _hsub, hdata⟩ := exists_uniform_series_bounds hO hF hK hKO
  -- constants independent of the approximant
  set Sw := supConst w with hSw
  have hSw0 : 0 ≤ Sw := supConst_nonneg w
  set Cw := prodConst hw with hCw
  have hCw0 : 0 ≤ Cw := prodConst_nonneg hw
  set q : ℝ := Cw * (2 / ρ) with hq
  have hq0 : 0 ≤ q := by positivity
  set R : ℝ := min (1 / (q + 1)) (ρ / (Sw + 1)) with hR
  have hRpos : 0 < R := lt_min (by positivity) (by positivity)
  have hqR : q * R ≤ 1 := by
    calc q * R ≤ q * (1 / (q + 1)) := by gcongr; exact min_le_left _ _
      _ ≤ 1 := by rw [mul_one_div, div_le_one (by linarith)]; linarith
  have hSR : Sw * R < ρ := by
    calc Sw * R ≤ Sw * (ρ / (Sw + 1)) := by gcongr; exact min_le_right _ _
      _ < ρ := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith
  -- Step 2: the trigonometric approximant
  set ε : ℝ := min (R / 2) (δ / (Sw + 1)) with hε
  have hεpos : 0 < ε := lt_min (by positivity) (by positivity)
  obtain ⟨Sset, hSset⟩ := exists_truncate_near g₀ hεpos
  set p := truncate Sset g₀ with hp
  have hpR : ‖g₀ - p‖ < R := lt_of_lt_of_le hSset ((min_le_left _ _).trans (by linarith))
  have hpδ : Sw * ‖p - g₀‖ < δ := by
    rw [norm_sub_rev]
    calc Sw * ‖g₀ - p‖ ≤ Sw * (δ / (Sw + 1)) := by
          gcongr; exact hSset.le.trans (min_le_right _ _)
      _ < δ := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith
  set v : ℤ → X := coeff w g₀ with hv
  have hpsynth : ∀ θ, synth w p θ = ∑ n ∈ Sset, fourier n θ • v n := fun θ =>
    synth_truncate Sset g₀ θ
  have hγ : ∀ θ : AddCircle (1 : ℝ), (∑ n ∈ Sset, fourier n θ • v n) ∈ Metric.thickening δ K := by
    intro θ
    rw [← hpsynth]
    exact synth_mem_thickening hw hpδ θ
  -- Step 3: Taylor coefficients in `A_w`
  obtain ⟨D, hD0, hB⟩ := taylorFun_memAw hw hδ hρ hM hdata Sset v hγ
  set Bk : (k : ℕ) → Model (ContinuousMultilinearMap ℝ (fun _ : Fin k => X) Y) :=
    fun k => toModel hw (hB k).1 with hBk
  have hBk_norm : ∀ k, ‖Bk k‖ ≤ 2 * M * (2 / ρ) ^ k * D := fun k => by
    simp only [hBk]; rw [norm_toModel]; exact (hB k).2
  have hBk_synth : ∀ k θ, synth w (Bk k) θ = taylorFun F Sset v k θ := fun k θ => by
    simp only [hBk]; rw [synth_toModel]
  -- Step 4: the formal series on the model
  set P : FormalMultilinearSeries ℝ (Model X) (Model Y) := fun k => multCLM hw k (Bk k) with hP
  refine ⟨p, P, 2 * M * D, q, R, by positivity, hq0, hRpos, hqR, fun k => ?_, ?_, hpR⟩
  · have h1 := (multCLM hw k (X := X) (Y := Y)).le_opNorm (Bk k)
    have h2 := norm_multCLM_le hw k (X := X) (Y := Y)
    have h3 := hBk_norm k
    have hn0 : 0 ≤ ‖Bk k‖ := norm_nonneg _
    calc ‖P k‖ ≤ Cw ^ k * (2 * M * (2 / ρ) ^ k * D) :=
          h1.trans (mul_le_mul h2 h3 hn0 (by positivity))

      _ = 2 * M * D * q ^ k := by rw [hq, mul_pow]; ring
  · intro r hr θ
    have hy : synth w p θ ∈ Metric.thickening δ K := by rw [hpsynth]; exact hγ θ
    obtain ⟨pser, hpser, -⟩ := hdata _ hy
    have hz : synth w r θ ∈ Metric.eball (0 : X) (ENNReal.ofReal ρ) := by
      rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff hρ]
      calc ‖synth w r θ‖ ≤ Sw * ‖r‖ := norm_synth_le hw r θ
        _ ≤ Sw * R := by gcongr
        _ < ρ := hSR
    have hsum := hpser.hasSum_iteratedFDeriv hz
    rw [synth_add hw]
    refine hsum.congr_fun fun k => ?_
    simp only [hP]
    rw [synth_multCLM, hBk_synth, taylorFun, ← hpsynth]
    rfl

/-- **`D:lem:composition`, analyticity (model form).**  For an admissible weight, an open
`O ⊆ X` and `F` real analytic on `O`, the set of model elements whose synthesized function
takes values in `O` is open, the composition map is real analytic on it, and it represents
`F ∘ synth`. -/
theorem composition_analytic (hw : AdmissibleWeight w) {F : X → Y} {O : Set X}
    (hO : IsOpen O) (hF : AnalyticOnNhd ℝ F O) :
    IsOpen (rangeSet w O) ∧ AnalyticOnNhd ℝ (compMap hw F) (rangeSet w O) ∧
      ∀ g ∈ rangeSet w O, MemAw w (F ∘ synth w g) ∧ synth w (compMap hw F g) = F ∘ synth w g := by
  refine ⟨isOpen_rangeSet hw hO, fun g hg => ?_, fun g hg => ?_⟩
  · obtain ⟨p, P, A, q, R, hA, hq, hR, hqR, hP, hpt, hgp⟩ := exists_local_expansion hw hO hF hg
    have hps := hasFPowerSeriesOnBall_compMap hw F p P hA hq hR hqR hP hpt
    have hmem : g ∈ Metric.eball p (ENNReal.ofReal R) := by
      rw [Metric.mem_eball, edist_dist, dist_eq_norm, ENNReal.ofReal_lt_ofReal_iff hR]
      exact hgp
    exact hps.analyticAt_of_mem hmem
  · obtain ⟨p, P, A, q, R, hA, hq, hR, hqR, hP, hpt, hgp⟩ := exists_local_expansion hw hO hF hg
    have hm := memAw_comp_of_expansion hw F p P hA hq hR hqR hP hpt hgp
    have e : p + (g - p) = g := add_sub_cancel p g
    rw [e] at hm
    exact ⟨hm, synth_compMap hw hm⟩

/-- **`D:lem:composition`, second assertion (function form).**  If `F : X → Y` is real analytic
on the open set `O` and `f ∈ A_w(X)` takes values in `O`, then `F ∘ f ∈ A_w(Y)`.  No smallness
of `‖f‖_{A_w}` is assumed. -/
theorem composition_mem (hw : AdmissibleWeight w) {F : X → Y} {O : Set X} (hO : IsOpen O)
    (hF : AnalyticOnNhd ℝ F O) {f : AddCircle (1 : ℝ) → X} (hf : MemAw w f)
    (hfO : ∀ θ, f θ ∈ O) : MemAw w (F ∘ f) := by
  have hg : toModel hw hf ∈ rangeSet w O := fun θ => by rw [synth_toModel]; exact hfO θ
  have := ((composition_analytic hw hO hF).2.2 _ hg).1
  rwa [synth_toModel] at this

/-! ### Specialization to the source weight `w_n = exp(a √|n|) ⟨n⟩^b` -/

/-- (i) for the source weight. -/
theorem srcWeight_composition_bilinear {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    [CompleteSpace Z] {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : X →L[ℝ] Y →L[ℝ] Z) {f : AddCircle (1 : ℝ) → X}
      {g : AddCircle (1 : ℝ) → Y}, MemAw (srcWeight a b) f → MemAw (srcWeight a b) g →
      MemAw (srcWeight a b) (fun θ => B (f θ) (g θ)) ∧
      awNorm (srcWeight a b) (fun θ => B (f θ) (g θ)) ≤
        C * ‖B‖ * awNorm (srcWeight a b) f * awNorm (srcWeight a b) g :=
  ⟨prodConst (srcWeight_admissible ha b), prodConst_nonneg _,
    fun B _ _ hf hg => composition_bilinear (srcWeight_admissible ha b) B hf hg⟩

/-- (ii) for the source weight. -/
theorem srcWeight_composition_mem {a : ℝ} (ha : 0 < a) (b : ℝ) {F : X → Y} {O : Set X}
    (hO : IsOpen O) (hF : AnalyticOnNhd ℝ F O) {f : AddCircle (1 : ℝ) → X}
    (hf : MemAw (srcWeight a b) f) (hfO : ∀ θ, f θ ∈ O) : MemAw (srcWeight a b) (F ∘ f) :=
  composition_mem (srcWeight_admissible ha b) hO hF hf hfO

/-- (iii) for the source weight. -/
theorem srcWeight_composition_analytic {a : ℝ} (ha : 0 < a) (b : ℝ) {F : X → Y} {O : Set X}
    (hO : IsOpen O) (hF : AnalyticOnNhd ℝ F O) :
    IsOpen (rangeSet (srcWeight a b) O) ∧
      AnalyticOnNhd ℝ (compMap (srcWeight_admissible ha b) F) (rangeSet (srcWeight a b) O) ∧
      ∀ g ∈ rangeSet (srcWeight a b) O, MemAw (srcWeight a b) (F ∘ synth (srcWeight a b) g) ∧
        synth (srcWeight a b) (compMap (srcWeight_admissible ha b) F g) =
          F ∘ synth (srcWeight a b) g :=
  composition_analytic (srcWeight_admissible ha b) hO hF

end NlsGge.Composition
