import Mathlib
import QuantumNLS.FormCoreReduction

/-!
# R-1602B09D `CC:F03:core`: assembly of the density theorem from the mollification step

`core_density`: for `μ = ρ dx` with `CoreHyp ρ`, if `MollifyCore ρ` holds then every measurable `h` with `N_μ(h) < ∞`
(`N_μ(h) = ‖h‖²_{L²(μ)} + E_μ(h)`) is approximable by `C_c^∞(ℝ;ℝ)` in the form norm.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff Real

noncomputable section

namespace QuantumNLS.FormCore

variable {ρ : ℝ → ℝ}

theorem muRho_null_compl (H : CoreHyp ρ) : muRho ρ {x | ¬ 0 < ρ x} = 0 := by
  have hm : MeasurableSet {x : ℝ | ¬ 0 < ρ x} := (measurableSet_lt measurable_const H.cont.measurable).compl
  rw [withDensity_apply _ hm]
  rw [setLIntegral_congr_fun hm (g := fun _ => 0) (fun x hx => by
    have : ρ x = 0 := le_antisymm (not_lt.1 hx) (H.nonneg x)
    simp [this])]
  simp

theorem formN_eq_zero_of_null (H : CoreHyp ρ) {f : ℝ → ℝ} (h0 : ∀ x, 0 < ρ x → f x = 0) :
    formN (muRho ρ) f = 0 := by
  haveI := H.fin
  have hnull : ∀ᵐ x ∂(muRho ρ), 0 < ρ x := by
    have := muRho_null_compl H
    rw [measure_eq_zero_iff_ae_notMem] at this
    filter_upwards [this] with x hx
    simpa using hx
  have hL : formL2 (muRho ρ) f = 0 := by
    unfold formL2
    rw [lintegral_congr_ae (g := fun _ => 0) (by filter_upwards [hnull] with x hx; rw [h0 x hx]; simp)]
    simp
  have hE : formE (muRho ρ) f = 0 := by
    unfold formE
    have h1 : ∀ᵐ p ∂((muRho ρ).prod (muRho ρ)), 0 < ρ p.1 :=
      (Measure.quasiMeasurePreserving_fst (μ := muRho ρ) (ν := muRho ρ)).ae hnull
    have h2 : ∀ᵐ p ∂((muRho ρ).prod (muRho ρ)), 0 < ρ p.2 :=
      (Measure.quasiMeasurePreserving_snd (μ := muRho ρ) (ν := muRho ρ)).ae hnull
    rw [lintegral_congr_ae (g := fun _ => 0) (by
      filter_upwards [h1, h2] with p a b
      simp [dq, h0 _ a, h0 _ b])]
    simp
  simp [formN, hL, hE]

theorem rho_zero_of_frontier (H : CoreHyp ρ) {e : ℝ} (he : e ∈ frontier {x | 0 < ρ x}) : ρ e = 0 := by
  have hPopen : IsOpen {x : ℝ | 0 < ρ x} := isOpen_lt continuous_const H.cont
  have : e ∉ {x : ℝ | 0 < ρ x} := by
    intro h
    have := he.2
    rw [hPopen.interior_eq] at this
    exact this h
  exact le_antisymm (not_lt.1 this) (H.nonneg e)

theorem approx_compact_case (H : CoreHyp ρ) (hm : MollifyCore ρ) :
    ∀ g : ℝ → ℝ, Measurable g → (∃ M : ℝ, ∀ x, |g x| ≤ M) → (∃ R : ℝ, ∀ x, R ≤ |x| → g x = 0) →
      formN (muRho ρ) g < ⊤ → Approx (muRho ρ) g := by
  classical
  intro g hg ⟨M, hM⟩ ⟨R, hR⟩ hN
  haveI := H.fin
  set P : Set ℝ := {x | 0 < ρ x} with hP
  have hPopen : IsOpen P := isOpen_lt continuous_const H.cont
  set g' : ℝ → ℝ := fun x => if 0 < ρ x then g x else 0 with hg'def
  have hg'm : Measurable g' :=
    Measurable.ite (measurableSet_lt measurable_const H.cont.measurable) hg measurable_const
  have hgg' : formN (muRho ρ) (fun x => g x - g' x) = 0 :=
    formN_eq_zero_of_null H (fun x hx => by simp [hg'def, hx])
  have hg'M : ∀ x, |g' x| ≤ M := fun x => by
    by_cases hx : 0 < ρ x
    · simp [hg'def, hx, hM x]
    · simp only [hg'def, hx, if_false, abs_zero]; exact le_trans (abs_nonneg _) (hM x)
  have hNg' : formN (muRho ρ) g' < ⊤ :=
    formN_finite_of_close hg hg'm hN (by rw [hgg']; simp)
  have hg'R : ∀ x, R ≤ |x| → g' x = 0 := fun x hx => by simp only [hg'def]; split_ifs <;> simp [hR x hx]
  have hg'P : ∀ x, x ∉ P → g' x = 0 := fun x hx => by
    have : ¬ 0 < ρ x := hx
    simp [hg'def, this]
  set Fs : Finset ℝ := (H.lf (R + 1)).toFinset with hFs
  have hFsmem : ∀ e, e ∈ Fs ↔ e ∈ frontier P ∧ e ∈ Icc (-(R + 1)) (R + 1) := fun e =>
    (H.lf (R + 1)).mem_toFinset
  have hEρ : ∀ e ∈ Fs, ρ e = 0 := fun e he => rho_zero_of_frontier H ((hFsmem e).1 he).1
  apply approx_of_close hg
  intro ε hε
  obtain ⟨g2, hg2m, hg2, ⟨r, hr, hr'⟩, hN2⟩ :=
    remove_finset H Fs hEρ hg'm hg'M hNg' (ε / 4) (by positivity)
  have hg2M : ∀ x, |g2 x| ≤ M := fun x => le_trans (hg2 x) (hg'M x)
  have hNg2 : formN (muRho ρ) g2 < ⊤ :=
    formN_finite_of_close hg'm hg2m hNg' (lt_of_lt_of_le hN2 le_top)
  refine ⟨g2, hg2m, ?_, ?_⟩
  · set S : Set ℝ := {x | x ∈ closure P ∧ |x| ≤ R ∧ ∀ e ∈ Fs, r ≤ |x - e|} with hS
    have hSc : IsClosed S := by
      have h1 : IsClosed {x : ℝ | |x| ≤ R} := isClosed_le continuous_abs continuous_const
      have h2 : IsClosed {x : ℝ | ∀ e ∈ Fs, r ≤ |x - e|} := by
        have : {x : ℝ | ∀ e ∈ Fs, r ≤ |x - e|} = ⋂ e ∈ Fs, {x : ℝ | r ≤ |x - e|} := by
          ext x; simp
        rw [this]
        exact isClosed_biInter fun e _ => isClosed_le continuous_const (continuous_abs.comp (continuous_id.sub continuous_const))
      have : S = closure P ∩ ({x : ℝ | |x| ≤ R} ∩ {x : ℝ | ∀ e ∈ Fs, r ≤ |x - e|}) := by
        exact Set.ext fun x => Iff.rfl
      rw [this]
      exact isClosed_closure.inter (h1.inter h2)
    have hSb : S ⊆ Icc (-R) R := fun x hx => by
      have := hx.2.1
      rw [abs_le] at this; exact this
    have hSK : IsCompact S := isCompact_Icc.of_isClosed_subset hSc hSb
    have hSP : S ⊆ P := by
      intro x hx
      by_contra hxP
      have hfr : x ∈ frontier P := by
        refine ⟨hx.1, ?_⟩
        rw [hPopen.interior_eq]; exact hxP
      have hxI : x ∈ Icc (-(R + 1)) (R + 1) := by
        have := hx.2.1
        rw [abs_le] at this
        exact ⟨by linarith [this.1], by linarith [this.2]⟩
      have := hx.2.2 x ((hFsmem x).2 ⟨hfr, hxI⟩)
      rw [sub_self, abs_zero] at this
      linarith
    refine hm g2 hg2m ⟨M, hg2M⟩ S hSK hSP (fun x hx => ?_) hNg2
    -- g2 vanishes off S
    by_contra hne
    apply hx
    refine ⟨?_, ?_, ?_⟩
    · by_contra hcl
      have hxP : x ∉ P := fun h => hcl (subset_closure h)
      apply hne
      have := hg2 x
      rw [hg'P x hxP, abs_zero] at this
      exact abs_nonpos_iff.1 this
    · by_contra hlt
      push Not at hlt
      apply hne
      have := hg2 x
      rw [hg'R x hlt.le, abs_zero] at this
      exact abs_nonpos_iff.1 this
    · intro e he
      by_contra hlt
      push Not at hlt
      exact hne (hr' e he x hlt)
  · -- N(g - g2) < ε
    have e : (fun x => g x - g2 x) = fun x => (g x - g' x) + (g' x - g2 x) := by funext x; ring
    rw [e]
    refine lt_of_le_of_lt (formN_add_le (hg.sub hg'm) (hg'm.sub hg2m)) ?_
    rw [hgg', mul_zero, zero_add]
    have h4 : (2 : ℝ≥0∞) * formN (muRho ρ) (fun x => g' x - g2 x) < 2 * ENNReal.ofReal (ε / 4) := by
      rw [two_mul, two_mul]; exact ENNReal.add_lt_add hN2 hN2
    refine lt_of_lt_of_le h4 ?_
    calc (2 : ℝ≥0∞) * ENNReal.ofReal (ε / 4) = ENNReal.ofReal (2 * (ε / 4)) := by
          rw [ENNReal.ofReal_mul (by norm_num)]; simp
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by linarith)

/-- **The density theorem** (conditional on the mollification step). -/
theorem core_density (H : CoreHyp ρ) (hm : MollifyCore ρ) {h : ℝ → ℝ} (hh : Measurable h)
    (hN : formN (muRho ρ) h < ⊤) : Approx (muRho ρ) h := by
  haveI := H.fin
  refine approx_of_bounded (fun g hg hb hNg => ?_) hh hN
  obtain ⟨M, hM⟩ := hb
  exact approx_of_compact (approx_compact_case H hm) hg hM hNg

end QuantumNLS.FormCore

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.FormCore.core_density
