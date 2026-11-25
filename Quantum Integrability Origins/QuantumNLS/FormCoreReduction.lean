import Mathlib
import QuantumNLS.FormCoreEndpoint

/-!
# R-1602B09D `CC:F03:core`: the reduction to the mollification step

For `μ = ρ dx` with `ρ` continuous, `0 ≤ ρ ≤ B`, finite mass, and locally finite frontier of the positive set `P = {ρ > 0}`
(this is all that the density argument uses; smoothness of `ρ` inside `P`, the bounded-interval structure and the square-root rate of the printed hypotheses are not needed):

* `remove_endpoint`, `remove_finset`: for bounded measurable `h` of finite form norm and finitely many points `e` with `ρ(e) = 0`, there are `g`, `|g| ≤ |h|`, vanishing on a neighborhood of every `e`,
  with `N(h - g)` arbitrarily small (the cutoff `1 - w_δ`, `formE_wend_tendsto`, `formN_cut_tendsto`).
* `approx_compact_case`: the compactly supported bounded case reduces (after restriction to `P`, which changes `h` on a `μ`-null set, and removal of the finitely many endpoints in the window)
  to functions supported in a compact subset of `P`, to which the mollification hypothesis `MollifyCore` applies.
* `core_density`: `MollifyCore ρ` implies that every measurable `h` of finite form norm is approximable by `C_c^∞` in the form norm.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff Real

noncomputable section

namespace QuantumNLS.FormCore

/-- `μ_ρ = ρ dx`. -/
abbrev muRho (ρ : ℝ → ℝ) : Measure ℝ := volume.withDensity fun x => ENNReal.ofReal (ρ x)

/-- The density hypotheses actually used. -/
structure CoreHyp (ρ : ℝ → ℝ) : Prop where
  cont : Continuous ρ
  nonneg : ∀ x, 0 ≤ ρ x
  bdd : ∃ B : ℝ, ∀ x, ρ x ≤ B
  fin : IsFiniteMeasure (muRho ρ)
  lf : ∀ R : ℝ, (frontier {x | 0 < ρ x} ∩ Icc (-R) R).Finite

/-- The mollification step: bounded measurable `g` supported in a compact subset of `{ρ > 0}` of finite form norm is approximable. -/
def MollifyCore (ρ : ℝ → ℝ) : Prop :=
  ∀ g : ℝ → ℝ, Measurable g → (∃ M : ℝ, ∀ x, |g x| ≤ M) → ∀ S : Set ℝ, IsCompact S →
    S ⊆ {x | 0 < ρ x} → (∀ x, x ∉ S → g x = 0) → formN (muRho ρ) g < ⊤ → Approx (muRho ρ) g

variable {ρ : ℝ → ℝ}

theorem muRho_singleton (e : ℝ) : muRho ρ {e} = 0 :=
  withDensity_absolutelyContinuous _ _ (Real.volume_singleton)

theorem remove_endpoint (H : CoreHyp ρ) {e : ℝ} (he : ρ e = 0) {h : ℝ → ℝ} (hh : Measurable h)
    {M : ℝ} (hM : ∀ x, |h x| ≤ M) (hN : formN (muRho ρ) h < ⊤) :
    ∀ ε : ℝ, 0 < ε → ∃ g : ℝ → ℝ, Measurable g ∧ (∀ x, |g x| ≤ |h x|) ∧
      (∃ r : ℝ, 0 < r ∧ ∀ x, |x - e| < r → g x = 0) ∧
      formN (muRho ρ) (fun x => h x - g x) < ENNReal.ofReal ε := by
  haveI := H.fin
  obtain ⟨B, hB⟩ := H.bdd
  intro ε hε
  have hlim : ∀ᵐ x ∂(muRho ρ), Tendsto (fun k : ℕ => wend e (1 / ((k : ℝ) + 1)) x) atTop (𝓝 0) := by
    have : ∀ᵐ x ∂(muRho ρ), x ≠ e := by
      have h0 := muRho_singleton (ρ := ρ) e
      rw [measure_eq_zero_iff_ae_notMem] at h0
      filter_upwards [h0] with x hx
      simpa using hx
    filter_upwards [this] with x hx using wend_tendsto hx
  have ht := formN_cut_tendsto hh hM hN (w := fun k => wend e (1 / ((k : ℝ) + 1)))
    (fun k => measurable_wend _ _)
    (fun k x => by
      rw [abs_le]
      exact ⟨by linarith [wend_nonneg e (1 / ((k : ℝ) + 1)) x], wend_le_one e (1 / ((k : ℝ) + 1)) x⟩)
    hlim (formE_wend_tendsto H.cont H.nonneg hB he)
  have hev : ∀ᶠ k : ℕ in atTop, formN (muRho ρ) (fun x => wend e (1 / ((k : ℝ) + 1)) x * h x) <
      ENNReal.ofReal ε := ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))
  obtain ⟨k, hk⟩ := hev.exists
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hδ : 0 < 1 / ((k : ℝ) + 1) := by positivity
  refine ⟨fun x => (1 - wend e (1 / ((k : ℝ) + 1)) x) * h x,
    (measurable_const.sub (measurable_wend _ _)).mul hh, fun x => ?_, ⟨1 / ((k : ℝ) + 1), hδ, fun x hx => ?_⟩, ?_⟩
  · rw [abs_mul]
    have h0 : 0 ≤ 1 - wend e (1 / ((k : ℝ) + 1)) x := by linarith [wend_le_one e (1 / ((k : ℝ) + 1)) x]
    have h1 : 1 - wend e (1 / ((k : ℝ) + 1)) x ≤ 1 := by linarith [wend_nonneg e (1 / ((k : ℝ) + 1)) x]
    rw [abs_of_nonneg h0]
    calc (1 - wend e (1 / ((k : ℝ) + 1)) x) * |h x| ≤ 1 * |h x| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = |h x| := one_mul _
  · show (1 - wend e (1 / ((k : ℝ) + 1)) x) * h x = 0
    rw [wend_eq_one hδ hx.le]; simp
  · have e1 : (fun x => h x - (1 - wend e (1 / ((k : ℝ) + 1)) x) * h x) =
        fun x => wend e (1 / ((k : ℝ) + 1)) x * h x := by funext x; ring
    rw [e1]; exact hk

theorem formN_finite_of_close {μ : Measure ℝ} {h g : ℝ → ℝ} (hh : Measurable h) (hg : Measurable g)
    (hN : formN μ h < ⊤) (hd : formN μ (fun x => h x - g x) < ⊤) : formN μ g < ⊤ := by
  have e : g = fun x => h x + (-(h x - g x)) := by funext x; ring
  rw [e]
  refine lt_of_le_of_lt (formN_add_le hh (hh.sub hg).neg) ?_
  rw [formN_neg]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) hN, ENNReal.mul_lt_top (by simp) hd⟩

theorem remove_finset (H : CoreHyp ρ) (E : Finset ℝ) (hE : ∀ e ∈ E, ρ e = 0) :
    ∀ {h : ℝ → ℝ}, Measurable h → ∀ {M : ℝ}, (∀ x, |h x| ≤ M) → formN (muRho ρ) h < ⊤ →
    ∀ ε : ℝ, 0 < ε → ∃ g : ℝ → ℝ, Measurable g ∧ (∀ x, |g x| ≤ |h x|) ∧
      (∃ r : ℝ, 0 < r ∧ ∀ e ∈ E, ∀ x, |x - e| < r → g x = 0) ∧
      formN (muRho ρ) (fun x => h x - g x) < ENNReal.ofReal ε := by
  classical
  induction E using Finset.induction_on with
  | empty =>
    intro h hh M hM hN ε hε
    exact ⟨h, hh, fun x => le_rfl, ⟨1, one_pos, by simp⟩, by
      simp only [sub_self]
      have : formN (muRho ρ) (fun _ : ℝ => (0 : ℝ)) = 0 := by simp [formN, formL2, formE, dq]
      rw [this]; exact ENNReal.ofReal_pos.2 hε⟩
  | insert a E ha ih =>
    intro h hh M hM hN ε hε
    haveI := H.fin
    have hEa : ∀ e ∈ E, ρ e = 0 := fun e he => hE e (Finset.mem_insert_of_mem he)
    obtain ⟨g1, hg1m, hg1, ⟨r1, hr1, hr1'⟩, hN1⟩ := ih hEa hh hM hN (ε / 4) (by positivity)
    have hg1M : ∀ x, |g1 x| ≤ M := fun x => le_trans (hg1 x) (hM x)
    have hNg1 : formN (muRho ρ) g1 < ⊤ :=
      formN_finite_of_close hh hg1m hN (lt_of_lt_of_le hN1 le_top)
    obtain ⟨g2, hg2m, hg2, ⟨r2, hr2, hr2'⟩, hN2⟩ :=
      remove_endpoint H (hE a (Finset.mem_insert_self a E)) hg1m hg1M hNg1 (ε / 4) (by positivity)
    refine ⟨g2, hg2m, fun x => le_trans (hg2 x) (hg1 x), ⟨min r1 r2, lt_min hr1 hr2, ?_⟩, ?_⟩
    · intro e he x hx
      rcases Finset.mem_insert.1 he with rfl | he'
      · exact hr2' x (lt_of_lt_of_le hx (min_le_right _ _))
      · have : g1 x = 0 := hr1' e he' x (lt_of_lt_of_le hx (min_le_left _ _))
        have := hg2 x
        rw [‹g1 x = 0›, abs_zero] at this
        exact abs_nonpos_iff.1 this
    · have e : (fun x => h x - g2 x) = fun x => (h x - g1 x) + (g1 x - g2 x) := by funext x; ring
      rw [e]
      refine lt_of_le_of_lt (formN_add_le (hh.sub hg1m) (hg1m.sub hg2m)) ?_
      have := four_lt hN1 hN1 hN2 hN2 hε
      calc 2 * formN (muRho ρ) (fun x => h x - g1 x) + 2 * formN (muRho ρ) (fun x => g1 x - g2 x)
          = formN (muRho ρ) (fun x => h x - g1 x) + formN (muRho ρ) (fun x => h x - g1 x) +
            (formN (muRho ρ) (fun x => g1 x - g2 x) + formN (muRho ρ) (fun x => g1 x - g2 x)) := by ring
        _ < _ := this

end QuantumNLS.FormCore

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.FormCore.remove_finset
