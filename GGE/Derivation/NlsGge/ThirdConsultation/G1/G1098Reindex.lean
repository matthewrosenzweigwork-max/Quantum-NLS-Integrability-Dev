import NlsGge.GK38.Lib.HilbertValuedAnalytic

/- G1-098 SUPPORTING MODULE M3 (proof development, AUTHOR; not reviewed).
   Pro round 7-8 section 18, step 3 (index transfer for Hilbert-valued analyticity).
   Statement: a locally bounded map f from an open set U of a complex normed space into
   lp (fun _ : ℤ × Bool => ℂ) 2 whose coordinates x ↦ f x j are analytic on U is analytic on U.
   Route: an isometric reindexing of ℓ² along an equivalence σ : (ℤ × Bool) ≃ ℤ, then the scalar
   theorem NlsGge.GK38.Lib.analyticOnNhd_of_coords_of_locBdd, then the inverse reindexing.
   Hypotheses are exactly: U open, coordinatewise analyticity, local boundedness.
   No hypothesis assumes a conclusion. -/
set_option autoImplicit false

open Metric Set Filter Topology
open scoped ENNReal InnerProductSpace

namespace NlsGge.Atomic.G1098Reindex

noncomputable section

section Reindex

variable {α β : Type*}

/-- Summability of the reindexed rpow-norms of an ℓ² element. -/
theorem summable_rpow_reindex (σ : α ≃ β) (x : lp (fun _ : α => ℂ) 2) :
    Summable fun b : β => ‖x (σ.symm b)‖ ^ (ENNReal.toReal 2) := by
  have hs : Summable fun a : α => ‖x a‖ ^ (ENNReal.toReal 2) :=
    (memℓp_gen_iff (by norm_num)).mp (lp.memℓp x)
  exact (σ.symm.summable_iff).mpr hs

/-- The reindexed sequence `b ↦ x (σ.symm b)` is again in ℓ². -/
theorem memℓp_reindex (σ : α ≃ β) (x : lp (fun _ : α => ℂ) 2) :
    Memℓp (fun b : β => x (σ.symm b)) 2 :=
  memℓp_gen (summable_rpow_reindex σ x)

/-- Norm preservation of the reindexed element. -/
theorem norm_reindex_mk (σ : α ≃ β) (x : lp (fun _ : α => ℂ) 2) :
    ‖(⟨fun b => x (σ.symm b), memℓp_reindex σ x⟩ : lp (fun _ : β => ℂ) 2)‖ = ‖x‖ := by
  have hx := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) x
  have hy := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
    (⟨fun b => x (σ.symm b), memℓp_reindex σ x⟩ : lp (fun _ : β => ℂ) 2)
  simp only [ENNReal.toReal_ofNat] at hx hy
  have hsum : ∑' b : β, ‖x (σ.symm b)‖ ^ (2 : ℝ) = ∑' a : α, ‖x a‖ ^ (2 : ℝ) :=
    σ.symm.tsum_eq (fun a => ‖x a‖ ^ (2 : ℝ))
  have h2 : ‖(⟨fun b => x (σ.symm b), memℓp_reindex σ x⟩ : lp (fun _ : β => ℂ) 2)‖ ^ (2 : ℝ)
      = ‖x‖ ^ (2 : ℝ) := by
    rw [hy, hx]
    exact hsum
  simp only [Real.rpow_two] at h2
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- Reindexing of ℓ² along an equivalence. -/
def reindexLp (σ : α ≃ β) : lp (fun _ : α => ℂ) 2 →ₗᵢ[ℂ] lp (fun _ : β => ℂ) 2 where
  toFun x := ⟨fun b => x (σ.symm b), memℓp_reindex σ x⟩
  map_add' _ _ := lp.ext rfl
  map_smul' _ _ := lp.ext rfl
  norm_map' x := norm_reindex_mk σ x

theorem reindexLp_apply (σ : α ≃ β) (x : lp (fun _ : α => ℂ) 2) (b : β) :
    reindexLp σ x b = x (σ.symm b) :=
  rfl

theorem reindexLp_symm_comp (σ : α ≃ β) (x : lp (fun _ : α => ℂ) 2) :
    reindexLp σ.symm (reindexLp σ x) = x := by
  apply lp.ext
  funext a
  rw [reindexLp_apply, reindexLp_apply, Equiv.symm_symm, Equiv.symm_apply_apply]

theorem norm_reindexLp (σ : α ≃ β) (x : lp (fun _ : α => ℂ) 2) :
    ‖reindexLp σ x‖ = ‖x‖ :=
  (reindexLp σ).norm_map x

end Reindex

section Main

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Coordinatewise analytic and locally bounded maps into ℓ² over an arbitrary equivalent index
type are analytic: transport along the reindexing, apply the scalar theorem, transport back. -/
theorem analyticOnNhd_of_coords_of_locBdd_reindex {α : Type*} (σ : α ≃ ℤ)
    (f : E → lp (fun _ : α => ℂ) 2) {U : Set E} (hU : IsOpen U)
    (hc : ∀ a : α, AnalyticOnNhd ℂ (fun x => f x a) U)
    (hb : ∀ x ∈ U, ∃ r > 0, ∃ C : ℝ, ∀ y ∈ Metric.ball x r, ‖f y‖ ≤ C) :
    AnalyticOnNhd ℂ f U := by
  have hga : AnalyticOnNhd ℂ (fun x => reindexLp σ (f x)) U := by
    refine NlsGge.GK38.Lib.analyticOnNhd_of_coords_of_locBdd (fun x => reindexLp σ (f x)) hU ?_ ?_
    · intro m
      exact hc (σ.symm m)
    · intro x hx
      obtain ⟨r, hr, C, hC⟩ := hb x hx
      exact ⟨r, hr, C, fun y hy => by rw [norm_reindexLp]; exact hC y hy⟩
  intro x hx
  have h2 : AnalyticAt ℂ (fun y => reindexLp σ (f y)) x := hga x hx
  have h3 : AnalyticAt ℂ (fun z => reindexLp σ.symm z) (reindexLp σ (f x)) :=
    (reindexLp σ.symm).toContinuousLinearMap.analyticAt (reindexLp σ (f x))
  have h : AnalyticAt ℂ (fun y => reindexLp σ.symm (reindexLp σ (f y))) x := AnalyticAt.comp h3 h2
  simpa only [reindexLp_symm_comp] using h

/-- Locally bounded, coordinatewise analytic maps into `lp (fun _ : ℤ × Bool => ℂ) 2` are analytic.
Hypotheses: `U` open, each coordinate analytic on `U`, and local boundedness on `U`. -/
theorem analyticOnNhd_of_coords_of_locBdd_intBool (f : E → lp (fun _ : ℤ × Bool => ℂ) 2)
    {U : Set E} (hU : IsOpen U) (hc : ∀ j : ℤ × Bool, AnalyticOnNhd ℂ (fun x => f x j) U)
    (hb : ∀ x ∈ U, ∃ r > 0, ∃ C : ℝ, ∀ y ∈ Metric.ball x r, ‖f y‖ ≤ C) :
    AnalyticOnNhd ℂ f U := by
  obtain ⟨σ⟩ : Nonempty ((ℤ × Bool) ≃ ℤ) := nonempty_equiv_of_countable
  exact analyticOnNhd_of_coords_of_locBdd_reindex σ f hU hc hb

end Main

end

end NlsGge.Atomic.G1098Reindex

