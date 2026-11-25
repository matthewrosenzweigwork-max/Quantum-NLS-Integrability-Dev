import NlsGge.Composition.Model

/-!
# W03.08 (generic part): the composition map on the model and power-series transfer

Source: `paper/v2.tex`, lines 1443 and 1475-1478.

* `rangeSet w O = {g | ∀ θ, synth w g θ ∈ O}` and its openness;
* `compMap hw F g` : the model element of `F ∘ synth w g` (zero if that is not in `A_w`);
* `hasFPowerSeriesOnBall_compMap` : if a formal series `P` on the model with geometric bounds
  reproduces `F (synth w (p + r) θ)` pointwise for `‖r‖ < R`, then `compMap hw F` has `P` as a
  power series on the ball of radius `R` around `p`.
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

/-- Model elements whose synthesized function takes values in `O`. -/
def rangeSet (w : ℤ → ℝ) (O : Set X) : Set (Model X) := {g | ∀ θ, synth w g θ ∈ O}

/-- The composition map transported to the model: the model element of `F ∘ synth w g`
whenever this function lies in `A_w(Y)`, and `0` otherwise. -/
def compMap (hw : AdmissibleWeight w) (F : X → Y) (g : Model X) : Model Y := by
  classical
  exact if h : MemAw w (F ∘ synth w g) then toModel hw h else 0

theorem compMap_eq_of_synth (hw : AdmissibleWeight w) {F : X → Y} {g : Model X} {G : Model Y}
    (h : F ∘ synth w g = synth w G) : compMap hw F g = G := by
  classical
  have hm : MemAw w (F ∘ synth w g) := h ▸ memAw_synth hw G
  unfold compMap
  rw [dif_pos hm]
  apply synth_injective hw
  rw [synth_toModel, h]

theorem synth_compMap (hw : AdmissibleWeight w) {F : X → Y} {g : Model X}
    (hm : MemAw w (F ∘ synth w g)) : synth w (compMap hw F g) = F ∘ synth w g := by
  classical
  unfold compMap
  rw [dif_pos hm, synth_toModel]

theorem isCompact_range_synth (hw : AdmissibleWeight w) (g : Model X) :
    IsCompact (Set.range (synth w g)) :=
  isCompact_range (continuous_synth hw g)

/-- Distance of synthesized functions: `‖synth g θ - synth h θ‖ ≤ S_w ‖g - h‖`. -/
theorem norm_synth_sub_le (hw : AdmissibleWeight w) (g h : Model X) (θ : AddCircle (1 : ℝ)) :
    ‖synth w g θ - synth w h θ‖ ≤ supConst w * ‖g - h‖ := by
  have : synth w g θ - synth w h θ = synth w (g - h) θ := by
    have e := synth_add hw (g - h) h θ
    rw [sub_add_cancel] at e
    rw [e]; abel
  rw [this]; exact norm_synth_le hw _ θ

/-- Model elements close to `g` have synthesized values in the thickening of the range of `g`. -/
theorem synth_mem_thickening (hw : AdmissibleWeight w) {g h : Model X} {δ : ℝ}
    (hgh : supConst w * ‖h - g‖ < δ) (θ : AddCircle (1 : ℝ)) :
    synth w h θ ∈ Metric.thickening δ (Set.range (synth w g)) := by
  rw [Metric.mem_thickening_iff]
  exact ⟨synth w g θ, ⟨θ, rfl⟩, by
    rw [dist_eq_norm]; exact (norm_synth_sub_le hw h g θ).trans_lt hgh⟩

/-- `rangeSet w O` is open for open `O`. -/
theorem isOpen_rangeSet (hw : AdmissibleWeight w) {O : Set X} (hO : IsOpen O) :
    IsOpen (rangeSet w O) := by
  rw [Metric.isOpen_iff]
  intro g hg
  have hK := isCompact_range_synth hw g
  have hKO : Set.range (synth w g) ⊆ O := by rintro _ ⟨θ, rfl⟩; exact hg θ
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_thickening_subset_open hO hKO
  refine ⟨δ / (supConst w + 1), div_pos hδ (by linarith [supConst_nonneg w]), fun h hh θ => ?_⟩
  apply hsub
  apply synth_mem_thickening hw
  rw [Metric.mem_ball, dist_eq_norm] at hh
  have hS := supConst_nonneg w
  calc supConst w * ‖h - g‖ ≤ supConst w * (δ / (supConst w + 1)) := by gcongr
    _ < δ := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
      nlinarith

/-- Power-series transfer: pointwise expansions plus geometric bounds give a power series of
`compMap` in the model. -/
theorem hasFPowerSeriesOnBall_compMap (hw : AdmissibleWeight w) (F : X → Y) (p : Model X)
    (P : FormalMultilinearSeries ℝ (Model X) (Model Y)) {A q R : ℝ} (hA : 0 ≤ A) (hq : 0 ≤ q)
    (hR : 0 < R) (hqR : q * R ≤ 1) (hP : ∀ k, ‖P k‖ ≤ A * q ^ k)
    (hpt : ∀ r : Model X, ‖r‖ < R → ∀ θ : AddCircle (1 : ℝ),
      HasSum (fun k => synth w (P k (fun _ => r)) θ) (F (synth w (p + r) θ))) :
    HasFPowerSeriesOnBall (compMap hw F) P p (ENNReal.ofReal R) := by
  refine ⟨?_, by simpa using hR, fun {r} hr => ?_⟩
  · refine ENNReal.le_of_forall_nnreal_lt fun t ht => ?_
    have htR : (t : ℝ) < R := by
      rw [← ENNReal.ofReal_coe_nnreal] at ht
      exact (ENNReal.ofReal_lt_ofReal_iff hR).mp ht
    refine P.le_radius_of_bound A fun k => ?_
    calc ‖P k‖ * (t : ℝ) ^ k ≤ A * q ^ k * (t : ℝ) ^ k := by gcongr; exact hP k
      _ = A * (q * t) ^ k := by ring
      _ ≤ A * 1 ^ k := by
          gcongr
          nlinarith [t.coe_nonneg]
      _ = A := by simp
  · have hr' : ‖r‖ < R := by
      rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm,
        ENNReal.ofReal_lt_ofReal_iff hR] at hr
      exact hr
    -- norm summability of the series
    have hsum : Summable fun k => ‖P k (fun _ => r)‖ := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
        ((summable_geometric_of_lt_one (by positivity) (?_ : q * ‖r‖ < 1)).mul_left A)
      · calc ‖P k (fun _ => r)‖ ≤ ‖P k‖ * ∏ _i : Fin k, ‖r‖ := (P k).le_opNorm _
          _ ≤ A * q ^ k * ‖r‖ ^ k := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
              gcongr; exact hP k
          _ = A * (q * ‖r‖) ^ k := by ring
      · rcases eq_or_lt_of_le hq with h0 | h0
        · rw [← h0]; simp
        · calc q * ‖r‖ < q * R := mul_lt_mul_of_pos_left hr' h0
            _ ≤ 1 := hqR
    obtain ⟨G, hG⟩ := hsum.of_norm
    have hfun : F ∘ synth w (p + r) = synth w G := by
      funext θ
      have h1 := (evalCLM hw θ).hasSum hG
      simp only [evalCLM_apply] at h1
      exact (hpt r hr' θ).unique h1
    rw [compMap_eq_of_synth hw hfun]
    exact hG

/-- Under the same hypotheses, `F ∘ synth w (p + r)` lies in `A_w(Y)` for `‖r‖ < R`. -/
theorem memAw_comp_of_expansion (hw : AdmissibleWeight w) (F : X → Y) (p : Model X)
    (P : FormalMultilinearSeries ℝ (Model X) (Model Y)) {A q R : ℝ} (hA : 0 ≤ A) (hq : 0 ≤ q)
    (hR : 0 < R) (hqR : q * R ≤ 1) (hP : ∀ k, ‖P k‖ ≤ A * q ^ k)
    (hpt : ∀ r : Model X, ‖r‖ < R → ∀ θ : AddCircle (1 : ℝ),
      HasSum (fun k => synth w (P k (fun _ => r)) θ) (F (synth w (p + r) θ)))
    {r : Model X} (hr : ‖r‖ < R) : MemAw w (F ∘ synth w (p + r)) := by
  have hps := hasFPowerSeriesOnBall_compMap hw F p P hA hq hR hqR hP hpt
  have hrm : r ∈ Metric.eball (0 : Model X) (ENNReal.ofReal R) := by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff hR]
    exact hr
  have hG := hps.hasSum hrm
  have hfun : F ∘ synth w (p + r) = synth w (compMap hw F (p + r)) := by
    funext θ
    have h1 := (evalCLM hw θ).hasSum hG
    simp only [evalCLM_apply] at h1
    exact (hpt r hr θ).unique h1
  rw [hfun]
  exact memAw_synth hw _

end NlsGge.Composition
