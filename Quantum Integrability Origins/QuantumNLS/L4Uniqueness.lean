import QuantumNLS.LocalL4Contraction

/-!
# EXT-003, Route Y stage (v), part A: uniqueness in the whole `L⁴` Duhamel class and rebasing

Toward R-AEE17FD6 (`thm:root-L2-flow`, `ROOT_L2_extension.tex`): "Uniqueness in the `L⁴` Duhamel
class is the local uniqueness in the quoted input applied successively on subintervals."

Route Y deviates from Bourgain's `X^{0,b}` proof (Bourgain 1993, §4); the linear inputs are the
elementary estimates of LS1/LS2, DD1, SG1, DL4a/DL4b and LC1 (imported read-only).

Here, on `J = (α, β]` with `0 < β − α ≤ min(1, T_L)` and data time `a ∈ [α, β]`:
* `V_congr`: the Duhamel integral `∫_a^t U(t−s)F(s) ds` depends only on `F` on the oriented
  interval between `a` and `t`;
* `ind_small`: `L⁴` norms over short time slabs are uniformly small;
* **`duhamel_unique`**: two solutions in `L⁴(J × 𝕋_L)` of the cubic Duhamel equation with the same
  data are equal — no bound on their norms is assumed (successive short slabs, forward and
  backward from `a`);
* `isDuhamel_rebase`: a solution with data `f` at time `a` is a solution with data `u(b)` at any
  other time `b`, where `u(b)` is its continuous `L²` representative.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate BigOperators Topology ENNReal InnerProductSpace
open MeasureTheory Filter QuantumNLS.Fourier QuantumNLS.LocalWellPosedness QuantumNLS.L4Strichartz
  QuantumNLS.L4StrichartzL2 QuantumNLS.DuhamelDuality QuantumNLS.ShortTimeGain QuantumNLS.DuhamelL4
  QuantumNLS.DuhamelL4Limit QuantumNLS.LocalL4Contraction

namespace QuantumNLS.L4Uniqueness

attribute [local irreducible] QuantumNLS.L4StrichartzL2.evol

variable {L : ℝ} [Fact (0 < L)]

/-! ## 1. Linearity of `U(t)` -/

lemma evol_add (f g : HL L) (t : ℝ) : evol (f + g) t = evol f t + evol g t := by
  have h := evol_sub (f + g) g t
  rw [add_sub_cancel_right] at h
  rw [h, sub_add_cancel]

lemma evol_zero (t : ℝ) : evol (0 : HL L) t = 0 := by
  have h := evol_sub (0 : HL L) 0 t
  rw [sub_self, sub_self] at h
  exact h

lemma evol_smul (c : ℂ) (f : HL L) (t : ℝ) : evol (c • f) t = c • evol f t := by
  apply (fourierL2 L).injective
  rw [map_smul]
  refine lp.ext (funext fun n => ?_)
  rw [lp.coeFn_smul, Pi.smul_apply, fourierL2_evol, fourierL2_evol, DuhamelDuality.coef_smul]
  try simp only [smul_eq_mul]
  ring

/-! ## 2. Locality of the Duhamel integral -/

section Local

variable {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L)

/-- `∫_a^t U(t−s)F(s) ds` only depends on `F` on `(a,t]` (or `(t,a]`). -/
theorem V_congr (F G : Lp ℂ (4 / 3) (μJ (L := L) α β)) {a t : ℝ} (ha : α ≤ a) (ht : α ≤ t)
    (hFG : ∀ᵐ p ∂(μJ (L := L) α β), p.1 ∈ Set.uIoc a t → F p = G p) :
    V hαβ hlen F a t = V hαβ hlen G a t := by
  have hS : Sop hαβ hlen F a t = Sop hαβ hlen G a t := by
    refine ext_inner_left ℂ fun h => ?_
    rw [inner_Sop hαβ hlen F ha ht, inner_Sop hαβ hlen G ha ht]
    refine integral_congr_ae ?_
    filter_upwards [hFG] with p hp
    by_cases h1 : p ∈ Set.Ioc a t ×ˢ (Set.univ : Set (AddCircle L))
    · have hu : p.1 ∈ Set.uIoc a t := Set.Ioc_subset_uIoc h1.1
      have h2 : p ∉ Set.Ioc t a ×ˢ (Set.univ : Set (AddCircle L)) := fun h2 => by
        have := h1.1; have := h2.1; simp only [Set.mem_Ioc] at *; linarith
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h1, Set.indicator_of_notMem h2,
        Set.indicator_of_notMem h2, hp hu]
    · by_cases h2 : p ∈ Set.Ioc t a ×ˢ (Set.univ : Set (AddCircle L))
      · have hu : p.1 ∈ Set.uIoc a t := Set.Ioc_subset_uIoc' h2.1
        rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h1, Set.indicator_of_mem h2,
          Set.indicator_of_mem h2, hp hu]
      · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2,
          Set.indicator_of_notMem h2]
  rw [V, V, hS]

end Local

#print axioms V_congr

/-! ## 3. Short slabs carry small `L⁴` norm -/

lemma norm_ind_eq {α β : ℝ} (c d : ℝ) (f : Lp ℂ 4 (μJ (L := L) α β)) :
    ‖ind c d f‖ = (eLpNorm ((slab c d).indicator f) 4 (μJ α β)).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_ind c d f)]

lemma norm_ind_le {α β : ℝ} (c d : ℝ) (f : Lp ℂ 4 (μJ (L := L) α β)) : ‖ind c d f‖ ≤ ‖f‖ := by
  rw [norm_ind_eq, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp f).ne
    (eLpNorm_indicator_le _ (measurableSet_slab c d))

theorem ind_small {α β : ℝ} (u : Lp ℂ 4 (μJ (L := L) α β)) :
    ∀ ε > 0, ∃ δ > 0, ∀ c d : ℝ, c ≤ d → d - c < δ → ‖ind c d u‖ ≤ ε := by
  have hL : 0 < L := Fact.out
  intro ε hε
  obtain ⟨δE, hδE, hind⟩ := (Lp.memLp u).eLpNorm_indicator_le (by norm_num)
    (by norm_num : (4 : ℝ≥0∞) ≠ ⊤) (ε := ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.mp hδE
  have hr : 0 < r := ENNReal.ofReal_pos.mp hr1
  refine ⟨r / L, by positivity, fun c d hcd hlt => ?_⟩
  have hμ : μJ (L := L) α β (slab c d) ≤ δE := by
    have h1 : slab (L := L) c d ⊆ Set.uIoc c d ×ˢ Set.univ := fun p hp =>
      ⟨Set.Ioc_subset_uIoc hp.1, hp.2⟩
    refine (measure_mono h1).trans ((measure_cut_le (L := L) (α := α) (β := β) c d).trans ?_)
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hr2.le
    have := (lt_div_iff₀ hL).mp hlt
    rw [abs_of_nonneg (by linarith)]; linarith
  have hb := hind _ (measurableSet_slab c d) hμ
  rw [norm_ind_eq]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rwa [ENNReal.toReal_ofReal hε.le] at this

/-! ## 4. Slices of a cut -/

lemma ind_slice {α β : ℝ} (c d : ℝ) (f : Lp ℂ 4 (μJ (L := L) α β)) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc α β)), ∀ᵐ x ∂(volume : Measure (AddCircle L)),
      ind c d f (t, x) = if t ∈ Set.Ioc c d then f (t, x) else 0 := by
  filter_upwards [Measure.ae_ae_of_ae_prod (coeFn_ind c d f)] with t ht
  filter_upwards [ht] with x hx
  rw [hx]
  by_cases h : t ∈ Set.Ioc c d
  · rw [Set.indicator_of_mem (show (t, x) ∈ slab (L := L) c d from ⟨h, trivial⟩)]
    simp only [h, ↓reduceIte]
  · rw [Set.indicator_of_notMem (show (t, x) ∉ slab (L := L) c d from fun h' => h h'.1)]
    simp only [h, ↓reduceIte]

lemma ae_eq_on_of_ind_eq {α β : ℝ} {c d : ℝ} {u v : Lp ℂ 4 (μJ (L := L) α β)}
    (h : ind c d u = ind c d v) :
    ∀ᵐ p ∂(μJ (L := L) α β), p.1 ∈ Set.Ioc c d → u p = v p := by
  filter_upwards [coeFn_ind c d u, coeFn_ind c d v] with p h1 h2 hp
  have hs : p ∈ slab (L := L) c d := ⟨hp, trivial⟩
  have e : (ind c d u : ℝ × AddCircle L → ℂ) p = (ind c d v : ℝ × AddCircle L → ℂ) p := by rw [h]
  rw [h1, h2, Set.indicator_of_mem hs, Set.indicator_of_mem hs] at e
  exact e

/-! ## 5. One slab step and uniqueness -/

section Unique

variable {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L) (h1 : β - α ≤ 1) (hlt : α < β)

lemma diff_slice (c : ℂ) (a : ℝ) (f : HL L) {u v : Lp ℂ 4 (μJ (L := L) α β)}
    (hu : IsDuhamel hαβ hlen c a f u) (hv : IsDuhamel hαβ hlen c a f v) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc α β)), ∀ᵐ x ∂(volume : Measure (AddCircle L)),
      u (t, x) - v (t, x) = (c • V hαβ hlen (cub u - cub v) a t : HL L) x := by
  filter_upwards [hu, hv] with t e1 e2
  have hE : (evol f (t - a) + c • V hαβ hlen (cub u) a t) -
      (evol f (t - a) + c • V hαβ hlen (cub v) a t) = c • V hαβ hlen (cub u - cub v) a t := by
    rw [V_sub, smul_sub]; abel
  filter_upwards [e1, e2, Lp.coeFn_sub (evol f (t - a) + c • V hαβ hlen (cub u) a t)
    (evol f (t - a) + c • V hαβ hlen (cub v) a t)] with x x1 x2 x3
  rw [x1, x2, ← Pi.sub_apply, ← x3, hE]

include h1 hlt in
/-- **One slab**: if `u = v` a.e. on a set `Z` containing the part of every oriented interval
`(a, t]`, `t ∈ K = (e₁, e₂]`, outside `K`, and the cuts of `u`, `v` to `K` are small, then
`u = v` a.e. on `K`. -/
theorem slab_step (c : ℂ) (a : ℝ) (ha : α ≤ a) (f : HL L) {u v : Lp ℂ 4 (μJ (L := L) α β)}
    (hu : IsDuhamel hαβ hlen c a f u) (hv : IsDuhamel hαβ hlen c a f v) {e₁ e₂ ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hKu : ‖ind e₁ e₂ u‖ ≤ ρ) (hKv : ‖ind e₁ e₂ v‖ ≤ ρ)
    (hρ : ‖c‖ * (c0 L * (β - α) ^ (16⁻¹ : ℝ)) * (3 * ρ ^ 2) ≤ 1 / 2) (Z : Set ℝ)
    (hZ : ∀ t ∈ Set.Ioc e₁ e₂, ∀ s ∈ Set.uIoc a t, s ∉ Set.Ioc e₁ e₂ → s ∈ Z)
    (hzero : ∀ᵐ p ∂(μJ (L := L) α β), p.1 ∈ Z → u p = v p) :
    ind e₁ e₂ u = ind e₁ e₂ v := by
  set iu := ind e₁ e₂ u
  set iv := ind e₁ e₂ v
  set G : Lp ℂ (4 / 3) (μJ (L := L) α β) := cub iu - cub iv with hG
  -- the cut difference is a cut Duhamel term
  have hDG : ∀ t ∈ Set.Ioc e₁ e₂, α ≤ t →
      V hαβ hlen (cub u - cub v) a t = V hαβ hlen G a t := by
    intro t htK ht
    refine V_congr hαβ hlen _ _ ha ht ?_
    filter_upwards [hzero, Lp.coeFn_sub (cub u) (cub v), Lp.coeFn_sub (cub iu) (cub iv),
      coeFn_cub u, coeFn_cub v, coeFn_cub iu, coeFn_cub iv, coeFn_ind e₁ e₂ u,
      coeFn_ind e₁ e₂ v] with p z0 z1 z2 z3 z4 z5 z6 z7 z8 hp
    rw [z1, z2, Pi.sub_apply, Pi.sub_apply, z3, z4, z5, z6]
    simp only [cubF]
    rw [z7, z8]
    by_cases hK : p ∈ slab (L := L) e₁ e₂
    · rw [Set.indicator_of_mem hK, Set.indicator_of_mem hK]
    · rw [Set.indicator_of_notMem hK, Set.indicator_of_notMem hK,
        z0 (hZ t htK p.1 hp fun h => hK ⟨h, trivial⟩)]
      simp
  -- slices
  have hslice : iu - iv = ind e₁ e₂ (c • Vst hαβ hlen G a) := by
    refine Lp_eq_of_slices _ _ ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ind_slice e₁ e₂ u, ind_slice e₁ e₂ v,
      ind_slice e₁ e₂ (c • Vst hαβ hlen G a), diff_slice hαβ hlen c a f hu hv,
      Vst_slice hαβ hlen h1 G a, Measure.ae_ae_of_ae_prod (Lp.coeFn_sub iu iv),
      Measure.ae_ae_of_ae_prod (Lp.coeFn_smul c (Vst hαβ hlen G a))]
      with t ht s1 s2 s3 s4 s5 s6 s7
    filter_upwards [s1, s2, s3, s4, s5, s6, s7,
      Lp.coeFn_smul c (V hαβ hlen G a t)] with x x1 x2 x3 x4 x5 x6 x7 x8
    show (iu - iv : Lp ℂ 4 (μJ (L := L) α β)) (t, x) = _
    rw [x6, Pi.sub_apply, x1, x2, x3]
    by_cases hK : t ∈ Set.Ioc e₁ e₂
    · simp only [hK, ↓reduceIte]
      rw [x4, hDG t hK ht.1.le, x8, x7, Pi.smul_apply, Pi.smul_apply, x5]
    · simp only [hK, ↓reduceIte, sub_zero]
  -- the estimate
  have hT : 0 ≤ c0 L * (β - α) ^ (16⁻¹ : ℝ) :=
    mul_nonneg c0_nonneg (Real.rpow_nonneg (by linarith) _)
  have hd := norm_nonneg (iu - iv)
  have hest : ‖iu - iv‖ ≤ ‖c‖ * (c0 L * (β - α) ^ (16⁻¹ : ℝ)) * (3 * ρ ^ 2) * ‖iu - iv‖ := by
    calc ‖iu - iv‖ = ‖ind e₁ e₂ (c • Vst hαβ hlen G a)‖ := by rw [hslice]
      _ ≤ ‖c • Vst hαβ hlen G a‖ := norm_ind_le _ _ _
      _ = ‖c‖ * ‖Vst hαβ hlen G a‖ := norm_smul _ _
      _ ≤ ‖c‖ * (c0 L * (β - α) ^ (16⁻¹ : ℝ) * ‖G‖) :=
          mul_le_mul_of_nonneg_left (norm_Vst_le' hαβ hlen h1 hlt G a) (norm_nonneg _)
      _ ≤ ‖c‖ * (c0 L * (β - α) ^ (16⁻¹ : ℝ) *
            ((‖iu‖ * ‖iu‖ + ‖iu‖ * ‖iv‖ + ‖iv‖ * ‖iv‖) * ‖iu - iv‖)) := by
          gcongr
          exact norm_cub_sub_le iu iv
      _ ≤ ‖c‖ * (c0 L * (β - α) ^ (16⁻¹ : ℝ) * ((3 * ρ ^ 2) * ‖iu - iv‖)) := by
          gcongr
          have e1 : ‖iu‖ * ‖iu‖ ≤ ρ * ρ := mul_le_mul hKu hKu (norm_nonneg _) hρ0
          have e2 : ‖iu‖ * ‖iv‖ ≤ ρ * ρ := mul_le_mul hKu hKv (norm_nonneg _) hρ0
          have e3 : ‖iv‖ * ‖iv‖ ≤ ρ * ρ := mul_le_mul hKv hKv (norm_nonneg _) hρ0
          nlinarith
      _ = _ := by ring
  have h0 : ‖iu - iv‖ ≤ 1 / 2 * ‖iu - iv‖ :=
    hest.trans (mul_le_mul_of_nonneg_right hρ hd)
  have : ‖iu - iv‖ = 0 := by linarith
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

include h1 hlt in
/-- **Uniqueness in the whole `L⁴` Duhamel class.** On `J = (α, β]` with
`0 < β − α ≤ min(1, T_L)`, two solutions `u, v ∈ L⁴(J × 𝕋_L)` of the cubic Duhamel equation with
the same coefficient, the same data `f` and the same data time `a ∈ [α, β]` coincide. No bound on
`‖u‖₄`, `‖v‖₄` is assumed. -/
theorem duhamel_unique (c : ℂ) (a : ℝ) (ha : a ∈ Set.Icc α β) (f : HL L)
    {u v : Lp ℂ 4 (μJ (L := L) α β)}
    (hu : IsDuhamel hαβ hlen c a f u) (hv : IsDuhamel hαβ hlen c a f v) : u = v := by
  set M := ‖c‖ * (c0 L * (β - α) ^ (16⁻¹ : ℝ)) with hM
  have hM0 : 0 ≤ M := mul_nonneg (norm_nonneg _)
    (mul_nonneg c0_nonneg (Real.rpow_nonneg (by linarith) _))
  set ρ : ℝ := 1 / (6 * (M + 1)) with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 := by
    rw [hρdef, div_le_one (by positivity)]; linarith
  have hρ : M * (3 * ρ ^ 2) ≤ 1 / 2 := by
    have hρM : ρ * (6 * (M + 1)) = 1 := by
      rw [hρdef]; field_simp
    have : M * (3 * ρ ^ 2) ≤ M * (3 * ρ) := by
      have : ρ ^ 2 ≤ ρ := by nlinarith
      gcongr
    nlinarith
  obtain ⟨δu, hδu, hu'⟩ := ind_small u ρ hρ0
  obtain ⟨δv, hδv, hv'⟩ := ind_small v ρ hρ0
  set δ := min δu δv / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδu' : δ < δu := by
    have := min_le_left δu δv; rw [hδ]; linarith
  have hδv' : δ < δv := by
    have := min_le_right δu δv; rw [hδ]; linarith
  have hsmall : ∀ e : ℝ, ‖ind e (e + δ) u‖ ≤ ρ ∧ ‖ind e (e + δ) v‖ ≤ ρ := fun e =>
    ⟨hu' e (e + δ) (by linarith) (by linarith), hv' e (e + δ) (by linarith) (by linarith)⟩
  -- forward slabs
  have hfwd : ∀ k : ℕ, ∀ᵐ p ∂(μJ (L := L) α β), p.1 ∈ Set.Ioc a (a + k * δ) → u p = v p := by
    intro k
    induction k with
    | zero =>
      refine Eventually.of_forall fun p hp => ?_
      simp only [CharP.cast_eq_zero, zero_mul, add_zero, Set.mem_Ioc] at hp
      linarith [hp.1, hp.2]
    | succ k ih =>
      have hstep := slab_step hαβ hlen h1 hlt c a ha.1 f hu hv hρ0.le
        (hsmall (a + k * δ)).1 (hsmall (a + k * δ)).2 hρ (Set.Ioc a (a + k * δ))
        (fun t ht s hs hsK => by
          have hat : a ≤ t := by
            have := ht.1; have : 0 ≤ (k : ℝ) * δ := by positivity
            linarith
          rw [Set.uIoc_of_le hat] at hs
          refine ⟨hs.1, ?_⟩
          by_contra hc
          push Not at hc
          exact hsK ⟨hc, hs.2.trans ht.2⟩) ih
      have hK := ae_eq_on_of_ind_eq hstep
      have e : a + ((k + 1 : ℕ) : ℝ) * δ = a + k * δ + δ := by push_cast; ring
      filter_upwards [ih, hK] with p p1 p2 hp
      rw [e] at hp
      by_cases hpk : p.1 ≤ a + k * δ
      · exact p1 ⟨hp.1, hpk⟩
      · push Not at hpk
        exact p2 ⟨hpk, hp.2⟩
  -- backward slabs
  have hbwd : ∀ k : ℕ, ∀ᵐ p ∂(μJ (L := L) α β), p.1 ∈ Set.Ioc (a - k * δ) a → u p = v p := by
    intro k
    induction k with
    | zero =>
      refine Eventually.of_forall fun p hp => ?_
      simp only [CharP.cast_eq_zero, zero_mul, sub_zero, Set.mem_Ioc] at hp
      linarith [hp.1, hp.2]
    | succ k ih =>
      have e1 : a - (k + 1) * δ + δ = a - k * δ := by ring
      have hkδ : 0 ≤ (k : ℝ) * δ := by positivity
      have hstep := slab_step hαβ hlen h1 hlt c a ha.1 f hu hv hρ0.le
        (hsmall (a - (k + 1) * δ)).1 (hsmall (a - (k + 1) * δ)).2 hρ (Set.Ioc (a - k * δ) a)
        (fun t ht s hs hsK => by
          rw [e1] at ht hsK
          have hta : t ≤ a := by
            have := ht.2; linarith
          rw [Set.uIoc_of_ge hta] at hs
          refine ⟨?_, hs.2⟩
          by_contra hc
          push Not at hc
          exact hsK ⟨by linarith [ht.1, hs.1], hc⟩) ih
      rw [e1] at hstep
      have hK := ae_eq_on_of_ind_eq hstep
      have e : a - ((k + 1 : ℕ) : ℝ) * δ = a - (k + 1) * δ := by push_cast; ring
      filter_upwards [ih, hK] with p p1 p2 hp
      rw [e] at hp
      by_cases hpk : a - k * δ < p.1
      · exact p1 ⟨hpk, hp.2⟩
      · push Not at hpk
        exact p2 ⟨hp.1, hpk⟩
  obtain ⟨k, hk⟩ := exists_nat_gt ((β - α) / δ)
  have hkδ : β - α < k * δ := by rwa [div_lt_iff₀ hδ0] at hk
  refine Lp.ext ?_
  have hJ : ∀ᵐ p ∂(μJ (L := L) α β), p.1 ∈ Set.Ioc α β := by
    have h := (Measure.ae_prod_mem_iff_ae_ae_mem (μ := volume.restrict (Set.Ioc α β))
      (ν := (volume : Measure (AddCircle L))) (measurableSet_Ioc.prod MeasurableSet.univ)).2 (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact Eventually.of_forall fun _ => ⟨ht, trivial⟩)
    exact h.mono fun p hp => hp.1
  filter_upwards [hJ, hfwd k, hbwd k] with p hp p1 p2
  by_cases hpa : a < p.1
  · exact p1 ⟨hpa, by linarith [hp.2, ha.1]⟩
  · push Not at hpa
    exact p2 ⟨by linarith [hp.1, ha.2], hpa⟩

end Unique

#print axioms slab_step
#print axioms duhamel_unique

/-! ## 6. Rebasing the data time -/

section Rebase

variable {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L)

lemma V_rebase (F : Lp ℂ (4 / 3) (μJ (L := L) α β)) (a b t : ℝ) :
    V hαβ hlen F a t = evol (V hαβ hlen F a b) (t - b) + V hαβ hlen F b t := by
  rw [V, V, V, evol_evol, sub_add_cancel, Sop, Sop, Sop, ← evol_add]
  congr 1
  abel

lemma V_self (F : Lp ℂ (4 / 3) (μJ (L := L) α β)) (a : ℝ) : V hαβ hlen F a a = 0 := by
  rw [V, Sop, sub_self, evol_zero]

/-- The curve at its own data time is the datum. -/
lemma Dcurve_self (c : ℂ) (a : ℝ) (f : HL L) (u : Lp ℂ 4 (μJ (L := L) α β)) :
    Dcurve hαβ hlen c a f u a = f := by
  rw [Dcurve, V_self, smul_zero, add_zero, sub_self]
  apply (fourierL2 L).injective
  refine lp.ext (funext fun n => ?_)
  rw [fourierL2_evol, phase_zero, one_mul]

/-- **Rebasing**: the Duhamel curve with data `f` at `a` is the Duhamel curve with data `u(b)`
at `b`. -/
theorem Dcurve_rebase (c : ℂ) (a b : ℝ) (f : HL L) (u : Lp ℂ 4 (μJ (L := L) α β)) (t : ℝ) :
    Dcurve hαβ hlen c a f u t =
      Dcurve hαβ hlen c b (Dcurve hαβ hlen c a f u b) u t := by
  rw [Dcurve, Dcurve, Dcurve, evol_add, evol_smul, evol_evol, V_rebase hαβ hlen _ a b t,
    smul_add, show t - b + (b - a) = t - a by ring]
  abel

theorem isDuhamel_rebase (c : ℂ) (a b : ℝ) (f : HL L) {u : Lp ℂ 4 (μJ (L := L) α β)}
    (hu : IsDuhamel hαβ hlen c a f u) :
    IsDuhamel hαβ hlen c b (Dcurve hαβ hlen c a f u b) u := by
  have e : ∀ t, (evol (Dcurve hαβ hlen c a f u b) (t - b) + c • V hαβ hlen (cub u) b t : HL L) =
      evol f (t - a) + c • V hαβ hlen (cub u) a t := fun t =>
    (Dcurve_rebase hαβ hlen c a b f u t).symm
  filter_upwards [hu] with t ht
  rw [e t]
  exact ht

end Rebase

#print axioms Dcurve_rebase
#print axioms isDuhamel_rebase

end QuantumNLS.L4Uniqueness
