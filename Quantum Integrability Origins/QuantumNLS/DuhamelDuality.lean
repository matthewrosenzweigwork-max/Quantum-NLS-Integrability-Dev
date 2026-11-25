import QuantumNLS.L4StrichartzL2

/-!
# `lem:root-L4-duality` (R-02871DC6), second half: the duality Duhamel map `L^{4/3} → C_t L²`

Source: `source/chapters/foundations/ROOT_L2_extension.tex`, lines 20-71: eq. `root-L4-dual` and the
second paragraph of the proof ("For a measurable subinterval `K ⊂ J`, define `S_K F ∈ L²` by
`⟨h, S_K F⟩ = ∫_K ∫ conj(U(s)h(x)) F(s,x) dx ds` ... Hölder ... the Hilbert-space representation
theorem ... `V(t) = U(t) S_{[a,t]} F`, negative oriented integral when `t < a` ... absolute continuity
... strong continuity of `U` ... unitarity").

Imports the frozen LS2 (`L4StrichartzL2`, `66db0da6…`) and LS1 (`L4Strichartz`, `546d7e5b…`)
read-only. The free solution `U(·)h ∈ L⁴(J × 𝕋_L)` is LS2's `L⁴` limit (`freeL4`), whose slices are
`U(s)h` for a.e. `s` (LS2 `slice_eq`); `U(t) = evol · t` (LS2).

Proved here, for `J = (α, β]` with `β − α ≤ T_L`, `F ∈ L^{4/3}(J × 𝕋_L)` and any base point `a`:
* `S_G` (`rep`): the Riesz representative of `h ↦ ∫ (U(·)h) · conj G`, with
  `⟨h, S_G⟩ = ∫ conj(U(s)h(x)) G(s,x)` and `‖S_G‖ ≤ C_L ‖G‖_{4/3}` (Hölder + LS2);
* `V(t) = U(t)(S_{(a,t]}F − S_{(t,a]}F)` (the oriented integral);
* `‖V(t)‖₂ ≤ C_L ‖F‖_{L^{4/3}}` for every `t` (unitarity of `U(t)`);
* `t ↦ V(t)` is continuous into `L²` (absolute continuity of the `L^{4/3}` integral and strong
  continuity of `U`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate BigOperators Topology ENNReal InnerProductSpace
open MeasureTheory Filter QuantumNLS.Fourier QuantumNLS.LocalWellPosedness QuantumNLS.L4Strichartz
  QuantumNLS.L4StrichartzL2

namespace QuantumNLS.DuhamelDuality

variable {L : ℝ} [Fact (0 < L)]

/-- `L²(𝕋_L)`. -/
abbrev HL (L : ℝ) [Fact (0 < L)] := Lp ℂ 2 (volume : Measure (AddCircle L))

instance : Fact (1 ≤ (4 / 3 : ℝ≥0∞)) := ⟨by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]; norm_num⟩

instance : ENNReal.HolderTriple 4 (4 / 3) 1 := ⟨by
  rw [ENNReal.inv_div (Or.inl (by norm_num)) (Or.inl (by norm_num)), inv_one, ENNReal.div_eq_inv_mul,
    show (4 : ℝ≥0∞)⁻¹ + 4⁻¹ * 3 = 4⁻¹ * 4 by ring]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩

/-- The constant `C_L = (2T_L/L)^{1/4}`. -/
def CL (L : ℝ) : ℝ := (2 * TL L / L) ^ (4⁻¹ : ℝ)

lemma CL_nonneg : 0 ≤ CL L := Real.rpow_nonneg (by
  have hL : 0 < L := Fact.out
  have := TL_pos (L := L); positivity) _

/-! ## 1. Linearity of the truncated free solutions and of the `L⁴` free solution -/

lemma coef_add (f g : HL L) (n : ℤ) : coef (f + g) n = coef f n + coef g n := by
  simp only [coef, map_add, lp.coeFn_add, Pi.add_apply]

lemma coef_smul (c : ℂ) (f : HL L) (n : ℤ) : coef (c • f) n = c * coef f n := by
  simp only [coef, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]

lemma solP_add (S : Finset ℤ) (f g : HL L) :
    solP (L := L) S (coef (f + g)) = solP S (coef f) + solP S (coef g) := by
  funext p
  simp only [solP, freeSol, Pi.add_apply, coef_add, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

lemma solP_smul (S : Finset ℤ) (c : ℂ) (f : HL L) :
    solP (L := L) S (coef (c • f)) = c • solP S (coef f) := by
  funext p
  simp only [solP, freeSol, Pi.smul_apply, smul_eq_mul, coef_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by ring

lemma wN_add (f g : HL L) (α β : ℝ) (N : ℕ) : wN (f + g) α β N = wN f α β N + wN g α β N := by
  rw [wN, wN, wN, ← MemLp.toLp_add]
  exact (MemLp.toLp_eq_toLp_iff _ _).mpr
    (Eventually.of_forall fun p => congrFun (solP_add (win N) f g) p)

lemma wN_smul (c : ℂ) (f : HL L) (α β : ℝ) (N : ℕ) : wN (c • f) α β N = c • wN f α β N := by
  rw [wN, wN, ← MemLp.toLp_const_smul]
  exact (MemLp.toLp_eq_toLp_iff _ _).mpr
    (Eventually.of_forall fun p => congrFun (solP_smul (win N) c f) p)

/-- `U(·)h ∈ L⁴(J × 𝕋_L)`: the `L⁴` limit of the Fourier truncations (LS2). -/
def freeL4 (α β : ℝ) (h : HL L) : Lp ℂ 4 (μJ (L := L) α β) := limUnder atTop (wN h α β)

section Interval

variable {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L)
include hαβ hlen

lemma tendsto_freeL4 (h : HL L) : Tendsto (wN h α β) atTop (𝓝 (freeL4 α β h)) := by
  obtain ⟨u, hu, -⟩ := L4_free h hαβ hlen
  exact tendsto_nhds_limUnder ⟨u, hu⟩

lemma norm_freeL4_le (h : HL L) : ‖freeL4 α β h‖ ≤ CL L * ‖h‖ := by
  obtain ⟨u, hu, -, h1, -⟩ := L4_free h hαβ hlen
  rw [tendsto_nhds_unique (tendsto_freeL4 hαβ hlen h) hu]
  exact h1

lemma freeL4_add (f g : HL L) : freeL4 α β (f + g) = freeL4 α β f + freeL4 α β g := by
  have h1 := tendsto_freeL4 hαβ hlen (f + g)
  have h2 := (tendsto_freeL4 hαβ hlen f).add (tendsto_freeL4 hαβ hlen g)
  exact tendsto_nhds_unique (h1.congr fun N => wN_add f g α β N) h2

lemma freeL4_smul (c : ℂ) (f : HL L) : freeL4 α β (c • f) = c • freeL4 α β f := by
  have h1 := tendsto_freeL4 hαβ hlen (c • f)
  have h2 := (tendsto_freeL4 hαβ hlen f).const_smul c
  exact tendsto_nhds_unique (h1.congr fun N => wN_smul c f α β N) h2

/-- The slices of `U(·)h` are `U(s)h` (LS2). -/
lemma freeL4_slice (h : HL L) : ∀ᵐ s ∂(volume.restrict (Set.Ioc α β)),
    (fun x => freeL4 α β h (s, x)) =ᵐ[volume] (evol h s : AddCircle L → ℂ) :=
  slice_eq h _ (tendsto_freeL4 hαβ hlen h)

end Interval

#print axioms freeL4_add
#print axioms norm_freeL4_le

/-! ## 2. Hölder and the functional `h ↦ ∫ (U(·)h) conj G` -/

lemma memLp_conj {α β : ℝ} {G : ℝ × AddCircle L → ℂ} (hG : MemLp G (4 / 3) (μJ α β)) :
    MemLp (fun p => conj (G p)) (4 / 3) (μJ α β) :=
  hG.congr_norm (Complex.continuous_conj.comp_aestronglyMeasurable hG.aestronglyMeasurable)
    (Eventually.of_forall fun _ => (Complex.norm_conj _).symm)

/-- Hölder `L⁴ × L^{4/3} → L¹`: `|∫ f conj G| ≤ ‖f‖₄ ‖G‖_{4/3}`. -/
lemma holder {α β : ℝ} (f : Lp ℂ 4 (μJ (L := L) α β)) {G : ℝ × AddCircle L → ℂ}
    (hG : MemLp G (4 / 3) (μJ α β)) :
    ‖∫ p, f p * conj (G p) ∂(μJ α β)‖ ≤ ‖f‖ * (eLpNorm G (4 / 3) (μJ α β)).toReal := by
  have hcG := memLp_conj hG
  have hf := Lp.memLp f
  have hfg : (fun p => f p * conj (G p)) = (f : ℝ × AddCircle L → ℂ) • fun p => conj (G p) := by
    funext p; simp [smul_eq_mul]
  have h1 : eLpNorm (fun p => f p * conj (G p)) 1 (μJ α β) ≤
      eLpNorm f 4 (μJ α β) * eLpNorm (fun p => conj (G p)) (4 / 3) (μJ α β) := by
    rw [hfg]; exact eLpNorm_smul_le_mul_eLpNorm hf.aestronglyMeasurable hcG.aestronglyMeasurable
  have h2 : eLpNorm (fun p => conj (G p)) (4 / 3) (μJ α β) = eLpNorm G (4 / 3) (μJ α β) :=
    eLpNorm_congr_norm_ae hcG.aestronglyMeasurable hG.aestronglyMeasurable
      (Eventually.of_forall fun p => Complex.norm_conj _)
  rw [h2] at h1
  have hmeas : AEStronglyMeasurable (fun p => f p * conj (G p)) (μJ α β) :=
    hf.aestronglyMeasurable.mul hcG.aestronglyMeasurable
  calc ‖∫ p, f p * conj (G p) ∂(μJ α β)‖ ≤ ∫ p, ‖f p * conj (G p)‖ ∂(μJ α β) :=
        norm_integral_le_integral_norm _
    _ = (eLpNorm (fun p => f p * conj (G p)) 1 (μJ α β)).toReal := by
        rw [integral_norm_eq_lintegral_enorm hmeas, eLpNorm_one_eq_lintegral_enorm]
        exact hmeas
    _ ≤ (eLpNorm f 4 (μJ α β) * eLpNorm G (4 / 3) (μJ α β)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hf.ne hG.ne) h1
    _ = ‖f‖ * (eLpNorm G (4 / 3) (μJ α β)).toReal := by
        rw [ENNReal.toReal_mul, Lp.norm_def]

lemma integrable_pair {α β : ℝ} (f : Lp ℂ 4 (μJ (L := L) α β)) {G : ℝ × AddCircle L → ℂ}
    (hG : MemLp G (4 / 3) (μJ α β)) :
    Integrable (fun p => f p * conj (G p)) (μJ α β) :=
  (Lp.memLp f).integrable_mul (memLp_conj hG)

section Interval2

variable {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L)

/-- The bounded linear functional `h ↦ ∫∫ (U(s)h)(x) conj G(s,x)`. -/
def psi {G : ℝ × AddCircle L → ℂ} (hG : MemLp G (4 / 3) (μJ α β)) : HL L →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun h => ∫ p, freeL4 α β h p * conj (G p) ∂(μJ α β)
      map_add' := fun f g => by
        rw [freeL4_add hαβ hlen, ← integral_add (integrable_pair _ hG) (integrable_pair _ hG)]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add (freeL4 α β f) (freeL4 α β g)] with p hp
        rw [hp, Pi.add_apply, add_mul]
      map_smul' := fun c f => by
        rw [freeL4_smul hαβ hlen, RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c (freeL4 α β f)] with p hp
        rw [hp, Pi.smul_apply, smul_eq_mul, mul_assoc] }
    (CL L * (eLpNorm G (4 / 3) (μJ α β)).toReal) fun h => by
      refine (holder _ hG).trans ?_
      have := norm_freeL4_le hαβ hlen h
      have h0 : 0 ≤ (eLpNorm G (4 / 3) (μJ α β)).toReal := ENNReal.toReal_nonneg
      calc ‖freeL4 α β h‖ * (eLpNorm G (4 / 3) (μJ α β)).toReal
          ≤ (CL L * ‖h‖) * (eLpNorm G (4 / 3) (μJ α β)).toReal :=
            mul_le_mul_of_nonneg_right this h0
        _ = CL L * (eLpNorm G (4 / 3) (μJ α β)).toReal * ‖h‖ := by ring

lemma psi_apply {G : ℝ × AddCircle L → ℂ} (hG : MemLp G (4 / 3) (μJ α β)) (h : HL L) :
    psi hαβ hlen hG h = ∫ p, freeL4 α β h p * conj (G p) ∂(μJ α β) := rfl

/-- `S_G`: the Riesz representative, `⟨h, S_G⟩ = ∫∫ conj(U(s)h(x)) G(s,x)`. -/
def rep {G : ℝ × AddCircle L → ℂ} (hG : MemLp G (4 / 3) (μJ α β)) : HL L :=
  (InnerProductSpace.toDual ℂ (HL L)).symm (psi hαβ hlen hG)

lemma inner_rep {G : ℝ × AddCircle L → ℂ} (hG : MemLp G (4 / 3) (μJ α β)) (h : HL L) :
    ⟪h, rep hαβ hlen hG⟫_ℂ = ∫ p, conj (freeL4 α β h p) * G p ∂(μJ α β) := by
  rw [← inner_conj_symm, rep, InnerProductSpace.toDual_symm_apply, psi_apply, ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp [map_mul, mul_comm]

lemma norm_rep_le {G : ℝ × AddCircle L → ℂ} (hG : MemLp G (4 / 3) (μJ α β)) :
    ‖rep hαβ hlen hG‖ ≤ CL L * (eLpNorm G (4 / 3) (μJ α β)).toReal := by
  rw [rep, LinearIsometryEquiv.norm_map]
  exact LinearMap.mkContinuous_norm_le _ (mul_nonneg CL_nonneg ENNReal.toReal_nonneg) _

lemma rep_sub {G₁ G₂ : ℝ × AddCircle L → ℂ} (h1 : MemLp G₁ (4 / 3) (μJ α β))
    (h2 : MemLp G₂ (4 / 3) (μJ α β)) :
    rep hαβ hlen (h1.sub h2) = rep hαβ hlen h1 - rep hαβ hlen h2 := by
  rw [rep, rep, rep, ← map_sub]
  congr 1
  ext h
  show _ = psi hαβ hlen h1 h - psi hαβ hlen h2 h
  rw [psi_apply, psi_apply, psi_apply,
    ← integral_sub (integrable_pair _ h1) (integrable_pair _ h2)]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [Pi.sub_apply, map_sub, mul_sub]

#print axioms inner_rep
#print axioms norm_rep_le

end Interval2

/-! ## 3. The free group `U(t)` on `L²`: unitarity, linearity, strong continuity -/

lemma coef_sub (f g : HL L) (n : ℤ) : coef (f - g) n = coef f n - coef g n := by
  simp only [coef, map_sub, lp.coeFn_sub, Pi.sub_apply]

lemma norm_evol (f : HL L) (t : ℝ) : ‖evol f t‖ = ‖f‖ := by
  have h1 : ‖evolCoef f t‖ ^ 2 = ‖fourierL2 L f‖ ^ 2 := by
    rw [norm_sq_lp, norm_sq_lp]
    refine tsum_congr fun n => ?_
    show ‖phase L t n * coef f n‖ ^ 2 = _
    rw [norm_mul, norm_phase, one_mul]
  rw [LinearIsometryEquiv.norm_map] at h1
  rw [evol, LinearIsometryEquiv.norm_map]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1

lemma evol_sub (f g : HL L) (t : ℝ) : evol (f - g) t = evol f t - evol g t := by
  apply (fourierL2 L).injective
  rw [map_sub]
  refine lp.ext (funext fun n => ?_)
  rw [lp.coeFn_sub, Pi.sub_apply, fourierL2_evol, fourierL2_evol, fourierL2_evol, coef_sub]
  ring

lemma summable_coef (f : HL L) : Summable fun n => ‖coef f n‖ ^ 2 := by
  have h := (lp.memℓp (fourierL2 L f)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

/-- Strong continuity of `t ↦ U(t)f` in `L²`. -/
lemma continuous_evol (f : HL L) : Continuous fun t => evol f t := by
  rw [continuous_iff_continuousAt]
  intro t0
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hsq : ∀ t, ‖evol f t - evol f t0‖ ^ 2 =
      ∑' n, ‖(phase L t n - phase L t0 n) * coef f n‖ ^ 2 := by
    intro t
    rw [← (fourierL2 L).norm_map, map_sub, norm_sq_lp]
    refine tsum_congr fun n => ?_
    rw [lp.coeFn_sub, Pi.sub_apply, fourierL2_evol, fourierL2_evol, ← sub_mul]
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝 t0) (G := ℝ)
    (f := fun t n => ‖(phase L t n - phase L t0 n) * coef f n‖ ^ 2) (g := fun _ => 0)
    (bound := fun n => 4 * ‖coef f n‖ ^ 2) ((summable_coef f).mul_left 4) (fun n => ?_)
    (Eventually.of_forall fun t n => ?_)
  · rw [tsum_zero] at h
    have h2 := (h.congr fun t => (hsq t).symm).sqrt
    rw [Real.sqrt_zero] at h2
    exact h2.congr fun t => Real.sqrt_sq (norm_nonneg _)
  · have hc : Continuous fun t => ‖(phase L t n - phase L t0 n) * coef f n‖ ^ 2 :=
      (((continuous_phase L n).sub continuous_const).mul continuous_const).norm.pow 2
    have := hc.tendsto t0
    simpa using this
  · rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
    have h1 : ‖phase L t n - phase L t0 n‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by rw [norm_phase, norm_phase]; norm_num)
    have h2 : ‖phase L t n - phase L t0 n‖ ^ 2 ≤ 4 := by
      nlinarith [norm_nonneg (phase L t n - phase L t0 n)]
    nlinarith [sq_nonneg ‖coef f n‖]

#print axioms continuous_evol

/-! ## 4. The duality Duhamel map -/

section Duhamel

variable {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L) (F : Lp ℂ (4 / 3) (μJ (L := L) α β))

/-- `1_{(α,t] × 𝕋_L} F`. -/
def Fcut (t : ℝ) : ℝ × AddCircle L → ℂ := (Set.Ioc α t ×ˢ Set.univ).indicator F

lemma measurableSet_cut (a b : ℝ) : MeasurableSet (Set.Ioc a b ×ˢ (Set.univ : Set (AddCircle L))) :=
  measurableSet_Ioc.prod MeasurableSet.univ

lemma memLp_Fcut (t : ℝ) : MemLp (Fcut F t) (4 / 3) (μJ α β) :=
  (Lp.memLp F).indicator (measurableSet_cut _ _)

/-- `R(t) = S_{(α,t]} F`. -/
def Rt (t : ℝ) : HL L := rep hαβ hlen (memLp_Fcut F t)

/-- `S_{(a,t]}F − S_{(t,a]}F`, realized as `R(t) − R(a)`. -/
def Sop (a t : ℝ) : HL L := Rt hαβ hlen F t - Rt hαβ hlen F a

/-- **The Duhamel term** `V(t) = U(t)(S_{(a,t]}F − S_{(t,a]}F)` (`= ∫_a^t U(t−s)F(s) ds` by duality). -/
def V (a t : ℝ) : HL L := evol (Sop hαβ hlen F a t) t

lemma Sop_eq (a t : ℝ) :
    Sop hαβ hlen F a t = rep hαβ hlen ((memLp_Fcut F t).sub (memLp_Fcut F a)) := by
  rw [Sop, Rt, Rt, rep_sub]

set_option linter.unusedSimpArgs false in
/-- The oriented cut: for `a, t ≥ α`, `1_{(α,t]} − 1_{(α,a]} = 1_{(a,t]} − 1_{(t,a]}`. -/
lemma Fcut_sub {a t : ℝ} (ha : α ≤ a) (ht : α ≤ t) (p : ℝ × AddCircle L) :
    Fcut F t p - Fcut F a p =
      (Set.Ioc a t ×ˢ Set.univ).indicator F p - (Set.Ioc t a ×ˢ Set.univ).indicator F p := by
  obtain ⟨s, x⟩ := p
  simp only [Fcut, Set.indicator_apply, Set.mem_prod, Set.mem_Ioc, Set.mem_univ, and_true]
  by_cases h1 : α < s <;> by_cases h2 : s ≤ t <;> by_cases h3 : s ≤ a <;>
    by_cases h4 : a < s <;> by_cases h5 : t < s <;>
    simp only [h1, h2, h3, h4, h5, true_and, and_true, and_false, false_and, ↓reduceIte] <;>
    first | ring1 | (exfalso; linarith)

/-- **The duality identity** (printed definition of `S_K F`, oriented): for `a, t ≥ α`,
`⟨h, S_{(a,t]}F − S_{(t,a]}F⟩ = ∫∫ conj(U(s)h(x)) (1_{(a,t]}(s) − 1_{(t,a]}(s)) F(s,x)`. -/
theorem inner_Sop {a t : ℝ} (ha : α ≤ a) (ht : α ≤ t) (h : HL L) :
    ⟪h, Sop hαβ hlen F a t⟫_ℂ = ∫ p, conj (freeL4 α β h p) *
      ((Set.Ioc a t ×ˢ Set.univ).indicator F p - (Set.Ioc t a ×ˢ Set.univ).indicator F p)
        ∂(μJ α β) := by
  rw [Sop_eq, inner_rep]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [Pi.sub_apply]
  rw [Fcut_sub F ha ht p]

lemma norm_Fcut_sub_le (a t : ℝ) (p : ℝ × AddCircle L) : ‖Fcut F t p - Fcut F a p‖ ≤ ‖F p‖ := by
  simp only [Fcut, Set.indicator_apply]
  split_ifs <;> simp

/-- **`eq:root-L4-dual`, the bound**: `‖V(t)‖₂ ≤ C_L ‖F‖_{L^{4/3}}`. -/
theorem norm_V_le (a t : ℝ) : ‖V hαβ hlen F a t‖ ≤ CL L * ‖F‖ := by
  rw [V, norm_evol, Sop_eq]
  refine (norm_rep_le hαβ hlen _).trans (mul_le_mul_of_nonneg_left ?_ CL_nonneg)
  rw [Lp.norm_def]
  refine ENNReal.toReal_mono (Lp.memLp F).ne (eLpNorm_mono
    ((memLp_Fcut F t).sub (memLp_Fcut F a)).aestronglyMeasurable fun p => ?_)
  exact norm_Fcut_sub_le F a t p

set_option linter.unusedSimpArgs false in
lemma norm_Fcut_diff_le (t t' : ℝ) (p : ℝ × AddCircle L) :
    ‖Fcut F t' p - Fcut F t p‖ ≤ ‖(Set.uIoc t t' ×ˢ Set.univ).indicator F p‖ := by
  obtain ⟨s, x⟩ := p
  simp only [Fcut, Set.indicator_apply, Set.mem_prod, Set.mem_Ioc, Set.mem_univ, and_true,
    Set.mem_uIoc]
  by_cases h1 : α < s <;> by_cases h2 : s ≤ t <;> by_cases h3 : s ≤ t' <;>
    by_cases h4 : t < s <;> by_cases h5 : t' < s <;>
    simp only [h1, h2, h3, h4, h5, true_and, and_true, and_false, false_and, true_or, or_true,
      false_or, or_false, ↓reduceIte] <;>
    first | (simp [Set.mem_uIoc, Set.mem_prod, h1, h2, h3, h4, h5]; done) | (exfalso; linarith)

lemma measure_cut_le (t t' : ℝ) :
    μJ (L := L) α β (Set.uIoc t t' ×ˢ Set.univ) ≤ ENNReal.ofReal (|t' - t| * L) := by
  have hL : 0 < L := Fact.out
  rw [μJ, Measure.prod_prod, AddCircle.measure_univ]
  calc (volume.restrict (Set.Ioc α β)) (Set.uIoc t t') * ENNReal.ofReal L
      ≤ volume (Set.uIoc t t') * ENNReal.ofReal L := by
        gcongr; exact Measure.restrict_le_self
    _ = ENNReal.ofReal (|t' - t| * L) := by
        rw [Set.uIoc, Real.volume_Ioc, max_sub_min_eq_abs, ← ENNReal.ofReal_mul (abs_nonneg _)]

/-- `t ↦ S_{(α,t]}F` is continuous into `L²` (absolute continuity of the `L^{4/3}` integral). -/
lemma continuous_Rt : Continuous (Rt hαβ hlen F) := by
  have hL : 0 < L := Fact.out
  rw [Metric.continuous_iff]
  intro t0 ε hε
  set η := ε / (CL L + 1) / 2
  have hη : 0 < η := by have := CL_nonneg (L := L); positivity
  obtain ⟨δ, hδ, hind⟩ := (Lp.memLp F).eLpNorm_indicator_le (by exact Fact.out) (ENNReal.div_ne_top (by norm_num) (by norm_num))
    (ε := ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hη)
  obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.mp hδ
  have hr : 0 < r := ENNReal.ofReal_pos.mp hr1
  refine ⟨r / L, by positivity, fun t ht => ?_⟩
  rw [dist_eq_norm, Rt, Rt, ← rep_sub]
  have hE := measurableSet_cut (L := L) (min t0 t) (max t0 t)
  have hμ : μJ (L := L) α β (Set.uIoc t0 t ×ˢ Set.univ) ≤ δ := by
    refine (measure_cut_le t0 t).trans (le_trans (ENNReal.ofReal_le_ofReal ?_) hr2.le)
    rw [Real.dist_eq] at ht
    have := (lt_div_iff₀ hL).mp ht
    linarith
  have hb := hind _ hE hμ
  have hle : (eLpNorm (Fcut F t - Fcut F t0) (4 / 3) (μJ α β)).toReal ≤ η := by
    have h1 : eLpNorm (Fcut F t - Fcut F t0) (4 / 3) (μJ α β) ≤
        eLpNorm ((Set.uIoc t0 t ×ˢ Set.univ).indicator F) (4 / 3) (μJ α β) :=
      eLpNorm_mono ((memLp_Fcut F t).sub (memLp_Fcut F t0)).aestronglyMeasurable
        fun p => norm_Fcut_diff_le F t0 t p
    have h2 := h1.trans hb
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
    rwa [ENNReal.toReal_ofReal hη.le] at this
  calc ‖rep hαβ hlen ((memLp_Fcut F t).sub (memLp_Fcut F t0))‖
      ≤ CL L * (eLpNorm (Fcut F t - Fcut F t0) (4 / 3) (μJ α β)).toReal := norm_rep_le _ _ _
    _ ≤ CL L * η := mul_le_mul_of_nonneg_left hle CL_nonneg
    _ < ε := by
        have hC := CL_nonneg (L := L)
        simp only [η]
        rw [show CL L * (ε / (CL L + 1) / 2) = ε * (CL L / (CL L + 1)) / 2 by ring]
        have : CL L / (CL L + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
        nlinarith

/-- **`eq:root-L4-dual`, continuity**: `V ∈ C(ℝ; L²)`. -/
theorem continuous_V (a : ℝ) : Continuous (V hαβ hlen F a) := by
  have hS : Continuous (Sop hαβ hlen F a) :=
    (continuous_Rt hαβ hlen F).sub continuous_const
  rw [continuous_iff_continuousAt]
  intro t0
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ t, ‖V hαβ hlen F a t - V hαβ hlen F a t0‖ ≤
      ‖Sop hαβ hlen F a t - Sop hαβ hlen F a t0‖ +
        ‖evol (Sop hαβ hlen F a t0) t - evol (Sop hαβ hlen F a t0) t0‖ := by
    intro t
    rw [V, V]
    calc ‖evol (Sop hαβ hlen F a t) t - evol (Sop hαβ hlen F a t0) t0‖
        = ‖evol (Sop hαβ hlen F a t - Sop hαβ hlen F a t0) t +
            (evol (Sop hαβ hlen F a t0) t - evol (Sop hαβ hlen F a t0) t0)‖ := by
          rw [evol_sub]; congr 1; abel
      _ ≤ _ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_evol]
  have h1 : Tendsto (fun t => ‖Sop hαβ hlen F a t - Sop hαβ hlen F a t0‖) (𝓝 t0) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (hS.tendsto t0)
  have h2 : Tendsto (fun t => ‖evol (Sop hαβ hlen F a t0) t - evol (Sop hαβ hlen F a t0) t0‖)
      (𝓝 t0) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp ((continuous_evol _).tendsto t0)
  have h3 := h1.add h2
  rw [add_zero] at h3
  exact squeeze_zero (fun _ => norm_nonneg _) hb h3

include hαβ hlen in
/-- The pairing written as the printed iterated integral `∫_s ∫_x conj((U(s)h)(x)) G(s,x)`,
using that the slices of `U(·)h` are `U(s)h`. -/
theorem pairing_iterated (h : HL L) {G : ℝ × AddCircle L → ℂ} (hG : MemLp G (4 / 3) (μJ α β)) :
    ∫ p, conj (freeL4 α β h p) * G p ∂(μJ α β) =
      ∫ s in Set.Ioc α β, ∫ x, conj ((evol h s : AddCircle L → ℂ) x) * G (s, x) := by
  have hint : Integrable (fun p => conj (freeL4 α β h p) * G p) (μJ α β) := by
    have := (integrable_pair (freeL4 α β h) hG).norm
    refine this.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (Complex.continuous_conj.comp_aestronglyMeasurable
        (Lp.aestronglyMeasurable _)).mul hG.aestronglyMeasurable
    · simp
  have hP := integral_prod (μ := (volume.restrict (Set.Ioc α β) : Measure ℝ))
    (ν := (volume : Measure (AddCircle L))) (fun p => conj (freeL4 α β h p) * G p) hint
  refine hP.trans ?_
  refine integral_congr_ae ?_
  filter_upwards [freeL4_slice hαβ hlen h] with s hs
  refine integral_congr_ae ?_
  filter_upwards [hs] with x hx
  rw [hx]

#print axioms inner_Sop
#print axioms norm_V_le
#print axioms continuous_V
#print axioms pairing_iterated

end Duhamel

/-! ## 5. Agreement with the ordinary integral -/

lemma evol_evol (g : HL L) (r s : ℝ) : evol (evol g r) s = evol g (s + r) := by
  apply (fourierL2 L).injective
  refine lp.ext (funext fun n => ?_)
  simp only [fourierL2_evol, coef, phase_add]
  ring

lemma conj_phase_neg (t : ℝ) (n : ℤ) : conj (phase L (-t) n) = phase L t n := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast; ring

/-- `U(t)* = U(−t)`. -/
lemma inner_evol (h g : HL L) (t : ℝ) : ⟪h, evol g t⟫_ℂ = ⟪evol h (-t), g⟫_ℂ := by
  rw [← (fourierL2 L).inner_map_map h, ← (fourierL2 L).inner_map_map (evol h (-t)) g,
    lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  rw [fourierL2_evol, fourierL2_evol, RCLike.inner_apply, RCLike.inner_apply, map_mul,
    conj_phase_neg]
  ring

lemma continuous_evol_comp {G : ℝ → HL L} {τ : ℝ → ℝ} (hG : Continuous G) (hτ : Continuous τ) :
    Continuous fun s => evol (G s) (τ s) := by
  rw [continuous_iff_continuousAt]
  intro s0
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ s, ‖evol (G s) (τ s) - evol (G s0) (τ s0)‖ ≤
      ‖G s - G s0‖ + ‖evol (G s0) (τ s) - evol (G s0) (τ s0)‖ := by
    intro s
    calc ‖evol (G s) (τ s) - evol (G s0) (τ s0)‖
        = ‖evol (G s - G s0) (τ s) + (evol (G s0) (τ s) - evol (G s0) (τ s0))‖ := by
          rw [evol_sub]; congr 1; abel
      _ ≤ _ := by refine (norm_add_le _ _).trans ?_; rw [norm_evol]
  have h1 : Tendsto (fun s => ‖G s - G s0‖) (𝓝 s0) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (hG.tendsto s0)
  have h2 : Tendsto (fun s => ‖evol (G s0) (τ s) - evol (G s0) (τ s0)‖) (𝓝 s0) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (((continuous_evol (G s0)).comp hτ).tendsto s0)
  have h3 := h1.add h2
  rw [add_zero] at h3
  exact squeeze_zero (fun _ => norm_nonneg _) hb h3

section Agree

variable {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L) (F : Lp ℂ (4 / 3) (μJ (L := L) α β))

lemma memLp_cut (a t : ℝ) : MemLp (fun p => (Set.Ioc a t ×ˢ Set.univ).indicator F p -
    (Set.Ioc t a ×ˢ Set.univ).indicator F p) (4 / 3) (μJ (L := L) α β) :=
  ((Lp.memLp F).indicator (measurableSet_cut _ _)).sub ((Lp.memLp F).indicator (measurableSet_cut _ _))

/-- **"The integral agrees with the ordinary integral whenever the latter is defined"**: if `F`
has slices `F(s,·) = F_s` (a.e. `s`) for a continuous `s ↦ F_s ∈ L²`, then for `a, t ∈ [α, β]`,
`V(t) = ∫_a^t U(t−s) F_s ds` (Bochner integral in `L²`). -/
theorem V_eq_integral (Fc : ℝ → HL L) (hFc : Continuous Fc)
    (hsl : ∀ᵐ s ∂(volume.restrict (Set.Ioc α β)),
      (fun x => F (s, x)) =ᵐ[volume] (Fc s : AddCircle L → ℂ))
    {a t : ℝ} (ha : a ∈ Set.Icc α β) (ht : t ∈ Set.Icc α β) :
    V hαβ hlen F a t = ∫ s in a..t, evol (Fc s) (t - s) := by
  refine ext_inner_left ℂ fun h => ?_
  set g : ℝ → ℂ := fun s => ⟪evol h (s - t), Fc s⟫_ℂ
  have hg : Continuous g :=
    ((continuous_evol_comp continuous_const (continuous_id.sub continuous_const)).inner hFc)
  have hcont : Continuous fun s => evol (Fc s) (t - s) :=
    continuous_evol_comp hFc (continuous_const.sub continuous_id)
  -- the ordinary integral
  have hR : ⟪h, ∫ s in a..t, evol (Fc s) (t - s)⟫_ℂ = ∫ s in a..t, g s := by
    have hc := (innerSL ℂ h).intervalIntegral_comp_comm (hcont.intervalIntegrable (μ := volume) a t)
    simp only [innerSL_apply_apply] at hc
    rw [← hc]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [g]
    rw [inner_evol, neg_sub]
  rw [hR, V, inner_evol, inner_Sop hαβ hlen F ha.1 ht.1, pairing_iterated hαβ hlen _ (memLp_cut F a t)]
  -- the inner integral is `σ(s) g(s)` for a.e. `s`
  have hin : ∀ᵐ s ∂(volume.restrict (Set.Ioc α β)),
      ∫ x, conj ((evol (evol h (-t)) s : AddCircle L → ℂ) x) *
        ((Set.Ioc a t ×ˢ Set.univ).indicator F (s, x) - (Set.Ioc t a ×ˢ Set.univ).indicator F (s, x)) =
      (Set.Ioc a t).indicator g s - (Set.Ioc t a).indicator g s := by
    filter_upwards [hsl] with s hs
    have hgs : g s = ∫ x, conj ((evol h (s - t) : AddCircle L → ℂ) x) * F (s, x) := by
      simp only [g]
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hs] with x hx
      rw [hx, RCLike.inner_apply, mul_comm]
    rw [evol_evol, ← sub_eq_add_neg]
    by_cases h1 : s ∈ Set.Ioc a t <;> by_cases h2 : s ∈ Set.Ioc t a <;>
      simp only [Set.indicator_apply, Set.mem_prod, Set.mem_univ, and_true, h1, h2, ↓reduceIte,
        sub_zero, zero_sub, mul_zero, mul_neg, integral_neg, integral_zero, hgs, sub_self]
  rw [integral_congr_ae hin]
  have hgi : IntegrableOn g (Set.Ioc α β) := hg.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hsub1 : Set.Ioc a t ⊆ Set.Ioc α β := Set.Ioc_subset_Ioc ha.1 ht.2
  have hsub2 : Set.Ioc t a ⊆ Set.Ioc α β := Set.Ioc_subset_Ioc ht.1 ha.2
  rw [integral_sub (hgi.indicator (measurableSet_Ioc : MeasurableSet (Set.Ioc a t)))
      (hgi.indicator (measurableSet_Ioc : MeasurableSet (Set.Ioc t a))),
    integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    Set.inter_eq_self_of_subset_left hsub1, Set.inter_eq_self_of_subset_left hsub2]
  rfl

#print axioms V_eq_integral

end Agree

end QuantumNLS.DuhamelDuality
