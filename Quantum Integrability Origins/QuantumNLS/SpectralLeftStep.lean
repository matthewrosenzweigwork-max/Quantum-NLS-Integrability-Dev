import QuantumNLS.SpectralFamilySteps

/-!
# The left step at level `y` for antitone compact resolvent families (EXT-001 helpers only)

Authorized scope (VERIFIED SCOPED OWNER APPROVAL, `implementation/ops/STATUS.md`, S2): compact
spectral HELPER lemmas. NO continuity principle, NO `AbstractContinuity`, NO density/completeness
claim is stated or proved here.

* `uniform_indep`: a finite independent family is uniformly independent
  (`κ Σ|c_i| ≤ ‖Σ c_i u_i‖`);
* `proj_lower`: for a finite-dimensional subspace `W` reducing a symmetric contraction `T` with
  `Re⟨Tb, b⟩ ≤ y'‖b‖²` on `Wᗮ`: `Re⟨Tw, w⟫ − y'‖w‖² ≤ (1 − y')‖P_W w‖²`;
* `proj_upper`: a vector `a` in the span of a perturbed family, with `‖a‖² = Re⟨a, w⟩` and
  `w ⊥` the unperturbed family, is small;
* `Hyp.left_step`: in the setting of `SpectralFamilySteps.Hyp`, if the level-`y` spanning property
  `FullAt` holds at every `s < t` (`t > 0`), it holds at `t`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped InnerProductSpace ComplexConjugate NNReal Topology
open Filter

namespace QuantumNLS.SpectralLeftStep

open QuantumNLS.CompactSpectralHelpers QuantumNLS.SpectralFamilySteps

/-- A finite linearly independent family is uniformly independent. -/
theorem uniform_indep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {J : Type*} [Fintype J]
    (u : J → E) (hu : LinearIndependent ℂ u) :
    ∃ κ > 0, ∀ c : J → ℂ, κ * ∑ i, ‖c i‖ ≤ ‖∑ i, c i • u i‖ := by
  set Lm : (J → ℂ) →ₗ[ℂ] E := Fintype.linearCombination ℂ u
  have hker : LinearMap.ker Lm = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    have := (Fintype.linearIndependent_iff.1 hu) c
      (by rw [← Fintype.linearCombination_apply]; exact hc)
    funext i; exact this i
  obtain ⟨K, hK, hanti⟩ := Lm.exists_antilipschitzWith hker
  refine ⟨1 / ((Fintype.card J + 1) * K), by positivity, fun c => ?_⟩
  have h1 : ‖c‖ ≤ K * ‖Lm c‖ := hanti.le_mul_norm (map_zero Lm) c
  have h2 : ∑ i, ‖c i‖ ≤ Fintype.card J * ‖c‖ := by
    calc ∑ i, ‖c i‖ ≤ ∑ _i : J, ‖c‖ := Finset.sum_le_sum fun i _ => norm_le_pi_norm c i
      _ = Fintype.card J * ‖c‖ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h3 : Lm c = ∑ i, c i • u i := Fintype.linearCombination_apply ℂ u c
  rw [h3] at h1
  have hKpos : (0 : ℝ) < K := hK
  have hcn := norm_nonneg c
  rw [one_div, inv_mul_le_iff₀ (by positivity)]
  calc ∑ i, ‖c i‖ ≤ Fintype.card J * ‖c‖ := h2
    _ ≤ (Fintype.card J + 1) * ‖c‖ := by gcongr; linarith
    _ ≤ (Fintype.card J + 1) * (K * ‖∑ i, c i • u i‖) := by gcongr
    _ = _ := by ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Lower bound for the projection onto a reducing finite-rank subspace. -/
theorem proj_lower {T : E →L[ℂ] E} (hT1 : ∀ x, ‖T x‖ ≤ ‖x‖)
    (W : Submodule ℂ E) [W.HasOrthogonalProjection] (hinv : ∀ x ∈ W, T x ∈ W)
    (hinv' : ∀ x ∈ Wᗮ, T x ∈ Wᗮ) {y' : ℝ} (horth : ∀ b ∈ Wᗮ, RCLike.re ⟪T b, b⟫_ℂ ≤ y' * ‖b‖ ^ 2)
    (w : E) :
    RCLike.re ⟪T w, w⟫_ℂ - y' * ‖w‖ ^ 2 ≤ (1 - y') * ‖W.starProjection w‖ ^ 2 := by
  set a := W.starProjection w
  set b := w - a
  have ha : a ∈ W := W.starProjection_apply_mem w
  have hb : b ∈ Wᗮ := Submodule.sub_starProjection_mem_orthogonal w
  have hw : w = a + b := by simp [b]
  have hab : ⟪a, b⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal ha hb
  have hTab : ⟪T a, b⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal (hinv a ha) hb
  have hTba : ⟪T b, a⟫_ℂ = 0 := Submodule.inner_left_of_mem_orthogonal ha (hinv' b hb)
  have hexp : RCLike.re ⟪T w, w⟫_ℂ = RCLike.re ⟪T a, a⟫_ℂ + RCLike.re ⟪T b, b⟫_ℂ := by
    rw [hw, map_add, inner_add_left, inner_add_right, inner_add_right, hTab, hTba]
    simp
  have hnorm : ‖w‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    rw [hw, @norm_add_sq ℂ, hab]; simp
  have hTa : RCLike.re ⟪T a, a⟫_ℂ ≤ ‖a‖ ^ 2 := by
    calc RCLike.re ⟪T a, a⟫_ℂ ≤ ‖⟪T a, a⟫_ℂ‖ := RCLike.re_le_norm _
      _ ≤ ‖T a‖ * ‖a‖ := norm_inner_le_norm _ _
      _ ≤ ‖a‖ * ‖a‖ := by gcongr; exact hT1 a
      _ = ‖a‖ ^ 2 := by ring
  have hTb := horth b hb
  rw [hexp, hnorm]
  nlinarith

/-- Upper bound for a vector in the span of a perturbed family. -/
theorem proj_upper {J : Type*} [Fintype J] (u u' : J → E) {κ : ℝ} (hκ : 0 < κ)
    (hind : ∀ c : J → ℂ, κ * ∑ i, ‖c i‖ ≤ ‖∑ i, c i • u i‖) {w a : E}
    (horth : ∀ i, ⟪u i, w⟫_ℂ = 0) (ha : a ∈ Submodule.span ℂ (Set.range u'))
    (haw : ‖a‖ ^ 2 = RCLike.re ⟪a, w⟫_ℂ) {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ i, ‖u' i - u i‖ ≤ D)
    (hDκ : D ≤ κ / 2) : ‖a‖ ≤ 2 / κ * D * ‖w‖ := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 ha
  set S := ∑ i, ‖c i‖
  set a := ∑ i, c i • u' i
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hpert : ‖∑ i, c i • u i‖ ≤ ‖a‖ + S * D := by
    have e : ∑ i, c i • u i = a - ∑ i, c i • (u' i - u i) := by
      simp only [a, smul_sub, Finset.sum_sub_distrib, sub_sub_cancel]
    rw [e]
    refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
    calc ‖∑ i, c i • (u' i - u i)‖ ≤ ∑ i, ‖c i • (u' i - u i)‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖c i‖ * D := Finset.sum_le_sum fun i _ => by rw [norm_smul]; gcongr; exact hD i
      _ = S * D := by rw [← Finset.sum_mul]
  have hSa : S ≤ 2 / κ * ‖a‖ := by
    have h1 := hind c
    rw [div_mul_eq_mul_div, le_div_iff₀ hκ]
    nlinarith
  have hinner : RCLike.re ⟪a, w⟫_ℂ ≤ S * D * ‖w‖ := by
    have e : ⟪a, w⟫_ℂ = ∑ i, conj (c i) * ⟪u' i - u i, w⟫_ℂ := by
      simp only [a, sum_inner, inner_smul_left, inner_sub_left, horth, sub_zero]
    rw [e]
    calc RCLike.re (∑ i, conj (c i) * ⟪u' i - u i, w⟫_ℂ)
        ≤ ‖∑ i, conj (c i) * ⟪u' i - u i, w⟫_ℂ‖ := RCLike.re_le_norm _
      _ ≤ ∑ i, ‖conj (c i) * ⟪u' i - u i, w⟫_ℂ‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖c i‖ * (D * ‖w‖) := Finset.sum_le_sum fun i _ => by
          rw [norm_mul, Complex.norm_conj]
          gcongr
          exact (norm_inner_le_norm _ _).trans (by gcongr; exact hD i)
      _ = S * D * ‖w‖ := by rw [← Finset.sum_mul]; ring
  have hsq : ‖a‖ ^ 2 ≤ 2 / κ * ‖a‖ * D * ‖w‖ := by
    rw [haw]
    refine hinner.trans ?_
    have := mul_le_mul_of_nonneg_right hSa (mul_nonneg hD0 (norm_nonneg w))
    nlinarith
  rcases (norm_nonneg a).lt_or_eq with hpos | hzero
  · have : ‖a‖ * ‖a‖ ≤ ‖a‖ * (2 / κ * D * ‖w‖) := by nlinarith
    exact le_of_mul_le_mul_left this hpos
  · rw [← hzero]; positivity

variable {ι : Type*} {R : ℝ≥0 → E →L[ℂ] E} {v : ℝ≥0 → ι → E} {μ : ℝ≥0 → ι → ℝ}

/-- **Left step at level `y`**: if the level-`y` spanning property holds at every `s < t`
(`t > 0`), it holds at `t`. -/
theorem Hyp.left_step (H : Hyp R v μ) {y : ℝ} (hy : 0 < y) {t : ℝ≥0} (ht : 0 < t)
    (hfull : ∀ s, s < t → FullAt (v s) (μ s) (R s) y) : FullAt (v t) (μ t) (R t) y := by
  classical
  intro x lam hlam hx
  by_contra hxn
  have hlam0 : lam ≠ 0 := (hy.trans hlam).ne'
  obtain ⟨w, hw0, hTw, horth⟩ :=
    exists_orth_eigvec (v t) (μ t) (H.compact t) (H.symm t) (H.eig t) hlam0 hx hxn
  set y' := (y + lam) / 2 with hy'def
  have hy1 : y < y' := by rw [hy'def]; linarith
  have hy2 : y' < lam := by rw [hy'def]; linarith
  have hy'0 : 0 < y' := hy.trans hy1
  have hfull' : ∀ s, s < t → FullAt (v s) (μ s) (R s) y' := fun s hs x' l hl hx' =>
    hfull s hs x' l (hy1.trans hl) hx'
  -- the index sets above `y'` decrease on `[0, t)`
  have hanti : ∀ a b, a ≤ b → b < t → {i | y' < μ b i} ⊆ {i | y' < μ a i} := by
    intro a b hab hbt i hi
    by_contra hc
    have hc' : μ a i ≤ y' := not_lt.1 hc
    have := H.no_entry hy'0 hab (fun s _ hs2 => hfull' s (hs2.trans_lt hbt)) i hc'
    exact absurd hi (not_lt.2 this)
  have hfin : ∀ s, ({i | y' < μ s i} : Set ι).Finite := fun s => by
    have := finiteDimensional_eigUp (H.compact s) (H.symm s) hy'0
    exact (count_in_subspace (eigUp (R s) y') (v s) (H.indep s) _
      (fun i hi => mem_eigUp hi (H.eig s i))).1
  -- stabilization on `[s₀, t)`
  have hex : ∃ n, ∃ s, s < t ∧ ({i | y' < μ s i} : Set ι).ncard = n := ⟨_, 0, ht, rfl⟩
  obtain ⟨s0, hs0t, hs0m⟩ := Nat.find_spec hex
  have hstab : ∀ s, s0 ≤ s → s < t → {i | y' < μ s i} = {i | y' < μ s0 i} := by
    intro s h1 h2
    have hsub := hanti s0 s h1 h2
    have hle : ({i | y' < μ s0 i} : Set ι).ncard ≤ ({i | y' < μ s i} : Set ι).ncard := by
      rw [hs0m]; exact Nat.find_min' hex ⟨s, h2, rfl⟩
    exact Set.eq_of_subset_of_ncard_le hsub hle (hfin s0)
  set J : Set ι := {i | y' < μ s0 i}
  have : Fintype J := (hfin s0).fintype
  obtain ⟨κ, hκ, hind⟩ := uniform_indep (fun i : J => v t i)
    ((H.indep t).comp Subtype.val Subtype.val_injective)
  set D : ℝ≥0 → ℝ := fun s => ∑ i : J, ‖v s i - v t i‖
  have hDlim : Tendsto D (𝓝 t) (𝓝 0) := by
    have : Tendsto D (𝓝 t) (𝓝 (∑ i : J, ‖v t i - v t i‖)) :=
      tendsto_finsetSum _ fun i _ => (((H.vcont i).tendsto t).sub tendsto_const_nhds).norm
    simpa using this
  have hDi : ∀ s (i : J), ‖v s i - v t i‖ ≤ D s := fun s i =>
    Finset.single_le_sum (f := fun i : J => ‖v s i - v t i‖) (fun j _ => norm_nonneg _)
      (Finset.mem_univ i)
  have hD0 : ∀ s, 0 ≤ D s := fun s => Finset.sum_nonneg fun _ _ => norm_nonneg _
  set c0 := (lam - y') * ‖w‖ ^ 2
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hc0 : 0 < c0 := by have : 0 < lam - y' := by linarith
                          positivity
  have hne : (𝓝[<] t).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_Iio' ⟨(0 : ℝ≥0), ht⟩]; exact Set.mem_Iic.2 le_rfl)
  have hlim2 : Tendsto (fun s => (2 / κ * D s * ‖w‖) ^ 2) (𝓝[<] t) (𝓝 0) := by
    have := ((hDlim.const_mul (2 / κ)).mul_const ‖w‖).pow 2
    simp only [mul_zero, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
    exact this.mono_left nhdsWithin_le_nhds
  have e1 : ∀ᶠ s in 𝓝[<] t, s ∈ Set.Ioo s0 t := Ioo_mem_nhdsLT hs0t
  have e2 : ∀ᶠ s in 𝓝[<] t, D s ≤ κ / 2 :=
    (hDlim.mono_left nhdsWithin_le_nhds).eventually (ge_mem_nhds (by positivity))
  have e3 : ∀ᶠ s in 𝓝[<] t, (2 / κ * D s * ‖w‖) ^ 2 < c0 := hlim2.eventually (gt_mem_nhds hc0)
  obtain ⟨s, ⟨hs0, hst⟩, hDs, hsmall⟩ := (e1.and (e2.and e3)).exists
  -- at this `s`
  have := finiteDimensional_eigUp (H.compact s) (H.symm s) hy'0
  set W := eigUp (R s) y'
  set a := W.starProjection w
  have hlow := proj_lower (H.norm_apply_le s) W (eigUp_invariant (R s) y')
    (orth_invariant (H.symm s) y')
    (fun b hb => re_inner_le_of_mem_orth (H.compact s) (H.symm s) (H.pos s) hy'0 hb) w
  have hant := H.anti s t hst.le w
  rw [hTw, re_inner_real_smul] at hant
  have ha2 : c0 ≤ ‖a‖ ^ 2 := by
    have h1 : c0 ≤ (1 - y') * ‖a‖ ^ 2 := by
      show (lam - y') * ‖w‖ ^ 2 ≤ _
      nlinarith
    nlinarith [sq_nonneg ‖a‖]
  -- `a` lies in the span of `v s` on `J`
  have hcount := (fullAt_iff_count (v s) (μ s) (H.compact s) (H.symm s) (H.indep s) (H.eig s)
    hy'0).1 (hfull' s hst)
  obtain ⟨-, -, hspan⟩ := count_in_subspace W (v s) (H.indep s) {i | y' < μ s i}
    (fun i hi => mem_eigUp hi (H.eig s i))
  have haW : a ∈ W := W.starProjection_apply_mem w
  have haspan : a ∈ Submodule.span ℂ (Set.range fun i : J => v s i) := by
    have h1 := hspan hcount haW
    rw [hstab s hs0.le hst] at h1
    have e : v s '' J = Set.range fun i : J => v s i := by
      ext z; simp [J]
    rwa [e] at h1
  have haw : ‖a‖ ^ 2 = RCLike.re ⟪a, w⟫_ℂ := by
    have hb : w - a ∈ Wᗮ := Submodule.sub_starProjection_mem_orthogonal w
    have h0 : ⟪a, w - a⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal haW hb
    have e : ⟪a, w⟫_ℂ = ⟪a, a⟫_ℂ := by
      have : w = a + (w - a) := by abel
      rw [this, inner_add_right, h0, add_zero]
    rw [e, inner_self_eq_norm_sq]
  have hup := proj_upper (fun i : J => v t i) (fun i : J => v s i) hκ hind
    (fun i => horth i) haspan haw (hD0 s) (fun i => hDi s i) hDs
  have : ‖a‖ ^ 2 ≤ (2 / κ * D s * ‖w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hup 2
  linarith

#print axioms uniform_indep
#print axioms proj_lower
#print axioms proj_upper
#print axioms Hyp.left_step

end QuantumNLS.SpectralLeftStep
