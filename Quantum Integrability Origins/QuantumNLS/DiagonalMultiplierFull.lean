import QuantumNLS.DiagonalMultiplier

/-!
# R-09DDF6D2 `lem:multiplier` (DYNAMICS_LEMMAS.tex:270), repair of DiagonalMultiplier 4896aa6b

Repairs the two points of Terra r80: (1) no hypothesis `T_N e_m = 0` off the admissible domain
`D N`; (2) the operator bound is an explicit hypothesis, not derived from a zero extension.

Setting. `T_N` is an ARBITRARY bounded operator on `ℓ²(ι)`, `‖T_N‖ ≤ Cop` (`hTb`).  On the admissible
domain `D N` it has the printed form `T_N e_m = c_N(m) e_{σ m}`, `σ` injective on `D N`, `|c_N(m)| ≤ C`.
Nothing is assumed about `T_N e_m` for `m ∉ D N`.  `Δ_N(m)=Λ_N(σ m)−Λ_N(m)` is defined only on `D N`,
so the complement of `D N` must lie in the discarded domain: `(D N)ᶜ ⊆ E N` (`hDE`) -- equivalently
the discarded domain is `E N ∪ (D N)ᶜ`.  Source wording used: "Δ_N(m) → δ in probability ... off a
discarded domain whose contribution vanishes or on which T_N = 0", and in the proof "an
admissible-boundary term is treated by its probability and the operator norm".  Accordingly
`hdisc` is: `P_N(E N) = Σ_{m∈E N}|ψ_N(m)|² → 0` (the term is then bounded by `Cop·√P_N(E N)`, using
the operator norm), OR `T_N e_m = 0` for all `m ∈ E N`.  (A weaker "‖T P_E ψ‖ → 0" would not give the
time-uniform bound for a general `T`, since `U(t)` rotates the phases inside `P_Eψ`; that reading
is therefore not used.)  The in-probability hypothesis `hgap` is `badProb → 0` on `D N ∖ E N`.
Proof: split `ψ = P_G ψ + P_{Gᶜ} ψ`, `G = D∖E`, `Gᶜ = E`; `T' = T P_G` is a zero-extended shift
operator, so the frozen `key_bound`/`sum_bound` apply to it (`full_bound`); the remainder
`T P_E (Uψ)` is `0` (T=0 on E) or `≤ Cop √P(E)`.
Conclusions (all proved): `multiplier_full` (main clause, real iSup), `multiplier_zero_diag_full`
(τ=0, T*T diagonal: static residual alone), `multiplier_full_norm_close` (norm-close preparations,
using the explicit bound `Cop`), `opBound_of_zero_extension` (bridge: in the zero-extended setting
`‖T‖ ≤ C` holds automatically).
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Filter Topology Complex
open scoped ComplexConjugate InnerProductSpace
open QuantumNLS.DiagonalMultiplier

namespace QuantumNLS.DiagonalMultiplierFull

variable {ι : Type*} [DecidableEq ι]

/-- Coordinate projection onto a set `G` of basis indices, as a vector map. -/
def projSeq (G : Set ι) (φ : L2 ι) : L2 ι :=
  mulVec (fun m => G.indicator (fun _ => (1 : ℂ)) m) (B := 1) (fun m => by
    by_cases h : m ∈ G <;> simp [Set.indicator, h]) φ

theorem projSeq_apply (G : Set ι) (φ : L2 ι) (m : ι) :
    projSeq G φ m = G.indicator (fun _ => (1 : ℂ)) m * φ m := rfl

theorem norm_projSeq_sq (G : Set ι) (φ : L2 ι) :
    ‖projSeq G φ‖ ^ 2 = ∑' m, G.indicator (fun m => ‖φ m‖ ^ 2) m := by
  rw [norm_sq_eq_tsum]
  refine tsum_congr fun m => ?_
  rw [projSeq_apply]
  by_cases h : m ∈ G <;> simp [Set.indicator, h]

/-- Coordinate projection as a bounded operator. -/
def projL (G : Set ι) : L2 ι →L[ℂ] L2 ι :=
  LinearMap.mkContinuous
    { toFun := projSeq G
      map_add' := fun φ χ => by ext m; simp [projSeq_apply]; ring
      map_smul' := fun c φ => by ext m; simp [projSeq_apply]; ring } 1 (by
    intro φ
    have h : ‖projSeq G φ‖ ^ 2 ≤ (1 * ‖φ‖) ^ 2 := by
      rw [norm_projSeq_sq, one_mul, norm_sq_eq_tsum]
      refine Summable.tsum_le_tsum (fun m => ?_) ?_ (summable_sq φ)
      · by_cases h : m ∈ G <;> simp [Set.indicator, h]
      · refine Summable.of_nonneg_of_le (fun m => Set.indicator_nonneg (fun m _ => by positivity) m)
          (fun m => ?_) (summable_sq φ)
        by_cases h : m ∈ G <;> simp [Set.indicator, h]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h)

theorem projL_apply (G : Set ι) (φ : L2 ι) (m : ι) :
    projL G φ m = G.indicator (fun _ => (1 : ℂ)) m * φ m := rfl

theorem projL_e_mem (G : Set ι) {m : ι} (hm : m ∈ G) : projL G (e m) = e m := by
  ext k
  simp only [projL_apply, e_apply]
  by_cases hk : k = m
  · subst hk; simp [Set.indicator, hm]
  · simp [hk]

theorem projL_e_notMem (G : Set ι) {m : ι} (hm : m ∉ G) : projL G (e m) = 0 := by
  ext k
  simp only [projL_apply, e_apply]
  by_cases hk : k = m
  · subst hk; simp [Set.indicator, hm]
  · simp [hk]

theorem projL_add_compl (G : Set ι) (φ : L2 ι) : projL G φ + projL Gᶜ φ = φ := by
  ext m
  simp only [lp.coeFn_add, Pi.add_apply, projL_apply]
  by_cases h : m ∈ G <;> simp [Set.indicator, h]

theorem norm_projL_sq (G : Set ι) (φ : L2 ι) :
    ‖projL G φ‖ ^ 2 = ∑' m, G.indicator (fun m => ‖φ m‖ ^ 2) m := norm_projSeq_sq G φ

theorem U_projL (Λ : ι → ℝ) (U : ℝ → L2 ι →L[ℂ] L2 ι)
    (hU : ∀ t m, U t (e m) = phase Λ t m • e m) (t : ℝ) (G : Set ι) (φ : L2 ι) :
    U t (projL G φ) = projL G (U t φ) := by
  ext k
  rw [U_coord Λ U hU, projL_apply, projL_apply, U_coord Λ U hU]
  ring

theorem T_projL_zero (T : L2 ι →L[ℂ] L2 ι) (E : Set ι) (hE : ∀ m ∈ E, T (e m) = 0)
    (φ : L2 ι) : T (projL E φ) = 0 := by
  ext k
  rw [coord_apply]
  have : ∀ m, projL E φ m * (T (e m)) k = 0 := by
    intro m
    by_cases hm : m ∈ E
    · simp [hE m hm]
    · simp [projL_apply, Set.indicator, hm]
  simpa using (tsum_congr this).trans tsum_zero

section PerN
variable (Λ : ι → ℝ) (U : ℝ → L2 ι →L[ℂ] L2 ι) (σ : ι → ι) (D E : Set ι) (c : ι → ℂ)
  (T : L2 ι →L[ℂ] L2 ι)

/-- The good set `D ∖ E`. -/
def good (D E : Set ι) : Set ι := D \ E

/-- One-`N` estimate for an arbitrary bounded `T` that is described only on `D`:
split off the discarded part `(D∖E)ᶜ`, on which `T` is controlled only by its norm. -/
theorem full_bound (hU : ∀ t m, U t (e m) = phase Λ t m • e m) (hinj : Set.InjOn σ D)
    (hT : ∀ m ∈ D, T (e m) = c m • e (σ m)) (ψ : L2 ι) (τ : ℂ) (δ t : ℝ) :
    ‖T (U t ψ) - (rot (t * δ) * τ) • U t ψ‖ ≤ ‖T ψ - τ • ψ‖ + ‖T (projL (good D E)ᶜ ψ)‖ +
      ‖T (projL (good D E)ᶜ (U t ψ))‖ +
      Real.sqrt (∑' m, (good D E).indicator (fun m => ‖c m‖ ^ 2 *
        (‖eps Λ σ δ t m‖ ^ 2 * ‖ψ m‖ ^ 2)) m) := by
  set G := good D E with hG
  have hGD : G ⊆ D := Set.diff_subset
  let T' : L2 ι →L[ℂ] L2 ι := T.comp (projL G)
  have hT1 : ∀ m ∈ G, T' (e m) = c m • e (σ m) := by
    intro m hm
    show T (projL G (e m)) = _
    rw [projL_e_mem G hm]; exact hT m (hGD hm)
  have hT0 : ∀ m, m ∉ G → T' (e m) = 0 := by
    intro m hm
    show T (projL G (e m)) = 0
    rw [projL_e_notMem G hm, map_zero]
  have hinjG : Set.InjOn σ G := hinj.mono hGD
  have hkey := key_bound Λ U σ G c T' hU hinjG hT1 hT0 ψ τ δ t
  have d1 : T (U t ψ) - (rot (t * δ) * τ) • U t ψ =
      (T' (U t ψ) - (rot (t * δ) * τ) • U t ψ) + T (projL Gᶜ (U t ψ)) := by
    have h := projL_add_compl G (U t ψ)
    have : T (U t ψ) = T' (U t ψ) + T (projL Gᶜ (U t ψ)) := by
      conv_lhs => rw [← h]
      rw [map_add]; rfl
    rw [this]; abel
  have d2 : T' ψ - τ • ψ = (T ψ - τ • ψ) - T (projL Gᶜ ψ) := by
    have h := projL_add_compl G ψ
    have : T ψ = T' ψ + T (projL Gᶜ ψ) := by
      conv_lhs => rw [← h]
      rw [map_add]; rfl
    rw [this]; abel
  rw [d1]
  refine (norm_add_le _ _).trans ?_
  have h2 : ‖T' ψ - τ • ψ‖ ≤ ‖T ψ - τ • ψ‖ + ‖T (projL Gᶜ ψ)‖ := by
    rw [d2]; exact norm_sub_le _ _
  linarith

end PerN

section Main

/-- The probability (law `|ψ_m|²`) of the discarded domain `E`. -/
def discProb (E : Set ι) (ψ : L2 ι) : ℝ := ∑' m, E.indicator (fun m => ‖ψ m‖ ^ 2) m

theorem norm_projL_eq_sqrt (E : Set ι) (φ : L2 ι) :
    ‖projL E φ‖ = Real.sqrt (∑' m, E.indicator (fun m => ‖φ m‖ ^ 2) m) := by
  rw [← norm_projL_sq, Real.sqrt_sq (norm_nonneg _)]

theorem norm_projL_U (Λ : ι → ℝ) (U : ℝ → L2 ι →L[ℂ] L2 ι)
    (hU : ∀ t m, U t (e m) = phase Λ t m • e m) (t : ℝ) (E : Set ι) (ψ : L2 ι) :
    ‖projL E (U t ψ)‖ = ‖projL E ψ‖ := by
  rw [← U_projL Λ U hU, norm_U Λ U hU]

theorem badProb_mono (Λ : ι → ℝ) (σ : ι → ι) (D E : Set ι) (δ η : ℝ) (ψ : L2 ι) :
    badProb Λ σ (good D E) ∅ δ η ψ ≤ badProb Λ σ D E δ η ψ := by
  have hP := summable_sq ψ
  have hs : ∀ (S : Set ι), Summable fun m => S.indicator (fun m => ‖ψ m‖ ^ 2) m := by
    intro S
    refine Summable.of_nonneg_of_le (fun m => Set.indicator_nonneg (fun m _ => by positivity) m)
      (fun m => ?_) hP
    by_cases hm : m ∈ S
    · rw [Set.indicator_of_mem hm]
    · rw [Set.indicator_of_notMem hm]; positivity
  refine Summable.tsum_le_tsum (fun m => ?_) (hs _) (hs _)
  by_cases hm : m ∈ badSet Λ σ (good D E) ∅ δ η
  · have hm' : m ∈ badSet Λ σ D E δ η := by
      obtain ⟨h1, _, h3⟩ := hm
      exact ⟨h1.1, h1.2, h3⟩
    rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm']
  · rw [Set.indicator_of_notMem hm]
    exact Set.indicator_nonneg (fun m _ => by positivity) m

theorem discContrib_empty (D : Set ι) (c : ι → ℂ) (ψ : L2 ι) :
    discContrib D ∅ c ψ = 0 := by
  unfold discContrib
  simp

end Main

section Final
variable (Λ : ℕ → ι → ℝ) (U : ℕ → ℝ → L2 ι →L[ℂ] L2 ι)

/-- **R-09DDF6D2 `lem:multiplier`, repaired.** `T_N` is an arbitrary bounded operator
(`‖T_N‖ ≤ Cop`), described only on the admissible domain `D N` by the shift form
`T e_m = c_N(m) e_{σ m}`, `|c_N(m)| ≤ C`.  The complement of `D N` lies in the discarded domain
`E N`, whose contribution vanishes (probability `→ 0`, treated by the operator norm as in the
printed proof) or on which `T_N = 0`.  No hypothesis is placed on `T_N e_m` for `m ∉ D N`
beyond this. -/
theorem multiplier_full_eventually
    (hU : ∀ N t m, U N t (e m) = phase (Λ N) t m • e m)
    (σ : ι → ι) (D : ℕ → Set ι) (hinj : ∀ N, Set.InjOn σ (D N))
    (c : ℕ → ι → ℂ) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ N, ∀ m ∈ D N, ‖c N m‖ ≤ C)
    (T : ℕ → L2 ι →L[ℂ] L2 ι) (Cop : ℝ) (hCop0 : 0 ≤ Cop)
    (hTb : ∀ N φ, ‖T N φ‖ ≤ Cop * ‖φ‖)
    (hT : ∀ N, ∀ m ∈ D N, T N (e m) = c N m • e (σ m))
    (ψ : ℕ → L2 ι) (hψ : ∀ N, ‖ψ N‖ = 1) (τ : ℂ) (δ : ℝ)
    (hstat : Tendsto (fun N => ‖T N (ψ N) - τ • ψ N‖) atTop (𝓝 0))
    (E : ℕ → Set ι) (hDE : ∀ N, (D N)ᶜ ⊆ E N)
    (hgap : ∀ η > 0, Tendsto (fun N => badProb (Λ N) σ (D N) (E N) δ η (ψ N)) atTop (𝓝 0))
    (hdisc : Tendsto (fun N => discProb (E N) (ψ N)) atTop (𝓝 0) ∨
      ∀ N, ∀ m ∈ E N, T N (e m) = 0)
    (Tmax : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ t : ℝ, |t| ≤ Tmax →
      ‖T N (U N t (ψ N)) - (rot (t * δ) * τ) • U N t (ψ N)‖ ≤ ε := by
  set Tm : ℝ := max Tmax 0 with hTm0
  have hTmnn : 0 ≤ Tm := le_max_right _ _
  set η : ℝ := ε / (4 * (C * Tm + 1)) with hη
  have hCT : 0 ≤ C * Tm := mul_nonneg hC0 hTmnn
  have hηpos : 0 < η := by rw [hη]; positivity
  have hCTη : C * Tm * η ≤ ε / 4 := by
    rw [hη, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  have hGc : ∀ N, (good (D N) (E N))ᶜ = E N := by
    intro N
    ext m
    simp only [good, Set.mem_compl_iff, Set.mem_diff, not_and, not_not]
    constructor
    · intro h
      by_cases hm : m ∈ D N
      · exact h hm
      · exact hDE N hm
    · intro hm _; exact hm
  -- the remainder sequence
  obtain ⟨ρ, hρ, hρ1, hρ2⟩ : ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧
      (∀ N, ‖T N (projL (good (D N) (E N))ᶜ (ψ N))‖ ≤ ρ N) ∧
      (∀ N t, ‖T N (projL (good (D N) (E N))ᶜ (U N t (ψ N)))‖ ≤ ρ N) := by
    rcases hdisc with h | h
    · refine ⟨fun N => Cop * Real.sqrt (discProb (E N) (ψ N)), ?_, ?_, ?_⟩
      · have h1 := (Real.continuous_sqrt.tendsto 0).comp h
        rw [Real.sqrt_zero] at h1
        simpa using h1.const_mul Cop
      · intro N
        rw [hGc N]
        refine (hTb N _).trans ?_
        rw [norm_projL_eq_sqrt]; rfl
      · intro N t
        rw [hGc N]
        refine (hTb N _).trans ?_
        rw [norm_projL_U (Λ N) (U N) (hU N), norm_projL_eq_sqrt]; rfl
    · refine ⟨fun _ => 0, tendsto_const_nhds, ?_, ?_⟩
      · intro N
        rw [hGc N, T_projL_zero (T N) (E N) (h N)]; simp
      · intro N t
        rw [hGc N, T_projL_zero (T N) (E N) (h N)]; simp
  have hpos8 : (0 : ℝ) < ε ^ 2 / 8 := by positivity
  have hB : ∀ᶠ N in atTop, 4 * C ^ 2 * badProb (Λ N) σ (D N) (E N) δ η (ψ N) < ε ^ 2 / 8 := by
    have := (hgap η hηpos).const_mul (4 * C ^ 2)
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds hpos8)
  have hS : ∀ᶠ N in atTop, ‖T N (ψ N) - τ • ψ N‖ < ε / 4 :=
    hstat.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 4))
  have hR : ∀ᶠ N in atTop, ρ N < ε / 8 :=
    hρ.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 8))
  filter_upwards [hB, hS, hR] with N hB hS hR t ht
  refine (full_bound (Λ N) (U N) σ (D N) (E N) (c N) (T N) (hU N) (hinj N) (hT N) (ψ N) τ δ t).trans ?_
  have hsb := sum_bound (Λ N) σ (good (D N) (E N)) (c N) hC0
    (fun m hm => hC N m hm.1) ∅ (ψ N) (hψ N) δ Tm t η (ht.trans (le_max_left _ _)) hηpos
  rw [discContrib_empty] at hsb
  have hbm := badProb_mono (Λ N) σ (D N) (E N) δ η (ψ N)
  have hsq : Real.sqrt (∑' m, (good (D N) (E N)).indicator (fun m => ‖c N m‖ ^ 2 *
      (‖eps (Λ N) σ δ t m‖ ^ 2 * ‖ψ N m‖ ^ 2)) m) ≤ ε / 2 := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    refine hsb.trans ?_
    have h1 : C ^ 2 * Tm ^ 2 * η ^ 2 = (C * Tm * η) ^ 2 := by ring
    have h2 : (C * Tm * η) ^ 2 ≤ (ε / 4) ^ 2 := pow_le_pow_left₀ (by positivity) hCTη 2
    have h3 : 4 * C ^ 2 * badProb (Λ N) σ (good (D N) (E N)) ∅ δ η (ψ N) ≤
        4 * C ^ 2 * badProb (Λ N) σ (D N) (E N) δ η (ψ N) :=
      mul_le_mul_of_nonneg_left hbm (by positivity)
    nlinarith
  have := hρ1 N
  have := hρ2 N t
  linarith

end Final

section Conclusions
variable (Λ : ℕ → ι → ℝ) (U : ℕ → ℝ → L2 ι →L[ℂ] L2 ι)

/-- **R-09DDF6D2, repaired main statement:** `sup_{|t| ≤ Tmax} ‖(T_N − e^{itδ}τ) U_N(t) ψ_N‖ → 0`
with `T_N` arbitrary bounded, described only on `D N ⊆ ι`; `(D N)ᶜ ⊆ E N`. -/
theorem multiplier_full
    (hU : ∀ N t m, U N t (e m) = phase (Λ N) t m • e m)
    (σ : ι → ι) (D : ℕ → Set ι) (hinj : ∀ N, Set.InjOn σ (D N))
    (c : ℕ → ι → ℂ) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ N, ∀ m ∈ D N, ‖c N m‖ ≤ C)
    (T : ℕ → L2 ι →L[ℂ] L2 ι) (Cop : ℝ) (hCop0 : 0 ≤ Cop)
    (hTb : ∀ N φ, ‖T N φ‖ ≤ Cop * ‖φ‖)
    (hT : ∀ N, ∀ m ∈ D N, T N (e m) = c N m • e (σ m))
    (ψ : ℕ → L2 ι) (hψ : ∀ N, ‖ψ N‖ = 1) (τ : ℂ) (δ : ℝ)
    (hstat : Tendsto (fun N => ‖T N (ψ N) - τ • ψ N‖) atTop (𝓝 0))
    (E : ℕ → Set ι) (hDE : ∀ N, (D N)ᶜ ⊆ E N)
    (hgap : ∀ η > 0, Tendsto (fun N => badProb (Λ N) σ (D N) (E N) δ η (ψ N)) atTop (𝓝 0))
    (hdisc : Tendsto (fun N => discProb (E N) (ψ N)) atTop (𝓝 0) ∨
      ∀ N, ∀ m ∈ E N, T N (e m) = 0)
    (Tmax : ℝ) :
    Tendsto (fun N => ⨆ t : Set.Icc (-Tmax) Tmax, ‖Fop (T N) τ δ t (U N t (ψ N))‖)
      atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun N =>
    lt_of_lt_of_le ha (Real.iSup_nonneg fun _ => norm_nonneg _), fun a ha => ?_⟩
  have hev := multiplier_full_eventually Λ U hU σ D hinj c C hC0 hC T Cop hCop0 hTb hT ψ hψ τ δ
    hstat E hDE hgap hdisc Tmax (ε := a / 2) (by linarith)
  filter_upwards [hev] with N hN
  refine lt_of_le_of_lt (Real.iSup_le (fun t => ?_) (by linarith)) (by linarith : a / 2 < a)
  rw [Fop_apply]
  exact hN t (abs_le.mpr ⟨by linarith [t.2.1], t.2.2⟩)

/-- Second clause: for `τ = 0` and `T_N^*T_N` diagonal, the static residual alone suffices
(no domain, no shift structure, no gap law, no unit-vector assumption).  Unchanged by the
repair; restated for the new setting. -/
theorem multiplier_zero_diag_full
    (hU : ∀ N t m, U N t (e m) = phase (Λ N) t m • e m)
    (T : ℕ → L2 ι →L[ℂ] L2 ι)
    (hdiag : ∀ N m, ∃ l : ℂ, ContinuousLinearMap.adjoint (T N) (T N (e m)) = l • e m)
    (ψ : ℕ → L2 ι) (δ : ℝ)
    (hstat : Tendsto (fun N => ‖T N (ψ N) - (0 : ℂ) • ψ N‖) atTop (𝓝 0)) (Tmax : ℝ) :
    Tendsto (fun N => ⨆ t : Set.Icc (-Tmax) Tmax, ‖Fop (T N) 0 δ t (U N t (ψ N))‖)
      atTop (𝓝 0) :=
  multiplier_zero_diag Λ U hU T hdiag ψ δ hstat Tmax

/-- Third clause in the repaired setting: norm-close preparations.  The uniform operator bound
`‖T_N‖ ≤ Cop` is now a hypothesis of the theorem itself (the printed proof uses "the operator
norm"), so the clause applies verbatim. -/
theorem multiplier_full_norm_close
    (hU : ∀ N t m, U N t (e m) = phase (Λ N) t m • e m)
    (σ : ι → ι) (D : ℕ → Set ι) (hinj : ∀ N, Set.InjOn σ (D N))
    (c : ℕ → ι → ℂ) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ N, ∀ m ∈ D N, ‖c N m‖ ≤ C)
    (T : ℕ → L2 ι →L[ℂ] L2 ι) (Cop : ℝ) (hCop0 : 0 ≤ Cop)
    (hTb : ∀ N φ, ‖T N φ‖ ≤ Cop * ‖φ‖)
    (hT : ∀ N, ∀ m ∈ D N, T N (e m) = c N m • e (σ m))
    (ψ : ℕ → L2 ι) (hψ : ∀ N, ‖ψ N‖ = 1) (τ : ℂ) (δ : ℝ)
    (hstat : Tendsto (fun N => ‖T N (ψ N) - τ • ψ N‖) atTop (𝓝 0))
    (E : ℕ → Set ι) (hDE : ∀ N, (D N)ᶜ ⊆ E N)
    (hgap : ∀ η > 0, Tendsto (fun N => badProb (Λ N) σ (D N) (E N) δ η (ψ N)) atTop (𝓝 0))
    (hdisc : Tendsto (fun N => discProb (E N) (ψ N)) atTop (𝓝 0) ∨
      ∀ N, ∀ m ∈ E N, T N (e m) = 0)
    (Tmax : ℝ) (ψ' : ℕ → L2 ι) (hclose : Tendsto (fun N => ‖ψ' N - ψ N‖) atTop (𝓝 0)) :
    Tendsto (fun N => ⨆ t : Set.Icc (-Tmax) Tmax, ‖Fop (T N) τ δ t (U N t (ψ' N))‖)
      atTop (𝓝 0) :=
  multiplier_norm_close Λ U hU T hCop0 hTb τ δ ψ ψ' Tmax
    (multiplier_full Λ U hU σ D hinj c C hC0 hC T Cop hCop0 hTb hT ψ hψ τ δ hstat E hDE hgap
      hdisc Tmax) hclose

/-- Bridge: in the zero-extended shift setting of `DiagonalMultiplier` (`T e_m = 0` off `D`),
the operator bound `‖T‖ ≤ C` holds automatically, so `Cop = C` is not an extra assumption there. -/
theorem opBound_of_zero_extension (σ : ι → ι) (D : Set ι) (c : ι → ℂ) (T : L2 ι →L[ℂ] L2 ι)
    (hinj : Set.InjOn σ D) (hT : ∀ m ∈ D, T (e m) = c m • e (σ m))
    (hT0 : ∀ m, m ∉ D → T (e m) = 0) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ m ∈ D, ‖c m‖ ≤ C)
    (φ : L2 ι) : ‖T φ‖ ≤ C * ‖φ‖ :=
  norm_T_le σ D c T hinj hT hT0 hC0 hC φ

end Conclusions

#print axioms multiplier_full
#print axioms multiplier_full_eventually
#print axioms multiplier_zero_diag_full
#print axioms multiplier_full_norm_close
#print axioms opBound_of_zero_extension
#print axioms full_bound

end QuantumNLS.DiagonalMultiplierFull
