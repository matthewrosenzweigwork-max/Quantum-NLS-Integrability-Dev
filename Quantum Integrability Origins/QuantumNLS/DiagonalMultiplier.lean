import Mathlib

/-!
# R-09DDF6D2 `lem:multiplier` (DYNAMICS_LEMMAS.tex:270)

Setting: `H = ℓ²(ι)` (`L2 ι`), `ι` = occupation data, `e m = δ_m` the fixed orthonormal basis.
* `U_N(t)`: bounded operator with `U_N(t) e_m = e^{-itΛ_N(m)} e_m` (`hU`, `phase`).
* `T_N`: bounded operator, admissible domain `D N`, fixed shift `σ` injective on `D N`
  (`Set.InjOn`), `T_N e_m = c_N(m) e_{σ m}` on `D N`, `|c_N(m)| ≤ C`; `T_N e_m = 0` off `D N`
  (convention: outside the admissible domain `T_N` vanishes; `Δ_N(m)=Λ_N(σ m)-Λ_N(m)`).
* `ψ_N` unit; law `|⟨e_m,ψ_N⟩|²` (`‖ψ N m‖^2`); `τ ∈ ℂ`, `δ ∈ ℝ`.
* static residual `‖T_N ψ_N - τ ψ_N‖ → 0` (`hstat`).
* "Δ_N → δ in probability off a discarded domain `E N`": for every `η>0`,
  `badProb = Σ_{m ∈ D N, m ∉ E N, |Δ_N(m)-δ|>η} |ψ_N(m)|² → 0` (`hgap`).
* "discarded domain contributes nothing": either `discContrib = Σ_{m ∈ E N ∩ D N} |c_N(m)|²|ψ_N(m)|²
  = ‖T_N P_{E_N} ψ_N‖² → 0`, or `T_N e_m = 0` on `E N` (`hdisc`, literal disjunction).
Conclusions (all proved): `multiplier` (sup over `|t| ≤ Tmax` of `‖(T_N - e^{itδ}τ) U_N(t) ψ_N‖ → 0`,
`Fop`, real `iSup`), `multiplier_zero_diag` (`τ=0`, `T_N^*T_N` diagonal, static residual only, no
gap law, no shift structure), `multiplier_norm_close`/`_shift` (persistence under `‖ψ̃_N-ψ_N‖→0`,
difference `≤ (C+|τ|)‖ψ̃_N-ψ_N‖` uniformly in time).
Printed proof followed: `U^*(T-e^{itδ}τ)U ψ = T D(e^{itΔ}-e^{itδ})ψ + e^{itδ}(T-τ)ψ` is `key_identity`;
`|e^{ia}-e^{ib}| ≤ min(2,|a-b|)`; split by `E`, in-probability bad set and good set (`sum_bound`).
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Filter Topology Complex
open scoped ComplexConjugate InnerProductSpace

namespace QuantumNLS.DiagonalMultiplier

/-- `ℓ²(ι)` with orthonormal basis `e m = δ_m`; `ι` indexes the occupation data. -/
abbrev L2 (ι : Type*) : Type _ := lp (fun _ : ι => ℂ) 2

variable {ι : Type*} [DecidableEq ι]

/-- The basis vector `e_m`. -/
def e (m : ι) : L2 ι := lp.single 2 m (1 : ℂ)

theorem norm_sq_eq_tsum (f : L2 ι) : ‖f‖ ^ 2 = ∑' m, ‖f m‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) f
  simpa using h

theorem e_apply (m k : ι) : (e m : L2 ι) k = if k = m then 1 else 0 := by
  simp [e, lp.single_apply, Pi.single_apply]

theorem summable_sq (f : L2 ι) : Summable fun m => ‖f m‖ ^ 2 := by
  have h := lp.hasSum_norm (p := (2 : ENNReal)) (E := fun _ : ι => ℂ) (by norm_num) f
  simpa using h.summable

/-- Coordinates of `A φ` in terms of `A e_m`. -/
theorem coord_apply (A : L2 ι →L[ℂ] L2 ι) (φ : L2 ι) (k : ι) :
    (A φ) k = ∑' m, φ m * (A (e m)) k := by
  have h1 := lp.hasSum_single (p := (2 : ENNReal)) (E := fun _ : ι => ℂ) (by norm_num) φ
  have h2 := (lp.evalCLM (E := fun _ : ι => ℂ) (p := (2 : ENNReal)) ℂ k).comp A
  have h3 := h1.mapL ((lp.evalCLM (E := fun _ : ι => ℂ) (p := (2 : ENNReal)) ℂ k).comp A)
  have h4 : (fun m => ((lp.evalCLM (E := fun _ : ι => ℂ) (p := (2 : ENNReal)) ℂ k).comp A)
      (lp.single 2 m (φ m))) = fun m => φ m * (A (e m)) k := by
    funext m
    have : lp.single 2 m (φ m) = φ m • (e m : L2 ι) := by
      rw [e, ← lp.single_smul]; simp
    simp [this]
    exact Or.inl rfl
  rw [h4] at h3
  exact h3.tsum_eq.symm

section Operators
variable (Λ : ι → ℝ) (U : ℝ → L2 ι →L[ℂ] L2 ι)

/-- The phase of the diagonal propagator `e^{-itΛ(m)}`. -/
def phase (Λ : ι → ℝ) (t : ℝ) (m : ι) : ℂ := Complex.exp (-(((t * Λ m : ℝ) : ℂ)) * Complex.I)

theorem norm_phase (Λ : ι → ℝ) (t : ℝ) (m : ι) : ‖phase Λ t m‖ = 1 := by
  unfold phase
  rw [Complex.norm_exp]
  simp

theorem U_coord (hU : ∀ t m, U t (e m) = phase Λ t m • e m) (t : ℝ) (φ : L2 ι) (k : ι) :
    (U t φ) k = phase Λ t k * φ k := by
  rw [coord_apply]
  rw [tsum_eq_single k]
  · simp [hU, e_apply]; ring
  · intro m hm
    simp [hU, e_apply, Ne.symm hm]

theorem norm_U (hU : ∀ t m, U t (e m) = phase Λ t m • e m) (t : ℝ) (φ : L2 ι) :
    ‖U t φ‖ = ‖φ‖ := by
  have h : ‖U t φ‖ ^ 2 = ‖φ‖ ^ 2 := by
    rw [norm_sq_eq_tsum, norm_sq_eq_tsum]
    congr 1; funext k
    rw [U_coord Λ U hU, norm_mul, norm_phase, one_mul]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

end Operators

section Shift
variable (σ : ι → ι) (D : Set ι) (c : ι → ℂ) (T : L2 ι →L[ℂ] L2 ι)

theorem T_coord_mem (hinj : Set.InjOn σ D)
    (hT : ∀ m ∈ D, T (e m) = c m • e (σ m)) (hT0 : ∀ m, m ∉ D → T (e m) = 0)
    (φ : L2 ι) {m : ι} (hm : m ∈ D) : (T φ) (σ m) = c m * φ m := by
  rw [coord_apply, tsum_eq_single m]
  · rw [hT m hm]; simp [e_apply]; ring
  · intro m' hm'
    by_cases h : m' ∈ D
    · rw [hT m' h]
      have : σ m ≠ σ m' := fun h' => hm' (hinj h hm h'.symm)
      simp [e_apply, this]
    · simp [hT0 m' h]

theorem T_coord_notMem (hT : ∀ m ∈ D, T (e m) = c m • e (σ m)) (hT0 : ∀ m, m ∉ D → T (e m) = 0)
    (φ : L2 ι) {j : ι} (hj : ∀ m ∈ D, σ m ≠ j) : (T φ) j = 0 := by
  rw [coord_apply]
  have : ∀ m, φ m * (T (e m)) j = 0 := by
    intro m
    by_cases h : m ∈ D
    · rw [hT m h]
      have : j ≠ σ m := fun h' => hj m h h'.symm
      simp [e_apply, this]
    · simp [hT0 m h]
  exact (tsum_congr this).trans tsum_zero

theorem norm_T_sq (hinj : Set.InjOn σ D)
    (hT : ∀ m ∈ D, T (e m) = c m • e (σ m)) (hT0 : ∀ m, m ∉ D → T (e m) = 0) (φ : L2 ι) :
    ‖T φ‖ ^ 2 = ∑' m, D.indicator (fun m => ‖c m‖ ^ 2 * ‖φ m‖ ^ 2) m := by
  rw [norm_sq_eq_tsum]
  let g : D → ι := fun m => σ m
  have hg : Function.Injective g := fun a b h => Subtype.ext (hinj a.2 b.2 h)
  have hsupp : Function.support (fun k => ‖(T φ) k‖ ^ 2) ⊆ Set.range g := by
    intro k hk
    by_contra hr
    apply hk
    have := T_coord_notMem σ D c T hT hT0 φ (j := k) (fun m hm hmk => hr ⟨⟨m, hm⟩, hmk⟩)
    simp [this]
  rw [← hg.tsum_eq hsupp, ← tsum_subtype D (fun m => ‖c m‖ ^ 2 * ‖φ m‖ ^ 2)]
  refine tsum_congr fun m => ?_
  simp only [g]
  rw [T_coord_mem σ D c T hinj hT hT0 φ m.2, norm_mul, mul_pow]

theorem norm_T_le (hinj : Set.InjOn σ D)
    (hT : ∀ m ∈ D, T (e m) = c m • e (σ m)) (hT0 : ∀ m, m ∉ D → T (e m) = 0)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ m ∈ D, ‖c m‖ ≤ C) (φ : L2 ι) : ‖T φ‖ ≤ C * ‖φ‖ := by
  have hsum : Summable fun m => ‖φ m‖ ^ 2 := summable_sq φ
  have h : ‖T φ‖ ^ 2 ≤ (C * ‖φ‖) ^ 2 := by
    rw [norm_T_sq σ D c T hinj hT hT0, mul_pow, norm_sq_eq_tsum, ← tsum_mul_left]
    have hs2 : Summable fun m => C ^ 2 * ‖φ m‖ ^ 2 := hsum.mul_left _
    refine Summable.tsum_le_tsum (fun m => ?_) ?_ hs2
    · by_cases hm : m ∈ D
      · rw [Set.indicator_of_mem hm]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hC m hm) 2)
          (sq_nonneg _)
      · rw [Set.indicator_of_notMem hm]; positivity
    · refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hs2
      · exact Set.indicator_nonneg (fun m _ => by positivity) m
      · by_cases hm : m ∈ D
        · rw [Set.indicator_of_mem hm]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hC m hm) 2)
            (sq_nonneg _)
        · rw [Set.indicator_of_notMem hm]; positivity
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h

end Shift

/-- `rot a = e^{ia}`. -/
def rot (a : ℝ) : ℂ := Complex.exp ((a : ℂ) * Complex.I)

theorem norm_rot (a : ℝ) : ‖rot a‖ = 1 := by
  unfold rot; rw [Complex.norm_exp]; simp

theorem rot_add (a b : ℝ) : rot (a + b) = rot a * rot b := by
  unfold rot; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem phase_eq (Λ : ι → ℝ) (t : ℝ) (m : ι) : phase Λ t m = rot (-(t * Λ m)) := by
  unfold phase rot; push_cast; ring_nf

theorem norm_rot_sub_rot_le (a b : ℝ) : ‖rot a - rot b‖ ≤ |a - b| := by
  have h : rot a - rot b = rot b * (rot (a - b) - 1) := by
    have : rot a = rot b * rot (a - b) := by rw [← rot_add]; congr 1; ring
    rw [this]; ring
  rw [h, norm_mul, norm_rot, one_mul]
  unfold rot
  have := Real.norm_eq_abs (a - b)
  have h2 := Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)
  rw [mul_comm] at h2
  simpa [Real.norm_eq_abs] using h2

theorem norm_rot_sub_rot_le_two (a b : ℝ) : ‖rot a - rot b‖ ≤ 2 := by
  calc ‖rot a - rot b‖ ≤ ‖rot a‖ + ‖rot b‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_rot, norm_rot]; norm_num

/-- Pointwise multiplication of an `ℓ²` vector by a bounded sequence. -/
def mulVec (w : ι → ℂ) {B : ℝ} (hw : ∀ m, ‖w m‖ ≤ B) (ψ : L2 ι) : L2 ι :=
  ⟨fun m => w m * ψ m, by
    refine memℓp_gen ?_
    have hs := (summable_sq ψ).mul_left (B ^ 2)
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hs
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (hw m) 2) (sq_nonneg _)⟩

theorem mulVec_apply (w : ι → ℂ) {B : ℝ} (hw : ∀ m, ‖w m‖ ≤ B) (ψ : L2 ι) (m : ι) :
    mulVec w hw ψ m = w m * ψ m := rfl

section Key
variable (Λ : ι → ℝ) (U : ℝ → L2 ι →L[ℂ] L2 ι) (σ : ι → ι) (D : Set ι) (c : ι → ℂ)
  (T : L2 ι →L[ℂ] L2 ι)

/-- The rotation `e^{it(Δ(m) - δ)}`-difference `ε_t(m) = e^{itΔ(m)} - e^{itδ}`. -/
def eps (Λ : ι → ℝ) (σ : ι → ι) (δ t : ℝ) (m : ι) : ℂ :=
  rot (t * (Λ (σ m) - Λ m)) - rot (t * δ)

theorem norm_eps_le_two (Λ : ι → ℝ) (σ : ι → ι) (δ t : ℝ) (m : ι) :
    ‖eps Λ σ δ t m‖ ≤ 2 := norm_rot_sub_rot_le_two _ _

theorem norm_eps_le (Λ : ι → ℝ) (σ : ι → ι) (δ t : ℝ) (m : ι) :
    ‖eps Λ σ δ t m‖ ≤ |t| * |Λ (σ m) - Λ m - δ| := by
  refine (norm_rot_sub_rot_le _ _).trans ?_
  rw [← mul_sub, abs_mul]

/-- The exact identity `U^*(T - e^{itδ}τ)U ψ = T D(e^{itΔ}) ψ - e^{itδ} τ ψ` in the form
`(T - e^{itδ}τ) U ψ = U (T (D(ε) ψ) + e^{itδ}(T ψ - τ ψ))`. -/
theorem key_identity (hU : ∀ t m, U t (e m) = phase Λ t m • e m) (hinj : Set.InjOn σ D)
    (hT : ∀ m ∈ D, T (e m) = c m • e (σ m)) (hT0 : ∀ m, m ∉ D → T (e m) = 0)
    (ψ : L2 ι) (τ : ℂ) (δ t : ℝ) :
    T (U t ψ) - (rot (t * δ) * τ) • U t ψ =
      U t (T (mulVec (eps Λ σ δ t) (norm_eps_le_two Λ σ δ t) ψ) +
        rot (t * δ) • (T ψ - τ • ψ)) := by
  ext k
  by_cases hk : ∃ m ∈ D, σ m = k
  · obtain ⟨m, hm, rfl⟩ := hk
    simp only [lp.coeFn_sub, lp.coeFn_add, lp.coeFn_smul, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, U_coord Λ U hU, T_coord_mem σ D c T hinj hT hT0 _ hm,
      mulVec_apply]
    have hqr : phase Λ t (σ m) * rot (t * (Λ (σ m) - Λ m)) = phase Λ t m := by
      rw [phase_eq, phase_eq, ← rot_add]; congr 1; ring
    unfold eps
    linear_combination (-(c m) * ψ m) * hqr
  · simp only [not_exists, not_and] at hk
    simp only [lp.coeFn_sub, lp.coeFn_add, lp.coeFn_smul, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, U_coord Λ U hU, T_coord_notMem σ D c T hT hT0 _ hk]
    ring

end Key

section Bound
variable (Λ : ι → ℝ) (U : ℝ → L2 ι →L[ℂ] L2 ι) (σ : ι → ι) (D : Set ι) (c : ι → ℂ)
  (T : L2 ι →L[ℂ] L2 ι)

/-- One-`N` estimate: static residual plus the `ℓ²`-norm of `T D(ε) ψ`. -/
theorem key_bound (hU : ∀ t m, U t (e m) = phase Λ t m • e m) (hinj : Set.InjOn σ D)
    (hT : ∀ m ∈ D, T (e m) = c m • e (σ m)) (hT0 : ∀ m, m ∉ D → T (e m) = 0)
    (ψ : L2 ι) (τ : ℂ) (δ t : ℝ) :
    ‖T (U t ψ) - (rot (t * δ) * τ) • U t ψ‖ ≤ ‖T ψ - τ • ψ‖ +
      Real.sqrt (∑' m, D.indicator (fun m => ‖c m‖ ^ 2 * (‖eps Λ σ δ t m‖ ^ 2 * ‖ψ m‖ ^ 2)) m) := by
  rw [key_identity Λ U σ D c T hU hinj hT hT0 ψ τ δ t, norm_U Λ U hU]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_rot, one_mul, add_comm]
  gcongr
  have h := norm_T_sq σ D c T hinj hT hT0 (mulVec (eps Λ σ δ t) (norm_eps_le_two Λ σ δ t) ψ)
  have h2 : ‖T (mulVec (eps Λ σ δ t) (norm_eps_le_two Λ σ δ t) ψ)‖ =
      Real.sqrt (∑' m, D.indicator (fun m => ‖c m‖ ^ 2 * (‖eps Λ σ δ t m‖ ^ 2 * ‖ψ m‖ ^ 2)) m) := by
    rw [← Real.sqrt_sq (norm_nonneg _), h]
    congr 1
    refine tsum_congr fun m => ?_
    by_cases hm : m ∈ D
    · simp [Set.indicator_of_mem hm, mulVec_apply, norm_mul, mul_pow]
    · simp [Set.indicator_of_notMem hm]
  rw [h2]

end Bound

section Prob
variable (Λ : ι → ℝ) (σ : ι → ι) (D : Set ι) (c : ι → ℂ)

/-- Bad set of the in-probability hypothesis, off the discarded domain `E`. -/
def badSet (Λ : ι → ℝ) (σ : ι → ι) (D E : Set ι) (δ η : ℝ) : Set ι :=
  {m | m ∈ D ∧ m ∉ E ∧ η < |Λ (σ m) - Λ m - δ|}

/-- The `ψ`-contribution of the discarded domain: `‖T P_E ψ‖²`. -/
def discContrib (D E : Set ι) (c : ι → ℂ) (ψ : L2 ι) : ℝ :=
  ∑' m, (E ∩ D).indicator (fun m => ‖c m‖ ^ 2 * ‖ψ m‖ ^ 2) m

/-- The probability (law `|ψ_m|²`) of the bad set. -/
def badProb (Λ : ι → ℝ) (σ : ι → ι) (D E : Set ι) (δ η : ℝ) (ψ : L2 ι) : ℝ :=
  ∑' m, (badSet Λ σ D E δ η).indicator (fun m => ‖ψ m‖ ^ 2) m

theorem sum_bound {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ m ∈ D, ‖c m‖ ≤ C) (E : Set ι)
    (ψ : L2 ι) (hψ : ‖ψ‖ = 1) (δ Tm t η : ℝ) (ht : |t| ≤ Tm) (hη : 0 < η) :
    ∑' m, D.indicator (fun m => ‖c m‖ ^ 2 * (‖eps Λ σ δ t m‖ ^ 2 * ‖ψ m‖ ^ 2)) m ≤
      4 * discContrib D E c ψ + 4 * C ^ 2 * badProb Λ σ D E δ η ψ + C ^ 2 * Tm ^ 2 * η ^ 2 := by
  have hP := summable_sq ψ
  have hPsum : ∑' m, ‖ψ m‖ ^ 2 = 1 := by rw [← norm_sq_eq_tsum, hψ]; norm_num
  have hTm : 0 ≤ Tm := (abs_nonneg t).trans ht
  -- summability of the pieces
  have hs1 : Summable fun m => (E ∩ D).indicator (fun m => ‖c m‖ ^ 2 * ‖ψ m‖ ^ 2) m := by
    refine Summable.of_nonneg_of_le (fun m => Set.indicator_nonneg (fun m _ => by positivity) m)
      (fun m => ?_) (hP.mul_left (C ^ 2))
    by_cases hm : m ∈ E ∩ D
    · rw [Set.indicator_of_mem hm]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hC m hm.2) 2) (sq_nonneg _)
    · rw [Set.indicator_of_notMem hm]; positivity
  have hs2 : Summable fun m => (badSet Λ σ D E δ η).indicator (fun m => ‖ψ m‖ ^ 2) m := by
    refine Summable.of_nonneg_of_le (fun m => Set.indicator_nonneg (fun m _ => by positivity) m)
      (fun m => ?_) hP
    by_cases hm : m ∈ badSet Λ σ D E δ η
    · rw [Set.indicator_of_mem hm]
    · rw [Set.indicator_of_notMem hm]; positivity
  have hs3 : Summable fun m => C ^ 2 * Tm ^ 2 * η ^ 2 * ‖ψ m‖ ^ 2 := hP.mul_left _
  have hsum : Summable fun m => 4 * (E ∩ D).indicator (fun m => ‖c m‖ ^ 2 * ‖ψ m‖ ^ 2) m +
      4 * C ^ 2 * (badSet Λ σ D E δ η).indicator (fun m => ‖ψ m‖ ^ 2) m +
      C ^ 2 * Tm ^ 2 * η ^ 2 * ‖ψ m‖ ^ 2 :=
    ((hs1.mul_left 4).add (hs2.mul_left _)).add hs3
  have hpt : ∀ m, D.indicator (fun m => ‖c m‖ ^ 2 * (‖eps Λ σ δ t m‖ ^ 2 * ‖ψ m‖ ^ 2)) m ≤
      4 * (E ∩ D).indicator (fun m => ‖c m‖ ^ 2 * ‖ψ m‖ ^ 2) m +
      4 * C ^ 2 * (badSet Λ σ D E δ η).indicator (fun m => ‖ψ m‖ ^ 2) m +
      C ^ 2 * Tm ^ 2 * η ^ 2 * ‖ψ m‖ ^ 2 := by
    intro m
    have n1 : 0 ≤ (E ∩ D).indicator (fun m => ‖c m‖ ^ 2 * ‖ψ m‖ ^ 2) m :=
      Set.indicator_nonneg (fun m _ => by positivity) m
    have n2 : 0 ≤ (badSet Λ σ D E δ η).indicator (fun m => ‖ψ m‖ ^ 2) m :=
      Set.indicator_nonneg (fun m _ => by positivity) m
    have n3 : 0 ≤ C ^ 2 * Tm ^ 2 * η ^ 2 * ‖ψ m‖ ^ 2 := by positivity
    have n2' : 0 ≤ 4 * C ^ 2 * (badSet Λ σ D E δ η).indicator (fun m => ‖ψ m‖ ^ 2) m :=
      mul_nonneg (by positivity) n2
    have n1' : 0 ≤ 4 * (E ∩ D).indicator (fun m => ‖c m‖ ^ 2 * ‖ψ m‖ ^ 2) m :=
      mul_nonneg (by norm_num) n1
    by_cases hD : m ∈ D
    · rw [Set.indicator_of_mem hD]
      have he2 := norm_eps_le_two Λ σ δ t m
      have hcm := hC m hD
      have hc2 : ‖c m‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hcm 2
      by_cases hE : m ∈ E
      · rw [Set.indicator_of_mem (show m ∈ E ∩ D from ⟨hE, hD⟩)]
        have : ‖eps Λ σ δ t m‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (eps Λ σ δ t m)]
        have h4 : ‖c m‖ ^ 2 * (‖eps Λ σ δ t m‖ ^ 2 * ‖ψ m‖ ^ 2) ≤ 4 * (‖c m‖ ^ 2 * ‖ψ m‖ ^ 2) := by
          have := mul_le_mul_of_nonneg_right this (sq_nonneg ‖ψ m‖)
          nlinarith [sq_nonneg ‖c m‖, mul_nonneg (sq_nonneg ‖c m‖) (sq_nonneg ‖ψ m‖)]
        linarith
      · by_cases hb : η < |Λ (σ m) - Λ m - δ|
        · have hmb : m ∈ badSet Λ σ D E δ η := ⟨hD, hE, hb⟩
          rw [Set.indicator_of_mem hmb]
          have : ‖eps Λ σ δ t m‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (eps Λ σ δ t m)]
          have h4 : ‖c m‖ ^ 2 * (‖eps Λ σ δ t m‖ ^ 2 * ‖ψ m‖ ^ 2) ≤ 4 * C ^ 2 * ‖ψ m‖ ^ 2 := by
            have h5 := mul_le_mul hc2 (mul_le_mul_of_nonneg_right this (sq_nonneg ‖ψ m‖))
              (by positivity) (by positivity)
            nlinarith [h5]
          have hn1 : (E ∩ D).indicator (fun m => ‖c m‖ ^ 2 * ‖ψ m‖ ^ 2) m = 0 :=
            Set.indicator_of_notMem (fun h => hE h.1) _
          rw [hn1]; linarith
        · push Not at hb
          have hn1 : (E ∩ D).indicator (fun m => ‖c m‖ ^ 2 * ‖ψ m‖ ^ 2) m = 0 :=
            Set.indicator_of_notMem (fun h => hE h.1) _
          have hn2 : (badSet Λ σ D E δ η).indicator (fun m => ‖ψ m‖ ^ 2) m = 0 :=
            Set.indicator_of_notMem (fun h => by have := h.2.2; linarith) _
          rw [hn1, hn2]
          have hε : ‖eps Λ σ δ t m‖ ≤ Tm * η :=
            (norm_eps_le Λ σ δ t m).trans (mul_le_mul ht hb (abs_nonneg _) hTm)
          have hε2 : ‖eps Λ σ δ t m‖ ^ 2 ≤ (Tm * η) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hε 2
          have h5 := mul_le_mul hc2 (mul_le_mul_of_nonneg_right hε2 (sq_nonneg ‖ψ m‖))
            (by positivity) (by positivity)
          nlinarith [h5]
    · rw [Set.indicator_of_notMem hD]; linarith
  have hsF : Summable fun m =>
      D.indicator (fun m => ‖c m‖ ^ 2 * (‖eps Λ σ δ t m‖ ^ 2 * ‖ψ m‖ ^ 2)) m :=
    Summable.of_nonneg_of_le (fun m => Set.indicator_nonneg (fun m _ => by positivity) m) hpt hsum
  refine (Summable.tsum_le_tsum hpt hsF hsum).trans (le_of_eq ?_)
  rw [Summable.tsum_add (((hs1.mul_left 4).add (hs2.mul_left _))) hs3,
    Summable.tsum_add (hs1.mul_left 4) (hs2.mul_left _), tsum_mul_left, tsum_mul_left,
    tsum_mul_left, hPsum, discContrib, badProb]
  ring

end Prob

section Main
open Filter Topology

theorem c_eq_zero_of_T_zero (σ : ι → ι) (D : Set ι) (c : ι → ℂ) (T : L2 ι →L[ℂ] L2 ι)
    (hT : ∀ m ∈ D, T (e m) = c m • e (σ m)) {m : ι} (hm : m ∈ D) (h0 : T (e m) = 0) : c m = 0 := by
  have h := congrArg (fun v : L2 ι => v (σ m)) (hT m hm)
  simp only [h0] at h
  simpa [e_apply] using h.symm

/-- **R-09DDF6D2 `lem:multiplier`, main clause.**  Uniform-in-time convergence. -/
theorem multiplier_eventually
    (Λ : ℕ → ι → ℝ) (U : ℕ → ℝ → L2 ι →L[ℂ] L2 ι)
    (hU : ∀ N t m, U N t (e m) = phase (Λ N) t m • e m)
    (σ : ι → ι) (D : ℕ → Set ι) (hinj : ∀ N, Set.InjOn σ (D N))
    (c : ℕ → ι → ℂ) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ N, ∀ m ∈ D N, ‖c N m‖ ≤ C)
    (T : ℕ → L2 ι →L[ℂ] L2 ι) (hT : ∀ N, ∀ m ∈ D N, T N (e m) = c N m • e (σ m))
    (hT0 : ∀ N m, m ∉ D N → T N (e m) = 0)
    (ψ : ℕ → L2 ι) (hψ : ∀ N, ‖ψ N‖ = 1) (τ : ℂ) (δ : ℝ)
    (hstat : Tendsto (fun N => ‖T N (ψ N) - τ • ψ N‖) atTop (𝓝 0))
    (E : ℕ → Set ι)
    (hgap : ∀ η > 0, Tendsto (fun N => badProb (Λ N) σ (D N) (E N) δ η (ψ N)) atTop (𝓝 0))
    (hdisc : Tendsto (fun N => discContrib (D N) (E N) (c N) (ψ N)) atTop (𝓝 0) ∨
      ∀ N, ∀ m ∈ E N, T N (e m) = 0)
    (Tmax : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ t : ℝ, |t| ≤ Tmax →
      ‖T N (U N t (ψ N)) - (rot (t * δ) * τ) • U N t (ψ N)‖ ≤ ε := by
  have hTm : 0 ≤ Tmax ∨ True := Or.inr trivial
  set Tm : ℝ := max Tmax 0 with hTm0
  have hTmnn : 0 ≤ Tm := le_max_right _ _
  set η : ℝ := ε / (4 * (C * Tm + 1)) with hη
  have hCT : 0 ≤ C * Tm := mul_nonneg hC0 hTmnn
  have hηpos : 0 < η := by rw [hη]; positivity
  have hCTη : C * Tm * η ≤ ε / 4 := by
    rw [hη, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  have hpos12 : (0 : ℝ) < ε ^ 2 / 12 := by positivity
  have hK : ∀ᶠ N in atTop, 4 * discContrib (D N) (E N) (c N) (ψ N) < ε ^ 2 / 12 := by
    rcases hdisc with h | h
    · have := h.const_mul 4
      rw [mul_zero] at this
      exact this.eventually (gt_mem_nhds hpos12)
    · refine Eventually.of_forall fun N => ?_
      have : discContrib (D N) (E N) (c N) (ψ N) = 0 := by
        unfold discContrib
        refine (tsum_congr (fun m => ?_)).trans tsum_zero
        by_cases hm : m ∈ E N ∩ D N
        · rw [Set.indicator_of_mem hm, c_eq_zero_of_T_zero σ (D N) (c N) (T N) (hT N) hm.2
            (h N m hm.1)]
          simp
        · rw [Set.indicator_of_notMem hm]
      rw [this, mul_zero]; exact hpos12
  have hB : ∀ᶠ N in atTop, 4 * C ^ 2 * badProb (Λ N) σ (D N) (E N) δ η (ψ N) < ε ^ 2 / 12 := by
    have := (hgap η hηpos).const_mul (4 * C ^ 2)
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds hpos12)
  have hS : ∀ᶠ N in atTop, ‖T N (ψ N) - τ • ψ N‖ < ε / 2 :=
    hstat.eventually (gt_mem_nhds (by linarith : (0:ℝ) < ε / 2))
  filter_upwards [hK, hB, hS] with N hK hB hS t ht
  refine (key_bound (Λ N) (U N) σ (D N) (c N) (T N) (hU N) (hinj N) (hT N) (hT0 N) (ψ N) τ δ t).trans ?_
  have hsb := sum_bound (Λ N) σ (D N) (c N) hC0 (hC N) (E N) (ψ N) (hψ N) δ Tm t η
    (ht.trans (le_max_left _ _)) hηpos
  have hsq : Real.sqrt (∑' m, (D N).indicator (fun m => ‖c N m‖ ^ 2 *
      (‖eps (Λ N) σ δ t m‖ ^ 2 * ‖ψ N m‖ ^ 2)) m) ≤ ε / 2 := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    refine hsb.trans ?_
    have h1 : C ^ 2 * Tm ^ 2 * η ^ 2 = (C * Tm * η) ^ 2 := by ring
    have h2 : (C * Tm * η) ^ 2 ≤ (ε / 4) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hCTη 2
    nlinarith
  linarith

end Main

section Final
open Filter Topology

/-- `T - e^{itδ} τ` as an operator. -/
def Fop (T : L2 ι →L[ℂ] L2 ι) (τ : ℂ) (δ t : ℝ) : L2 ι →L[ℂ] L2 ι :=
  T - (rot (t * δ) * τ) • (1 : L2 ι →L[ℂ] L2 ι)

theorem Fop_apply (T : L2 ι →L[ℂ] L2 ι) (τ : ℂ) (δ t : ℝ) (v : L2 ι) :
    Fop T τ δ t v = T v - (rot (t * δ) * τ) • v := by
  simp [Fop]

theorem norm_Fop_le (T : L2 ι →L[ℂ] L2 ι) (τ : ℂ) (δ t : ℝ) {C : ℝ} (hT : ∀ φ, ‖T φ‖ ≤ C * ‖φ‖)
    (v : L2 ι) : ‖Fop T τ δ t v‖ ≤ (C + ‖τ‖) * ‖v‖ := by
  rw [Fop_apply]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, norm_mul, norm_rot, one_mul, add_mul]
  linarith [hT v]

/-- **R-09DDF6D2 `lem:multiplier`.**  For every fixed `Tmax < ∞`,
`sup_{|t| ≤ Tmax} ‖(T_N - e^{itδ}τ) U_N(t) ψ_N‖ → 0`. -/
theorem multiplier
    (Λ : ℕ → ι → ℝ) (U : ℕ → ℝ → L2 ι →L[ℂ] L2 ι)
    (hU : ∀ N t m, U N t (e m) = phase (Λ N) t m • e m)
    (σ : ι → ι) (D : ℕ → Set ι) (hinj : ∀ N, Set.InjOn σ (D N))
    (c : ℕ → ι → ℂ) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ N, ∀ m ∈ D N, ‖c N m‖ ≤ C)
    (T : ℕ → L2 ι →L[ℂ] L2 ι) (hT : ∀ N, ∀ m ∈ D N, T N (e m) = c N m • e (σ m))
    (hT0 : ∀ N m, m ∉ D N → T N (e m) = 0)
    (ψ : ℕ → L2 ι) (hψ : ∀ N, ‖ψ N‖ = 1) (τ : ℂ) (δ : ℝ)
    (hstat : Tendsto (fun N => ‖T N (ψ N) - τ • ψ N‖) atTop (𝓝 0))
    (E : ℕ → Set ι)
    (hgap : ∀ η > 0, Tendsto (fun N => badProb (Λ N) σ (D N) (E N) δ η (ψ N)) atTop (𝓝 0))
    (hdisc : Tendsto (fun N => discContrib (D N) (E N) (c N) (ψ N)) atTop (𝓝 0) ∨
      ∀ N, ∀ m ∈ E N, T N (e m) = 0)
    (Tmax : ℝ) :
    Tendsto (fun N => ⨆ t : Set.Icc (-Tmax) Tmax, ‖Fop (T N) τ δ t (U N t (ψ N))‖)
      atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun N => lt_of_lt_of_le ha (Real.iSup_nonneg fun _ => norm_nonneg _),
    fun a ha => ?_⟩
  have hev := multiplier_eventually Λ U hU σ D hinj c C hC0 hC T hT hT0 ψ hψ τ δ hstat E hgap hdisc
    Tmax (ε := a / 2) (by linarith)
  filter_upwards [hev] with N hN
  refine lt_of_le_of_lt (Real.iSup_le (fun t => ?_) (by linarith)) (by linarith : a / 2 < a)
  rw [Fop_apply]
  exact hN t (abs_le.mpr ⟨by linarith [t.2.1], t.2.2⟩)

end Final

section Diag
open Filter Topology

theorem inner_U (Λ : ι → ℝ) (U : ℝ → L2 ι →L[ℂ] L2 ι)
    (hU : ∀ t m, U t (e m) = phase Λ t m • e m) (t : ℝ) (φ χ : L2 ι) :
    ⟪U t φ, U t χ⟫_ℂ = ⟪φ, χ⟫_ℂ := by
  let Ui : L2 ι →ₗᵢ[ℂ] L2 ι := ⟨(U t).toLinearMap, norm_U Λ U hU t⟩
  exact Ui.inner_map_map φ χ

/-- If `T^*T` is diagonal (in the basis `e`), then `‖T U(t) φ‖ = ‖T φ‖` for all `t`. -/
theorem norm_T_U (Λ : ι → ℝ) (U : ℝ → L2 ι →L[ℂ] L2 ι)
    (hU : ∀ t m, U t (e m) = phase Λ t m • e m) (T : L2 ι →L[ℂ] L2 ι)
    (hdiag : ∀ m, ∃ l : ℂ, ContinuousLinearMap.adjoint T (T (e m)) = l • e m)
    (t : ℝ) (φ : L2 ι) : ‖T (U t φ)‖ = ‖T φ‖ := by
  choose l hl using hdiag
  let A : L2 ι →L[ℂ] L2 ι := ContinuousLinearMap.adjoint T ∘L T
  have hA : ∀ (χ : L2 ι) (k : ι), (A χ) k = l k * χ k := by
    intro χ k
    rw [coord_apply, tsum_eq_single k]
    · show χ k * (ContinuousLinearMap.adjoint T (T (e k))) k = _
      rw [hl k]; simp [e_apply]; ring
    · intro m hm
      show χ m * (ContinuousLinearMap.adjoint T (T (e m))) k = 0
      rw [hl m]; simp [e_apply, Ne.symm hm]
  have hcomm : A (U t φ) = U t (A φ) := by
    ext k
    rw [hA, U_coord Λ U hU, U_coord Λ U hU, hA]
    ring
  have h1 : ⟪U t φ, A (U t φ)⟫_ℂ = ⟪φ, A φ⟫_ℂ := by
    rw [hcomm, inner_U Λ U hU]
  have h2 : ∀ v : L2 ι, ⟪v, A v⟫_ℂ = ((‖T v‖ ^ 2 : ℝ) : ℂ) := by
    intro v
    show ⟪v, ContinuousLinearMap.adjoint T (T v)⟫_ℂ = _
    rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    push_cast; rfl
  rw [h2, h2] at h1
  have h3 : ‖T (U t φ)‖ ^ 2 = ‖T φ‖ ^ 2 := by exact_mod_cast h1
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h3

/-- **R-09DDF6D2, second clause.**  If `τ = 0` and `T_N^*T_N` is diagonal, the conclusion follows
from the static residual alone: no gap law, no shift structure. -/
theorem multiplier_zero_diag
    (Λ : ℕ → ι → ℝ) (U : ℕ → ℝ → L2 ι →L[ℂ] L2 ι)
    (hU : ∀ N t m, U N t (e m) = phase (Λ N) t m • e m)
    (T : ℕ → L2 ι →L[ℂ] L2 ι)
    (hdiag : ∀ N m, ∃ l : ℂ, ContinuousLinearMap.adjoint (T N) (T N (e m)) = l • e m)
    (ψ : ℕ → L2 ι) (δ : ℝ)
    (hstat : Tendsto (fun N => ‖T N (ψ N) - (0 : ℂ) • ψ N‖) atTop (𝓝 0)) (Tmax : ℝ) :
    Tendsto (fun N => ⨆ t : Set.Icc (-Tmax) Tmax, ‖Fop (T N) 0 δ t (U N t (ψ N))‖)
      atTop (𝓝 0) := by
  have h : ∀ N, (⨆ t : Set.Icc (-Tmax) Tmax, ‖Fop (T N) 0 δ t (U N t (ψ N))‖) ≤
      ‖T N (ψ N) - (0 : ℂ) • ψ N‖ := by
    intro N
    refine Real.iSup_le (fun t => ?_) (norm_nonneg _)
    rw [Fop_apply, mul_zero, zero_smul, sub_zero, zero_smul, sub_zero]
    exact (norm_T_U (Λ N) (U N) (hU N) (T N) (hdiag N) t (ψ N)).le
  exact squeeze_zero (fun N => Real.iSup_nonneg fun _ => norm_nonneg _) h hstat

end Diag

section Persist
open Filter Topology

/-- **R-09DDF6D2, last clause**: the conclusion persists for norm-close preparations
(`‖ψ̃_N - ψ_N‖ → 0`), with the difference bounded by `(C+|τ|)‖ψ̃_N - ψ_N‖` uniformly in time.
Valid for any family with `‖T_N‖ ≤ C`, hence for both clauses above. -/
theorem multiplier_norm_close
    (Λ : ℕ → ι → ℝ) (U : ℕ → ℝ → L2 ι →L[ℂ] L2 ι)
    (hU : ∀ N t m, U N t (e m) = phase (Λ N) t m • e m)
    (T : ℕ → L2 ι →L[ℂ] L2 ι) {C : ℝ} (hC0 : 0 ≤ C) (hTb : ∀ N φ, ‖T N φ‖ ≤ C * ‖φ‖)
    (τ : ℂ) (δ : ℝ) (ψ ψ' : ℕ → L2 ι) (Tmax : ℝ)
    (h : Tendsto (fun N => ⨆ t : Set.Icc (-Tmax) Tmax, ‖Fop (T N) τ δ t (U N t (ψ N))‖)
      atTop (𝓝 0))
    (hclose : Tendsto (fun N => ‖ψ' N - ψ N‖) atTop (𝓝 0)) :
    Tendsto (fun N => ⨆ t : Set.Icc (-Tmax) Tmax, ‖Fop (T N) τ δ t (U N t (ψ' N))‖)
      atTop (𝓝 0) := by
  have hbound : ∀ N (t : ℝ), ‖Fop (T N) τ δ t (U N t (ψ' N))‖ ≤
      ‖Fop (T N) τ δ t (U N t (ψ N))‖ + (C + ‖τ‖) * ‖ψ' N - ψ N‖ := by
    intro N t
    have h1 : Fop (T N) τ δ t (U N t (ψ' N)) =
        Fop (T N) τ δ t (U N t (ψ N)) + Fop (T N) τ δ t (U N t (ψ' N - ψ N)) := by
      rw [← map_add, ← map_add]; congr 2; abel
    rw [h1]
    refine (norm_add_le _ _).trans ?_
    gcongr
    refine (norm_Fop_le (T N) τ δ t (hTb N) _).trans ?_
    rw [norm_U (Λ N) (U N) (hU N)]
  have hbdd : ∀ N, BddAbove (Set.range fun t : Set.Icc (-Tmax) Tmax =>
      ‖Fop (T N) τ δ t (U N t (ψ N))‖) := by
    intro N
    refine ⟨(C + ‖τ‖) * ‖ψ N‖, ?_⟩
    rintro _ ⟨t, rfl⟩
    refine (norm_Fop_le (T N) τ δ t (hTb N) _).trans ?_
    rw [norm_U (Λ N) (U N) (hU N)]
  have hle : ∀ N, (⨆ t : Set.Icc (-Tmax) Tmax, ‖Fop (T N) τ δ t (U N t (ψ' N))‖) ≤
      (⨆ t : Set.Icc (-Tmax) Tmax, ‖Fop (T N) τ δ t (U N t (ψ N))‖) +
        (C + ‖τ‖) * ‖ψ' N - ψ N‖ := by
    intro N
    refine Real.iSup_le (fun t => ?_) ?_
    · exact (hbound N t).trans (add_le_add_left (le_ciSup (hbdd N) t) _) |>.trans (le_refl _)
    · have := Real.iSup_nonneg (f := fun t : Set.Icc (-Tmax) Tmax =>
        ‖Fop (T N) τ δ t (U N t (ψ N))‖) (fun _ => norm_nonneg _)
      have hC : 0 ≤ C + ‖τ‖ := by positivity
      positivity
  have hsum : Tendsto (fun N => (⨆ t : Set.Icc (-Tmax) Tmax, ‖Fop (T N) τ δ t (U N t (ψ N))‖) +
      (C + ‖τ‖) * ‖ψ' N - ψ N‖) atTop (𝓝 0) := by
    simpa using h.add (hclose.const_mul (C + ‖τ‖))
  exact squeeze_zero (fun N => Real.iSup_nonneg fun _ => norm_nonneg _) hle hsum

/-- Under the shift hypotheses, `‖T_N‖ ≤ C` (so the persistence clause applies to the main clause). -/
theorem multiplier_norm_close_shift
    (Λ : ℕ → ι → ℝ) (U : ℕ → ℝ → L2 ι →L[ℂ] L2 ι)
    (hU : ∀ N t m, U N t (e m) = phase (Λ N) t m • e m)
    (σ : ι → ι) (D : ℕ → Set ι) (hinj : ∀ N, Set.InjOn σ (D N))
    (c : ℕ → ι → ℂ) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ N, ∀ m ∈ D N, ‖c N m‖ ≤ C)
    (T : ℕ → L2 ι →L[ℂ] L2 ι) (hT : ∀ N, ∀ m ∈ D N, T N (e m) = c N m • e (σ m))
    (hT0 : ∀ N m, m ∉ D N → T N (e m) = 0)
    (τ : ℂ) (δ : ℝ) (ψ ψ' : ℕ → L2 ι) (Tmax : ℝ)
    (h : Tendsto (fun N => ⨆ t : Set.Icc (-Tmax) Tmax, ‖Fop (T N) τ δ t (U N t (ψ N))‖)
      atTop (𝓝 0))
    (hclose : Tendsto (fun N => ‖ψ' N - ψ N‖) atTop (𝓝 0)) :
    Tendsto (fun N => ⨆ t : Set.Icc (-Tmax) Tmax, ‖Fop (T N) τ δ t (U N t (ψ' N))‖)
      atTop (𝓝 0) :=
  multiplier_norm_close Λ U hU T hC0
    (fun N φ => norm_T_le σ (D N) (c N) (T N) (hinj N) (hT N) (hT0 N) hC0 (hC N) φ) τ δ ψ ψ' Tmax h hclose

end Persist

#print axioms multiplier
#print axioms multiplier_zero_diag
#print axioms multiplier_norm_close
#print axioms multiplier_norm_close_shift
#print axioms key_identity
#print axioms norm_T_sq

end QuantumNLS.DiagonalMultiplier
