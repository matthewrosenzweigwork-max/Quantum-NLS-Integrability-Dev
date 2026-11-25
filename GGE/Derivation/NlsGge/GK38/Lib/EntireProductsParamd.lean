import NlsGge.GK38.Lib.EntireProductsParamc

/-!
# L4c, part 1d: the product with one factor omitted (book Lemma C.1, `f_n`)

`omitProd n s z = (1/π_n) ∏_{m ≠ n} (σ_m - z)/π_m` is the book's `f_n(λ, σ̃)`.

**Key device** (not in the book): the omitted product is the full product of a *modified*
sequence.  Put `ŝ = s + c · e_n` with `c = z + (π_n - nπ) - s_n`, which is affine-analytic in
`(z, s)`.  Then `σ̂ = σ° + ŝ` agrees with `σ` off `n` and has `σ̂_n = z + π_n`, so the `n`-th factor
`(σ̂_n - z)/π_n` of the full product is `1`.  Hence `∏_{m≠n} … = entProdJ (z, ŝ)`, and
multipliability, joint analyticity of `omitProd` follow from L4a and `analyticOnNhd_entProd_joint`.
Zeros and orders follow from `entProd = (σ_n - z) · omitProd` and `analyticOrderAt_entProd`.
-/

set_option autoImplicit false

open Filter Topology SummationFilter Metric

namespace NlsGge.GK38.Lib

noncomputable section

/-- The factor family with the `n`-th factor replaced by `1`. -/
def omitFactor (n : ℤ) (s : L2Seq) (z : ℂ) (m : ℤ) : ℂ :=
  if m = n then 1 else prodFactor (sigmaOf s) z m

/-- `f_n(λ, σ̃) = (1/π_n) ∏_{m ≠ n} (σ_m - λ)/π_m` (book Lemma C.1). -/
def omitProd (n : ℤ) (s : L2Seq) (z : ℂ) : ℂ :=
  (1 / (piN n : ℂ)) * ∏'[symmetricIcc ℤ] m : ℤ, (if m = n then 1 else prodFactor (sigmaOf s) z m)

/-- The modified perturbation `ŝ = s + (z + (π_n - nπ) - s_n) e_n`. -/
def sOmit (n : ℤ) (s : L2Seq) (z : ℂ) : L2Seq :=
  s + (z + ((piN n : ℂ) - (n : ℂ) * (Real.pi : ℂ)) - s n) • lp.single 2 n (1 : ℂ)

theorem sOmit_apply (n : ℤ) (s : L2Seq) (z : ℂ) (m : ℤ) :
    sOmit n s z m = s m + (if m = n then z + ((piN n : ℂ) - (n : ℂ) * (Real.pi : ℂ)) - s n else 0) := by
  unfold sOmit
  simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : m = n
  · subst h; simp
  · simp [h]

theorem prodFactor_sOmit (n : ℤ) (s : L2Seq) (z : ℂ) (m : ℤ) :
    prodFactor (sigmaOf (sOmit n s z)) z m = omitFactor n s z m := by
  unfold omitFactor
  by_cases h : m = n
  · subst h
    have hc : (piN m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (piN_ne_zero m)
    simp only [prodFactor, sigmaOf, sOmit_apply, ite_true]
    field_simp
    ring
  · simp [prodFactor, sigmaOf, sOmit_apply, h]

theorem omitProd_eq_entProdJ (n : ℤ) (s : L2Seq) (z : ℂ) :
    ∏'[symmetricIcc ℤ] m : ℤ, (if m = n then 1 else prodFactor (sigmaOf s) z m)
      = entProdJ (z, sOmit n s z) := by
  unfold entProdJ
  simp only
  congr 1
  funext m
  exact (prodFactor_sOmit n s z m).symm

/-- Pairing lemma first: the omitted family is multipliable. -/
theorem multipliable_omit (n : ℤ) (s : L2Seq) (z : ℂ) :
    Multipliable (fun m : ℤ => if m = n then 1 else prodFactor (sigmaOf s) z m)
      (symmetricIcc ℤ) := by
  have : (fun m : ℤ => if m = n then (1 : ℂ) else prodFactor (sigmaOf s) z m)
      = prodFactor (sigmaOf (sOmit n s z)) z := by
    funext m; exact (prodFactor_sOmit n s z m).symm
  rw [this]
  exact multipliable_prodFactor (summable_dev_sigmaOf _) z

/-- `ŝ` does not depend on the `n`-th coordinate of `s`. -/
theorem sOmit_add_single (n : ℤ) (s : L2Seq) (z c : ℂ) :
    sOmit n (s + c • lp.single 2 n (1 : ℂ)) z = sOmit n s z := by
  refine Subtype.ext (funext fun m => ?_)
  have h1 := sOmit_apply n (s + c • lp.single 2 n (1 : ℂ)) z m
  have h2 := sOmit_apply n s z m
  change sOmit n (s + c • lp.single 2 n (1 : ℂ)) z m = sOmit n s z m
  rw [h1, h2]
  by_cases h : m = n
  · subst h
    simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ite_true]
    simp
  · have := lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 n (1 : ℂ) h
    simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h,
      ite_false, this, mul_zero, add_zero]

/-- `f_n` does not depend on `σ̃_n` (the `n`-th factor is omitted). -/
theorem omitProd_add_single (n : ℤ) (s : L2Seq) (z c : ℂ) :
    omitProd n (s + c • lp.single 2 n (1 : ℂ)) z = omitProd n s z := by
  unfold omitProd
  rw [omitProd_eq_entProdJ, omitProd_eq_entProdJ, sOmit_add_single]

/-- The perturbation `ŝ` depends analytically on `(z, s)`. -/
theorem analyticOnNhd_sOmit (n : ℤ) :
    AnalyticOnNhd ℂ (fun p : ℂ × L2Seq => sOmit n p.2 p.1) Set.univ := by
  intro p _
  have h1 : AnalyticAt ℂ (fun p : ℂ × L2Seq => p.2) p := analyticAt_snd
  have h2 : AnalyticAt ℂ (fun p : ℂ × L2Seq => p.1) p := analyticAt_fst
  have h3 : AnalyticAt ℂ (fun p : ℂ × L2Seq => p.2 n) p :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).analyticAt _ |>.comp h1
  have h4 : AnalyticAt ℂ
      (fun p : ℂ × L2Seq => p.1 + ((piN n : ℂ) - (n : ℂ) * (Real.pi : ℂ)) - p.2 n) p :=
    (h2.add analyticAt_const).sub h3
  exact h1.add (h4.smul analyticAt_const)

theorem analyticOnNhd_omitProd (n : ℤ) :
    AnalyticOnNhd ℂ (fun p : ℂ × L2Seq => omitProd n p.2 p.1) Set.univ := by
  have e : (fun p : ℂ × L2Seq => omitProd n p.2 p.1)
      = fun p => (1 / (piN n : ℂ)) * entProdJ (p.1, sOmit n p.2 p.1) := by
    funext p
    unfold omitProd
    rw [omitProd_eq_entProdJ]
  rw [e]
  intro p hp
  have hmap : Set.MapsTo (fun p : ℂ × L2Seq => (p.1, sOmit n p.2 p.1)) Set.univ Set.univ :=
    fun _ _ => trivial
  have hcomp := (analyticOnNhd_entProd_joint.comp (f := fun p : ℂ × L2Seq => (p.1, sOmit n p.2 p.1))
      (s := Set.univ) ?_ hmap) p hp
  · exact analyticAt_const.mul hcomp
  · intro q hq
    exact AnalyticAt.prod analyticAt_fst (analyticOnNhd_sOmit n q hq)

theorem analyticAt_omitProd_line (n : ℤ) (s : L2Seq) (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => omitProd n s w) z := by
  have h := analyticOnNhd_omitProd n (z, s) trivial
  have hl : AnalyticAt ℂ (fun w : ℂ => (w, s)) z := AnalyticAt.prod analyticAt_id analyticAt_const
  exact AnalyticAt.comp (g := fun p : ℂ × L2Seq => omitProd n p.2 p.1) (f := fun w : ℂ => (w, s)) h hl

/-! ### Relation to the full product -/

theorem entProd_eq_prodFactor_mul (n : ℤ) (s : L2Seq) (z : ℂ) :
    ∏'[symmetricIcc ℤ] m : ℤ, prodFactor (sigmaOf s) z m
      = prodFactor (sigmaOf s) z n *
        ∏'[symmetricIcc ℤ] m : ℤ, (if m = n then 1 else prodFactor (sigmaOf s) z m) := by
  classical
  have hP := (multipliable_prodFactor (summable_dev_sigmaOf s) z).hasProd
  have hG := (multipliable_omit n s z).hasProd
  rw [hasProd_symmetricIcc_iff] at hP hG
  have hG' := hG.const_mul (prodFactor (sigmaOf s) z n)
  refine tendsto_nhds_unique hP (hG'.congr' ?_)
  filter_upwards [eventually_ge_atTop n.natAbs] with N hN
  have hn : n ∈ Finset.Icc (-(N : ℤ)) N := by
    simp only [Finset.mem_Icc]; omega
  have e1 := Finset.mul_prod_erase (Finset.Icc (-(N : ℤ)) N) (fun m => prodFactor (sigmaOf s) z m) hn
  have e2 := Finset.mul_prod_erase (Finset.Icc (-(N : ℤ)) N)
    (fun m => if m = n then (1 : ℂ) else prodFactor (sigmaOf s) z m) hn
  simp only [ite_true] at e2
  rw [← e1, ← e2, one_mul]
  congr 1
  refine Finset.prod_congr rfl fun m hm => ?_
  simp [Finset.ne_of_mem_erase hm]

/-- **`f(λ) = (σ_n - λ) · f_n(λ)`.** -/
theorem entProd_eq_mul_omitProd (n : ℤ) (s : L2Seq) (z : ℂ) :
    ∏'[symmetricIcc ℤ] m : ℤ, prodFactor (sigmaOf s) z m = (sigmaOf s n - z) * omitProd n s z := by
  rw [entProd_eq_prodFactor_mul n s z]
  unfold omitProd prodFactor
  have hc : (piN n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (piN_ne_zero n)
  field_simp

/-! ### Zeros -/

theorem analyticOrderAt_sub_const (a w : ℂ) :
    analyticOrderAt (fun z : ℂ => a - z) w = if a = w then 1 else 0 := by
  have e : (fun z : ℂ => a - z) = (fun _ => (-1 : ℂ)) * (fun z : ℂ => z - a) := by
    funext z; simp
  rw [e, analyticOrderAt_mul analyticAt_const (by fun_prop)]
  have h0 : analyticOrderAt (fun _ : ℂ => (-1 : ℂ)) w = 0 := by
    rw [analyticOrderAt_eq_zero]; right; simp
  rw [h0, zero_add]
  by_cases h : a = w
  · subst h; simp
  · simp only [h, ↓reduceIte]
    exact analyticOrderAt_id_sub_const_of_ne (Ne.symm h)

/-- Roots `σ_m`, `m ≠ n`, with multiplicity. -/
theorem analyticOrderAt_omitProd (n : ℤ) (s : L2Seq) (w : ℂ) :
    analyticOrderAt (fun z => omitProd n s z) w
      = Set.encard {m : ℤ | m ≠ n ∧ sigmaOf s m = w} := by
  have hσ := summable_dev_sigmaOf s
  have hfun : (fun z => ∏'[symmetricIcc ℤ] m : ℤ, prodFactor (sigmaOf s) z m)
      = (fun z : ℂ => sigmaOf s n - z) * (fun z => omitProd n s z) := by
    funext z; exact entProd_eq_mul_omitProd n s z
  have hord := analyticOrderAt_entProd hσ w
  rw [hfun, analyticOrderAt_mul (by fun_prop) (analyticAt_omitProd_line n s w),
    analyticOrderAt_sub_const] at hord
  have hfin := (Set.Finite.encard_lt_top (finite_roots hσ w)).ne
  by_cases h : sigmaOf s n = w
  · have hset : {m : ℤ | sigmaOf s m = w} = insert n {m : ℤ | m ≠ n ∧ sigmaOf s m = w} := by
      ext m
      by_cases hm : m = n
      · subst hm; simp [h]
      · simp [hm]
    rw [hset, Set.encard_insert_of_notMem (by simp)] at hord hfin
    simp only [h, ↓reduceIte] at hord
    rw [add_comm] at hord
    have hne : Set.encard {m : ℤ | m ≠ n ∧ sigmaOf s m = w} ≠ ⊤ := by
      intro ht; rw [ht] at hfin; simp at hfin
    exact ((WithTop.add_right_inj (by decide : (1 : ℕ∞) ≠ ⊤)).mp hord)
  · have hset : {m : ℤ | sigmaOf s m = w} = {m : ℤ | m ≠ n ∧ sigmaOf s m = w} := by
      ext m
      by_cases hm : m = n
      · subst hm; simp [h]
      · simp [hm]
    rw [hset] at hord
    simpa [h] using hord

/-- `f_n(λ, σ̃) = 0` iff `λ = σ_m` for some `m ≠ n`. -/
theorem omitProd_eq_zero_iff (n : ℤ) (s : L2Seq) (z : ℂ) :
    omitProd n s z = 0 ↔ ∃ m : ℤ, m ≠ n ∧ sigmaOf s m = z := by
  have h0 := (analyticAt_omitProd_line n s z).analyticOrderAt_eq_zero
  rw [analyticOrderAt_omitProd, Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem] at h0
  constructor
  · intro h
    by_contra hne
    push Not at hne
    exact (not_not.mpr h) (h0.mp (fun m hm => hne m hm.1 hm.2))
  · rintro ⟨m, hm, hmz⟩
    by_contra h
    exact (h0.mpr h) m ⟨hm, hmz⟩

/-- `f_n` does not vanish at its own root `σ_n` iff no other `σ_m` equals `σ_n` (simple root). -/
theorem omitProd_root_ne_zero_iff (n : ℤ) (s : L2Seq) :
    omitProd n s (sigmaOf s n) ≠ 0 ↔ ∀ m : ℤ, m ≠ n → sigmaOf s m ≠ sigmaOf s n := by
  rw [Ne, omitProd_eq_zero_iff]
  push Not
  exact Iff.rfl

/-- `f_n⁻¹` is analytic off the poles `σ_m`, `m ≠ n`. -/
theorem analyticOnNhd_omitProd_inv (n : ℤ) :
    AnalyticOnNhd ℂ (fun p : ℂ × L2Seq => (omitProd n p.2 p.1)⁻¹)
      {p | ∀ m : ℤ, m ≠ n → sigmaOf p.2 m ≠ p.1} := by
  intro p hp
  refine (analyticOnNhd_omitProd n p trivial).inv ?_
  rw [Ne, omitProd_eq_zero_iff]
  push Not
  exact hp

/-- The derivative of the full product at the root `σ_n` is `-f_n(σ_n)`. -/
theorem hasDerivAt_entProd_root (n : ℤ) (s : L2Seq) :
    HasDerivAt (fun z : ℂ => ∏'[symmetricIcc ℤ] m : ℤ, prodFactor (sigmaOf s) z m)
      (-omitProd n s (sigmaOf s n)) (sigmaOf s n) := by
  have hf : HasDerivAt (fun z : ℂ => sigmaOf s n - z) (-1) (sigmaOf s n) := by
    simpa using (hasDerivAt_id (sigmaOf s n)).const_sub (sigmaOf s n)
  have hg : HasDerivAt (fun z => omitProd n s z) (deriv (fun z => omitProd n s z) (sigmaOf s n))
      (sigmaOf s n) := (analyticAt_omitProd_line n s _).differentiableAt.hasDerivAt
  have := hf.mul hg
  have e : (fun z : ℂ => ∏'[symmetricIcc ℤ] m : ℤ, prodFactor (sigmaOf s) z m)
      = fun z => (sigmaOf s n - z) * omitProd n s z := by
    funext z; exact entProd_eq_mul_omitProd n s z
  rw [e]
  convert this using 1
  simp

end

end NlsGge.GK38.Lib
