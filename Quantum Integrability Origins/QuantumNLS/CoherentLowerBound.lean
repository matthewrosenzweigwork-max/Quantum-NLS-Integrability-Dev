import QuantumNLS.WickSpectralBridge
import QuantumNLS.OccupationUnitary

/-!
# Coherent-state lower bound for Wick operators

Source: `chapters/core/wick_calculus.tex`, `eq:full-coherent-test` and the paragraph after it
("`b^α ξ^{⊗N} = √(N)_d ξ^α ξ^{⊗(N-d)}`", "the liminf of the operator norm is at least `|f(z)|`").
The coherent vectors are the occupation images of the ACTUAL completed tensor powers `ξ^{⊗N}`
(`OccupationUnitary.U4_htpow`); no Bethe gauge is selected (an arbitrary supplied unit-modulus
gauge is handled by norm invariance under the unitary gauge conjugation).
-/

namespace QuantumNLS.CoherentLowerBound

open QuantumNLS.Occupation QuantumNLS.WickSymbols QuantumNLS.WickBounds QuantumNLS.WickSpectralBridge
open QuantumNLS.OccupationHilbert Filter

noncomputable section

/-! ### Coherent coefficients in the occupation basis -/

/-- `√(K!/∏ m_a!) ∏ ξ_a^{m_a}` on arrays of total `K` (zero otherwise). -/
def cohC (ξ : ℤ → ℂ) (K : ℕ) (m : Occ) : ℂ :=
  if total m = K then
    ((Real.sqrt ((K.factorial : ℝ) / (OccupationUnitary.multiplicityFactorial m : ℝ)) : ℝ) : ℂ)
      * m.prod (fun a k => ξ a ^ k)
  else 0

lemma cohC_support_finite {ξ : ℤ → ℂ} (hξ : (Function.support ξ).Finite) (K : ℕ) :
    (Function.support (cohC ξ K)).Finite := by
  classical
  set S : Finset ℤ := hξ.toFinset with hS
  -- the support lies in `{m | m ≤ K on S, supported in S}`
  have hsub : Function.support (cohC ξ K) ⊆ {m : Occ | (∀ a, m a ≠ 0 → a ∈ S) ∧ total m = K} := by
    intro m hm
    have hm' : cohC ξ K m ≠ 0 := hm
    unfold cohC at hm'
    by_cases ht : total m = K
    · refine ⟨fun a ha => ?_, ht⟩
      by_contra haS
      have hξa : ξ a = 0 := by
        by_contra h
        exact haS (by simp [hS, Set.Finite.mem_toFinset, Function.mem_support, h])
      apply hm'
      simp only [ht, ↓reduceIte]
      have : m.prod (fun a k => ξ a ^ k) = 0 := by
        apply Finset.prod_eq_zero (i := a) (Finsupp.mem_support_iff.mpr ha)
        show ξ a ^ m a = 0
        rw [hξa]; exact zero_pow ha
      rw [this, mul_zero]
    · simp only [ht, ↓reduceIte] at hm'; exact absurd rfl hm'
  refine Set.Finite.subset ?_ hsub
  have hinj : Set.InjOn (fun m : Occ => fun a : S => m a)
      {m : Occ | (∀ a, m a ≠ 0 → a ∈ S) ∧ total m = K} := by
    intro m hm n hn h
    ext a
    by_cases ha : a ∈ S
    · exact congrFun h ⟨a, ha⟩
    · have h1 : m a = 0 := by by_contra h'; exact ha (hm.1 a h')
      have h2 : n a = 0 := by by_contra h'; exact ha (hn.1 a h')
      rw [h1, h2]
  refine Set.Finite.of_finite_image ?_ hinj
  refine (Set.finite_Iic (fun _ : S => K)).subset ?_
  rintro _ ⟨m, hm, rfl⟩ a
  show m a ≤ K
  have := occ_le_total (a : ℤ) m
  rw [hm.2] at this
  exact this

/-- The coherent occupation vector of a finitely supported `ξ`. -/
def coh {ξ : ℤ → ℂ} (hξ : (Function.support ξ).Finite) (K : ℕ) : FS :=
  Finsupp.ofSupportFinite (cohC ξ K) (cohC_support_finite hξ K)

@[simp] lemma coh_apply {ξ : ℤ → ℂ} (hξ : (Function.support ξ).Finite) (K : ℕ) (m : Occ) :
    coh hξ K m = cohC ξ K m := rfl

/-- Coefficients of `b_a v`. -/
lemma Ann_apply (a : ℤ) (v : FS) (n : Occ) :
    Ann a v n = ((Real.sqrt ((n a : ℝ) + 1) : ℝ) : ℂ) * v (n + e a) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add u u' hu hu' => simp [map_add, hu, hu', mul_add]
  | single m c =>
    rw [single_eq_smul_ket, map_smul]
    simp only [Finsupp.smul_apply, Ann_ket, smul_eq_mul, ket]
    simp only [Finsupp.single_apply]
    by_cases h : m - e a = n
    · by_cases hma : 1 ≤ m a
      · have hm : m = n + e a := by
          rw [← h]; exact (shift_sub_add (a := a) (m := m) hma).symm
        subst hm
        have : (n + e a) a = n a + 1 := by simp
        simp [this]; ring
      · have hm0 : m a = 0 := by omega
        have hne : ¬ (n + e a = m) := by
          intro hh
          have := congrArg (fun x : Occ => x a) hh
          simp at this; omega
        have hne' : ¬ (m = n + e a) := fun hh => hne hh.symm
        simp [h, hne', hm0]
    · have hne : ¬ (m = n + e a) := by
        intro hh; apply h; rw [hh]; simp
      simp [h, hne]

/-! ### The annihilation eigen-relation `b_a Ψ_{K+1} = √(K+1) ξ_a Ψ_K` -/

lemma mult_add_single (n : Occ) (a : ℤ) :
    OccupationUnitary.multiplicityFactorial (n + e a)
      = OccupationUnitary.multiplicityFactorial n * (n a + 1) := by
  unfold OccupationUnitary.multiplicityFactorial
  set n' : Occ := Finsupp.erase a n with hn'
  have hn'a : n' a = 0 := by simp [hn']
  have hn : n = n' + Finsupp.single a (n a) := (Finsupp.erase_add_single a n).symm
  have h1 : n.prod (fun _ k => k.factorial) = n'.prod (fun _ k => k.factorial) * (n a).factorial := by
    conv_lhs => rw [hn]
    rw [Finsupp.prod_add_index_of_disjoint (disjoint_single_support hn'a _),
      Finsupp.prod_single_index (by simp)]
  have h2 : (n + e a).prod (fun _ k => k.factorial)
      = n'.prod (fun _ k => k.factorial) * (n a + 1).factorial := by
    have : n + e a = n' + Finsupp.single a (n a + 1) := by
      conv_lhs => rw [hn]
      rw [add_assoc, ← Finsupp.single_add]
    rw [this, Finsupp.prod_add_index_of_disjoint (disjoint_single_support hn'a _),
      Finsupp.prod_single_index (by simp)]
  rw [h2, h1, Nat.factorial_succ]; ring

lemma sqrt_step (A M K : ℕ) (hM : 0 < M) :
    Real.sqrt ((A : ℝ) + 1) * Real.sqrt (((K + 1).factorial : ℝ) / ((M * (A + 1) : ℕ) : ℝ))
      = Real.sqrt ((K : ℝ) + 1) * Real.sqrt ((K.factorial : ℝ) / (M : ℝ)) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
  congr 1
  push_cast [Nat.factorial_succ]
  field_simp

lemma prod_add_e (ξ : ℤ → ℂ) (n : Occ) (a : ℤ) :
    (n + e a).prod (fun b k => ξ b ^ k) = n.prod (fun b k => ξ b ^ k) * ξ a := by
  rw [Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _), Finsupp.prod_single_index (by simp)]
  simp

/-- `b_a Ψ_K = √K ξ_a Ψ_{K-1}`. -/
theorem ann_coh {ξ : ℤ → ℂ} (hξ : (Function.support ξ).Finite) (a : ℤ) (K : ℕ) :
    Ann a (coh hξ K) = (((Real.sqrt (K : ℝ) : ℝ) : ℂ) * ξ a) • coh hξ (K - 1) := by
  ext n
  rw [Ann_apply, Finsupp.smul_apply, coh_apply, coh_apply, smul_eq_mul]
  cases K with
  | zero =>
    have : total (n + e a) ≠ 0 := by rw [total_add_e]; omega
    simp [cohC, this]
  | succ K =>
    simp only [Nat.add_sub_cancel]
    unfold cohC
    by_cases hn : total n = K
    · have hn' : total (n + e a) = K + 1 := by rw [total_add_e, hn]
      simp only [hn, hn', ↓reduceIte]
      rw [prod_add_e, mult_add_single]
      have hM : 0 < OccupationUnitary.multiplicityFactorial n := OccupationUnitary.multiplicityFactorial_pos n
      have key := sqrt_step (n a) (OccupationUnitary.multiplicityFactorial n) K hM
      have key' : ((Real.sqrt ((n a : ℝ) + 1) : ℝ) : ℂ) *
          ((Real.sqrt (((K + 1).factorial : ℝ) /
            ((OccupationUnitary.multiplicityFactorial n * (n a + 1) : ℕ) : ℝ)) : ℝ) : ℂ)
          = ((Real.sqrt ((K : ℝ) + 1) : ℝ) : ℂ) *
            ((Real.sqrt ((K.factorial : ℝ) / (OccupationUnitary.multiplicityFactorial n : ℝ)) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, key]
      push_cast at key' ⊢
      linear_combination (n.prod fun b k => ξ b ^ k) * ξ a * key'
    · have hn' : total (n + e a) ≠ K + 1 := by rw [total_add_e]; omega
      simp [hn, hn']

/-! ### Iterated annihilation and the coherent expectation -/

theorem AnnProd_coh {ξ : ℤ → ℂ} (hξ : (Function.support ξ).Finite) (N : ℕ) (l : List ℤ) :
    AnnProd l (coh hξ N)
      = (((Real.sqrt (fall N l.length : ℝ) : ℝ) : ℂ) * (l.map ξ).prod) • coh hξ (N - l.length) := by
  induction l with
  | nil => simp [AnnProd, fall]
  | cons a l ih =>
    have hf : (fall N (l.length + 1) : ℝ) = (fall N l.length : ℝ) * ((N - l.length : ℕ) : ℝ) := by
      simp [fall, Finset.prod_range_succ]
    rw [AnnProd, Module.End.mul_apply, ih, map_smul, ann_coh, smul_smul, List.length_cons,
      List.map_cons, List.prod_cons, hf, Real.sqrt_mul (Nat.cast_nonneg _)]
    have : N - l.length - 1 = N - (l.length + 1) := by omega
    rw [this]
    congr 1
    push_cast
    ring

lemma labels_map_prod (ξ : ℤ → ℂ) (α : ℤ →₀ ℕ) :
    ((labels α).map ξ).prod = α.prod (fun a k => ξ a ^ k) := by
  unfold labels
  have h1 : (((α.toMultiset).toList.map ξ).prod) = ((α.toMultiset).map ξ).prod := by
    rw [← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]
  rw [h1, Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
    Finsupp.prod_mapDomain_index (by simp) (fun _ _ _ => pow_add _ _ _)]

theorem ip_CreProd (l : List ℤ) (u v : FS) : ip u (CreProd l v) = ip (AnnProd l.reverse u) v := by
  induction l generalizing u with
  | nil => simp [CreProd, AnnProd]
  | cons a l ih =>
    rw [CreProd, Module.End.mul_apply, Cre_adjoint, ih, List.reverse_cons, AnnProd_append]
    simp [AnnProd]

lemma conj_prod_eval (ξ : ℤ → ℂ) (β : ℤ →₀ ℕ) :
    (starRingEnd ℂ) (β.prod (fun a k => ξ a ^ k)) = β.prod (fun a k => (starRingEnd ℂ) (ξ a) ^ k) := by
  unfold Finsupp.prod
  rw [map_prod]
  simp [map_pow]

/-- **`eq:full-coherent-test`** (occupation form; `ip` is conjugate-linear in the first slot):
`⟨Ψ_N, W_N(z^α z̄^β) Ψ_N⟩ = ((N)_d/N^d) ξ^α conj(ξ)^β` for balanced monomials (`d = |α| = |β|`),
given that the coherent vectors are normalised. For `N < d` both sides vanish. -/
theorem coh_expect {ξ : ℤ → ℂ} (hξ : (Function.support ξ).Finite)
    (hnorm : ∀ K, ip (coh hξ K) (coh hξ K) = 1) (α β : ℤ →₀ ℕ) (hdeg : β.degree = α.degree) (N : ℕ) :
    ip (coh hξ N) (WN N (zm α β) (coh hξ N))
      = (((fall N α.degree : ℝ) / (N : ℝ) ^ α.degree : ℝ) : ℂ) * evalMon ξ (α, β) := by
  rw [WN_zm]
  unfold WMono
  rw [LinearMap.smul_apply, Module.End.mul_apply, ip_smul_right]
  unfold CreMono AnnMono
  have hl1 : (labels β).reverse.length = α.degree := by rw [List.length_reverse, labels_length, hdeg]
  have hl2 : (labels α).length = α.degree := labels_length α
  rw [ip_CreProd, AnnProd_coh, AnnProd_coh, ip_smul_left, ip_smul_right, hl1, hl2, hnorm, mul_one,
    List.map_reverse, List.prod_reverse, labels_map_prod, labels_map_prod, map_mul,
    Complex.conj_ofReal, conj_prod_eval]
  unfold evalMon
  have hs : (Real.sqrt (fall N α.degree : ℝ) : ℝ) * (Real.sqrt (fall N α.degree : ℝ)) = (fall N α.degree : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hs' : ((Real.sqrt (fall N α.degree : ℝ) : ℝ) : ℂ) * ((Real.sqrt (fall N α.degree : ℝ) : ℝ) : ℂ)
      = ((fall N α.degree : ℝ) : ℂ) := by rw [← Complex.ofReal_mul, hs]
  rw [inv_pow, Complex.ofReal_div, div_eq_mul_inv]
  push_cast
  linear_combination ((↑N ^ α.degree : ℂ)⁻¹ * (α.prod fun a k => ξ a ^ k) *
    (β.prod fun a k => (starRingEnd ℂ) (ξ a) ^ k)) * hs'

/-! ### The coherent vectors are the occupation images of the actual tensor powers -/

open QuantumNLS.TensorCarrier in
/-- The sector vector with the coherent coefficients. -/
def cohSector {ξ : ℤ → ℂ} (hξ : (Function.support ξ).Finite) (K : ℕ) : Sector K :=
  Finsupp.comapDomain (Subtype.val : Arr K → Occ) (coh hξ K) Subtype.val_injective.injOn

lemma coh_inSector {ξ : ℤ → ℂ} (hξ : (Function.support ξ).Finite) (K : ℕ) :
    InSector K (coh hξ K) := by
  intro m hm
  by_contra h
  have : cohC ξ K m = 0 := by simp [cohC, h]
  exact (Finsupp.mem_support_iff.mp hm) this

lemma emb_cohSector {ξ : ℤ → ℂ} (hξ : (Function.support ξ).Finite) (K : ℕ) :
    emb K (cohSector hξ K) = coh hξ K := by
  ext m
  by_cases hm : ∃ m' : Arr K, m'.1 = m
  · obtain ⟨m', rfl⟩ := hm
    rw [emb_apply]; rfl
  · have h1 : emb K (cohSector hξ K) m = 0 := by
      simp only [emb, Finsupp.lmapDomain_apply]
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨m', hm'⟩
      exact hm ⟨m', hm'⟩
    rw [h1]
    by_contra hne
    have := coh_inSector hξ K m (Finsupp.mem_support_iff.mpr (Ne.symm hne))
    exact hm ⟨⟨m, this⟩, rfl⟩

open QuantumNLS.TensorCarrier in
/-- **Link to U4**: `core (cohSector)` is `U4` of the actual completed tensor power `ξ^{⊗K}`. -/
theorem core_cohSector (ξ : OccupationUnitary.OneParticle) (hξ : (Function.support (ξ : ℤ → ℂ)).Finite)
    (K : ℕ) :
    core K (cohSector hξ K) = OccupationUnitary.U4 K ⟨htpow K ξ, htpow_mem_symSector K ξ⟩ := by
  apply lp.ext
  funext m
  rw [core_apply, OccupationUnitary.U4_htpow]
  have hm : total m.val = K := m.2
  simp only [cohSector, Finsupp.comapDomain_apply, coh_apply, cohC, hm, ↓reduceIte,
    OccupationUnitary.normalization]

open QuantumNLS.TensorCarrier in
theorem coh_ip_self (ξ : OccupationUnitary.OneParticle)
    (hξ : (Function.support (ξ : ℤ → ℂ)).Finite) (h1 : ‖ξ‖ = 1) (K : ℕ) :
    ip (coh hξ K) (coh hξ K) = 1 := by
  have hn : ‖core K (cohSector hξ K)‖ = 1 := by
    rw [core_cohSector ξ hξ K, LinearIsometryEquiv.norm_map]
    change ‖(htpow K ξ : HilbertTensorPower ℂ OccupationUnitary.OneParticle K)‖ = 1
    rw [norm_htpow, h1, one_pow]
  have h2 : ip (coh hξ K) (coh hξ K) = ipS K (cohSector hξ K) (cohSector hξ K) := by
    unfold ipS; rw [emb_cohSector]
  rw [h2, ← inner_core, inner_self_eq_norm_sq_to_K, hn]
  simp

/-! ### Polynomial expectation and factorial asymptotics -/

lemma ip_sum_right {ι : Type*} (s : Finset ι) (f : ι → FS) (u : FS) :
    ip u (∑ i ∈ s, f i) = ∑ i ∈ s, ip u (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ip_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ip_add_right, ih]

lemma evalSym_expand (z : ℤ → ℂ) (f : Sym) :
    evalSym z f = ∑ p ∈ f.coeff.support, f.coeff p * evalMon z p :=
  (symLin_expand _ f).trans (Finset.sum_congr rfl (fun p _ => by simp))

/-- **Coherent expectation of a balanced polynomial Wick operator**. -/
theorem coh_expect_poly {ξ : ℤ → ℂ} (hξ : (Function.support ξ).Finite)
    (hnorm : ∀ K, ip (coh hξ K) (coh hξ K) = 1) {f : Sym} (hb : Balanced f) (N : ℕ) :
    ip (coh hξ N) (WN N f (coh hξ N))
      = ∑ p ∈ f.coeff.support, f.coeff p *
          ((((fall N p.1.degree : ℝ) / (N : ℝ) ^ p.1.degree : ℝ) : ℂ) * evalMon ξ p) := by
  have e : WN N f = ∑ p ∈ f.coeff.support, f.coeff p • WMono N p.1 p.2 :=
    symLin_expand _ f
  rw [e, LinearMap.sum_apply, ip_sum_right]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [LinearMap.smul_apply, ip_smul_right]
  congr 1
  rw [← WN_zm]
  exact coh_expect hξ hnorm p.1 p.2 (hb p hp).symm N

/-- Factorial asymptotics: `(N)_d / N^d → 1`. -/
theorem fall_ratio_tendsto (d : ℕ) :
    Tendsto (fun N : ℕ => (fall N d : ℝ) / (N : ℝ) ^ d) atTop (nhds 1) := by
  have hev : ∀ᶠ N : ℕ in atTop, (fall N d : ℝ) / (N : ℝ) ^ d
      = ∏ j ∈ Finset.range d, (1 - (j : ℝ) * (N : ℝ)⁻¹) := by
    filter_upwards [Filter.eventually_ge_atTop (d + 1)] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    unfold fall
    rw [Nat.cast_prod, show ((N : ℝ) ^ d) = ∏ _j ∈ Finset.range d, (N : ℝ) by simp,
      ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl (fun j hj => ?_)
    have hj' : j ≤ N := by have := Finset.mem_range.mp hj; omega
    rw [Nat.cast_sub hj']
    field_simp
  have h0 : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => ∏ j ∈ Finset.range d, (1 - (j : ℝ) * (N : ℝ)⁻¹)) atTop (nhds 1) := by
    have := tendsto_finsetProd (Finset.range d)
      (fun j _ => (tendsto_const_nhds (x := (1 : ℝ))).sub (h0.const_mul (j : ℝ)))
    simpa using this
  exact hlim.congr' (hev.mono fun N h => h.symm)

/-- The coherent expectation of a balanced polynomial tends to the classical value. -/
theorem coh_expect_tendsto {ξ : ℤ → ℂ} (hξ : (Function.support ξ).Finite)
    (hnorm : ∀ K, ip (coh hξ K) (coh hξ K) = 1) {f : Sym} (hb : Balanced f) :
    Tendsto (fun N : ℕ => ip (coh hξ N) (WN N f (coh hξ N))) atTop (nhds (evalSym ξ f)) := by
  simp only [coh_expect_poly hξ hnorm hb, evalSym_expand]
  refine tendsto_finsetSum _ (fun p _ => ?_)
  have h := (Complex.continuous_ofReal.tendsto 1).comp (fall_ratio_tendsto p.1.degree)
  simpa using (h.mul_const (evalMon ξ p)).const_mul (f.coeff p)

/-! ### Hilbert-space lower bound (arbitrary gauge via inverse-gauge conjugation) -/

lemma norm_WHil_le_WHilq (N : ℕ) (q : Occ → ℂ) (hq : UnitGauge q) (h : Sym) :
    ‖WHil N h‖ ≤ ‖WHilq N q hq h‖ := by
  have e : WHil N h = gauge N q hq * WHilq N q hq h
      * gauge N (fun m => (starRingEnd ℂ) (q m)) (unitGauge_conj hq) := by
    unfold WHilq
    calc WHil N h = (gauge N q hq * gauge N (fun m => (starRingEnd ℂ) (q m)) (unitGauge_conj hq))
          * WHil N h * (gauge N q hq * gauge N (fun m => (starRingEnd ℂ) (q m)) (unitGauge_conj hq)) := by
          rw [gauge_mul_conj]; simp
      _ = _ := by simp only [mul_assoc]
  calc ‖WHil N h‖ = ‖gauge N q hq * WHilq N q hq h
        * gauge N (fun m => (starRingEnd ℂ) (q m)) (unitGauge_conj hq)‖ := by rw [← e]
    _ ≤ ‖gauge N q hq‖ * ‖WHilq N q hq h‖ * ‖gauge N (fun m => (starRingEnd ℂ) (q m)) (unitGauge_conj hq)‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖WHilq N q hq h‖ * 1 :=
        mul_le_mul (mul_le_mul (gauge_norm_le _ _ _) le_rfl (norm_nonneg _) zero_le_one)
          (gauge_norm_le _ _ _) (norm_nonneg _) (by positivity)
    _ = ‖WHilq N q hq h‖ := by ring

open QuantumNLS.TensorCarrier in
lemma norm_core_cohSector (ξ : OccupationUnitary.OneParticle)
    (hξ : (Function.support (ξ : ℤ → ℂ)).Finite) (h1 : ‖ξ‖ = 1) (K : ℕ) :
    ‖core K (cohSector hξ K)‖ = 1 := by
  rw [core_cohSector ξ hξ K, LinearIsometryEquiv.norm_map]
  change ‖(htpow K ξ : HilbertTensorPower ℂ OccupationUnitary.OneParticle K)‖ = 1
  rw [norm_htpow, h1, one_pow]

/-- The coherent expectation is bounded by the operator norm (`N ≥ 1`, balanced `f`). -/
theorem coh_expect_le {ξ : OccupationUnitary.OneParticle}
    (hξ : (Function.support (ξ : ℤ → ℂ)).Finite) (h1 : ‖ξ‖ = 1) {f : Sym} (hb : Balanced f)
    {N : ℕ} (hN : 0 < N) :
    ‖ip (coh hξ N) (WN N f (coh hξ N))‖ ≤ ‖WHil N f‖ := by
  set v := cohSector hξ N with hv
  have hn := norm_core_cohSector ξ hξ h1 N
  have e : ip (coh hξ N) (WN N f (coh hξ N)) = inner ℂ (core N v) (WHil N f (core N v)) := by
    rw [WHil_core hN hb, inner_core]
    unfold ipS
    rw [emb_WS hb, emb_cohSector]
  rw [e]
  calc ‖inner ℂ (core N v) (WHil N f (core N v))‖ ≤ ‖core N v‖ * ‖WHil N f (core N v)‖ :=
        norm_inner_le_norm _ _
    _ ≤ ‖core N v‖ * (‖WHil N f‖ * ‖core N v‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = ‖WHil N f‖ := by rw [hn]; ring

/-- Uniform bound of the Wick operator norms (including the conventional `N = 0` term). -/
lemma WHilq_bounded (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) {f : Sym} (hb : Balanced f) :
    ∃ M : ℝ, ∀ N : ℕ, ‖WHilq N (q N) (hq N) f‖ ≤ M := by
  refine ⟨max ‖WHilq 0 (q 0) (hq 0) f‖ (coeffNorm f), fun N => ?_⟩
  by_cases hN : N = 0
  · subst hN; exact le_max_left _ _
  · exact (WHilq_norm_le (Nat.pos_of_ne_zero hN) (q N) (hq N) hb).trans (le_max_right _ _)

/-- **Coherent-state lower bound**: for every finitely supported unit vector `ξ ∈ ℓ²(ℤ)` and every
balanced polynomial symbol `f`, `|f(ξ)| ≤ liminf_N ‖W^q_N(f)‖`, for any supplied unit-modulus
gauge family. The test vectors are the occupation images of `ξ^{⊗N}` (`U4_htpow`), conjugated
by the inverse gauge (norm invariance, `norm_WHil_le_WHilq`). -/
theorem coherent_lower_bound (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N))
    {ξ : OccupationUnitary.OneParticle} (hξ : (Function.support (ξ : ℤ → ℂ)).Finite) (h1 : ‖ξ‖ = 1)
    {f : Sym} (hb : Balanced f) :
    ‖evalSym (ξ : ℤ → ℂ) f‖ ≤ liminf (fun N => ‖WHilq N (q N) (hq N) f‖) atTop := by
  have hnorm := coh_ip_self ξ hξ h1
  have hT : Tendsto (fun N : ℕ => ‖ip (coh hξ N) (WN N f (coh hξ N))‖) atTop
      (nhds ‖evalSym (ξ : ℤ → ℂ) f‖) := (coh_expect_tendsto hξ hnorm hb).norm
  have hle : ∀ᶠ N : ℕ in atTop,
      ‖ip (coh hξ N) (WN N f (coh hξ N))‖ ≤ ‖WHilq N (q N) (hq N) f‖ := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact (coh_expect_le hξ h1 hb hN).trans (norm_WHil_le_WHilq N (q N) (hq N) f)
  obtain ⟨M, hM⟩ := WHilq_bounded q hq hb
  rw [← hT.liminf_eq]
  exact Filter.liminf_le_liminf hle
    (Filter.isBoundedUnder_of ⟨0, fun N => norm_nonneg _⟩)
    (Filter.isCoboundedUnder_ge_of_le atTop (x := M) hM)

/-! ### Unit test vectors from points of `ℂ^I` -/

lemma evalSym_congr (I : Finset ℤ) {f : Sym} (hI : LabelsIn I f) {ξ₁ ξ₂ : ℤ → ℂ}
    (h : ∀ a ∈ I, ξ₁ a = ξ₂ a) : evalSym ξ₁ f = evalSym ξ₂ f := by
  rw [evalSym_expand, evalSym_expand]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  congr 1
  unfold evalMon
  congr 1
  · apply Finsupp.prod_congr
    intro a ha
    rw [h a (hI p hp a (Or.inl (Finsupp.mem_support_iff.mp ha)))]
  · apply Finsupp.prod_congr
    intro a ha
    rw [h a (hI p hp a (Or.inr (Finsupp.mem_support_iff.mp ha)))]

lemma lc_apply (c : ℤ →₀ ℂ) (b : ℤ) :
    (Finsupp.linearCombination ℂ OccupationUnitary.oneBasis c : OccupationUnitary.OneParticle) b = c b := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add u u' hu hu' => simp [hu, hu']
  | single a r =>
    simp only [Finsupp.linearCombination_single, OccupationUnitary.oneBasis_apply]
    by_cases h : a = b
    · subst h; simp
    · simp [lp.single_apply, h]

/-- A finitely supported unit vector of `ℓ²(ℤ)` extending a point `z` of the closed unit ball of
`ℂ^I` (the extra label carries `√(1 − ‖z‖²)`). -/
theorem exists_unit_extension (I : Finset ℤ) (z : EuclideanSpace ℂ I) (hz : ‖z‖ ≤ 1) :
    ∃ ξ : OccupationUnitary.OneParticle, (Function.support (ξ : ℤ → ℂ)).Finite ∧ ‖ξ‖ = 1 ∧
      ∀ a ∈ I, (ξ : ℤ → ℂ) a = zext I z a := by
  classical
  obtain ⟨e, he⟩ := Infinite.exists_notMem_finset I
  set r : ℝ := Real.sqrt (1 - ‖z‖ ^ 2) with hr
  set c : ℤ →₀ ℂ := Finsupp.onFinset (insert e I)
    (fun a => if a ∈ I then zext I z a else if a = e then (r : ℂ) else 0) (by
      intro a ha
      by_contra h
      rw [Finset.mem_insert, not_or] at h
      simp [h.1, h.2] at ha) with hc
  have hca : ∀ a ∈ I, c a = zext I z a := by
    intro a ha; simp [hc, Finsupp.onFinset_apply, ha]
  have hce : c e = r := by simp [hc, Finsupp.onFinset_apply, he]
  have hsupp : c.support ⊆ insert e I := Finsupp.support_onFinset_subset
  refine ⟨Finsupp.linearCombination ℂ OccupationUnitary.oneBasis c, ?_, ?_, ?_⟩
  · refine (Finset.finite_toSet c.support).subset ?_
    intro b hb
    rw [Function.mem_support, lc_apply] at hb
    exact Finsupp.mem_support_iff.mpr hb
  · have hin := OccupationUnitary.oneBasis.orthonormal.inner_finsupp_eq_sum_left c c
    rw [Finsupp.sum_of_support_subset c hsupp _ (by simp), Finset.sum_insert he] at hin
    have hsum : ∑ a ∈ I, (starRingEnd ℂ) (c a) * c a = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
      have h1 : ∑ a ∈ I, (starRingEnd ℂ) (c a) * c a = ∑ a ∈ I, (starRingEnd ℂ) (zext I z a) * zext I z a :=
        Finset.sum_congr rfl (fun a ha => by rw [hca a ha])
      rw [h1, ← Finset.sum_coe_sort I, EuclideanSpace.norm_sq_eq]
      push_cast
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have : zext I z (i : ℤ) = z i := by simp [zext, i.2]
      rw [this, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      push_cast; rfl
    have hr2 : (starRingEnd ℂ) (c e) * c e = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by
      rw [hce, Complex.conj_ofReal, ← Complex.ofReal_mul, hr, Real.mul_self_sqrt (by nlinarith [norm_nonneg z])]
    rw [hsum, hr2] at hin
    have h2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ)
      (Finsupp.linearCombination ℂ OccupationUnitary.oneBasis c)
    rw [hin] at h2
    have h3 := congrArg Complex.re h2
    simp [sq] at h3
    nlinarith [norm_nonneg (Finsupp.linearCombination ℂ OccupationUnitary.oneBasis c)]
  · intro a ha
    rw [lc_apply, hca a ha]

/-! ### Lower bound on the unit ball and the norm limit -/

/-- Every point of the closed unit ball of `ℂ^I` gives a lower bound. -/
theorem lower_bound_ball (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (I : Finset ℤ) {f : Sym}
    (hb : Balanced f) (hI : LabelsIn I f) (z : EuclideanSpace ℂ I) (hz : ‖z‖ ≤ 1) :
    ‖evalSym (zext I z) f‖ ≤ liminf (fun N => ‖WHilq N (q N) (hq N) f‖) atTop := by
  obtain ⟨ξ, hfin, h1, hag⟩ := exists_unit_extension I z hz
  have := coherent_lower_bound q hq hfin h1 hb
  rwa [evalSym_congr I hI hag] at this

/-- The unit-ball supremum of the classical Wick symbol is below the liminf of the operator norms. -/
theorem unitBallSup_le_liminf (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (I : Finset ℤ)
    {f : Sym} (hb : Balanced f) (hI : LabelsIn I f) :
    SpectralUpperBound.unitBallSup I (fun z => evalSym (zext I z) f)
      ≤ liminf (fun N => ‖WHilq N (q N) (hq N) f‖) atTop := by
  unfold SpectralUpperBound.unitBallSup
  apply csSup_le
  · exact ⟨_, 0, Metric.mem_closedBall_self zero_le_one, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact lower_bound_ball q hq I hb hI z (by simpa using hz)

/-- **Norm limit for balanced Wick polynomials** (`eq:full-norm-limit`): for a balanced polynomial
symbol `f` with labels in `I` and ANY supplied unit-modulus gauge family `q N`,
`‖W^q_N(f)‖ → sup_{‖z‖≤1} |f(z)|`, the supremum of the classical Wick symbol over the unit ball of
`ℂ^I`. Upper half: ordered-word comparison with the Gelfand/character upper bound
(`wick_balanced_limsup_le`); lower half: coherent states `U4(ξ^{⊗N})`. No Bethe gauge is
selected. -/
theorem wick_balanced_norm_limit (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (I : Finset ℤ)
    {f : Sym} (hb : Balanced f) (hI : LabelsIn I f) :
    Tendsto (fun N => ‖WHilq N (q N) (hq N) f‖) atTop
      (nhds (SpectralUpperBound.unitBallSup I (fun z => evalSym (zext I z) f))) := by
  obtain ⟨M, hM⟩ := WHilq_bounded q hq hb
  exact tendsto_of_le_liminf_of_limsup_le (unitBallSup_le_liminf q hq I hb hI)
    (wick_balanced_limsup_le q hq I hb hI)
    (Filter.isBoundedUnder_of ⟨M, hM⟩) (Filter.isBoundedUnder_of ⟨0, fun N => norm_nonneg _⟩)

/-! Axiom audit (printed at compile time). -/
#print axioms cohC_support_finite
#print axioms Ann_apply
#print axioms mult_add_single
#print axioms ann_coh
#print axioms AnnProd_coh
#print axioms labels_map_prod
#print axioms ip_CreProd
#print axioms coh_expect
#print axioms core_cohSector
#print axioms coh_ip_self
#print axioms coh_expect_poly
#print axioms fall_ratio_tendsto
#print axioms coh_expect_tendsto
#print axioms norm_WHil_le_WHilq
#print axioms coh_expect_le
#print axioms coherent_lower_bound
#print axioms evalSym_congr
#print axioms exists_unit_extension
#print axioms lower_bound_ball
#print axioms unitBallSup_le_liminf
#print axioms wick_balanced_norm_limit

end

end QuantumNLS.CoherentLowerBound
