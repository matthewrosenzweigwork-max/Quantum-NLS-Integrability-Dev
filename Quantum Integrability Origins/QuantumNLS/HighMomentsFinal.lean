import QuantumNLS.HighMomentsAssembly

/-!
# PROP-008 `lem:B4-high-moments` (`spectral_calculus.tex:24-60`): the centered high moments of a normal
summable interaction series

Hypotheses of the printed lemma: `u` a unit vector, `A_r` bounded on `Sym^r H`, `Σ_r r^m ‖A_r‖ < ∞` for every
`m`, `X_N = A_0 Id + Σ_{r=1}^N (N)_r/N^r U_{N,r}(A_r)` (`Xop`) normal on `Sym^N H`, `x = A_0 + Σ_r a_r`
(`xlim`), `a_r = ⟨u^{⊗r}, A_r u^{⊗r}⟩`.

`high_moments`: for every `p ≥ 1` and `N ≥ 1`,
`⟨u^{⊗N}, |X_N − x|^{2p} u^{⊗N}⟩ = ‖(X_N − x)^p u^{⊗N}‖² ≤ C_p N^{-p}`, where `|Z|^{2p} = (Z^*Z)^p` and

`C_p = (p+1) Σ_{k=0}^p C(p,k)² (S₂ + S₁)^{2(p−k)} (2k)^{2k} (2 S_{4k})^{2k}`,  `S_q = Σ_{r≥1} r^q ‖A_r‖`,

which depends only on `p` and the finitely many rank sums `S₁, S₂, S₄, S₈, …, S_{4p}` (hence is uniform over any
parameter family on which these are uniformly bounded).  Route: `X_N − x = Y_N + b_N` exactly (stage A),
`|b_N| ≤ (S₂+S₁)/N`, `⟨u^N, (Y_N^*)^k Y_N^k u^N⟩ ≤ (2k)^{2k}(2S_{4k})^{2k} N^{-k}` (stage B: word algebra,
isolated-vertex vanishing, counting), normality `(Z^*Z)^p = (Z^*)^p Z^p`, binomial expansion of
`(Y+b)^p`, Cauchy–Schwarz.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements QuantumNLS.KernelDefinition
  QuantumNLS.PlacementGrouping QuantumNLS.RootOverlapCommutator QuantumNLS.RootOverlapLimit
  QuantumNLS.HighMomentsWord QuantumNLS.HighMomentsOps QuantumNLS.HighMomentsRank
  QuantumNLS.HighMomentsCount QuantumNLS.HighMomentsAssembly

namespace QuantumNLS.HighMomentsFinal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem aa_adjFam (u : H) (A : ∀ r : ℕ, BoundedSymmetricKernel H r) (r : ℕ) :
    aa u (adjFam A) r = (starRingEnd ℂ) (aa u A r) := by
  unfold aa kernelProductSymbol adjFam
  show ⟪wvec r u, ContinuousLinearMap.adjoint (A r) (wvec r u)⟫_ℂ = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm (A r (wvec r u)) (wvec r u)).symm

theorem isAdj_Tf (u : H) (A : ∀ r : ℕ, BoundedSymmetricKernel H r) (N : ℕ) (s : Finset (Fin N)) :
    IsAdj (Tf u A N s) (Tf u (adjFam A) N s) := by
  unfold Tf
  rw [aa_adjFam]
  exact (Pl_adj A s).sub ((IsAdj.one).smul _)

theorem isAdj_Yfull (u : H) (A : ∀ r : ℕ, BoundedSymmetricKernel H r) (N : ℕ) :
    IsAdj (Yfull u A N) (Yfull u (adjFam A) N) := by
  rw [Yfull_eq_sum, Yfull_eq_sum]
  refine IsAdj.sum _ _ _ (fun s _ => ?_)
  have := (isAdj_Tf u A N s).smul ((wt N s : ℝ) : ℂ)
  rwa [Complex.conj_ofReal] at this

theorem norm_adjFam (A : ∀ r : ℕ, BoundedSymmetricKernel H r) (r : ℕ) :
    ‖adjFam A r‖ = ‖A r‖ := by
  unfold adjFam
  exact LinearIsometryEquiv.norm_map _ _

theorem coe_Yop_pow (u : H) (A : ∀ r : ℕ, BoundedSymmetricKernel H r) (N : ℕ) (k : ℕ)
    (x : SymSector ℂ H N) :
    (((Yop u A N ^ k) x : SymSector ℂ H N) : HilbertTensorPower ℂ H N) =
      (Yfull u A N ^ k) (x : HilbertTensorPower ℂ H N) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    show (((Yop u A N ^ k) (Yop u A N x) : SymSector ℂ H N) : HilbertTensorPower ℂ H N) =
      (Yfull u A N ^ k) (Yfull u A N (x : HilbertTensorPower ℂ H N))
    rw [ih, coe_Yop]

/-- Second moment of `Y^k`: `‖Y^k u^N‖² ≤ (2k)^{2k} (2S)^{2k} / N^k`. -/
theorem Yk_bound {N : ℕ} (hN : 0 < N) (k : ℕ) (hk : 1 ≤ k) (u : H) (hu : ‖u‖ = 1)
    (A : ∀ r : ℕ, BoundedSymmetricKernel H r) (S : ℝ)
    (hS : HasSum (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ (2 * (k + k)) * ‖A (j + 1)‖) S) :
    ‖(Yfull u A N ^ k) (htpow N u : HilbertTensorPower ℂ H N)‖ ^ 2 ≤
      (((2 * k) ^ (2 * k) : ℕ) : ℝ) * (2 * S) ^ (2 * k) / (N : ℝ) ^ k := by
  set v : HilbertTensorPower ℂ H N := htpow N u with hv
  have hadj := (isAdj_Yfull u A N).pow k
  have hword : ⟪v, wprod (k + k) (Fin.append (fun _ : Fin k => Yfull u (adjFam A) N)
      (fun _ : Fin k => Yfull u A N)) v⟫_ℂ =
      ⟪(Yfull u A N ^ k) v, (Yfull u A N ^ k) v⟫_ℂ := by
    rw [wprod_append, wprod_const, wprod_const]
    show ⟪v, (Yfull u (adjFam A) N ^ k) ((Yfull u A N ^ k) v)⟫_ℂ = _
    rw [← hadj]
  have hb := word_bound hN k (by ring) (by omega : 1 ≤ k) u hu A
    (Fin.append (fun _ : Fin k => adjFam A) (fun _ : Fin k => A))
    (by
      intro j r
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp only [Fin.append_left, norm_adjFam, le_refl]
      · simp only [Fin.append_right, le_refl]) S hS
    (Fin.append (fun _ : Fin k => Yfull u (adjFam A) N) (fun _ : Fin k => Yfull u A N))
    (by
      intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · rw [Fin.append_left, Fin.append_left]
      · rw [Fin.append_right, Fin.append_right])
  rw [hword] at hb
  have hsq : ⟪(Yfull u A N ^ k) v, (Yfull u A N ^ k) v⟫_ℂ =
      (((‖(Yfull u A N ^ k) v‖ ^ 2 : ℝ)) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [hsq, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at hb
  have h2 : (k + k : ℕ) = 2 * k := by ring
  rw [h2] at hb
  exact hb

/-- The rank sums `S_q = Σ_{r ≥ 1} r^q ‖A_r‖`. -/
def Sq (A : ∀ r : ℕ, BoundedSymmetricKernel H r) (q : ℕ) : ℝ :=
  ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ q * ‖A (j + 1)‖

/-- The constant `(2k)^{2k} (2 S_{4k})^{2k}` of the `2k`-word bound. -/
def Dk (A : ∀ r : ℕ, BoundedSymmetricKernel H r) (k : ℕ) : ℝ :=
  (((2 * k) ^ (2 * k) : ℕ) : ℝ) * (2 * Sq A (2 * (k + k))) ^ (2 * k)

/-- The constant `C_p` of the lemma. -/
def Cp (A : ∀ r : ℕ, BoundedSymmetricKernel H r) (p : ℕ) : ℝ :=
  ((p : ℝ) + 1) * ∑ k ∈ Finset.range (p + 1),
    ((p.choose k : ℝ) ^ 2 * (Sq A 2 + Sq A 1) ^ (2 * (p - k)) * Dk A k)

/-- `Z = X_N − x · Id` on `Sym^N H`. -/
def Zop (u : H) (A0 : ℂ) (A : ∀ r : ℕ, BoundedSymmetricKernel H r) (N : ℕ) :
    SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  Xop A0 A N - xlim u A0 A • (1 : SymSector ℂ H N →L[ℂ] SymSector ℂ H N)

theorem Sq_nonneg (A : ∀ r : ℕ, BoundedSymmetricKernel H r) (q : ℕ) : 0 ≤ Sq A q :=
  tsum_nonneg (fun j => by positivity)

theorem hasSum_Sq (A : ∀ r : ℕ, BoundedSymmetricKernel H r)
    (hsum : ∀ q : ℕ, Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ q * ‖A (j + 1)‖)) (q : ℕ) :
    HasSum (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ q * ‖A (j + 1)‖) (Sq A q) :=
  (hsum q).hasSum

theorem norm_wvec (u : H) (hu : ‖u‖ = 1) (N : ℕ) : ‖wvec N u‖ = 1 := by
  rw [← Submodule.norm_coe]
  show ‖(htpow N u : HilbertTensorPower ℂ H N)‖ = 1
  rw [norm_htpow, hu, one_pow]

theorem Yk_sym_bound {N : ℕ} (hN : 0 < N) (k : ℕ) (u : H) (hu : ‖u‖ = 1)
    (A : ∀ r : ℕ, BoundedSymmetricKernel H r)
    (hsum : ∀ q : ℕ, Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ q * ‖A (j + 1)‖)) :
    ‖(Yop u A N ^ k) (wvec N u)‖ ^ 2 ≤ Dk A k / (N : ℝ) ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [Dk, norm_wvec u hu]
  · have h1 := Yk_bound hN k hk u hu A (Sq A (2 * (k + k))) (hasSum_Sq A hsum _)
    have h2 : ‖(Yop u A N ^ k) (wvec N u)‖ = ‖(Yfull u A N ^ k) (htpow N u : HilbertTensorPower ℂ H N)‖ := by
      rw [← Submodule.norm_coe, coe_Yop_pow]
      rfl
    rw [h2]
    exact h1

theorem smul_one_pow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (b : ℂ) (n : ℕ) (x : E) :
    ((b • (1 : E →L[ℂ] E)) ^ n) x = b ^ n • x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ContinuousLinearMap.mul_apply, ih, pow_succ]
    simp [smul_smul, mul_comm]

theorem Zop_eq (u : H) (hu : ‖u‖ = 1) (A0 : ℂ) (A : ∀ r : ℕ, BoundedSymmetricKernel H r)
    (hsum : ∀ q : ℕ, Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ q * ‖A (j + 1)‖)) (N : ℕ) :
    Zop u A0 A N = Yop u A N + bN u A N • (1 : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) := by
  have h1 : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ‖A (j + 1)‖) := by
    simpa using hsum 1
  exact centered_identity u A0 A N (summable_aa u hu A h1)

/-- **`lem:B4-high-moments`** (PROP-008). -/
theorem high_moments (u : H) (hu : ‖u‖ = 1) (A0 : ℂ) (A : ∀ r : ℕ, BoundedSymmetricKernel H r)
    (hsum : ∀ q : ℕ, Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ q * ‖A (j + 1)‖))
    (N : ℕ) (hN : 0 < N)
    (hnormal : Commute (ContinuousLinearMap.adjoint (Zop u A0 A N)) (Zop u A0 A N))
    (p : ℕ) (hp : 1 ≤ p) :
    ⟪wvec N u, ((ContinuousLinearMap.adjoint (Zop u A0 A N) * Zop u A0 A N) ^ p) (wvec N u)⟫_ℂ =
        ((‖(Zop u A0 A N ^ p) (wvec N u)‖ ^ 2 : ℝ) : ℂ) ∧
      ‖(Zop u A0 A N ^ p) (wvec N u)‖ ^ 2 ≤ Cp A p / (N : ℝ) ^ p := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  constructor
  · rw [hnormal.mul_pow]
    have : (ContinuousLinearMap.adjoint (Zop u A0 A N)) ^ p =
        ContinuousLinearMap.adjoint (Zop u A0 A N ^ p) := by
      rw [← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint, star_pow]
    rw [this]
    show ⟪wvec N u, (ContinuousLinearMap.adjoint (Zop u A0 A N ^ p))
      ((Zop u A0 A N ^ p) (wvec N u))⟫_ℂ = _
    rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    norm_cast
  · -- bias
    have hb : ‖bN u A N‖ ≤ (Sq A 2 + Sq A 1) / N := by
      have h1 : HasSum (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ‖A (j + 1)‖) (Sq A 1) := by
        have := hasSum_Sq A hsum 1
        simpa using this
      exact norm_bN_le u hu A (Sq A 1) (Sq A 2) h1 (hasSum_Sq A hsum 2) N hN
    set β : ℝ := Sq A 2 + Sq A 1 with hβ
    have hβ0 : 0 ≤ β := add_nonneg (Sq_nonneg A 2) (Sq_nonneg A 1)
    -- binomial expansion
    have hcomm : Commute (Yop u A N) (bN u A N • (1 : SymSector ℂ H N →L[ℂ] SymSector ℂ H N)) := by
      show Yop u A N * (bN u A N • (1 : SymSector ℂ H N →L[ℂ] SymSector ℂ H N)) =
        (bN u A N • (1 : SymSector ℂ H N →L[ℂ] SymSector ℂ H N)) * Yop u A N
      ext x
      simp
    have hexp : (Zop u A0 A N ^ p) (wvec N u) = ∑ k ∈ Finset.range (p + 1),
        ((p.choose k : ℂ) * (bN u A N) ^ (p - k)) • (Yop u A N ^ k) (wvec N u) := by
      rw [Zop_eq u hu A0 A hsum N, hcomm.add_pow', ContinuousLinearMap.sum_apply,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      show (p.choose k • (Yop u A N ^ k * (bN u A N • (1 : SymSector ℂ H N →L[ℂ] SymSector ℂ H N)) ^ (p - k)))
        (wvec N u) = _
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply, smul_one_pow, map_smul,
        mul_smul, Nat.cast_smul_eq_nsmul]
    set a : ℕ → ℝ := fun k => (p.choose k : ℝ) * ‖bN u A N‖ ^ (p - k) * ‖(Yop u A N ^ k) (wvec N u)‖
      with ha
    have hnorm : ‖(Zop u A0 A N ^ p) (wvec N u)‖ ≤ ∑ k ∈ Finset.range (p + 1), a k := by
      rw [hexp]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
      rw [norm_smul, norm_mul, norm_pow]
      simp only [ha, Complex.norm_natCast, le_refl]
    have ha0 : ∀ k, 0 ≤ a k := fun k => by simp only [ha]; positivity
    have hsq : ‖(Zop u A0 A N ^ p) (wvec N u)‖ ^ 2 ≤
        ((p : ℝ) + 1) * ∑ k ∈ Finset.range (p + 1), (a k) ^ 2 := by
      have h1 : ‖(Zop u A0 A N ^ p) (wvec N u)‖ ^ 2 ≤ (∑ k ∈ Finset.range (p + 1), a k) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      refine h1.trans ?_
      have := sq_sum_le_card_mul_sum_sq (s := Finset.range (p + 1)) (f := a)
      simpa using this
    refine hsq.trans ?_
    unfold Cp
    rw [mul_div_assoc, Finset.sum_div]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine Finset.sum_le_sum (fun k hk => ?_)
    have hkp : k ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hY := Yk_sym_bound hN k u hu A hsum
    have hD0 : 0 ≤ Dk A k := by
      unfold Dk
      have := Sq_nonneg A (2 * (k + k))
      positivity
    have hbb : ‖bN u A N‖ ^ (p - k) ≤ (β / N) ^ (p - k) := pow_le_pow_left₀ (norm_nonneg _) hb _
    have hak : (a k) ^ 2 = (p.choose k : ℝ) ^ 2 * (‖bN u A N‖ ^ (p - k)) ^ 2 *
        ‖(Yop u A N ^ k) (wvec N u)‖ ^ 2 := by
      simp only [ha]; ring
    rw [hak]
    have hb2 : (‖bN u A N‖ ^ (p - k)) ^ 2 ≤ ((β / N) ^ (p - k)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hbb 2
    have hmul : (‖bN u A N‖ ^ (p - k)) ^ 2 * ‖(Yop u A N ^ k) (wvec N u)‖ ^ 2 ≤
        ((β / N) ^ (p - k)) ^ 2 * (Dk A k / (N : ℝ) ^ k) :=
      mul_le_mul hb2 hY (by positivity) (by positivity)
    have hfin : ((β / N) ^ (p - k)) ^ 2 * (Dk A k / (N : ℝ) ^ k) ≤
        β ^ (2 * (p - k)) * Dk A k / (N : ℝ) ^ p := by
      have e1 : ((β / N) ^ (p - k)) ^ 2 * (Dk A k / (N : ℝ) ^ k) =
          β ^ (2 * (p - k)) * Dk A k / ((N : ℝ) ^ (2 * (p - k)) * (N : ℝ) ^ k) := by
        have hN0 : (N : ℝ) ≠ 0 := hNr.ne'
        have h2 : ((β / N) ^ (p - k)) ^ 2 = β ^ (2 * (p - k)) / (N : ℝ) ^ (2 * (p - k)) := by
          rw [← pow_mul, mul_comm (p - k) 2, div_pow]
        rw [h2]
        field_simp
      rw [e1]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      rw [← pow_add]
      exact pow_le_pow_right₀ hN1 (by omega)
    calc (p.choose k : ℝ) ^ 2 * (‖bN u A N‖ ^ (p - k)) ^ 2 * ‖(Yop u A N ^ k) (wvec N u)‖ ^ 2
        = (p.choose k : ℝ) ^ 2 * ((‖bN u A N‖ ^ (p - k)) ^ 2 *
            ‖(Yop u A N ^ k) (wvec N u)‖ ^ 2) := by ring
      _ ≤ (p.choose k : ℝ) ^ 2 * (β ^ (2 * (p - k)) * Dk A k / (N : ℝ) ^ p) :=
          mul_le_mul_of_nonneg_left (hmul.trans hfin) (by positivity)
      _ = _ := by ring

theorem adjoint_shift {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (X : E →L[ℂ] E) (c : ℂ) :
    ContinuousLinearMap.adjoint (X - c • (1 : E →L[ℂ] E)) =
      ContinuousLinearMap.adjoint X - (starRingEnd ℂ) c • (1 : E →L[ℂ] E) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    ContinuousLinearMap.adjoint_inner_left]

theorem normal_shift {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (X : E →L[ℂ] E) (c : ℂ) (h : Commute (ContinuousLinearMap.adjoint X) X) :
    Commute (ContinuousLinearMap.adjoint (X - c • (1 : E →L[ℂ] E))) (X - c • (1 : E →L[ℂ] E)) := by
  rw [adjoint_shift]
  have h' : ∀ x : E, ContinuousLinearMap.adjoint X (X x) = X (ContinuousLinearMap.adjoint X x) :=
    fun x => congrArg (fun T : E →L[ℂ] E => T x) h.eq
  show (ContinuousLinearMap.adjoint X - (starRingEnd ℂ) c • (1 : E →L[ℂ] E)) *
      (X - c • (1 : E →L[ℂ] E)) = (X - c • (1 : E →L[ℂ] E)) *
      (ContinuousLinearMap.adjoint X - (starRingEnd ℂ) c • (1 : E →L[ℂ] E))
  ext x
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, map_sub, map_smul, h' x]
  module

/-- **`lem:B4-high-moments`** with the hypothesis stated on `X_N` itself: `X_N` normal. -/
theorem high_moments_of_normal (u : H) (hu : ‖u‖ = 1) (A0 : ℂ)
    (A : ∀ r : ℕ, BoundedSymmetricKernel H r)
    (hsum : ∀ q : ℕ, Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ q * ‖A (j + 1)‖))
    (N : ℕ) (hN : 0 < N)
    (hX : Commute (ContinuousLinearMap.adjoint (Xop A0 A N)) (Xop A0 A N))
    (p : ℕ) (hp : 1 ≤ p) :
    ⟪wvec N u, ((ContinuousLinearMap.adjoint (Zop u A0 A N) * Zop u A0 A N) ^ p) (wvec N u)⟫_ℂ =
        ((‖(Zop u A0 A N ^ p) (wvec N u)‖ ^ 2 : ℝ) : ℂ) ∧
      ‖(Zop u A0 A N ^ p) (wvec N u)‖ ^ 2 ≤ Cp A p / (N : ℝ) ^ p :=
  high_moments u hu A0 A hsum N hN (normal_shift (Xop A0 A N) (xlim u A0 A) hX) p hp

#print axioms high_moments_of_normal
#print axioms high_moments
#print axioms Yk_bound

end QuantumNLS.HighMomentsFinal
