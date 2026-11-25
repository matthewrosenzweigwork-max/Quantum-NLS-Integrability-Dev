import Mathlib
import QuantumNLS.Prop022CTensorIso
import QuantumNLS.Prop022BFock1

/-! PROP-022 route A, round 4, stage C2: the INTRINSIC H-level canonical operators.

For an arbitrary complex Hilbert space `E` (no basis, no torus) this module defines, on the bosonic
Fock space `FockSpace E = ⊕_n Sym^n E`:

* `creS f n : Sym^n E → Sym^{n+1} E` (creation `a*(f)` on sectors, `√(n+1) P_{n+1}(x ⊗ f)`), its Hilbert
  adjoint `annS f n` (annihilation `a(f)`);
* the finite-particle core `Dfin E` and the operators `creF f`, `annF f`, `Zgen f = a*(f) - a(f)` on it,
  with the adjointness `⟪a*(f) x, w⟫ = ⟪x, a(f) w⟫` and the skew-symmetry of `a*(f) - a(f)`;
* the pair operators `ann2 b n : Sym^{2+n} → Sym^n` (contraction of the first two tensor factors with
  `b ∈ Sym² E`, identical in form to `Ext005PairSector.annihilation`) and `cre2 b n` (its adjoint);
* the second-quantization block `numberBlockE a n = n · Q_{n,1}(a)` (average one-body placement,
  identical in form to `Ext005QuadraticEnergyR108.numberBlock`);

and proves their covariance under every linear isometry `J : E → F` (`SecCov`):
`Γ(J) a*(f) = a*(Jf) Γ(J)`, `Γ(J) a(f) = a(Jf) Γ(J)`, and the adjoint forms with `Γ(J)†`, both for
the one-particle operators and the pair operators, plus `Γ_n(J) dΓ(a) = dΓ(J a J†) Γ_n(J)`. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable section
open scoped InnerProductSpace

namespace QuantumNLS.Prop022CCanon
open QuantumNLS.TensorCarrier QuantumNLS.Prop022GTensor QuantumNLS.Prop022AIsoTensor
open QuantumNLS.Prop022BIso QuantumNLS.IntrinsicContact QuantumNLS.Prop022CTensorIso
open QuantumNLS.Prop022BFock1

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma inner_adj {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (A : X →L[ℂ] Y) (x : X) (y : Y) :
    ⟪A x, y⟫_ℂ = ⟪x, ContinuousLinearMap.adjoint A y⟫_ℂ :=
  (ContinuousLinearMap.adjoint_inner_right A x y).symm

/-! ### Sector projections -/

lemma symProjToSector_eq (n : ℕ) (w : HilbertTensorPower ℂ E n) :
    TensorPlacements.symProjToSector n w = (SymSector ℂ E n).orthogonalProjectionOnto w := by
  apply Subtype.ext
  have h : ((SymSector ℂ E n).orthogonalProjectionOnto w : HilbertTensorPower ℂ E n) =
      symProj ℂ E n w := by
    rw [symProj_eq_starProjection]; rfl
  rw [h]; rfl

lemma inner_symProj_left {n : ℕ} (x : SymSector ℂ E n) (w : HilbertTensorPower ℂ E n) :
    ⟪x, TensorPlacements.symProjToSector n w⟫_ℂ = ⟪(x : HilbertTensorPower ℂ E n), w⟫_ℂ := by
  rw [symProjToSector_eq]
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left x w

lemma inner_symProj_right {n : ℕ} (w : HilbertTensorPower ℂ E n) (x : SymSector ℂ E n) :
    ⟪TensorPlacements.symProjToSector n w, x⟫_ℂ = ⟪w, (x : HilbertTensorPower ℂ E n)⟫_ℂ := by
  rw [symProjToSector_eq]
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right x w

/-- The sector map `P_m ∘ X ∘ ι_n` of a tensor-level map. -/
def secOf {n m : ℕ} (X : HilbertTensorPower ℂ E n →L[ℂ] HilbertTensorPower ℂ E m) :
    SymSector ℂ E n →L[ℂ] SymSector ℂ E m :=
  (TensorPlacements.symProjToSector m).comp (X.comp (SymSector ℂ E n).subtypeL)

lemma secOf_apply {n m : ℕ} (X : HilbertTensorPower ℂ E n →L[ℂ] HilbertTensorPower ℂ E m)
    (x : SymSector ℂ E n) :
    secOf X x = TensorPlacements.symProjToSector m (X (x : HilbertTensorPower ℂ E n)) := rfl

lemma secOf_adjoint_apply {n m : ℕ} (X : HilbertTensorPower ℂ E n →L[ℂ] HilbertTensorPower ℂ E m)
    (y : SymSector ℂ E m) :
    ContinuousLinearMap.adjoint (secOf X) y =
      TensorPlacements.symProjToSector n
        (ContinuousLinearMap.adjoint X (y : HilbertTensorPower ℂ E m)) := by
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right, secOf_apply, inner_symProj_right,
    inner_symProj_left]
  exact inner_adj X _ _

/-! ### Isometric covariance of sector maps -/

/-- Covariance of a sector creation map `cE : Sym^n E → Sym^m E` under `Γ(J)`, together with its
adjoint (annihilation) form. -/
structure SecCov (J : E →ₗᵢ[ℂ] F) {n m : ℕ} (cE : SymSector ℂ E n →L[ℂ] SymSector ℂ E m)
    (cF : SymSector ℂ F n →L[ℂ] SymSector ℂ F m) : Prop where
  fwd : ∀ x, symI J m (cE x) = cF (symI J n x)
  ann : ∀ y, symI J n (ContinuousLinearMap.adjoint cE y) =
    ContinuousLinearMap.adjoint cF (symI J m y)

theorem SecCov.adj_cre {J : E →ₗᵢ[ℂ] F} {n m : ℕ} {cE : SymSector ℂ E n →L[ℂ] SymSector ℂ E m}
    {cF : SymSector ℂ F n →L[ℂ] SymSector ℂ F m} (h : SecCov J cE cF) (y : SymSector ℂ F n) :
    symAdj J m (cF y) = cE (symAdj J n y) := by
  apply ext_inner_right ℂ
  intro v
  rw [inner_symAdj_left, inner_adj cF y (symI J m v), ← h.ann v, ← inner_symAdj_left,
    ← inner_adj cE (symAdj J n y) v]

theorem SecCov.adj_ann {J : E →ₗᵢ[ℂ] F} {n m : ℕ} {cE : SymSector ℂ E n →L[ℂ] SymSector ℂ E m}
    {cF : SymSector ℂ F n →L[ℂ] SymSector ℂ F m} (h : SecCov J cE cF) (y : SymSector ℂ F m) :
    symAdj J n (ContinuousLinearMap.adjoint cF y) =
      ContinuousLinearMap.adjoint cE (symAdj J m y) := by
  apply ext_inner_right ℂ
  intro v
  rw [inner_symAdj_left, ContinuousLinearMap.adjoint_inner_left cF (symI J n v) y, ← h.fwd v,
    ← inner_symAdj_left, ContinuousLinearMap.adjoint_inner_left cE v (symAdj J m y)]

lemma tensor_adj_cov (J : E →ₗᵢ[ℂ] F) {n m : ℕ}
    (XE : HilbertTensorPower ℂ E n →L[ℂ] HilbertTensorPower ℂ E m)
    (XF : HilbertTensorPower ℂ F n →L[ℂ] HilbertTensorPower ℂ F m)
    (hC' : ∀ w, ContinuousLinearMap.adjoint (tcI J m) (XF w) =
      XE (ContinuousLinearMap.adjoint (tcI J n) w)) (z : HilbertTensorPower ℂ E m) :
    tensorMapI J n (ContinuousLinearMap.adjoint XE z) =
      ContinuousLinearMap.adjoint XF (tensorMapI J m z) := by
  apply ext_inner_right ℂ
  intro v
  have e1 : ⟪tensorMapI J n (ContinuousLinearMap.adjoint XE z), v⟫_ℂ =
      ⟪ContinuousLinearMap.adjoint XE z, ContinuousLinearMap.adjoint (tcI J n) v⟫_ℂ :=
    inner_adj (tcI J n) _ _
  rw [e1, ContinuousLinearMap.adjoint_inner_left XE (ContinuousLinearMap.adjoint (tcI J n) v) z,
    ← hC' v, ContinuousLinearMap.adjoint_inner_right (tcI J m) z (XF v),
    ContinuousLinearMap.adjoint_inner_left XF v (tensorMapI J m z)]
  rfl

theorem secCov_of_tensor (J : E →ₗᵢ[ℂ] F) {n m : ℕ}
    (XE : HilbertTensorPower ℂ E n →L[ℂ] HilbertTensorPower ℂ E m)
    (XF : HilbertTensorPower ℂ F n →L[ℂ] HilbertTensorPower ℂ F m)
    (hC : ∀ z, tensorMapI J m (XE z) = XF (tensorMapI J n z))
    (hC' : ∀ w, ContinuousLinearMap.adjoint (tcI J m) (XF w) =
      XE (ContinuousLinearMap.adjoint (tcI J n) w)) :
    SecCov J (secOf XE) (secOf XF) where
  fwd x := by
    apply Subtype.ext
    change tensorMapI J m (symProj ℂ E m (XE (x : HilbertTensorPower ℂ E n))) =
      symProj ℂ F m (XF (tensorMapI J n (x : HilbertTensorPower ℂ E n)))
    rw [tensorMapI_symProj, hC]
  ann y := by
    rw [secOf_adjoint_apply, secOf_adjoint_apply]
    apply Subtype.ext
    change tensorMapI J n (symProj ℂ E n (ContinuousLinearMap.adjoint XE
        (y : HilbertTensorPower ℂ E m))) =
      symProj ℂ F n (ContinuousLinearMap.adjoint XF (tensorMapI J m (y : HilbertTensorPower ℂ E m)))
    rw [tensorMapI_symProj, tensor_adj_cov J XE XF hC']

/-! ### One-particle creation and annihilation -/

/-- Tensor-level creation `√(n+1) · (x ↦ x ⊗ f)` into the last slot. -/
def creT (f : E) (n : ℕ) :
    HilbertTensorPower ℂ E n →L[ℂ] HilbertTensorPower ℂ E (n + 1) :=
  ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) • insLast n 1 (htpow 1 f : HilbertTensorPower ℂ E 1)

/-- Creation `a*(f) : Sym^n E → Sym^{n+1} E`. -/
def creS (f : E) (n : ℕ) : SymSector ℂ E n →L[ℂ] SymSector ℂ E (n + 1) := secOf (creT f n)

/-- Annihilation `a(f) : Sym^{n+1} E → Sym^n E`, the Hilbert adjoint of creation. -/
def annS (f : E) (n : ℕ) : SymSector ℂ E (n + 1) →L[ℂ] SymSector ℂ E n :=
  ContinuousLinearMap.adjoint (creS f n)

theorem creT_cov (J : E →ₗᵢ[ℂ] F) (f : E) (n : ℕ) (z : HilbertTensorPower ℂ E n) :
    tensorMapI J (n + 1) (creT f n z) = creT (J f) n (tensorMapI J n z) := by
  unfold creT
  simp only [smul_apply, map_smul, tensorMapI_insLast J n 1, tensorMapI_htpow]

theorem creT_adj_cov (J : E →ₗᵢ[ℂ] F) (f : E) (n : ℕ) (w : HilbertTensorPower ℂ F n) :
    ContinuousLinearMap.adjoint (tcI J (n + 1)) (creT (J f) n w) =
      creT f n (ContinuousLinearMap.adjoint (tcI J n) w) := by
  unfold creT
  rw [← tensorMapI_htpow J 1 f]
  simp only [smul_apply, map_smul]
  rw [tcI_adj_insLast J n 1 (htpow 1 f) w]

theorem creS_cov (J : E →ₗᵢ[ℂ] F) (f : E) (n : ℕ) : SecCov J (creS f n) (creS (J f) n) :=
  secCov_of_tensor J _ _ (creT_cov J f n) (creT_adj_cov J f n)

/-! ### Pair annihilation and creation -/

/-- The two-particle annihilation block `a_n(b) : Sym^{2+n} → Sym^n` (first two tensor factors are
contracted with `b ∈ Sym²E`, then projected to the bosonic sector). -/
def ann2 (b : SymSector ℂ E 2) (n : ℕ) : SymSector ℂ E (2 + n) →L[ℂ] SymSector ℂ E n :=
  ((Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) : ℝ) : ℂ) •
    ((SymSector ℂ E n).orthogonalProjectionOnto ∘L
      contractL (F := HilbertTensorPower ℂ E n) (b : HilbertTensorPower ℂ E 2) ∘L
      (splitIsometry (𝕜 := ℂ) (E := E) 2 n).toContinuousLinearEquiv.toContinuousLinearMap ∘L
      (SymSector ℂ E (2 + n)).subtypeL)

/-- The two-particle creation block, the Hilbert adjoint of `ann2`. -/
def cre2 (b : SymSector ℂ E 2) (n : ℕ) : SymSector ℂ E n →L[ℂ] SymSector ℂ E (2 + n) :=
  ContinuousLinearMap.adjoint (ann2 b n)

/-- Tensor-level pair creation. -/
def creT2 (b : SymSector ℂ E 2) (n : ℕ) :
    HilbertTensorPower ℂ E n →L[ℂ] HilbertTensorPower ℂ E (2 + n) :=
  ((Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) : ℝ) : ℂ) •
    insFirst 2 n (b : HilbertTensorPower ℂ E 2)

lemma inner_contractL' {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [CompleteSpace A] [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
    (a : A) (y : B) (Φ : HilbertTensor ℂ A B) :
    ⟪contractL a Φ, y⟫_ℂ = ⟪Φ, htmul a y⟫_ℂ := by
  rw [← inner_conj_symm, inner_contractL, inner_conj_symm]

theorem ann2_eq (b : SymSector ℂ E 2) (n : ℕ) :
    ann2 b n = ContinuousLinearMap.adjoint (secOf (creT2 b n)) := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro y x
  have hL : ⟪ann2 b n y, x⟫_ℂ = ((Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) : ℝ) : ℂ) *
      ⟪splitIsometry (𝕜 := ℂ) (E := E) 2 n (y : HilbertTensorPower ℂ E (2 + n)),
        htmul (b : HilbertTensorPower ℂ E 2) (x : HilbertTensorPower ℂ E n)⟫_ℂ := by
    unfold ann2
    rw [smul_apply, inner_smul_left, Complex.conj_ofReal]
    congr 1
    change ⟪(SymSector ℂ E n).orthogonalProjectionOnto (contractL (b : HilbertTensorPower ℂ E 2)
      (splitIsometry (𝕜 := ℂ) (E := E) 2 n (y : HilbertTensorPower ℂ E (2 + n)))), x⟫_ℂ = _
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
    exact inner_contractL' _ _ _
  have hR : ⟪y, secOf (creT2 b n) x⟫_ℂ = ((Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) : ℝ) : ℂ) *
      ⟪splitIsometry (𝕜 := ℂ) (E := E) 2 n (y : HilbertTensorPower ℂ E (2 + n)),
        htmul (b : HilbertTensorPower ℂ E 2) (x : HilbertTensorPower ℂ E n)⟫_ℂ := by
    rw [secOf_apply, inner_symProj_left]
    unfold creT2
    rw [smul_apply, inner_smul_right, insFirst_apply,
      ← LinearIsometryEquiv.inner_map_eq_flip]
  rw [hL, hR]

theorem cre2_eq (b : SymSector ℂ E 2) (n : ℕ) : cre2 b n = secOf (creT2 b n) := by
  rw [cre2, ann2_eq, ContinuousLinearMap.adjoint_adjoint]

theorem creT2_cov (J : E →ₗᵢ[ℂ] F) (b : SymSector ℂ E 2) (n : ℕ) (z : HilbertTensorPower ℂ E n) :
    tensorMapI J (2 + n) (creT2 b n z) = creT2 (symI J 2 b) n (tensorMapI J n z) := by
  unfold creT2
  simp only [smul_apply, map_smul, tensorMapI_insFirst J 2 n]
  rfl

theorem creT2_adj_cov (J : E →ₗᵢ[ℂ] F) (b : SymSector ℂ E 2) (n : ℕ)
    (w : HilbertTensorPower ℂ F n) :
    ContinuousLinearMap.adjoint (tcI J (2 + n)) (creT2 (symI J 2 b) n w) =
      creT2 b n (ContinuousLinearMap.adjoint (tcI J n) w) := by
  unfold creT2
  simp only [smul_apply, map_smul]
  have h : ((symI J 2 b : SymSector ℂ F 2) : HilbertTensorPower ℂ F 2) =
      tensorMapI J 2 (b : HilbertTensorPower ℂ E 2) := rfl
  rw [h, tcI_adj_insFirst J 2 n (b : HilbertTensorPower ℂ E 2) w]

theorem cre2_cov (J : E →ₗᵢ[ℂ] F) (b : SymSector ℂ E 2) (n : ℕ) :
    SecCov J (cre2 b n) (cre2 (symI J 2 b) n) := by
  rw [cre2_eq, cre2_eq]
  exact secCov_of_tensor J _ _ (creT2_cov J b n) (creT2_adj_cov J b n)

/-! ### Second quantization `dΓ(a)` -/

/-- Cast of a sector operator along an equality of particle numbers. -/
def castSymOp {m n : ℕ} (h : m = n) (A : SymSector ℂ E m →L[ℂ] SymSector ℂ E m) :
    SymSector ℂ E n →L[ℂ] SymSector ℂ E n := by
  cases h
  exact A

/-- The DEF-041 placement `Q_{N,p}(A)` at total particle number `N`. -/
def physQ (N p : ℕ) (hp : p ≤ N) (A : SymSector ℂ E p →L[ℂ] SymSector ℂ E p) :
    SymSector ℂ E N →L[ℂ] SymSector ℂ E N :=
  castSymOp (Nat.add_sub_of_le hp) (TensorPlacements.Q_N_p (q := N - p) A)

/-- The second quantization `dΓ(a)` of `a ∈ B(Sym¹ E)` on the sector `n`: `n` times the average
one-body placement (zero on the vacuum sector). -/
def numberBlockE (a : SymSector ℂ E 1 →L[ℂ] SymSector ℂ E 1) (n : ℕ) :
    SymSector ℂ E n →L[ℂ] SymSector ℂ E n :=
  if hn : 1 ≤ n then (n : ℂ) • physQ n 1 hn a else 0

theorem symI_castSymOp (J : E →ₗᵢ[ℂ] F) {m n : ℕ} (h : m = n)
    (A : SymSector ℂ E m →L[ℂ] SymSector ℂ E m) (A' : SymSector ℂ F m →L[ℂ] SymSector ℂ F m)
    (hA : ∀ y, symI J m (A y) = A' (symI J m y)) (y : SymSector ℂ E n) :
    symI J n (castSymOp h A y) = castSymOp h A' (symI J n y) := by
  subst h
  exact hA y

theorem numberBlockE_cov (J : E →ₗᵢ[ℂ] F) (a : SymSector ℂ E 1 →L[ℂ] SymSector ℂ E 1)
    (a' : SymSector ℂ F 1 →L[ℂ] SymSector ℂ F 1)
    (ha : ∀ y, symI J 1 (a y) = a' (symI J 1 y)) (n : ℕ) (y : SymSector ℂ E n) :
    symI J n (numberBlockE a n y) = numberBlockE a' n (symI J n y) := by
  unfold numberBlockE
  by_cases hn : 1 ≤ n
  · simp only [hn, ↓reduceDIte, smul_apply, map_smul]
    congr 1
    unfold physQ
    exact symI_castSymOp J _ _ _ (fun y => symMapI_Q_N_p J a a' ha y) y
  · simp only [hn, ↓reduceDIte, zero_apply, map_zero]

/-! ### The finite-particle core and Fock-space operators -/

/-- Finite-particle vectors of `FockSpace E`. -/
def Dfin (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    Submodule ℂ (FockSpace E) where
  carrier := {x | ∃ N : ℕ, ∀ n, N < n → x n = 0}
  zero_mem' := ⟨0, fun n _ => rfl⟩
  add_mem' := by
    rintro x y ⟨N, hN⟩ ⟨M, hM⟩
    refine ⟨max N M, fun n hn => ?_⟩
    change x n + y n = 0
    rw [hN n (lt_of_le_of_lt (le_max_left _ _) hn), hM n (lt_of_le_of_lt (le_max_right _ _) hn),
      add_zero]
  smul_mem' := by
    rintro c x ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    change c • x n = 0
    rw [hN n hn, smul_zero]

lemma memℓp_of_support (g : ∀ n : ℕ, SymSector ℂ E n) (N : ℕ) (h : ∀ n, N < n → g n = 0) :
    Memℓp g 2 := by
  apply memℓp_gen
  apply summable_of_ne_finset_zero (s := Finset.range (N + 1))
  intro n hn
  have hn' : N < n := by
    simpa using hn
  simp [h n hn']

/-- Annihilation sequence `(a(f) x)_n = a_n(f) x_{n+1}`. -/
def annSeq (f : E) (x : FockSpace E) : ∀ n : ℕ, SymSector ℂ E n :=
  fun n => annS f n (x (n + 1))

/-- Creation sequence `(a*(f) x)_0 = 0`, `(a*(f) x)_{k+1} = a*_k(f) x_k`. -/
def creSeq (f : E) (x : FockSpace E) : ∀ n : ℕ, SymSector ℂ E n
  | 0 => 0
  | k + 1 => creS f k (x k)

/-- `a(f)` on the finite-particle core. -/
def annF (f : E) : Dfin E →ₗ[ℂ] FockSpace E where
  toFun x := ⟨annSeq f x.1, memℓp_of_support _ (Classical.choose x.2) (fun n hn => by
    have h := Classical.choose_spec x.2 (n + 1) (by omega)
    simp only [annSeq, h, map_zero])⟩
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact map_add (annS f n) _ _
  map_smul' c x := by
    apply Subtype.ext
    funext n
    exact map_smul (annS f n) c _

/-- `a*(f)` on the finite-particle core. -/
def creF (f : E) : Dfin E →ₗ[ℂ] FockSpace E where
  toFun x := ⟨creSeq f x.1, memℓp_of_support _ ((Classical.choose x.2) + 1) (fun n hn => by
    have hN := Classical.choose_spec x.2
    cases n with
    | zero => omega
    | succ k =>
      have h := hN k (by omega)
      simp only [creSeq, h, map_zero])⟩
  map_add' x y := by
    apply Subtype.ext
    funext n
    cases n with
    | zero => exact (add_zero _).symm
    | succ k => exact map_add (creS f k) _ _
  map_smul' c x := by
    apply Subtype.ext
    funext n
    cases n with
    | zero =>
      show (0 : SymSector ℂ E 0) = c • (0 : SymSector ℂ E 0)
      exact (smul_zero c).symm
    | succ k => exact map_smul (creS f k) c _

lemma annF_apply (f : E) (x : Dfin E) (n : ℕ) :
    (annF f x : FockSpace E) n = annS f n ((x : FockSpace E) (n + 1)) := rfl

lemma creF_zero (f : E) (x : Dfin E) : (creF f x : FockSpace E) 0 = 0 := rfl

lemma creF_succ (f : E) (x : Dfin E) (k : ℕ) :
    (creF f x : FockSpace E) (k + 1) = creS f k ((x : FockSpace E) k) := rfl

/-- **Adjointness** `⟪a*(f) x, w⟫ = ⟪x, a(f) w⟫` on the finite-particle core. -/
theorem inner_creF_annF (f : E) (x w : Dfin E) :
    ⟪(creF f x : FockSpace E), (w : FockSpace E)⟫_ℂ = ⟪(x : FockSpace E), (annF f w : FockSpace E)⟫_ℂ := by
  rw [lp.inner_eq_tsum (𝕜 := ℂ), lp.inner_eq_tsum (𝕜 := ℂ)]
  have hs := lp.summable_inner (𝕜 := ℂ) (creF f x : FockSpace E) (w : FockSpace E)
  rw [hs.tsum_eq_zero_add]
  have h0 : ⟪(creF f x : FockSpace E) 0, (w : FockSpace E) 0⟫_ℂ = 0 := by
    rw [creF_zero, inner_zero_left]
  rw [h0, zero_add]
  refine tsum_congr (fun k => ?_)
  rw [creF_succ, annF_apply]
  exact (ContinuousLinearMap.adjoint_inner_right (creS f k) _ _).symm

/-- The Weyl generator `a*(f) - a(f)` on the finite-particle core. -/
def Zgen (f : E) : Dfin E →ₗ[ℂ] FockSpace E := creF f - annF f

lemma Zgen_apply (f : E) (x : Dfin E) :
    (Zgen f x : FockSpace E) = (creF f x : FockSpace E) - (annF f x : FockSpace E) := rfl

/-- **Skew-symmetry** of `a*(f) - a(f)` on the finite-particle core. -/
theorem Zgen_skew (f : E) (x w : Dfin E) :
    ⟪(Zgen f x : FockSpace E), (w : FockSpace E)⟫_ℂ + ⟪(x : FockSpace E), (Zgen f w : FockSpace E)⟫_ℂ = 0 := by
  rw [Zgen_apply, Zgen_apply, inner_sub_left, inner_sub_right, inner_creF_annF f x w]
  have h2 : ⟪(annF f x : FockSpace E), (w : FockSpace E)⟫_ℂ =
      ⟪(x : FockSpace E), (creF f w : FockSpace E)⟫_ℂ := by
    rw [← inner_conj_symm, ← inner_conj_symm (x : FockSpace E), inner_creF_annF f w x]
  rw [h2]
  ring

/-! ### Isometric covariance on the Fock space -/

lemma gam_mem_dfin (J : E →ₗᵢ[ℂ] F) (x : Dfin E) : fockMapI J (x : FockSpace E) ∈ Dfin F := by
  obtain ⟨N, hN⟩ := x.2
  refine ⟨N, fun n hn => ?_⟩
  rw [fockMapI_apply, hN n hn, map_zero]

lemma gamAdj_mem_dfin (J : E →ₗᵢ[ℂ] F) (z : Dfin F) : gamAdj J (z : FockSpace F) ∈ Dfin E := by
  obtain ⟨N, hN⟩ := z.2
  refine ⟨N, fun n hn => ?_⟩
  rw [gamAdj_sector, hN n hn, map_zero]

/-- `Γ(J)` on the finite-particle cores. -/
def gamD (J : E →ₗᵢ[ℂ] F) : Dfin E →ₗ[ℂ] Dfin F where
  toFun x := ⟨fockMapI J (x : FockSpace E), gam_mem_dfin J x⟩
  map_add' x y := Subtype.ext (map_add (fockMapI J) _ _)
  map_smul' c x := Subtype.ext (map_smul (fockMapI J) c _)

/-- `Γ(J)†` on the finite-particle cores. -/
def gamAdjD (J : E →ₗᵢ[ℂ] F) : Dfin F →ₗ[ℂ] Dfin E where
  toFun z := ⟨gamAdj J (z : FockSpace F), gamAdj_mem_dfin J z⟩
  map_add' x y := Subtype.ext (map_add (gamAdj J) _ _)
  map_smul' c x := Subtype.ext (map_smul (gamAdj J) c _)

theorem annF_gam (J : E →ₗᵢ[ℂ] F) (f : E) (x : Dfin E) :
    (annF (J f) (gamD J x) : FockSpace F) = fockMapI J (annF f x : FockSpace E) := by
  apply Subtype.ext
  funext n
  change annS (J f) n (symMapI J (n + 1) ((x : FockSpace E) (n + 1))) =
    symMapI J n (annS f n ((x : FockSpace E) (n + 1)))
  exact ((creS_cov J f n).ann _).symm

theorem creF_gam (J : E →ₗᵢ[ℂ] F) (f : E) (x : Dfin E) :
    (creF (J f) (gamD J x) : FockSpace F) = fockMapI J (creF f x : FockSpace E) := by
  apply Subtype.ext
  funext n
  cases n with
  | zero => exact (map_zero (symMapI J 0)).symm
  | succ k => exact ((creS_cov J f k).fwd _).symm

theorem annF_gamAdj (J : E →ₗᵢ[ℂ] F) (f : E) (z : Dfin F) :
    (annF f (gamAdjD J z) : FockSpace E) = gamAdj J (annF (J f) z : FockSpace F) := by
  apply Subtype.ext
  funext n
  show annS f n ((gamAdj J (z : FockSpace F)) (n + 1)) =
    (gamAdj J (annF (J f) z : FockSpace F)) n
  rw [gamAdj_sector, gamAdj_sector]
  exact ((creS_cov J f n).adj_ann _).symm

theorem creF_gamAdj (J : E →ₗᵢ[ℂ] F) (f : E) (z : Dfin F) :
    (creF f (gamAdjD J z) : FockSpace E) = gamAdj J (creF (J f) z : FockSpace F) := by
  apply Subtype.ext
  funext n
  cases n with
  | zero =>
    change (0 : SymSector ℂ E 0) = (gamAdj J (creF (J f) z : FockSpace F)) 0
    rw [gamAdj_sector]
    exact (map_zero _).symm
  | succ k =>
    show creS f k ((gamAdj J (z : FockSpace F)) k) =
      (gamAdj J (creF (J f) z : FockSpace F)) (k + 1)
    rw [gamAdj_sector, gamAdj_sector]
    exact ((creS_cov J f k).adj_cre _).symm

end QuantumNLS.Prop022CCanon

#print axioms QuantumNLS.Prop022CCanon.creS_cov
#print axioms QuantumNLS.Prop022CCanon.cre2_cov
#print axioms QuantumNLS.Prop022CCanon.numberBlockE_cov
#print axioms QuantumNLS.Prop022CCanon.inner_creF_annF
#print axioms QuantumNLS.Prop022CCanon.Zgen_skew
#print axioms QuantumNLS.Prop022CCanon.creF_gamAdj
