import QuantumNLS.CartesianOccupationTransfer

/-!
# CountFunctionsS01Ops: intensive count operators `B_{N,J}` and the functional calculus `f(B_{N,J})`

(sonnet_fourier, gap G1 of R-AF8F7562 `thm:main`; no acceptance claim)

PRINTED SOURCES
* `source-text/chapters/core/GAUGE_RETARGETING.tex:249-250`: "Put `B_{N,a}=M_{N,a}/N` and ... `E_{N,aa}=B_{N,a}`."
* `source-text/chapters/principal_correspondence.tex:42` : "... continuous functions of finitely many intensive
  counts ..."
* `source-text/chapters/core/canonical_algebra.tex:15-17` (eq:exact-algebra) and `:38-44` (eq:finite-difference):
  "`[f(B_{N,J}),E^q_{N,ab}] = E^q_{N,ab}(f(B_{N,J}+h/N)-f(B_{N,J}))`, `h=e_b-e_a`, on allowed edges and by zero
  extension on the donor boundary".

OBJECTS (all defined from the accepted `Occupation`, `OccupationHilbert`, `BetheCoefficientTransform`,
`CartesianOccupationTransfer` objects; no new assumption beyond Lean core and Mathlib):
* `cube J` the cube `[0,1]^J`, `pt J N m` the intensive count point `(m_j / N)_{j ∈ J}` of an occupation array;
* `cntH N J f : H N →L H N` the diagonal operator `f(B_{N,J})` on the coefficient carrier `ℓ²(𝓜_N)`
  (`(cntH f v) m = f(pt m) * v m`; the joint spectrum of `B_{N,J}` is contained in `cube J` since `m_j ≤ N`);
* `countOp b g J f := conjOp b g (cntH N J f)` the same operator on the Bethe-sector carrier `HN L N` through the
  literal gauged coefficient transform (the same conjugation that defines `CartesianOccupationTransfer.physical`);
  the diagonal does not depend on the gauge (`countOp_coord : countOp b g J (coord j) = E^q_{N,jj}`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open scoped InnerProductSpace ComplexConjugate ENNReal
open QuantumNLS Occupation OccupationHilbert BetheCoefficientTransform BetheOccupationGauge

namespace QuantumNLS.CountFunctionsS01Ops

/-! ### The cube and the intensive count point -/

/-- The cube `[0,1]^J`. -/
def cube (J : Finset ℤ) : Set (↥J → ℝ) := {x | ∀ j, x j ∈ Set.Icc (0 : ℝ) 1}

/-- The intensive count point `(B_{N,j})_{j∈J}` evaluated on the occupation array `m`: `m_j / N`. -/
def pt (J : Finset ℤ) (N : ℕ) (m : Occ) : ↥J → ℝ := fun j => (m (j : ℤ) : ℝ) / N

lemma occ_le_total {N : ℕ} {m : Occ} (hm : IsArray N m) (a : ℤ) : m a ≤ N := by
  have h := Finsupp.le_degree a m
  unfold IsArray total at hm
  omega

lemma pt_mem_cube (J : Finset ℤ) {N : ℕ} {m : Occ} (hm : IsArray N m) : pt J N m ∈ cube J := by
  intro j
  refine ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0; simp [pt]
  · exact (div_le_one (by exact_mod_cast hpos)).2 (by exact_mod_cast occ_le_total hm _)

lemma zero_mem_cube (J : Finset ℤ) : (0 : ↥J → ℝ) ∈ cube J := fun j => ⟨le_refl _, zero_le_one⟩

/-! ### Bounded diagonal multipliers on `ℓ²(𝓜_N)` -/

/-- A bounded coefficient family. -/
def Bdd {N : ℕ} (c : Arr N → ℂ) : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ m, ‖c m‖ ≤ C

open Classical in
/-- The diagonal operator with coefficient `c` (zero when `c` is unbounded). -/
def dg {N : ℕ} (c : Arr N → ℂ) : H N →L[ℂ] H N :=
  if h : Bdd c then diagonal c h.choose h.choose_spec.1 h.choose_spec.2 else 0

lemma dg_apply {N : ℕ} {c : Arr N → ℂ} (h : Bdd c) (v : H N) (m : Arr N) :
    dg c v m = c m * v m := by
  unfold dg
  rw [dif_pos h]
  rfl

lemma bdd_mul {N : ℕ} {c d : Arr N → ℂ} (hc : Bdd c) (hd : Bdd d) : Bdd (fun m => c m * d m) := by
  obtain ⟨C, hC, hc⟩ := hc
  obtain ⟨D, hD, hd⟩ := hd
  exact ⟨C * D, mul_nonneg hC hD, fun m => by
    rw [norm_mul]; exact mul_le_mul (hc m) (hd m) (norm_nonneg _) hC⟩

lemma bdd_conj {N : ℕ} {c : Arr N → ℂ} (hc : Bdd c) : Bdd (fun m => conj (c m)) := by
  obtain ⟨C, hC, h⟩ := hc
  exact ⟨C, hC, fun m => by simpa using h m⟩

lemma bdd_sub {N : ℕ} {c d : Arr N → ℂ} (hc : Bdd c) (hd : Bdd d) : Bdd (fun m => c m - d m) := by
  obtain ⟨C, hC, hc⟩ := hc
  obtain ⟨D, hD, hd⟩ := hd
  exact ⟨C + D, add_nonneg hC hD, fun m => (norm_sub_le _ _).trans (add_le_add (hc m) (hd m))⟩

lemma bdd_const {N : ℕ} (z : ℂ) : Bdd (fun _ : Arr N => z) := ⟨‖z‖, norm_nonneg _, fun _ => le_rfl⟩

lemma dg_ext {N : ℕ} {c d : Arr N → ℂ} (hc : Bdd c) (hd : Bdd d) (hcd : ∀ m, c m = d m) :
    dg c = dg d := by
  ext v m
  rw [dg_apply hc, dg_apply hd, hcd]

lemma dg_mul {N : ℕ} {c d : Arr N → ℂ} (hc : Bdd c) (hd : Bdd d) :
    dg c * dg d = dg (fun m => c m * d m) := by
  ext v m
  rw [show (dg c * dg d) v = dg c (dg d v) from rfl, dg_apply hc, dg_apply hd,
    dg_apply (bdd_mul hc hd)]
  ring

lemma dg_comm {N : ℕ} {c d : Arr N → ℂ} (hc : Bdd c) (hd : Bdd d) :
    dg c * dg d = dg d * dg c := by
  rw [dg_mul hc hd, dg_mul hd hc]
  exact dg_ext (bdd_mul hc hd) (bdd_mul hd hc) fun m => mul_comm _ _

lemma dg_sub {N : ℕ} {c d : Arr N → ℂ} (hc : Bdd c) (hd : Bdd d) :
    dg c - dg d = dg (fun m => c m - d m) := by
  ext v m
  rw [sub_apply, lp.coeFn_sub, Pi.sub_apply, dg_apply hc, dg_apply hd,
    dg_apply (bdd_sub hc hd)]
  ring

lemma dg_const {N : ℕ} (z : ℂ) : dg (fun _ : Arr N => z) = z • ContinuousLinearMap.id ℂ (H N) := by
  ext v m
  rw [dg_apply (bdd_const z)]
  simp

lemma dg_adjoint {N : ℕ} {c : Arr N → ℂ} (hc : Bdd c) :
    (dg c).adjoint = dg (fun m => conj (c m)) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun m => ?_
  rw [dg_apply (bdd_conj hc), dg_apply hc]
  simp [inner]
  ring

lemma dg_norm_le {N : ℕ} {c : Arr N → ℂ} {C : ℝ} (hC : 0 ≤ C) (h : ∀ m, ‖c m‖ ≤ C) :
    ‖dg c‖ ≤ C := by
  have hb : Bdd c := ⟨C, hC, h⟩
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun v => ?_
  have := lp.norm_mono (p := 2) (by norm_num) (x := dg c v) (y := (C : ℂ) • v) (fun i => by
    change ‖dg c v i‖ ≤ ‖((C : ℂ) • v) i‖
    rw [dg_apply hb]
    simp only [lp.coeFn_smul, Pi.smul_apply, norm_smul, norm_mul]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right (h i) (norm_nonneg _))
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC] using this

/-! ### `f(B_{N,J})` on the coefficient carrier -/

/-- `f` is bounded on the cube. -/
def BddOn (J : Finset ℤ) (f : (↥J → ℝ) → ℂ) : Prop := ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ cube J, ‖f x‖ ≤ M

lemma BddOn.of_continuousOn {J : Finset ℤ} {f : (↥J → ℝ) → ℂ} (hf : ContinuousOn f (cube J)) :
    BddOn J f := by
  have hc : IsCompact (cube J) := by
    have : cube J = Set.pi Set.univ (fun _ : ↥J => Set.Icc (0 : ℝ) 1) := by
      ext x; simp [cube, Set.pi]
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuousOn hf
  refine ⟨max M 0, le_max_right _ _, fun x hx => (hM x hx).trans (le_max_left _ _)⟩

lemma bdd_cnt {N : ℕ} {J : Finset ℤ} {f : (↥J → ℝ) → ℂ} (hf : BddOn J f) :
    Bdd (fun m : Arr N => f (pt J N m.1)) := by
  obtain ⟨M, hM, h⟩ := hf
  exact ⟨M, hM, fun m => h _ (pt_mem_cube J m.2)⟩

/-- **`f(B_{N,J})`** on `ℓ²(𝓜_N)`: the diagonal operator with eigenvalue `f(m_j/N)_{j∈J}` on the basis vector `m`. -/
def cntH (N : ℕ) (J : Finset ℤ) (f : (↥J → ℝ) → ℂ) : H N →L[ℂ] H N :=
  dg (fun m : Arr N => f (pt J N m.1))

lemma cntH_apply {N : ℕ} {J : Finset ℤ} {f : (↥J → ℝ) → ℂ} (hf : BddOn J f) (v : H N) (m : Arr N) :
    cntH N J f v m = f (pt J N m.1) * v m :=
  dg_apply (bdd_cnt hf) v m

lemma cntH_norm_le {N : ℕ} {J : Finset ℤ} {f : (↥J → ℝ) → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ x ∈ cube J, ‖f x‖ ≤ M) : ‖cntH N J f‖ ≤ M :=
  dg_norm_le hM fun m => h _ (pt_mem_cube J m.2)

/-- The coordinate function `x ↦ x_j` (the intensive count of the label `j`). -/
def coordFn (J : Finset ℤ) (j : ↥J) : (↥J → ℝ) → ℂ := fun x => ((x j : ℝ) : ℂ)

lemma bddOn_coord (J : Finset ℤ) (j : ↥J) : BddOn J (coordFn J j) :=
  ⟨1, zero_le_one, fun x hx => by
    simp only [coordFn, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.2 ⟨by linarith [(hx j).1], (hx j).2⟩⟩

/-- `B_{N,j} = E_{N,jj}`: the count operator of one label is the diagonal Cartesian transfer
(`GAUGE_RETARGETING.tex:249-250`). -/
lemma cntH_coord (N : ℕ) (J : Finset ℤ) (j : ↥J) : cntH N J (coordFn J j) = E N (j : ℤ) (j : ℤ) := by
  ext v m
  rw [cntH_apply (bddOn_coord J j), E_diag_apply, coef_diag]
  simp [pt, coordFn]

lemma cntH_comm {N : ℕ} {J : Finset ℤ} {f g : (↥J → ℝ) → ℂ} (hf : BddOn J f) (hg : BddOn J g) :
    cntH N J f * cntH N J g = cntH N J g * cntH N J f :=
  dg_comm (bdd_cnt hf) (bdd_cnt hg)

lemma cntH_adjoint {N : ℕ} {J : Finset ℤ} {f : (↥J → ℝ) → ℂ} (hf : BddOn J f) :
    (cntH N J f).adjoint = cntH N J (fun x => conj (f x)) :=
  dg_adjoint (bdd_cnt hf)

lemma cntH_mul {N : ℕ} {J : Finset ℤ} {f g : (↥J → ℝ) → ℂ} (hf : BddOn J f) (hg : BddOn J g) :
    cntH N J f * cntH N J g = cntH N J (fun x => f x * g x) :=
  dg_mul (bdd_cnt hf) (bdd_cnt hg)


/-! ### Density: operators on `ℓ²(𝓜_N)` are determined by the basis vectors -/

lemma ext_basis {N : ℕ} {A B : H N →L[ℂ] H N}
    (h : ∀ m : Arr N, A (lp.single 2 m 1) = B (lp.single 2 m 1)) : A = B := by
  refine ContinuousLinearMap.ext_on (s := Set.range (basis N)) ?_ ?_
  · rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact (basis N).dense_span
  · rintro _ ⟨m, rfl⟩
    rw [basis_apply]
    exact h m

lemma dg_single {N : ℕ} {c : Arr N → ℂ} (hc : Bdd c) (m : Arr N) (z : ℂ) :
    dg c (lp.single 2 m z) = lp.single 2 m (c m * z) := by
  ext k
  rw [dg_apply hc]
  by_cases hk : k = m
  · subst hk; simp [lp.single_apply]
  · simp [lp.single_apply, Pi.single_apply, hk]

/-! ### The gauged transfer of a coefficient operator -/

section Physical

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- Conjugation of an operator of the coefficient carrier by the literal gauged coefficient transform; the same
construction that defines `CartesianOccupationTransfer.physical` (see `physical_eq_conjOp`). -/
def conjOp (b : BetheBasis L N) (g : Gauge) (A : H N →L[ℂ] H N) : HN L N →L[ℂ] HN L N :=
  (CartesianOccupationTransfer.coordinates b g).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L A ∘L
    (CartesianOccupationTransfer.coordinates b g).toContinuousLinearEquiv.toContinuousLinearMap

theorem physical_eq_conjOp (b : BetheBasis L N) (g : Gauge) (a c : ℤ) :
    CartesianOccupationTransfer.physical b g a c = conjOp b g (E N a c) := rfl

lemma conjOp_apply (b : BetheBasis L N) (g : Gauge) (A : H N →L[ℂ] H N) (ψ : HN L N) :
    conjOp b g A ψ =
      (CartesianOccupationTransfer.coordinates b g).symm (A (CartesianOccupationTransfer.coordinates b g ψ)) :=
  rfl

lemma coordinates_conjOp (b : BetheBasis L N) (g : Gauge) (A : H N →L[ℂ] H N) (ψ : HN L N) :
    CartesianOccupationTransfer.coordinates b g (conjOp b g A ψ) =
      A (CartesianOccupationTransfer.coordinates b g ψ) := by
  rw [conjOp_apply]
  exact LinearIsometryEquiv.apply_symm_apply _ _

lemma conjOp_mul (b : BetheBasis L N) (g : Gauge) (A B : H N →L[ℂ] H N) :
    conjOp b g (A * B) = conjOp b g A * conjOp b g B := by
  ext ψ
  rw [show (conjOp b g A * conjOp b g B) ψ = conjOp b g A (conjOp b g B ψ) from rfl, conjOp_apply,
    conjOp_apply, conjOp_apply, LinearIsometryEquiv.apply_symm_apply]
  rfl

lemma conjOp_sub (b : BetheBasis L N) (g : Gauge) (A B : H N →L[ℂ] H N) :
    conjOp b g (A - B) = conjOp b g A - conjOp b g B := by
  ext ψ
  simp only [conjOp_apply, sub_apply, map_sub]

lemma conjOp_add (b : BetheBasis L N) (g : Gauge) (A B : H N →L[ℂ] H N) :
    conjOp b g (A + B) = conjOp b g A + conjOp b g B := by
  ext ψ
  simp only [conjOp_apply, add_apply, map_add]

lemma conjOp_smul (b : BetheBasis L N) (g : Gauge) (z : ℂ) (A : H N →L[ℂ] H N) :
    conjOp b g (z • A) = z • conjOp b g A := by
  ext ψ
  simp only [conjOp_apply, ContinuousLinearMap.smul_apply, map_smul]

lemma conjOp_one (b : BetheBasis L N) (g : Gauge) :
    conjOp b g (ContinuousLinearMap.id ℂ (H N)) = ContinuousLinearMap.id ℂ (HN L N) := by
  ext ψ
  simp [conjOp_apply]

lemma conjOp_adjoint (b : BetheBasis L N) (g : Gauge) (A : H N →L[ℂ] H N) :
    (conjOp b g A).adjoint = conjOp b g A.adjoint := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [conjOp_apply, conjOp_apply]
  have h1 : ∀ (u : H N) (v : HN L N),
      inner ℂ ((CartesianOccupationTransfer.coordinates b g).symm u) v =
        inner ℂ u (CartesianOccupationTransfer.coordinates b g v) := by
    intro u v
    rw [← LinearIsometryEquiv.inner_map_map (CartesianOccupationTransfer.coordinates b g)]
    simp
  rw [h1, ContinuousLinearMap.adjoint_inner_left]
  rw [← LinearIsometryEquiv.inner_map_map (CartesianOccupationTransfer.coordinates b g)
    x ((CartesianOccupationTransfer.coordinates b g).symm _)]
  simp

lemma conjOp_norm_apply (b : BetheBasis L N) (g : Gauge) (A : H N →L[ℂ] H N) (ψ : HN L N) :
    ‖conjOp b g A ψ‖ = ‖A (CartesianOccupationTransfer.coordinates b g ψ)‖ := by
  rw [conjOp_apply, LinearIsometryEquiv.norm_map]

lemma conjOp_norm_le (b : BetheBasis L N) (g : Gauge) (A : H N →L[ℂ] H N) : ‖conjOp b g A‖ ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun ψ => ?_
  rw [conjOp_norm_apply]
  calc ‖A (CartesianOccupationTransfer.coordinates b g ψ)‖
      ≤ ‖A‖ * ‖CartesianOccupationTransfer.coordinates b g ψ‖ := A.le_opNorm _
    _ = ‖A‖ * ‖ψ‖ := by rw [LinearIsometryEquiv.norm_map]

/-- **`f(B_{N,J})`** on the Bethe-sector carrier `HN L N` (for the gauged Bethe basis `(b, g)`). -/
def countOp (b : BetheBasis L N) (g : Gauge) (J : Finset ℤ) (f : (↥J → ℝ) → ℂ) : HN L N →L[ℂ] HN L N :=
  conjOp b g (cntH N J f)

theorem countOp_coord (b : BetheBasis L N) (g : Gauge) (J : Finset ℤ) (j : ↥J) :
    countOp b g J (coordFn J j) = CartesianOccupationTransfer.physical b g (j : ℤ) (j : ℤ) := by
  rw [countOp, cntH_coord]
  rfl

theorem countOp_adjoint (b : BetheBasis L N) (g : Gauge) (J : Finset ℤ) {f : (↥J → ℝ) → ℂ}
    (hf : BddOn J f) :
    (countOp b g J f).adjoint = countOp b g J (fun x => conj (f x)) := by
  rw [countOp, countOp, conjOp_adjoint, cntH_adjoint hf]

theorem countOp_comm (b : BetheBasis L N) (g : Gauge) (J : Finset ℤ) {f h : (↥J → ℝ) → ℂ}
    (hf : BddOn J f) (hh : BddOn J h) :
    countOp b g J f * countOp b g J h = countOp b g J h * countOp b g J f := by
  rw [countOp, countOp, ← conjOp_mul, ← conjOp_mul, cntH_comm hf hh]

theorem countOp_norm_le (b : BetheBasis L N) (g : Gauge) (J : Finset ℤ) {f : (↥J → ℝ) → ℂ} {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ x ∈ cube J, ‖f x‖ ≤ M) : ‖countOp b g J f‖ ≤ M :=
  (conjOp_norm_le b g _).trans (cntH_norm_le hM h)

/-- **Exact algebra, second identity of eq:exact-algebra** (`canonical_algebra.tex:16-17`) for the gauged
transfers `E^q_{N,ab}` on the whole sector: `[E_ab, E_cd] = N⁻¹ (δ_ad E_cb - δ_bc E_ad)`. -/
theorem physical_comm (hN : 0 < N) (b : BetheBasis L N) (g : Gauge) (a b' c d : ℤ) :
    CartesianOccupationTransfer.physical b g a b' * CartesianOccupationTransfer.physical b g c d -
        CartesianOccupationTransfer.physical b g c d * CartesianOccupationTransfer.physical b g a b' =
      ((N : ℂ)⁻¹) • ((if a = d then (1 : ℂ) else 0) • CartesianOccupationTransfer.physical b g c b'
        - (if b' = c then (1 : ℂ) else 0) • CartesianOccupationTransfer.physical b g a d) := by
  simp only [physical_eq_conjOp]
  rw [← conjOp_mul, ← conjOp_mul, ← conjOp_sub, E_comm hN, conjOp_smul, conjOp_sub, conjOp_smul,
    conjOp_smul]

end Physical


/-! ### eq:finite-difference at the level of the coefficient carrier -/

/-- `h = e_b - e_a` as a vector of `ℝ^J`. -/
def hvec (J : Finset ℤ) (a b : ↥J) : ↥J → ℝ := fun j => (if j = b then 1 else 0) - (if j = a then 1 else 0)

lemma norm_hvec_le (J : Finset ℤ) (a b : ↥J) : ‖hvec J a b‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  unfold hvec
  rw [Real.norm_eq_abs, abs_le]
  split_ifs <;> constructor <;> norm_num

/-- The count point of the shifted array is `B + h/N` on an allowed edge. -/
lemma pt_shift (J : Finset ℤ) (N : ℕ) (a b : ↥J) {m : Occ} (hd : DonorOK (a : ℤ) m) :
    pt J N (shift (a : ℤ) (b : ℤ) m) = pt J N m + (N : ℝ)⁻¹ • hvec J a b := by
  funext j
  simp only [pt, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hvec]
  rw [occupation_fraction_shift hd]
  have e1 : ((j : ℤ) = (b : ℤ)) ↔ j = b := Subtype.coe_inj
  have e2 : ((j : ℤ) = (a : ℤ)) ↔ j = a := Subtype.coe_inj
  simp only [e1, e2]
  ring

/-- `f(B + h/N) - f(B)` on allowed edges, extended by zero on the donor boundary. -/
def fdiffCoef (N : ℕ) (J : Finset ℤ) (f : (↥J → ℝ) → ℂ) (a b : ↥J) (m : Arr N) : ℂ :=
  if DonorOK (a : ℤ) m.1 then f (pt J N m.1 + (N : ℝ)⁻¹ • hvec J a b) - f (pt J N m.1) else 0

lemma bdd_fdiff {N : ℕ} {J : Finset ℤ} {f : (↥J → ℝ) → ℂ} (hf : BddOn J f) (a b : ↥J) :
    Bdd (fdiffCoef N J f a b) := by
  obtain ⟨M, hM, h⟩ := hf
  refine ⟨2 * M, by positivity, fun m => ?_⟩
  unfold fdiffCoef
  split_ifs with hd
  · have h1 := h _ (pt_mem_cube J m.2)
    have h2 : f (pt J N m.1 + (N : ℝ)⁻¹ • hvec J a b) = f (pt J N (shift (a : ℤ) (b : ℤ) m.1)) := by
      rw [pt_shift J N a b hd]
    rw [h2]
    have h3 := h _ (pt_mem_cube J (isArray_shift (a := (a : ℤ)) (b := (b : ℤ)) m.2 hd))
    calc ‖f (pt J N (shift (a : ℤ) (b : ℤ) m.1)) - f (pt J N m.1)‖
        ≤ ‖f (pt J N (shift (a : ℤ) (b : ℤ) m.1))‖ + ‖f (pt J N m.1)‖ := norm_sub_le _ _
      _ ≤ 2 * M := by linarith
  · simp; positivity

/-- **eq:finite-difference** (`canonical_algebra.tex:41-43`), on the coefficient carrier and for every bounded `f`:
`[f(B_{N,J}), E_{N,ab}] = E_{N,ab} (f(B_{N,J}+h/N) - f(B_{N,J}))`, `h = e_b - e_a`, on allowed edges and by zero
extension on the donor boundary. -/
theorem cntH_comm_E {N : ℕ} {J : Finset ℤ} {f : (↥J → ℝ) → ℂ} (hf : BddOn J f) (a b : ↥J) :
    cntH N J f * E N (a : ℤ) (b : ℤ) - E N (a : ℤ) (b : ℤ) * cntH N J f =
      E N (a : ℤ) (b : ℤ) * dg (fdiffCoef N J f a b) := by
  apply ext_basis
  intro m
  rw [sub_apply, show (cntH N J f * E N (a : ℤ) (b : ℤ)) (lp.single 2 m 1) =
      cntH N J f (E N (a : ℤ) (b : ℤ) (lp.single 2 m 1)) from rfl,
    show (E N (a : ℤ) (b : ℤ) * cntH N J f) (lp.single 2 m 1) =
      E N (a : ℤ) (b : ℤ) (cntH N J f (lp.single 2 m 1)) from rfl,
    show (E N (a : ℤ) (b : ℤ) * dg (fdiffCoef N J f a b)) (lp.single 2 m 1) =
      E N (a : ℤ) (b : ℤ) (dg (fdiffCoef N J f a b) (lp.single 2 m 1)) from rfl]
  have h1 : cntH N J f (lp.single 2 m (1 : ℂ)) = lp.single 2 m (f (pt J N m.1) * 1) :=
    dg_single (bdd_cnt hf) m 1
  have h2 : dg (fdiffCoef N J f a b) (lp.single 2 m (1 : ℂ)) = lp.single 2 m (fdiffCoef N J f a b m * 1) :=
    dg_single (bdd_fdiff hf a b) m 1
  rw [h1, h2]
  by_cases hd : DonorOK (a : ℤ) m.1
  · rw [E_single N (a : ℤ) (b : ℤ) m 1, E_single N (a : ℤ) (b : ℤ) m (f (pt J N m.1) * 1),
      E_single N (a : ℤ) (b : ℤ) m (fdiffCoef N J f a b m * 1)]
    simp only [hd, dite_true]
    have hp : pt J N (shiftArr (a : ℤ) (b : ℤ) m hd).1 = pt J N m.1 + (N : ℝ)⁻¹ • hvec J a b :=
      pt_shift J N a b hd
    have h3 : cntH N J f (lp.single 2 (shiftArr (a : ℤ) (b : ℤ) m hd) (↑(coef N (a : ℤ) (b : ℤ) m.1) * 1)) =
        lp.single 2 (shiftArr (a : ℤ) (b : ℤ) m hd)
          (f (pt J N (shiftArr (a : ℤ) (b : ℤ) m hd).1) * (↑(coef N (a : ℤ) (b : ℤ) m.1) * 1)) :=
      dg_single (bdd_cnt hf) _ _
    rw [h3, hp]
    ext k
    simp only [lp.coeFn_sub, Pi.sub_apply, lp.single_apply, Pi.single_apply, fdiffCoef, hd, ite_true]
    split_ifs <;> ring
  · rw [E_single N (a : ℤ) (b : ℤ) m 1, E_single N (a : ℤ) (b : ℤ) m (f (pt J N m.1) * 1),
      E_single N (a : ℤ) (b : ℤ) m (fdiffCoef N J f a b m * 1)]
    simp [hd]


section PhysicalFD

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- `f(B_{N,J}+h/N) - f(B_{N,J})` on the Bethe-sector carrier (zero on the donor boundary). -/
def fdiffOp (b : BetheBasis L N) (g : Gauge) (J : Finset ℤ) (f : (↥J → ℝ) → ℂ) (a c : ↥J) :
    HN L N →L[ℂ] HN L N :=
  conjOp b g (dg (fdiffCoef N J f a c))

/-- **eq:finite-difference** (`canonical_algebra.tex:41-43`) for the gauged transfers on the Bethe-sector carrier:
`[f(B_{N,J}), E^q_{N,ab}] = E^q_{N,ab} (f(B_{N,J}+h/N) - f(B_{N,J}))`, `h = e_b - e_a`, on allowed edges and by zero
extension on the donor boundary. -/
theorem countOp_comm_E (b : BetheBasis L N) (g : Gauge) (J : Finset ℤ) {f : (↥J → ℝ) → ℂ}
    (hf : BddOn J f) (a c : ↥J) :
    countOp b g J f * CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ) -
        CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ) * countOp b g J f =
      CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ) * fdiffOp b g J f a c := by
  simp only [physical_eq_conjOp, countOp, fdiffOp]
  rw [← conjOp_mul, ← conjOp_mul, ← conjOp_mul, ← conjOp_sub, cntH_comm_E hf]

end PhysicalFD

/-! ### Chebyshev estimate for the functional calculus -/

lemma summable_sq_lp {N : ℕ} (v : H N) : Summable (fun m : Arr N => ‖v m‖ ^ 2) := by
  have h := Memℓp.summable (p := 2) (by norm_num) (lp.memℓp v)
  simpa [ENNReal.toReal_ofNat, Real.rpow_two] using h

lemma norm_sq_eq_tsum {N : ℕ} (v : H N) : ‖v‖ ^ 2 = ∑' m : Arr N, ‖v m‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) v
  simpa [ENNReal.toReal_ofNat, Real.rpow_two] using h

lemma norm_sq_dg {N : ℕ} {c : Arr N → ℂ} (hc : Bdd c) (v : H N) :
    ‖dg c v‖ ^ 2 = ∑' m : Arr N, ‖c m‖ ^ 2 * ‖v m‖ ^ 2 := by
  rw [norm_sq_eq_tsum]
  refine tsum_congr fun m => ?_
  rw [dg_apply hc, norm_mul, mul_pow]

lemma summable_bdd_mul_sq {N : ℕ} {c : Arr N → ℂ} (hc : Bdd c) (v : H N) :
    Summable (fun m : Arr N => ‖c m‖ ^ 2 * ‖v m‖ ^ 2) := by
  obtain ⟨C, hC, h⟩ := hc
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    ((summable_sq_lp v).mul_left (C ^ 2))
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (h m) 2) (by positivity)

/-- **Chebyshev (quadratic form comparison).** If `|c|² ≤ α + β Σ_j |d_j|²` pointwise then
`‖c v‖² ≤ α ‖v‖² + β Σ_j ‖d_j v‖²`. -/
lemma norm_sq_dg_le {N : ℕ} {ι : Type*} (s : Finset ι) {c : Arr N → ℂ} {d : ι → Arr N → ℂ}
    (hc : Bdd c) (hd : ∀ i, Bdd (d i)) {α β : ℝ} (hβ : 0 ≤ β)
    (h : ∀ m, ‖c m‖ ^ 2 ≤ α + β * ∑ i ∈ s, ‖d i m‖ ^ 2) (v : H N) :
    ‖dg c v‖ ^ 2 ≤ α * ‖v‖ ^ 2 + β * ∑ i ∈ s, ‖dg (d i) v‖ ^ 2 := by
  rw [norm_sq_dg hc, norm_sq_eq_tsum v]
  simp only [fun i => norm_sq_dg (hd i) v]
  have hs : ∀ i, Summable (fun m : Arr N => ‖d i m‖ ^ 2 * ‖v m‖ ^ 2) := fun i =>
    summable_bdd_mul_sq (hd i) v
  have hsum : Summable (fun m : Arr N => ∑ i ∈ s, ‖d i m‖ ^ 2 * ‖v m‖ ^ 2) :=
    summable_sum fun i _ => hs i
  have e1 : ∑' m : Arr N, (α * ‖v m‖ ^ 2 + β * ∑ i ∈ s, ‖d i m‖ ^ 2 * ‖v m‖ ^ 2) =
      α * ∑' m : Arr N, ‖v m‖ ^ 2 + β * ∑ i ∈ s, ∑' m : Arr N, ‖d i m‖ ^ 2 * ‖v m‖ ^ 2 := by
    rw [Summable.tsum_add ((summable_sq_lp v).mul_left α) (hsum.mul_left β),
      (summable_sq_lp v).tsum_mul_left, hsum.tsum_mul_left, Summable.tsum_finsetSum (fun i _ => hs i)]
  rw [← e1]
  refine Summable.tsum_le_tsum (fun m => ?_) (summable_bdd_mul_sq hc v)
    (((summable_sq_lp v).mul_left α).add (hsum.mul_left β))
  calc ‖c m‖ ^ 2 * ‖v m‖ ^ 2 ≤ (α + β * ∑ i ∈ s, ‖d i m‖ ^ 2) * ‖v m‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (h m) (by positivity)
    _ = α * ‖v m‖ ^ 2 + β * ∑ i ∈ s, ‖d i m‖ ^ 2 * ‖v m‖ ^ 2 := by
        rw [add_mul, mul_assoc, Finset.sum_mul]


/-- Pointwise Chebyshev bound for a function that is bounded and has a modulus of continuity on the cube. -/
lemma count_pointwise {J : Finset ℤ} {f : (↥J → ℝ) → ℂ} {M ε δ : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hbd : ∀ x ∈ cube J, ‖f x‖ ≤ M)
    (hmod : ∀ x ∈ cube J, ∀ y ∈ cube J, (∀ j, |x j - y j| < δ) → ‖f x - f y‖ ≤ ε)
    {a : ↥J → ℝ} (ha : a ∈ cube J) {x : ↥J → ℝ} (hx : x ∈ cube J) :
    ‖f x - f a‖ ^ 2 ≤ ε ^ 2 + (2 * M / δ) ^ 2 * ∑ j, (x j - a j) ^ 2 := by
  have hnn : 0 ≤ (2 * M / δ) ^ 2 * ∑ j, (x j - a j) ^ 2 :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _)
  by_cases hall : ∀ j, |x j - a j| < δ
  · have h1 := hmod x hx a ha hall
    have h2 : ‖f x - f a‖ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    linarith
  · push_neg at hall
    obtain ⟨j, hj⟩ := hall
    have h1 : δ ^ 2 ≤ ∑ j, (x j - a j) ^ 2 := by
      calc δ ^ 2 ≤ |x j - a j| ^ 2 := pow_le_pow_left₀ hδ.le hj 2
        _ = (x j - a j) ^ 2 := sq_abs _
        _ ≤ ∑ j, (x j - a j) ^ 2 :=
          Finset.single_le_sum (f := fun j => (x j - a j) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    have h2 : ‖f x - f a‖ ≤ 2 * M := by
      calc ‖f x - f a‖ ≤ ‖f x‖ + ‖f a‖ := norm_sub_le _ _
        _ ≤ 2 * M := by linarith [hbd x hx, hbd a ha]
    have h3 : ‖f x - f a‖ ^ 2 ≤ (2 * M) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    have h4 : (2 * M) ^ 2 = (2 * M / δ) ^ 2 * δ ^ 2 := by
      field_simp
    have h5 : (2 * M / δ) ^ 2 * δ ^ 2 ≤ (2 * M / δ) ^ 2 * ∑ j, (x j - a j) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    nlinarith [sq_nonneg ε]

/-- **Strong-symbol estimate for `f(B_{N,J})` on the coefficient carrier.** For every vector `v`,
`‖(f(B_{N,J}) - f(a)) v‖ ≤ ε ‖v‖ + (2M/δ) Σ_{j∈J} ‖(B_{N,j} - a_j) v‖`. -/
theorem cntH_sub_le {N : ℕ} {J : Finset ℤ} {f : (↥J → ℝ) → ℂ} {M ε δ : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hδ : 0 < δ) (hbd : ∀ x ∈ cube J, ‖f x‖ ≤ M)
    (hmod : ∀ x ∈ cube J, ∀ y ∈ cube J, (∀ j, |x j - y j| < δ) → ‖f x - f y‖ ≤ ε)
    {a : ↥J → ℝ} (ha : a ∈ cube J) (v : H N) :
    ‖(cntH N J f - f a • ContinuousLinearMap.id ℂ (H N)) v‖ ≤
      ε * ‖v‖ + (2 * M / δ) * ∑ j : ↥J,
        ‖(E N (j : ℤ) (j : ℤ) - ((a j : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (H N)) v‖ := by
  have hf : BddOn J f := ⟨M, hM, hbd⟩
  have hc : Bdd (fun m : Arr N => f (pt J N m.1) - f a) :=
    bdd_sub (bdd_cnt hf) (bdd_const _)
  have hd : ∀ j : ↥J, Bdd (fun m : Arr N => ((pt J N m.1 j : ℝ) : ℂ) - ((a j : ℝ) : ℂ)) := fun j =>
    bdd_sub (bdd_cnt (bddOn_coord J j)) (bdd_const _)
  have e1 : cntH N J f - f a • ContinuousLinearMap.id ℂ (H N) =
      dg (fun m : Arr N => f (pt J N m.1) - f a) := by
    rw [← dg_const (f a), cntH, dg_sub (bdd_cnt hf) (bdd_const _)]
  have e2 : ∀ j : ↥J, E N (j : ℤ) (j : ℤ) - ((a j : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (H N) =
      dg (fun m : Arr N => ((pt J N m.1 j : ℝ) : ℂ) - ((a j : ℝ) : ℂ)) := fun j => by
    rw [← dg_const ((a j : ℝ) : ℂ), ← cntH_coord N J j, cntH, dg_sub (bdd_cnt (bddOn_coord J j)) (bdd_const _)]
    rfl
  have hpt : ∀ m : Arr N, ‖f (pt J N m.1) - f a‖ ^ 2 ≤
      ε ^ 2 + (2 * M / δ) ^ 2 * ∑ j : ↥J, ‖((pt J N m.1 j : ℝ) : ℂ) - ((a j : ℝ) : ℂ)‖ ^ 2 := by
    intro m
    have := count_pointwise hM hε hδ hbd hmod ha (pt_mem_cube J m.2)
    refine this.trans (le_of_eq ?_)
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hq := norm_sq_dg_le (Finset.univ : Finset ↥J) hc hd (α := ε ^ 2) (β := (2 * M / δ) ^ 2)
    (sq_nonneg _) hpt v
  set w : ↥J → ℝ := fun j => ‖(E N (j : ℤ) (j : ℤ) - ((a j : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (H N)) v‖
    with hw
  have hw0 : ∀ j, 0 ≤ w j := fun j => norm_nonneg _
  have hK : 0 ≤ 2 * M / δ := by positivity
  rw [e1]
  have hq' : ‖dg (fun m : Arr N => f (pt J N m.1) - f a) v‖ ^ 2 ≤
      ε ^ 2 * ‖v‖ ^ 2 + (2 * M / δ) ^ 2 * ∑ j, w j ^ 2 := by
    simp only [hw, e2]
    exact hq
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  calc ‖dg (fun m : Arr N => f (pt J N m.1) - f a) v‖ ^ 2
      ≤ ε ^ 2 * ‖v‖ ^ 2 + (2 * M / δ) ^ 2 * ∑ j, w j ^ 2 := hq'
    _ ≤ ε ^ 2 * ‖v‖ ^ 2 + (2 * M / δ) ^ 2 * (∑ j, w j) ^ 2 := by
        gcongr
        exact Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => hw0 j
    _ ≤ (ε * ‖v‖ + (2 * M / δ) * ∑ j, w j) ^ 2 := by
        have h0 : 0 ≤ ε * ‖v‖ := by positivity
        have h1 : 0 ≤ (2 * M / δ) * ∑ j, w j := mul_nonneg hK (Finset.sum_nonneg fun j _ => hw0 j)
        nlinarith [mul_nonneg h0 h1]

section PhysicalCheb

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- **Strong-symbol estimate for `f(B_{N,J})` on the Bethe-sector carrier**: the same inequality for `countOp`. -/
theorem countOp_sub_le (b : BetheBasis L N) (g : Gauge) {J : Finset ℤ} {f : (↥J → ℝ) → ℂ}
    {M ε δ : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε) (hδ : 0 < δ) (hbd : ∀ x ∈ cube J, ‖f x‖ ≤ M)
    (hmod : ∀ x ∈ cube J, ∀ y ∈ cube J, (∀ j, |x j - y j| < δ) → ‖f x - f y‖ ≤ ε)
    {a : ↥J → ℝ} (ha : a ∈ cube J) (ψ : HN L N) :
    ‖(countOp b g J f - f a • ContinuousLinearMap.id ℂ (HN L N)) ψ‖ ≤
      ε * ‖ψ‖ + (2 * M / δ) * ∑ j : ↥J,
        ‖(CartesianOccupationTransfer.physical b g (j : ℤ) (j : ℤ) -
          ((a j : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (HN L N)) ψ‖ := by
  have h := cntH_sub_le (N := N) hM hε hδ hbd hmod ha
    (CartesianOccupationTransfer.coordinates b g ψ)
  have e1 : countOp b g J f - f a • ContinuousLinearMap.id ℂ (HN L N) =
      conjOp b g (cntH N J f - f a • ContinuousLinearMap.id ℂ (H N)) := by
    rw [conjOp_sub, conjOp_smul, conjOp_one]; rfl
  have e2 : ∀ j : ↥J, CartesianOccupationTransfer.physical b g (j : ℤ) (j : ℤ) -
      ((a j : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (HN L N) =
      conjOp b g (E N (j : ℤ) (j : ℤ) - ((a j : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (H N)) := fun j => by
    rw [conjOp_sub, conjOp_smul, conjOp_one]; rfl
  rw [e1, conjOp_norm_apply]
  simp only [e2, conjOp_norm_apply]
  rw [← LinearIsometryEquiv.norm_map (CartesianOccupationTransfer.coordinates b g) ψ]
  exact h

end PhysicalCheb

end QuantumNLS.CountFunctionsS01Ops
