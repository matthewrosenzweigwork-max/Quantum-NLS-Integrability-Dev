import NlsGge.Analysis.RegularizedDeterminant.All

/-! # F01 (wave A3), file b: abstract operator algebra for `lem:determinants` (B-free)

Plan and status: `NlsGge/Birkhoff/F01_PLAN.md`.  Nothing in this file mentions `BirkhoffInput38`;
the Birkhoff input enters only in the files `F01Determinant38c/d`.

Contents.
* a real Hilbert space `H` with a complex structure `J` and an orthogonal projection `P` commuting with
  `J` (`CplxProj38`); `V = P H`;
* F01.04: the compression `⟪J L̃ u, L̃ v⟫ = ⟪J u, v⟫ − ⟪J C u, C v⟫` (v2: `L_N^*J_NL_N = J_N − C_N^*J_{>N}C_N`);
* F01.06 (identity): `(det L_N)² = det (1 + J_N C_N^* J_{>N} C_N)` for real finite determinants;
* F01.05/06 (estimate): `|det(1+M|_V) − 1| ≤ detErr38 (‖C‖_HS²)`, dimension free, via the existing `det2`;
* F01.07 (compactness): two metric-space lemmas turning pointwise/uniform-on-compact convergence
  statements into uniformity on compact sets.
-/

set_option autoImplicit false
noncomputable section
open NlsGge.Analysis.RegularizedDeterminant
open scoped InnerProductSpace

namespace NlsGge.Birkhoff

section FiniteDim
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem det_adjoint_real38 (T : V →ₗ[ℝ] V) :
    LinearMap.det (LinearMap.adjoint T) = LinearMap.det T := by
  classical
  let b := stdOrthonormalBasis ℝ V
  rw [← LinearMap.det_toMatrix b.toBasis (LinearMap.adjoint T),
    ← LinearMap.det_toMatrix b.toBasis T, LinearMap.toMatrix_adjoint, Matrix.det_conjTranspose]
  simp

theorem det_ne_zero_of_sq_neg_one38 (J : V →ₗ[ℝ] V) (hJ : J * J = -1) : LinearMap.det J ≠ 0 := by
  intro h0
  have h := congrArg LinearMap.det hJ
  rw [map_mul, h0, mul_zero] at h
  have h2 : LinearMap.det (-1 : V →ₗ[ℝ] V) = (-1) ^ Module.finrank ℝ V := by
    have : (-1 : V →ₗ[ℝ] V) = (-1 : ℝ) • (1 : V →ₗ[ℝ] V) := by simp
    rw [this, LinearMap.det_smul]; simp
  rw [h2] at h
  exact pow_ne_zero _ (by norm_num) h.symm

theorem sq_det_eq_det_one_add38 (J T Q : V →ₗ[ℝ] V) (hJ : J * J = -1)
    (h : LinearMap.adjoint T * J * T = J - Q) :
    (LinearMap.det T) ^ 2 = LinearMap.det (1 + J * Q) := by
  have hJ0 := det_ne_zero_of_sq_neg_one38 J hJ
  have h1 : LinearMap.det (LinearMap.adjoint T * J * T) = LinearMap.det T ^ 2 * LinearMap.det J := by
    rw [map_mul, map_mul, det_adjoint_real38]; ring
  have h2 : J - Q = J * (1 + J * Q) := by
    rw [mul_add, mul_one, ← mul_assoc, hJ, neg_one_mul, sub_eq_add_neg]
  have h3 : LinearMap.det (J - Q) = LinearMap.det J * LinearMap.det (1 + J * Q) := by
    rw [h2, map_mul]
  rw [h] at h1
  rw [h3] at h1
  have := mul_left_cancel₀ hJ0 (h1.trans (mul_comm _ _))
  exact this.symm

end FiniteDim

section Compression

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A real Hilbert space with a complex structure `J` (`J² = -1`, `J* = -J`) and an orthogonal
projection `P` commuting with `J`. -/
structure CplxProj38 (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] where
  J : H →L[ℝ] H
  P : H →L[ℝ] H
  JJ : J * J = -1
  adjJ : ContinuousLinearMap.adjoint J = -J
  PP : P * P = P
  adjP : ContinuousLinearMap.adjoint P = P
  PJ : P * J = J * P

namespace CplxProj38

variable (D : CplxProj38 H)

theorem JJ_apply (x : H) : D.J (D.J x) = -x := by
  have := congrArg (fun T : H →L[ℝ] H => T x) D.JJ
  simpa using this

theorem PP_apply (x : H) : D.P (D.P x) = D.P x := by
  have := congrArg (fun T : H →L[ℝ] H => T x) D.PP
  simpa using this

theorem PJ_apply (x : H) : D.P (D.J x) = D.J (D.P x) := by
  have := congrArg (fun T : H →L[ℝ] H => T x) D.PJ
  simpa using this

theorem P_selfadj (u v : H) : ⟪D.P u, v⟫_ℝ = ⟪u, D.P v⟫_ℝ := by
  rw [← ContinuousLinearMap.adjoint_inner_left, D.adjP]

theorem J_skew (u v : H) : ⟪D.J u, v⟫_ℝ = -⟪u, D.J v⟫_ℝ := by
  rw [← ContinuousLinearMap.adjoint_inner_left, D.adjJ]; simp

/-- `V = P H`. -/
def V : Submodule ℝ H := LinearMap.range (D.P : H →ₗ[ℝ] H)

theorem mem_V_iff (x : H) : x ∈ D.V ↔ D.P x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact D.PP_apply y
  · intro h
    exact ⟨x, h⟩

theorem P_mem_V (x : H) : D.P x ∈ D.V := ⟨x, rfl⟩

theorem J_mem_V {x : H} (hx : x ∈ D.V) : D.J x ∈ D.V := by
  rw [mem_V_iff] at hx ⊢
  rw [D.PJ_apply, hx]

/-- `L̃ = P L P`. -/
def Lt (L : H →L[ℝ] H) : H →L[ℝ] H := D.P * L * D.P

/-- `C = (1 - P)(L - 1) P`. -/
def C (L : H →L[ℝ] H) : H →L[ℝ] H := (1 - D.P) * (L - 1) * D.P

/-- `Q = C^* J C`. -/
def Qop (L : H →L[ℝ] H) : H →L[ℝ] H :=
  ContinuousLinearMap.adjoint (D.C L) * D.J * D.C L

/-- `M = J C^* J C = J Q`. -/
def M (L : H →L[ℝ] H) : H →L[ℝ] H := D.J * D.Qop L

theorem Lt_mem (L : H →L[ℝ] H) (x : H) : D.Lt L x ∈ D.V := by
  simp only [Lt, mul_apply_eq_comp]; exact D.P_mem_V _

theorem adjMul (A B : H →L[ℝ] H) :
    ContinuousLinearMap.adjoint (A * B) =
      ContinuousLinearMap.adjoint B * ContinuousLinearMap.adjoint A :=
  ContinuousLinearMap.adjoint_comp A B

theorem adjC (L : H →L[ℝ] H) :
    ContinuousLinearMap.adjoint (D.C L) = D.P * ContinuousLinearMap.adjoint (L - 1) * (1 - D.P) := by
  have h1 : ContinuousLinearMap.adjoint (1 - D.P) = 1 - D.P := by
    rw [map_sub, D.adjP]; congr 1; exact ContinuousLinearMap.adjoint_id
  simp only [C, adjMul, D.adjP, h1, mul_assoc]

theorem adjC_mem (L : H →L[ℝ] H) (y : H) : ContinuousLinearMap.adjoint (D.C L) y ∈ D.V := by
  rw [D.adjC]
  simp only [mul_apply_eq_comp]
  exact D.P_mem_V _

theorem Qop_mem (L : H →L[ℝ] H) (x : H) : D.Qop L x ∈ D.V := by
  simp only [Qop, mul_apply_eq_comp]
  exact D.adjC_mem L _

theorem M_mem (L : H →L[ℝ] H) (x : H) : D.M L x ∈ D.V := by
  simp only [M, mul_apply_eq_comp]
  exact D.J_mem_V (D.Qop_mem L _)

theorem M_eq (L : H →L[ℝ] H) :
    D.M L = D.J * ContinuousLinearMap.adjoint (D.C L) * D.J * D.C L := by
  simp only [M, Qop, mul_assoc]

theorem C_apply (L : H →L[ℝ] H) (u : H) :
    D.C L u = (L (D.P u) - D.P u) - D.P (L (D.P u) - D.P u) := by
  rfl

theorem Lt_apply (L : H →L[ℝ] H) (u : H) : D.Lt L u = D.P (L (D.P u)) := by
  simp only [Lt, mul_apply_eq_comp]

theorem inner_V_perp (a w : H) (ha : a ∈ D.V) : ⟪a, w - D.P w⟫_ℝ = 0 := by
  rw [inner_sub_right, ← D.P_selfadj, ((D.mem_V_iff a).1 ha), sub_self]

theorem inner_perp_V (a w : H) (hw : w ∈ D.V) : ⟪a - D.P a, w⟫_ℝ = 0 := by
  rw [real_inner_comm, inner_V_perp D w a hw]

/-- **F01.04, pointwise form.** Compression of `⟪J L u, L v⟫ = ⟪J u, v⟫` to `V = P H`. -/
theorem compress_form (L : H →L[ℝ] H) (hL : ∀ u v, ⟪D.J (L u), L v⟫_ℝ = ⟪D.J u, v⟫_ℝ)
    (u v : H) (hu : u ∈ D.V) (hv : v ∈ D.V) :
    ⟪D.J (D.Lt L u), D.Lt L v⟫_ℝ = ⟪D.J u, v⟫_ℝ - ⟪D.J (D.C L u), D.C L v⟫_ℝ := by
  have hu' := (D.mem_V_iff u).1 hu
  have hv' := (D.mem_V_iff v).1 hv
  have hcu : D.C L u = L u - D.P (L u) := by
    rw [C_apply, hu', map_sub, hu']; abel
  have hcv : D.C L v = L v - D.P (L v) := by
    rw [C_apply, hv', map_sub, hv']; abel
  have hau : D.Lt L u = D.P (L u) := by rw [Lt_apply, hu']
  have hav : D.Lt L v = D.P (L v) := by rw [Lt_apply, hv']
  have hLu : L u = D.P (L u) + (L u - D.P (L u)) := by abel
  have hLv : L v = D.P (L v) + (L v - D.P (L v)) := by abel
  have key := hL u v
  rw [hLu, hLv] at key
  simp only [map_add, inner_add_left, inner_add_right] at key
  have hJa : D.J (D.P (L u)) ∈ D.V := D.J_mem_V (D.P_mem_V _)
  have e1 : ⟪D.J (D.P (L u)), L v - D.P (L v)⟫_ℝ = 0 := D.inner_V_perp _ _ hJa
  have e2 : ⟪D.J (L u - D.P (L u)), D.P (L v)⟫_ℝ = 0 := by
    rw [← D.P_selfadj, D.PJ_apply, map_sub, D.PP_apply, sub_self]
    simp
  rw [hau, hav, hcu, hcv]
  rw [e1, e2] at key
  linarith

/-- `J` restricted to `V`. -/
def resV (A : H →L[ℝ] H) (hA : ∀ x ∈ D.V, A x ∈ D.V) : D.V →ₗ[ℝ] D.V :=
  (A : H →ₗ[ℝ] H).restrict hA

@[simp] theorem coe_resV_apply (A : H →L[ℝ] H) (hA : ∀ x ∈ D.V, A x ∈ D.V) (x : D.V) :
    ((D.resV A hA x : D.V) : H) = A x := rfl

/-- Restriction of an operator with range in `V`. -/
def resRange (A : H →L[ℝ] H) (hA : ∀ x, A x ∈ D.V) : D.V →ₗ[ℝ] D.V :=
  D.resV A (fun x _ => hA x)

def JV : D.V →ₗ[ℝ] D.V := D.resV D.J (fun _ hx => D.J_mem_V hx)

theorem JV_mul_JV : D.JV * D.JV = -1 := by
  ext x
  show D.J (D.J (x : H)) = -(x : H)
  exact D.JJ_apply _

theorem adjoint_resRange_Lt [FiniteDimensional ℝ D.V] (L : H →L[ℝ] H) :
    LinearMap.adjoint (D.resRange (D.Lt L) (D.Lt_mem L)) =
      D.resRange (D.Lt (ContinuousLinearMap.adjoint L)) (D.Lt_mem _) := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  show ⟪(D.Lt (ContinuousLinearMap.adjoint L) (x : H)), (y : H)⟫_ℝ =
    ⟪(x : H), D.Lt L (y : H)⟫_ℝ
  rw [Lt_apply, Lt_apply, D.P_selfadj, ContinuousLinearMap.adjoint_inner_left]
  exact D.P_selfadj _ _

/-- **F01.04, operator form on `V`**: `L_N^* J_N L_N = J_N − C_N^* J_{>N} C_N`. -/
theorem adjoint_JV_T [FiniteDimensional ℝ D.V] (L : H →L[ℝ] H)
    (hL : ∀ u v, ⟪D.J (L u), L v⟫_ℝ = ⟪D.J u, v⟫_ℝ) :
    LinearMap.adjoint (D.resRange (D.Lt L) (D.Lt_mem L)) * D.JV *
        D.resRange (D.Lt L) (D.Lt_mem L) =
      D.JV - D.resRange (D.Qop L) (D.Qop_mem L) := by
  apply LinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [Module.End.mul_apply, Module.End.mul_apply, LinearMap.adjoint_inner_left, LinearMap.sub_apply,
    inner_sub_left]
  have h := D.compress_form L hL (u : H) (v : H) u.2 v.2
  have hq : ⟪D.resRange (D.Qop L) (D.Qop_mem L) u, v⟫_ℝ = ⟪D.J (D.C L u), D.C L v⟫_ℝ := by
    show ⟪D.Qop L (u : H), (v : H)⟫_ℝ = _
    simp only [Qop, mul_apply_eq_comp]
    rw [ContinuousLinearMap.adjoint_inner_left]
  rw [hq]
  show ⟪D.J (D.Lt L (u : H)), D.Lt L (v : H)⟫_ℝ = ⟪D.J (u : H), (v : H)⟫_ℝ - _
  exact h

theorem JV_mul_resRange_Qop [FiniteDimensional ℝ D.V] (L : H →L[ℝ] H) :
    D.JV * D.resRange (D.Qop L) (D.Qop_mem L) = D.resRange (D.M L) (D.M_mem L) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- **F01.06 (identity part).** `(det L_N)² = det (1 + J_N C_N^* J_{>N} C_N)` on `V = P H`. -/
theorem sq_det_Lt [FiniteDimensional ℝ D.V] (L : H →L[ℝ] H)
    (hL : ∀ u v, ⟪D.J (L u), L v⟫_ℝ = ⟪D.J u, v⟫_ℝ) :
    (LinearMap.det (D.resRange (D.Lt L) (D.Lt_mem L))) ^ 2 =
      LinearMap.det (1 + D.resRange (D.M L) (D.M_mem L)) := by
  rw [← D.JV_mul_resRange_Qop L]
  exact sq_det_eq_det_one_add38 D.JV _ _ D.JV_mul_JV (D.adjoint_JV_T L hL)

end CplxProj38
end Compression

section Estimate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Dimension-free error function for `|det(1+M) − 1|` when `‖M‖_HS, |tr M| ≤ s`. -/
def detErr38 (s : ℝ) : ℝ := s * Real.exp (2 * (s + 1) ^ 2) * Real.exp s + (Real.exp s - 1)

theorem continuous_detErr38 : Continuous detErr38 := by
  unfold detErr38; fun_prop

@[simp] theorem detErr38_zero : detErr38 0 = 0 := by simp [detErr38]

namespace CplxProj38

variable (D : CplxProj38 H)

theorem inner_J_J (a b : H) : ⟪D.J a, D.J b⟫_ℝ = ⟪a, b⟫_ℝ := by
  rw [D.J_skew, D.JJ_apply]; simp

theorem norm_J (x : H) : ‖D.J x‖ = ‖x‖ := by
  have h : ⟪D.J x, D.J x⟫_ℝ = ⟪x, x⟫_ℝ := D.inner_J_J x x
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

theorem opNorm_J_le : ‖D.J‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x; simp [D.norm_J]

/-- `J` as a linear isometry. -/
def Jiso : H →ₗᵢ[ℝ] H where
  toFun := D.J
  map_add' := map_add D.J
  map_smul' := map_smul D.J
  norm_map' := D.norm_J

theorem trace_eq_sum_inner [FiniteDimensional ℝ D.V] (T : D.V →ₗ[ℝ] D.V) :
    LinearMap.trace ℝ D.V T =
      ∑ i, ⟪((stdOrthonormalBasis ℝ D.V i : D.V) : H),
        ((T (stdOrthonormalBasis ℝ D.V i) : D.V) : H)⟫_ℝ := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℝ (stdOrthonormalBasis ℝ D.V).toBasis, Matrix.trace]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.diag, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply]
  rfl

/-- `|tr (J C^* J C)|_V| ≤ ‖C‖_HS²`. -/
theorem abs_trace_M_le [FiniteDimensional ℝ D.V] (L : H →L[ℝ] H) (c : HilbertSchmidt H H)
    (hc : HilbertSchmidt.toCLM c = D.C L) :
    |LinearMap.trace ℝ D.V (D.resRange (D.M L) (D.M_mem L))| ≤ ‖c‖ ^ 2 := by
  classical
  set b := stdOrthonormalBasis ℝ D.V with hb
  have hv : Orthonormal ℝ (fun j => ((b j : D.V) : H)) :=
    b.orthonormal.comp_linearIsometry D.V.subtypeₗᵢ
  have hJv : Orthonormal ℝ (fun j => D.J ((b j : D.V) : H)) :=
    hv.comp_linearIsometry D.Jiso
  have h1 := sum_norm_sq_orthonormal_le c _ hv
  have h2 := sum_norm_sq_orthonormal_le c _ hJv
  rw [hc] at h1 h2
  rw [D.trace_eq_sum_inner]
  have hterm : ∀ j, |⟪((b j : D.V) : H),
        ((D.resRange (D.M L) (D.M_mem L) (b j) : D.V) : H)⟫_ℝ| ≤
      (‖D.C L (D.J ((b j : D.V) : H))‖ ^ 2 + ‖D.C L ((b j : D.V) : H)‖ ^ 2) / 2 := by
    intro j
    set v : H := ((b j : D.V) : H)
    have e : ⟪v, ((D.resRange (D.M L) (D.M_mem L) (b j) : D.V) : H)⟫_ℝ =
        -⟪D.C L (D.J v), D.J (D.C L v)⟫_ℝ := by
      show ⟪v, D.M L v⟫_ℝ = _
      simp only [M, Qop, mul_apply_eq_comp]
      rw [← neg_neg ⟪v, D.J _⟫_ℝ, ← D.J_skew, ContinuousLinearMap.adjoint_inner_right]
    rw [e, abs_neg]
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [D.norm_J]
    nlinarith [sq_nonneg (‖D.C L (D.J v)‖ - ‖D.C L v‖)]
  calc |∑ j, ⟪((b j : D.V) : H), ((D.resRange (D.M L) (D.M_mem L) (b j) : D.V) : H)⟫_ℝ|
      ≤ ∑ j, |⟪((b j : D.V) : H), ((D.resRange (D.M L) (D.M_mem L) (b j) : D.V) : H)⟫_ℝ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, (‖D.C L (D.J ((b j : D.V) : H))‖ ^ 2 + ‖D.C L ((b j : D.V) : H)‖ ^ 2) / 2 :=
        Finset.sum_le_sum (fun j _ => hterm j)
    _ = (∑ j, ‖D.C L (D.J ((b j : D.V) : H))‖ ^ 2 + ∑ j, ‖D.C L ((b j : D.V) : H)‖ ^ 2) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ ‖c‖ ^ 2 := by linarith

/-- The Hilbert-Schmidt operator `J C^* J`. -/
def Xhs (c : HilbertSchmidt H H) : HilbertSchmidt H H :=
  HilbertSchmidt.postcompose D.J
    (HilbertSchmidt.precompose (HilbertSchmidt.adjoint c) D.J)

/-- The Hilbert-Schmidt operator `J C^* J C`. -/
def Mhs (c : HilbertSchmidt H H) : HilbertSchmidt H H :=
  HilbertSchmidt.precompose (D.Xhs c) (HilbertSchmidt.toCLM c)

theorem toCLM_Mhs (L : H →L[ℝ] H) (c : HilbertSchmidt H H)
    (hc : HilbertSchmidt.toCLM c = D.C L) : HilbertSchmidt.toCLM (D.Mhs c) = D.M L := by
  apply ContinuousLinearMap.ext
  intro x
  rw [M_eq]
  simp only [Mhs, Xhs, HilbertSchmidt.toCLM_precompose, HilbertSchmidt.toCLM_postcompose,
    HilbertSchmidt.toCLM_adjoint, hc, ContinuousLinearMap.comp_apply, mul_apply_eq_comp]

theorem norm_Mhs_le (c : HilbertSchmidt H H) : ‖D.Mhs c‖ ≤ ‖c‖ ^ 2 := by
  have hJ := D.opNorm_J_le
  have hc0 := norm_nonneg c
  have h1 : ‖HilbertSchmidt.precompose (HilbertSchmidt.adjoint c) D.J‖ ≤ ‖c‖ := by
    refine (HilbertSchmidt.norm_precompose_le _ _).trans ?_
    rw [HilbertSchmidt.norm_adjoint]
    nlinarith [norm_nonneg D.J]
  have h2 : ‖D.Xhs c‖ ≤ ‖c‖ := by
    refine (HilbertSchmidt.norm_postcompose_le _ _).trans ?_
    nlinarith [norm_nonneg D.J, norm_nonneg
      (HilbertSchmidt.precompose (HilbertSchmidt.adjoint c) D.J)]
  have h3 : ‖HilbertSchmidt.toCLM c‖ ≤ ‖c‖ := HilbertSchmidt.opNorm_le c
  refine (HilbertSchmidt.norm_precompose_le _ _).trans ?_
  rw [sq]
  exact mul_le_mul h2 h3 (norm_nonneg _) hc0

theorem hasFiniteRank_Mhs [FiniteDimensional ℝ D.V] (L : H →L[ℝ] H) (c : HilbertSchmidt H H)
    (hc : HilbertSchmidt.toCLM c = D.C L) :
    HilbertSchmidt.HasFiniteRank (HilbertSchmidt.toCLM (D.Mhs c)) := by
  unfold HilbertSchmidt.HasFiniteRank
  refine Submodule.finiteDimensional_of_le (S₂ := D.V) ?_
  rintro z ⟨x, rfl⟩
  rw [ContinuousLinearMap.coe_coe, D.toCLM_Mhs L c hc]
  exact D.M_mem L x

theorem abs_exp_sub_one_le_of_abs_le {t s : ℝ} (h : |t| ≤ s) : |Real.exp t - 1| ≤ Real.exp s - 1 := by
  have h1 := abs_le.1 h
  have h2 := Real.exp_le_exp.2 h1.2
  have h3 := Real.add_one_le_exp s
  have h4 := Real.add_one_le_exp (-s)
  have h5 := Real.exp_le_exp.2 h1.1
  have h6 : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add]; simp
  rw [abs_le]
  constructor
  · nlinarith [Real.exp_pos s, Real.exp_pos (-s), Real.exp_pos t]
  · linarith

/-- **F01.05/06, estimate.** For `C = (1-P)(L-1)P` Hilbert-Schmidt with norm `‖c‖`,
`|det (1 + (J C^*J C)|_V) − 1| ≤ detErr38 (‖c‖²)`; dimension free. -/
theorem abs_det_sub_one_le [FiniteDimensional ℝ D.V] (L : H →L[ℝ] H) (c : HilbertSchmidt H H)
    (hc : HilbertSchmidt.toCLM c = D.C L) :
    |LinearMap.det (1 + D.resRange (D.M L) (D.M_mem L)) - 1| ≤ detErr38 (‖c‖ ^ 2) := by
  set m := D.Mhs c with hmdef
  have hm : HilbertSchmidt.toCLM m = D.M L := D.toCLM_Mhs L c hc
  have hfr := D.hasFiniteRank_Mhs L c hc
  have hV : LinearMap.range (HilbertSchmidt.toCLM m).toLinearMap ≤ D.V := by
    rintro z ⟨x, rfl⟩
    rw [ContinuousLinearMap.coe_coe, hm]
    exact D.M_mem L x
  have hR : restrictedEnd (HilbertSchmidt.toCLM m).toLinearMap D.V hV =
      D.resRange (D.M L) (D.M_mem L) := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    show HilbertSchmidt.toCLM m (x : H) = D.M L (x : H)
    rw [hm]
  have h2 : det2 m = LinearMap.det (1 + D.resRange (D.M L) (D.M_mem L)) *
      Real.exp (-LinearMap.trace ℝ D.V (D.resRange (D.M L) (D.M_mem L))) := by
    rw [det2_of_finiteRank m hfr, finiteRankDet2_eq_restriction _ hfr D.V hV, hR]
    rfl
  set d := LinearMap.det (1 + D.resRange (D.M L) (D.M_mem L)) with hd
  set t := LinearMap.trace ℝ D.V (D.resRange (D.M L) (D.M_mem L)) with ht
  set s := ‖c‖ ^ 2 with hs
  have hs0 : 0 ≤ s := sq_nonneg _
  have hmn : ‖m‖ ≤ s := D.norm_Mhs_le c
  have ht' : |t| ≤ s := D.abs_trace_M_le L c hc
  have hdet2 : |det2 m - 1| ≤ s * Real.exp (2 * (s + 1) ^ 2) := by
    have h := det2_lipschitz m 0
    rw [det2_zero, sub_zero, norm_zero, add_zero] at h
    refine h.trans (mul_le_mul hmn ?_ (Real.exp_pos _).le hs0)
    apply Real.exp_le_exp.2
    have : (‖m‖ + 1) ^ 2 ≤ (s + 1) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    linarith
  have hd' : d = det2 m * Real.exp t := by
    rw [h2, mul_assoc, ← Real.exp_add]; simp
  have het : Real.exp t ≤ Real.exp s := Real.exp_le_exp.2 ((le_abs_self t).trans ht')
  have hexp := abs_exp_sub_one_le_of_abs_le ht'
  have hsplit : d - 1 = (det2 m - 1) * Real.exp t + (Real.exp t - 1) := by
    rw [hd']; ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_pos (Real.exp_pos t)]
  unfold detErr38
  have : |det2 m - 1| * Real.exp t ≤ s * Real.exp (2 * (s + 1) ^ 2) * Real.exp s :=
    mul_le_mul hdet2 het (Real.exp_pos _).le (by positivity)
  linarith

end CplxProj38
end Estimate

/-! ## F01.07: two metric-space lemmas turning pointwise statements into uniformity on compacts -/

section Compactness

open Filter Topology Metric

/-- If `φ_N → id` uniformly on a compact `K` and `g` is continuous, then `g ∘ φ_N → g` uniformly
on `K`.  (Lebesgue number lemma; `g` is not assumed uniformly continuous.) -/
theorem eventually_dist_comp_lt38 {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {K : Set X} (hK : IsCompact K) {g : X → Y} (hg : Continuous g) {φ : ℕ → X → X}
    (hφ : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ K, dist (φ N x) x < ε) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ K, dist (g (φ N x)) (g x) < ε := by
  intro ε hε
  have hopen : ∀ z : X, IsOpen {y : X | dist (g y) (g z) < ε / 2} := fun z =>
    isOpen_lt (hg.dist continuous_const) continuous_const
  obtain ⟨δ, hδ, hlebesgue⟩ := lebesgue_number_lemma_of_metric hK hopen
    (fun y _ => Set.mem_iUnion.2 ⟨y, by simpa using half_pos hε⟩)
  filter_upwards [hφ δ hδ] with N hN x hx
  obtain ⟨z, hz⟩ := hlebesgue x hx
  have h1 : φ N x ∈ {y : X | dist (g y) (g z) < ε / 2} := hz (by simpa using hN x hx)
  have h2 : x ∈ {y : X | dist (g y) (g z) < ε / 2} := hz (Metric.mem_ball_self hδ)
  have h1' : dist (g (φ N x)) (g z) < ε / 2 := h1
  have h2' : dist (g x) (g z) < ε / 2 := h2
  calc dist (g (φ N x)) (g x) ≤ dist (g (φ N x)) (g z) + dist (g x) (g z) := dist_triangle_right _ _ _
    _ < ε := by linarith

/-- A family of `1`-Lipschitz functions tending to `0` pointwise tends to `0` uniformly on compacts. -/
theorem eventually_abs_lt_of_lipschitz38 {X : Type*} [PseudoMetricSpace X] {K : Set X}
    (hK : IsCompact K) {F : ℕ → X → ℝ} (hlip : ∀ N x y, |F N x - F N y| ≤ dist x y)
    (hpt : ∀ x, Tendsto (fun N => F N x) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ K, |F N x| < ε := by
  intro ε hε
  obtain ⟨t, htK, htfin, hcover⟩ := finite_cover_balls_of_compact hK (half_pos hε)
  have hev : ∀ᶠ N in atTop, ∀ y ∈ t, |F N y| < ε / 2 := by
    rw [Filter.eventually_all_finite htfin]
    intro y _
    have := (hpt y).abs
    simp only [abs_zero] at this
    exact this.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hev] with N hN x hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcover hx)
  have h1 := hN y hy
  have h2 := hlip N x y
  have h3 : dist x y < ε / 2 := hxy
  have h4 : |F N x| ≤ |F N y| + |F N x - F N y| := by
    have := abs_add_le (F N y) (F N x - F N y)
    simpa using this
  linarith

end Compactness

end NlsGge.Birkhoff
