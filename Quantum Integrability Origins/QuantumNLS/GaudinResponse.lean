import QuantumNLS.RootContraction
import QuantumNLS.GroundRootBound

/-!
# DEF-051: the Gaudin response matrix

Source (ledger DEF-051, canonical occurrence `source/chapters/root_response/F01.tex`,
`CC:F01:jacobian`, lines 1-18; prerequisite DEF-006):
"For a fixed ordered real root array `q` at coupling `c > 0`, the Gaudin matrix is the Jacobian of
the logarithmic Bethe map: `(Bv)_i = L v_i + Σ_{j≠i} 2c (c² + (q_i − q_j)²)^{-1} (v_i − v_j)`.
The response vector is `B^{-1} q`."
F01 (lines 1-18): fix `L, c > 0`, `N ≥ 1`; the Bose form `CC:F01:bose`
`L q_i − 2 Σ_{j≠i} arctan (c/(q_i − q_j)) = 2π n_i`, the smooth form `CC:F01:smooth`
`T_i(q) = L q_i + 2 Σ_{j≠i} arctan ((q_i − q_j)/c) = 2π n_i + π(2i − N − 1)`, and the Jacobian
`CC:F01:jacobian` `(DT(x)v)_i = L v_i + Σ_{j≠i} 2c/(c² + (x_i − x_j)²) (v_i − v_j)`.

Lean indices are zero based (`Fin N`); the source's `i` is `i.val + 1`.

Realization (all imported modules frozen and read-only):
* `gaudinMatrix L c q` (the matrix `B`), its literal action `gaudinMatrix_mulVec`;
* `Tsmooth` = the printed `T` (`CC:F01:smooth`), `bose_iff_smooth` (the two equivalent forms);
* `hasFDerivAt_Tsmooth`/`fderiv_Tsmooth_apply`: `B` is the Jacobian of `T` at `q` (`CC:F01:jacobian`);
* `responseVec L c q = B^{-1} q`, `gaudin_responseVec`, `responseVec_unique`;
* well-definedness: symmetry, the quadratic form `vᵀBv = L|v|² + Σ_{i<j} w_ij (v_i − v_j)²`,
  positive definiteness (`Matrix.PosDef`), invertibility, `B 1 = L 1`;
* bridges: DEF-006 rapidities and the accepted roots R-4C8D7C9E (`def006_root_array`,
  `roots_root_array`), and the accepted ground lemma R-39906D9E (`ground_roots_symmetric`,
  `ground_responseVec_antisymm`).
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
open Finset

namespace QuantumNLS.GaudinResponse

open QuantumNLS.RootContraction QuantumNLS.OrderedResponse QuantumNLS.BetheAdmission
open QuantumNLS.BetheSmooth QuantumNLS.BetheLabels QuantumNLS.BetheRoots

variable {N : ℕ}

/-! ## 1. The matrix and its literal action -/

/-- **DEF-051**: the Gaudin matrix `B` at the root array `q` (entries `B_ii = L + Σ_{j≠i} w_ij`,
`B_ik = −w_ik`, `w_ij = 2c/(c² + (q_i − q_j)²)`). -/
def gaudinMatrix (L c : ℝ) (q : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ := Bmat L c q

/-- The printed action `(Bv)_i = L v_i + Σ_{j≠i} 2c (c² + (q_i − q_j)²)^{-1} (v_i − v_j)`. -/
theorem gaudinMatrix_mulVec (L c : ℝ) (q v : Fin N → ℝ) (i : Fin N) :
    (gaudinMatrix L c q *ᵥ v) i =
      L * v i + ∑ j ∈ univ.erase i, 2 * c * (c ^ 2 + (q i - q j) ^ 2)⁻¹ * (v i - v j) := by
  unfold gaudinMatrix
  rw [mulVec_Bmat_eq]
  simp only [wt, div_eq_mul_inv]

/-- The printed smooth map `T_i(x) = L x_i + 2 Σ_{j≠i} arctan ((x_i − x_j)/c)` (`CC:F01:smooth`). -/
def Tsmooth (L c : ℝ) (x : Fin N → ℝ) (i : Fin N) : ℝ :=
  L * x i + 2 * ∑ j ∈ univ.erase i, Real.arctan ((x i - x j) / c)

theorem Tsmooth_eq_Tmap (L c : ℝ) : Tsmooth (N := N) L c = Tmap L c := rfl

/-- `CC:F01:bose` written literally. -/
def BoseForm (L c : ℝ) (n : Fin N → ℤ) (q : Fin N → ℝ) : Prop :=
  ∀ i, L * q i - 2 * ∑ j ∈ univ.erase i, Real.arctan (c / (q i - q j)) = 2 * Real.pi * n i

/-- **The two equivalent forms** `CC:F01:bose` ⇔ `CC:F01:smooth` for strictly ordered `q`, `c > 0`
(one-based source index `i = i.val + 1`). -/
theorem bose_iff_smooth {L c : ℝ} (hc : 0 < c) {q : Fin N → ℝ} (hq : StrictMono q)
    (n : Fin N → ℤ) :
    BoseForm L c n q ↔ ∀ i : Fin N, Tsmooth L c q i =
      2 * Real.pi * n i + Real.pi * (2 * ((i.val : ℝ) + 1) - N - 1) := by
  have h := boseBethe_iff_log (L := L) hc hq n
  have e1 : BoseForm L c n q ↔ BoseBethe L c n q := by
    unfold BoseForm BoseBethe
    exact forall_congr' fun i => by constructor <;> intro h <;> linarith
  rw [e1, h, Tsmooth_eq_Tmap]
  exact forall_congr' fun i => by constructor <;> intro h <;> linarith

/-- **`B` is the Jacobian of the logarithmic Bethe map** at `q` (`c > 0`). -/
theorem hasFDerivAt_Tsmooth (L : ℝ) {c : ℝ} (hc : 0 < c) (q : Fin N → ℝ) :
    HasFDerivAt (Tsmooth L c) (Matrix.toLin' (gaudinMatrix L c q)).toContinuousLinearMap q := by
  have h := Tmap_hasFDerivAt (N := N) L hc q
  rw [Tsmooth_eq_Tmap]
  convert h using 1
  ext v i
  simp only [LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply]
  rw [RootDisplacement.gaudin_eq_Bmat]
  rfl

/-- **`CC:F01:jacobian`**: `(DT(x)v)_i = L v_i + Σ_{j≠i} 2c/(c² + (x_i − x_j)²) (v_i − v_j)`. -/
theorem fderiv_Tsmooth_apply (L : ℝ) {c : ℝ} (hc : 0 < c) (x v : Fin N → ℝ) (i : Fin N) :
    fderiv ℝ (Tsmooth L c) x v i =
      L * v i + ∑ j ∈ univ.erase i, 2 * c / (c ^ 2 + (x i - x j) ^ 2) * (v i - v j) := by
  rw [(hasFDerivAt_Tsmooth L hc x).fderiv]
  simp only [LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply]
  rw [gaudinMatrix_mulVec]
  simp only [div_eq_mul_inv]

/-! ## 2. Well-definedness: symmetry, positivity, invertibility -/

/-- `B` is symmetric. -/
theorem gaudinMatrix_transpose (L c : ℝ) (q : Fin N → ℝ) :
    (gaudinMatrix L c q)ᵀ = gaudinMatrix L c q := jacobian_symm L c q

theorem gaudinMatrix_isSymm (L c : ℝ) (q : Fin N → ℝ) : (gaudinMatrix L c q).IsSymm :=
  gaudinMatrix_transpose L c q

/-- The positive quadratic form
`vᵀBv = L Σ v_i² + Σ_{i<j} 2c/(c² + (q_i − q_j)²) (v_i − v_j)² ≥ L Σ v_i²`. -/
theorem gaudinMatrix_quadratic (L : ℝ) {c : ℝ} (hc : 0 < c) (q v : Fin N → ℝ) :
    v ⬝ᵥ (gaudinMatrix L c q *ᵥ v) = L * ∑ i, v i ^ 2 +
      ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 2 * c / (c ^ 2 + (q i - q j) ^ 2) * (v i - v j) ^ 2 ∧
    L * ∑ i, v i ^ 2 ≤ v ⬝ᵥ (gaudinMatrix L c q *ᵥ v) := by
  have e : v ⬝ᵥ (gaudinMatrix L c q *ᵥ v) = ∑ j, v j * gaudin L c q v j := by
    unfold dotProduct gaudinMatrix
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [RootDisplacement.gaudin_eq_Bmat]
  rw [e]
  exact jacobian_quadratic L hc q v

/-- **Positive definiteness** (`L, c > 0`). -/
theorem gaudinMatrix_posDef {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (q : Fin N → ℝ) :
    (gaudinMatrix L c q).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v hv => ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact gaudinMatrix_transpose L c q
  · have h := (gaudinMatrix_quadratic L hc q v).2
    have hpos : 0 < ∑ i, v i ^ 2 := by
      obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
        by_contra h'; push Not at h'; exact hv (funext h')
      exact lt_of_lt_of_le (pow_pos (abs_pos.mpr hi) 2 |>.trans_eq (sq_abs _))
        (Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (mem_univ i))
    simp only [star_trivial]
    nlinarith

/-- **Invertibility** (`L, c > 0`). -/
theorem gaudinMatrix_isUnit_det {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (q : Fin N → ℝ) :
    IsUnit (gaudinMatrix L c q).det := Bmat_isUnit_det hL hc q

/-- `B 1 = L 1`. -/
theorem gaudinMatrix_mulVec_one (L c : ℝ) (q : Fin N → ℝ) :
    gaudinMatrix L c q *ᵥ (fun _ => 1) = fun _ => L := by
  funext i
  rw [gaudinMatrix_mulVec]
  simp

/-! ## 3. The response vector `B^{-1} q` -/

/-- **DEF-051**: the response vector `B^{-1} q`. -/
def responseVec (L c : ℝ) (q : Fin N → ℝ) : Fin N → ℝ := (gaudinMatrix L c q)⁻¹ *ᵥ q

theorem responseVec_eq_respF (L c : ℝ) (q : Fin N → ℝ) : responseVec L c q = respF L c q := rfl

theorem gaudin_responseVec {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (q : Fin N → ℝ) :
    gaudinMatrix L c q *ᵥ responseVec L c q = q := Bmat_respF hL hc q

/-- The response vector is the unique solution of `B f = q`. -/
theorem responseVec_unique {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (q f : Fin N → ℝ) :
    gaudinMatrix L c q *ᵥ f = q ↔ f = responseVec L c q := by
  constructor
  · intro h
    exact Bmat_injective hL hc q (h.trans (gaudin_responseVec hL hc q).symm)
  · rintro rfl; exact gaudin_responseVec hL hc q

/-! ## 4. Bridges: DEF-006, the accepted roots R-4C8D7C9E, and R-39906D9E -/

/-- **DEF-006 bridge**: a DEF-006 rapidity vector (logarithmic labels of nondecreasing Bose labels
`n`) is a fixed ordered real root array solving `CC:F01:bose`, and it is the accepted root vector. -/
theorem def006_root_array {L c : ℝ} (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Monotone n)
    (q : Fin N → ℝ) (h : RapidityEq L c (labelsOf ⟨n, hn⟩).I q) :
    StrictMono q ∧ BoseForm L c n q ∧ q = roots L n c := by
  have ha := (rapidityEq_iff_isActual hL hc hn q).1 h
  refine ⟨ha.sorted, fun i => ?_, (isActual_iff_eq_roots hL hc hn q).1 ha⟩
  have := ha.bethe i
  linarith

/-- **R-4C8D7C9E bridge**: the accepted roots `roots L n c` are a strictly ordered root array
solving `CC:F01:bose`; in particular `B` and `B^{-1} q` are defined there with all the above
properties. -/
theorem roots_root_array {L c : ℝ} (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Monotone n) :
    StrictMono (roots L n c) ∧ BoseForm L c n (roots L n c) ∧
      gaudinMatrix L c (roots L n c) *ᵥ responseVec L c (roots L n c) = roots L n c := by
  have ha := isActual_roots hL hc hn
  refine ⟨ha.sorted, fun i => ?_, gaudin_responseVec hL hc _⟩
  have := ha.bethe i
  linarith

/-- **R-39906D9E bridge**: the ground roots (all labels zero, `N ≥ 1`) satisfy the hypotheses of the
accepted ground lemma, hence `q_i = −q_{N+1−i}` and `|q_i| ≤ 2√(cN/L)`. -/
theorem ground_roots_symmetric {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (hN : 1 ≤ N) :
    (∀ i, roots L (fun _ : Fin N => (0 : ℤ)) c i = -roots L (fun _ : Fin N => (0 : ℤ)) c (Fin.rev i)) ∧
    ∀ i, |roots L (fun _ : Fin N => (0 : ℤ)) c i| ≤ 2 * Real.sqrt (c * (N : ℝ) / L) := by
  have ha := isActual_roots (N := N) hL hc (n := fun _ => 0) (fun _ _ _ => le_rfl)
  refine GroundRootBound.ground_root_bound hN hL hc (fun _ => 0) (fun _ => rfl) _ ha.sorted ?_
  intro i
  have := ha.bethe i
  simp only [GroundRootBound.boseLHS]
  linarith

/-- Reversal commutes with `B` at a reflection-antisymmetric root array. -/
theorem gaudinMatrix_rev {L c : ℝ} {q : Fin N → ℝ} (hq : ∀ i, q i = -q (Fin.rev i))
    (f : Fin N → ℝ) (i : Fin N) :
    (gaudinMatrix L c q *ᵥ (fun j => f (Fin.rev j))) i = (gaudinMatrix L c q *ᵥ f) (Fin.rev i) := by
  unfold gaudinMatrix
  rw [mulVec_Bmat_full, mulVec_Bmat_full]
  congr 1
  refine (Fintype.sum_equiv Fin.revPerm _ _ fun j => ?_).symm
  simp only [Fin.revPerm_apply, Fin.rev_rev]
  rw [hq (Fin.rev i), hq (Fin.rev j), Fin.rev_rev, Fin.rev_rev, wt]
  unfold wt
  ring_nf

/-- **Ground response**: at the ground roots the response vector is reflection-antisymmetric,
`(B^{-1}q)_i = −(B^{-1}q)_{N+1−i}`. -/
theorem ground_responseVec_antisymm {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (hN : 1 ≤ N) (i : Fin N) :
    responseVec L c (roots L (fun _ : Fin N => (0 : ℤ)) c) i =
      -responseVec L c (roots L (fun _ : Fin N => (0 : ℤ)) c) (Fin.rev i) := by
  set q := roots L (fun _ : Fin N => (0 : ℤ)) c
  have hq := (ground_roots_symmetric (N := N) hL hc hN).1
  set f := responseVec L c q
  have hB : gaudinMatrix L c q *ᵥ (fun j => -f (Fin.rev j)) = q := by
    funext k
    have e : (fun j => -f (Fin.rev j)) = -(fun j => f (Fin.rev j)) := rfl
    rw [e, Matrix.mulVec_neg, Pi.neg_apply, gaudinMatrix_rev hq f k,
      gaudin_responseVec hL hc q]
    exact (hq k).symm ▸ by simp [q, hq k]
  have := (responseVec_unique hL hc q _).1 hB
  have h2 := congrFun this (Fin.rev i)
  simp only [Fin.rev_rev] at h2
  linarith

/-! Kernel axiom audit (checkpoint GR1). -/
#print axioms gaudinMatrix_mulVec
#print axioms bose_iff_smooth
#print axioms hasFDerivAt_Tsmooth
#print axioms fderiv_Tsmooth_apply
#print axioms gaudinMatrix_transpose
#print axioms gaudinMatrix_isSymm
#print axioms gaudinMatrix_quadratic
#print axioms gaudinMatrix_posDef
#print axioms gaudinMatrix_isUnit_det
#print axioms gaudinMatrix_mulVec_one
#print axioms gaudin_responseVec
#print axioms responseVec_unique
#print axioms def006_root_array
#print axioms roots_root_array
#print axioms ground_roots_symmetric
#print axioms gaudinMatrix_rev
#print axioms ground_responseVec_antisymm

end QuantumNLS.GaudinResponse
