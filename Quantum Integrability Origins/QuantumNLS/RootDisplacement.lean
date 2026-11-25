import QuantumNLS.BetheSmooth
import QuantumNLS.OrderedResponse

/-!
# Monotone root displacement (R-CED0D2FC, `adj:lem:total-displacement`)

Source: `source/chapters/quantitative/response_auxiliaries.tex`, lemma
`adj:lem:total-displacement` (about line 9), with its printed proof.

Data and conventions (source DEF-006, `chapters/definitions.tex`):
* `L > 0`, `c > 0`.
* Corrected labels are integers `n : Fin N → ℤ`, nondecreasing (zero-based `i` is the
  source index `j - 1`).
* Logarithmic labels `I_i = n_i + i - (N-1)/2` (`BetheAdmission.quantumNumbers`); the
  Bethe roots of `n` are `BetheSmooth.roots L n c = root L (2π I) c`, the accepted smooth
  root map (`BetheSmooth.root` is defined for every real forcing, not only integer labels).

Fractional labels: `n(s) = n + s δ`, `δ = n' - n`, `s ∈ [0,1]`; the roots along the path are
`root L (2π I(n(s))) c`, `fracRoots L c n δ`. The printed derivative equation `G q̇ = 2π δ`
has `G = BetheRoots.gaudin`, and `OrderedResponse.Bmat` is the same matrix
(`gaudin_eq_Bmat`, `printed_equation`).

Printed argument, as proved here:
* inverse positivity: `BetheSmooth.gaudin_inverse_nonneg` (accepted minimum-component proof);
* column sums: `1ᵀ G = L 1ᵀ` by symmetry of the weights (`gaudin_sum`), hence
  `Σ_j q̇_j = (2π/L) Σ_i δ_i`;
* integration: the coordinate sum is affine in `s` (`sum_fracRoots_sub`), and each coordinate
  is monotone in `s` (`fracRoots_mono_of_nonneg`), so `Σ_j |q'_j - q_j| = Σ_j (q'_j - q_j)`.

Replacement hypothesis: `k` with `n k = a` (one occurrence of `a`), and `n'` sorted with
`n' ∘ σ = Function.update n k b` for a permutation `σ` (sorting of the replaced tuple).

Standard axioms only: no `sorry`, `admit`, `native_decide`, `axiom`, `implemented_by`.
-/

noncomputable section
open scoped BigOperators Topology ContDiff
open Filter Finset Matrix
open QuantumNLS.BetheAdmission QuantumNLS.BetheRoots QuantumNLS.BetheSmooth
open QuantumNLS.OrderedResponse

namespace QuantumNLS.RootDisplacement

variable {N : ℕ}

/-! ### Labels and the fractional interpolation -/

/-- Logarithmic label of a real corrected-label tuple `x` (zero-based):
`x_i + i - (N-1)/2`. For integer `n` this is `quantumNumbers n`. -/
def logLabel (x : Fin N → ℝ) (i : Fin N) : ℝ :=
  x i + (i.val : ℝ) - ((N : ℝ) - 1) / 2

/-- Real corrected labels of an integer tuple. -/
def realLabels (n : Fin N → ℤ) : Fin N → ℝ := fun i => (n i : ℝ)

/-- The increment `δ_i = n'_i - n_i`. -/
def labelIncrement (n n' : Fin N → ℤ) : Fin N → ℝ := fun i => (n' i : ℝ) - (n i : ℝ)

/-- The fractional corrected labels `n(s) = x + s δ`. -/
def labelAt (x δ : Fin N → ℝ) (s : ℝ) : Fin N → ℝ := fun i => x i + s * δ i

/-- The forcing `2π I(n(s))` of the accepted root map. -/
def forcingPath (x δ : Fin N → ℝ) (s : ℝ) : Fin N → ℝ :=
  fun i => 2 * Real.pi * logLabel (labelAt x δ s) i

/-- Bethe roots along the fractional-label interpolation, via `BetheSmooth.root`. -/
def fracRoots (L c : ℝ) (x δ : Fin N → ℝ) : ℝ → (Fin N → ℝ) :=
  fun s => root L (forcingPath x δ s) c

theorem fracRoots_zero (L c : ℝ) (n : Fin N → ℤ) (δ : Fin N → ℝ) :
    fracRoots L c (realLabels n) δ 0 = BetheSmooth.roots L n c := by
  unfold fracRoots BetheSmooth.roots
  congr 1
  funext i
  simp [forcingPath, labelAt, logLabel, realLabels, quantumNumbers]

theorem fracRoots_one (L c : ℝ) (n n' : Fin N → ℤ) :
    fracRoots L c (realLabels n) (labelIncrement n n') 1 = BetheSmooth.roots L n' c := by
  unfold fracRoots BetheSmooth.roots
  congr 1
  funext i
  simp only [forcingPath, labelAt, logLabel, realLabels, labelIncrement, quantumNumbers, one_mul]
  ring

/-- The forcing path is affine in `s`, with slope `2π δ`. -/
theorem forcingPath_hasDerivAt (x δ : Fin N → ℝ) (s : ℝ) :
    HasDerivAt (forcingPath x δ) (fun i => 2 * Real.pi * δ i) s := by
  refine hasDerivAt_pi.mpr fun i => ?_
  have h := ((((hasDerivAt_id s).mul_const (δ i)).const_add (x i)).add_const
    ((i.val : ℝ) - ((N : ℝ) - 1) / 2)).const_mul (2 * Real.pi)
  convert h using 1
  · funext t
    simp only [forcingPath, logLabel, labelAt, id]
    ring
  · ring

/-! ### Smoothness of the accepted root map in the forcing variable -/

theorem logMap_contDiffAt_fixed (L : ℝ) {c : ℝ} (hc : c ≠ 0) (q : Fin N → ℝ) :
    ContDiffAt ℝ ∞ (logMap L c) q := by
  apply contDiffAt_pi.mpr
  intro i
  unfold logMap
  apply ContDiffAt.add
  · fun_prop
  · apply ContDiffAt.mul contDiffAt_const
    apply ContDiffAt.sum
    intro j _
    apply ContDiffAt.arctan
    apply ContDiffAt.div
    · fun_prop
    · fun_prop
    · exact hc

/-- The accepted root map `b ↦ root L b c` is smooth at every real forcing `b0`, by the
implicit function theorem in the forcing variable. The local branch is identified with
`root` by uniqueness (`eq_root`). -/
theorem root_contDiffAt_forcing {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (b0 : Fin N → ℝ) :
    ContDiffAt ℝ ∞ (fun b : Fin N → ℝ => root L b c) b0 := by
  set q0 := root L b0 c with hq0
  let f : (Fin N → ℝ) × (Fin N → ℝ) → (Fin N → ℝ) := fun p => logMap L c p.2 - p.1
  have hlog : ContDiffAt ℝ ∞ (logMap L c) q0 := logMap_contDiffAt_fixed L hc.ne' q0
  have hf : ContDiffAt ℝ ∞ f (b0, q0) :=
    (hlog.comp (b0, q0) contDiffAt_snd).sub contDiffAt_fst
  have hsnd : HasFDerivAt (Prod.snd : (Fin N → ℝ) × (Fin N → ℝ) → (Fin N → ℝ))
      (ContinuousLinearMap.snd ℝ (Fin N → ℝ) (Fin N → ℝ)) (b0, q0) := hasFDerivAt_snd
  have hfst : HasFDerivAt (Prod.fst : (Fin N → ℝ) × (Fin N → ℝ) → (Fin N → ℝ))
      (ContinuousLinearMap.fst ℝ (Fin N → ℝ) (Fin N → ℝ)) (b0, q0) := hasFDerivAt_fst
  have hcomp := (logMap_hasFDerivAt L hc q0).comp (b0, q0) hsnd
  have hD : HasFDerivAt f ((gaudin L c q0).comp (ContinuousLinearMap.snd ℝ (Fin N → ℝ) (Fin N → ℝ))
      - ContinuousLinearMap.fst ℝ (Fin N → ℝ) (Fin N → ℝ)) (b0, q0) :=
    hcomp.sub hfst
  have hfd : fderiv ℝ f (b0, q0) ∘L ContinuousLinearMap.inr ℝ (Fin N → ℝ) (Fin N → ℝ) =
      gaudin L c q0 := by
    rw [hD.fderiv]
    ext v i
    simp
  have hi : (fderiv ℝ f (b0, q0) ∘L ContinuousLinearMap.inr ℝ (Fin N → ℝ) (Fin N → ℝ)).IsInvertible := by
    rw [hfd]
    exact gaudin_isInvertible hL hc q0
  have hz : f (b0, q0) = 0 := by
    simp only [f]
    rw [hq0, root_solves hL hc b0, sub_self]
  let ψ := hf.implicitFunction (by simp) hi
  have he : (fun b : Fin N → ℝ => root L b c) =ᶠ[𝓝 b0] ψ := by
    filter_upwards [hf.eventually_apply_implicitFunction (by simp) hi] with b hb
    have h1 : logMap L c (ψ b) = b := by
      have h2 := hb.trans hz
      dsimp only [f] at h2
      exact sub_eq_zero.mp h2
    exact (QuantumNLS.BetheSmooth.eq_root hL hc h1).symm
  exact (hf.contDiffAt_implicitFunction (by simp) hi).congr_of_eventuallyEq he

theorem fracRoots_differentiableAt {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (x δ : Fin N → ℝ)
    (s : ℝ) : DifferentiableAt ℝ (fracRoots L c x δ) s := by
  have hR : DifferentiableAt ℝ (fun b : Fin N → ℝ => root L b c) (forcingPath x δ s) :=
    (root_contDiffAt_forcing hL hc (forcingPath x δ s)).differentiableAt (by simp)
  have hP : DifferentiableAt ℝ (forcingPath x δ) s :=
    (forcingPath_hasDerivAt x δ s).differentiableAt
  exact hR.comp s hP

theorem fracRoots_coord_hasDerivAt {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (x δ : Fin N → ℝ)
    (s : ℝ) (j : Fin N) :
    HasDerivAt (fun t => fracRoots L c x δ t j) (deriv (fracRoots L c x δ) s j) s :=
  hasDerivAt_pi.mp (fracRoots_differentiableAt hL hc x δ s).hasDerivAt j

/-! ### The printed equation `G q̇ = 2π δ` and its matrix form -/

/-- The printed Gaudin action `G v` equals `Bmat v`: `G = L Id + L_w`, `w_jk = 2c/(c²+(q_j-q_k)²)`. -/
theorem gaudin_eq_Bmat (L c : ℝ) (q v : Fin N → ℝ) :
    gaudin L c q v = Bmat L c q *ᵥ v := by
  funext i
  rw [mulVec_Bmat_eq, gaudin_apply, ← Finset.add_sum_erase univ _ (mem_univ i)]
  simp only [edgeWeight, wt, sub_self, mul_zero, zero_add]

/-- Entrywise: the matrix entry `Bmat i k` is the Gaudin map applied to the `k`-th basis vector. -/
theorem Bmat_apply_eq_gaudin (L c : ℝ) (q : Fin N → ℝ) (i k : Fin N) :
    Bmat L c q i k = gaudin L c q (Pi.single k 1) i := by
  rw [gaudin_eq_Bmat, Matrix.mulVec_single_one]
  rfl

/-- Differentiating the corrected Bethe equations along the fractional-label path:
`gaudin (q(s)) q̇(s) = 2π δ`. -/
theorem gaudin_deriv_eq {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (x δ : Fin N → ℝ) (s : ℝ) :
    gaudin L c (fracRoots L c x δ s) (deriv (fracRoots L c x δ) s) =
      fun i => 2 * Real.pi * δ i := by
  have hq : HasDerivAt (fracRoots L c x δ) (deriv (fracRoots L c x δ) s) s :=
    (fracRoots_differentiableAt hL hc x δ s).hasDerivAt
  have hlog : HasDerivAt (fun t => logMap L c (fracRoots L c x δ t))
      (gaudin L c (fracRoots L c x δ s) (deriv (fracRoots L c x δ) s)) s :=
    (logMap_hasFDerivAt L hc (fracRoots L c x δ s)).comp_hasDerivAt s hq
  have hfun : (fun t => logMap L c (fracRoots L c x δ t)) = forcingPath x δ := by
    funext t
    exact root_solves hL hc _
  rw [hfun] at hlog
  exact hlog.unique (forcingPath_hasDerivAt x δ s)

/-- The printed equation in matrix form: `B q̇ = 2π δ` with `B = Bmat`. -/
theorem printed_equation {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (x δ : Fin N → ℝ) (s : ℝ) :
    Bmat L c (fracRoots L c x δ s) *ᵥ deriv (fracRoots L c x δ) s =
      fun i => 2 * Real.pi * δ i := by
  rw [← gaudin_eq_Bmat]
  exact gaudin_deriv_eq hL hc x δ s

/-- The derivative as the inverse of the printed matrix: `q̇ = B⁻¹ (2π δ)`. -/
theorem deriv_eq_Bmat_inv {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (x δ : Fin N → ℝ) (s : ℝ) :
    deriv (fracRoots L c x δ) s =
      (Bmat L c (fracRoots L c x δ s))⁻¹ *ᵥ (fun i => 2 * Real.pi * δ i) := by
  have hu := Bmat_isUnit_det hL hc (fracRoots L c x δ s)
  rw [← printed_equation hL hc x δ s, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu,
    Matrix.one_mulVec]

/-- The derivative in gaudin form: `q̇ = G⁻¹ (2π δ)`. -/
theorem deriv_fracRoots_eq_inv {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (x δ : Fin N → ℝ)
    (s : ℝ) :
    deriv (fracRoots L c x δ) s =
      (gaudin L c (fracRoots L c x δ s)).inverse (fun i => 2 * Real.pi * δ i) := by
  rw [← gaudin_deriv_eq hL hc x δ s, (gaudin_isInvertible hL hc _).inverse_apply_self]

/-! ### Column sums of the Gaudin map -/

/-- `1ᵀ G = L 1ᵀ`: the weights are symmetric, so the Laplacian part has zero column sums. -/
theorem gaudin_sum (L c : ℝ) (q v : Fin N → ℝ) :
    ∑ i, gaudin L c q v i = L * ∑ i, v i := by
  simp only [gaudin_apply]
  have hT : ∑ i, ∑ j, edgeWeight c q i j * (v i - v j) = 0 := by
    have h1 : ∑ i, ∑ j, edgeWeight c q i j * (v i - v j) =
        ∑ i, ∑ j, edgeWeight c q j i * (v j - v i) := by
      rw [Finset.sum_comm]
    have h2 : ∑ i, ∑ j, edgeWeight c q j i * (v j - v i) =
        -∑ i, ∑ j, edgeWeight c q i j * (v i - v j) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [edgeWeight_symm]
      ring
    linarith
  rw [Finset.sum_add_distrib, hT, add_zero, Finset.mul_sum]

/-- Sum identity for the derivative: `Σ_j q̇_j = (2π/L) Σ_i δ_i`. -/
theorem sum_deriv_fracRoots {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (x δ : Fin N → ℝ) (s : ℝ) :
    ∑ j, deriv (fracRoots L c x δ) s j = 2 * Real.pi / L * ∑ i, δ i := by
  have h1 := gaudin_sum L c (fracRoots L c x δ s) (deriv (fracRoots L c x δ) s)
  rw [gaudin_deriv_eq hL hc x δ s] at h1
  dsimp only at h1
  rw [← Finset.mul_sum] at h1
  field_simp
  linear_combination -h1

/-! ### Signs of the derivative and monotonicity -/

/-- Increasing labels give nonnegative root derivatives (inverse positivity). -/
theorem fracRoots_deriv_nonneg {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (x δ : Fin N → ℝ)
    (hδ : ∀ i, 0 ≤ δ i) (s : ℝ) (j : Fin N) : 0 ≤ deriv (fracRoots L c x δ) s j := by
  rw [deriv_fracRoots_eq_inv hL hc x δ s]
  have hb : ∀ i, 0 ≤ 2 * Real.pi * δ i := fun i => mul_nonneg (by positivity) (hδ i)
  exact gaudin_inverse_nonneg hL hc _ hb j

/-- Decreasing labels give nonpositive root derivatives (linearity of the inverse). -/
theorem fracRoots_deriv_nonpos {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (x δ : Fin N → ℝ)
    (hδ : ∀ i, δ i ≤ 0) (s : ℝ) (j : Fin N) : deriv (fracRoots L c x δ) s j ≤ 0 := by
  rw [deriv_fracRoots_eq_inv hL hc x δ s]
  have hb : ∀ i, 0 ≤ -(2 * Real.pi * δ i) := fun i => by
    have := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi) (neg_nonneg.mpr (hδ i))
    linarith
  have h := gaudin_inverse_nonneg hL hc (fracRoots L c x δ s) hb j
  have hneg : (fun i => -(2 * Real.pi * δ i)) = -(fun i => 2 * Real.pi * δ i) := by
    funext i
    simp
  rw [hneg, map_neg] at h
  simp only [Pi.neg_apply] at h
  linarith

theorem fracRoots_mono_of_nonneg {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (x δ : Fin N → ℝ)
    (hδ : ∀ i, 0 ≤ δ i) (j : Fin N) :
    fracRoots L c x δ 0 j ≤ fracRoots L c x δ 1 j := by
  have hm : Monotone (fun t => fracRoots L c x δ t j) :=
    monotone_of_deriv_nonneg
      (fun s => (fracRoots_coord_hasDerivAt hL hc x δ s j).differentiableAt)
      (fun s => by
        rw [(fracRoots_coord_hasDerivAt hL hc x δ s j).deriv]
        exact fracRoots_deriv_nonneg hL hc x δ hδ s j)
  exact hm zero_le_one

theorem fracRoots_mono_of_nonpos {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (x δ : Fin N → ℝ)
    (hδ : ∀ i, δ i ≤ 0) (j : Fin N) :
    fracRoots L c x δ 1 j ≤ fracRoots L c x δ 0 j := by
  have hA : Antitone (fun t => fracRoots L c x δ t j) :=
    antitone_of_deriv_nonpos
      (fun s => (fracRoots_coord_hasDerivAt hL hc x δ s j).differentiableAt)
      (fun s => by
        rw [(fracRoots_coord_hasDerivAt hL hc x δ s j).deriv]
        exact fracRoots_deriv_nonpos hL hc x δ hδ s j)
  exact hA zero_le_one

/-- The coordinate sum is affine in `s`: `Σ_j (q_j(1) - q_j(0)) = (2π/L) Σ_i δ_i`. -/
theorem sum_fracRoots_sub {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (x δ : Fin N → ℝ) :
    ∑ j, (fracRoots L c x δ 1 j - fracRoots L c x δ 0 j) = 2 * Real.pi / L * ∑ i, δ i := by
  have hG : ∀ s : ℝ, HasDerivAt
      (fun t => ∑ j, fracRoots L c x δ t j - 2 * Real.pi / L * (∑ i, δ i) * t) 0 s := by
    intro s
    have h1 : HasDerivAt (fun t => ∑ j, fracRoots L c x δ t j)
        (∑ j, deriv (fracRoots L c x δ) s j) s :=
      HasDerivAt.fun_sum (u := Finset.univ)
        (fun j _ => fracRoots_coord_hasDerivAt hL hc x δ s j)
    have h2 : HasDerivAt (fun t => (∑ j, fracRoots L c x δ t j) -
        2 * Real.pi / L * (∑ i, δ i) * t)
        ((∑ j, deriv (fracRoots L c x δ) s j) - 2 * Real.pi / L * (∑ i, δ i) * 1) s :=
      h1.sub ((hasDerivAt_id s).const_mul (2 * Real.pi / L * (∑ i, δ i)))
    convert h2 using 1
    rw [sum_deriv_fracRoots hL hc x δ s]
    ring
  have hconst : (∑ j, fracRoots L c x δ 1 j) - 2 * Real.pi / L * (∑ i, δ i) * 1 =
      (∑ j, fracRoots L c x δ 0 j) - 2 * Real.pi / L * (∑ i, δ i) * 0 :=
    is_const_of_deriv_eq_zero
      (fun s => (hG s).differentiableAt) (fun s => (hG s).deriv) 1 0
  rw [Finset.sum_sub_distrib]
  linarith

/-! ### Counting lemmas for the sorted replacement -/

/-- Number of indices whose value is at most `t`. -/
def countLE (x : Fin N → ℤ) (t : ℤ) : ℕ := (univ.filter fun i => x i ≤ t).card

theorem countLE_eq_sum (x : Fin N → ℤ) (t : ℤ) :
    countLE x t = ∑ i, (if x i ≤ t then 1 else 0) := by
  unfold countLE
  rw [Finset.card_filter]

theorem countLE_perm (x : Fin N → ℤ) (σ : Equiv.Perm (Fin N)) (t : ℤ) :
    countLE (fun i => x (σ i)) t = countLE x t := by
  rw [countLE_eq_sum, countLE_eq_sum]
  exact Equiv.sum_comp σ (fun i => if x i ≤ t then 1 else 0)

theorem countLE_update (n : Fin N → ℤ) (k : Fin N) (b t : ℤ) :
    countLE (Function.update n k b) t + (if n k ≤ t then 1 else 0) =
      countLE n t + (if b ≤ t then 1 else 0) := by
  have e : ∀ x : Fin N → ℤ, ∑ i, (if x i ≤ t then 1 else 0) =
      (if x k ≤ t then 1 else 0) + ∑ i ∈ univ.erase k, (if x i ≤ t then 1 else 0) :=
    fun x => (Finset.add_sum_erase _ _ (mem_univ k)).symm
  have hs : ∑ i ∈ univ.erase k, (if Function.update n k b i ≤ t then 1 else 0) =
      ∑ i ∈ univ.erase k, (if n i ≤ t then 1 else 0) :=
    Finset.sum_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [countLE_eq_sum, countLE_eq_sum, e (Function.update n k b), e n, hs,
    Function.update_self]
  ring

/-- A sorted tuple `n'` with `n' ∘ σ = update n k b` satisfies the count identity. -/
theorem countLE_of_perm {n n' : Fin N → ℤ} {k : Fin N} {b : ℤ} {σ : Equiv.Perm (Fin N)}
    (hσ : ∀ i, n' (σ i) = Function.update n k b i) (t : ℤ) :
    countLE n' t + (if n k ≤ t then 1 else 0) = countLE n t + (if b ≤ t then 1 else 0) := by
  have h1 : countLE n' t = countLE (Function.update n k b) t := by
    rw [← countLE_perm n' σ t]
    congr 1
    funext i
    exact hσ i
  rw [h1]
  exact countLE_update n k b t

/-- Dominance of counting functions forces coordinatewise dominance of sorted tuples. -/
theorem le_of_countLE_le {x y : Fin N → ℤ} (hx : Monotone x) (hy : Monotone y)
    (h : ∀ t, countLE y t ≤ countLE x t) : ∀ j, x j ≤ y j := by
  intro j
  by_contra hlt
  have hlt' : y j < x j := not_le.mp hlt
  have h1 : (Finset.Iic j).card ≤ countLE y (y j) := by
    unfold countLE
    apply Finset.card_le_card
    intro i hi
    rw [Finset.mem_Iic] at hi
    rw [Finset.mem_filter]
    exact ⟨mem_univ i, hy hi⟩
  have h2 : countLE x (y j) ≤ (Finset.Iio j).card := by
    unfold countLE
    apply Finset.card_le_card
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_Iio]
    by_contra hij
    have h3 := hx (not_lt.mp hij)
    have h4 := hi.2
    omega
  rw [Fin.card_Iic] at h1
  rw [Fin.card_Iio] at h2
  have h5 := h (y j)
  omega

theorem sum_update_int (n : Fin N → ℤ) (k : Fin N) (b : ℤ) :
    ∑ i, Function.update n k b i = ∑ i, n i - n k + b := by
  have e : ∀ x : Fin N → ℤ, ∑ i, x i = x k + ∑ i ∈ univ.erase k, x i :=
    fun x => (Finset.add_sum_erase _ _ (mem_univ k)).symm
  have hs : ∑ i ∈ univ.erase k, Function.update n k b i = ∑ i ∈ univ.erase k, n i :=
    Finset.sum_congr rfl fun i hi => Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _
  rw [e (Function.update n k b), e n, hs, Function.update_self]
  ring

/-- The increment sums to `b - a`. -/
theorem sum_labelIncrement {n n' : Fin N → ℤ} {k : Fin N} {a b : ℤ}
    {σ : Equiv.Perm (Fin N)} (hk : n k = a) (hσ : ∀ i, n' (σ i) = Function.update n k b i) :
    ∑ i, labelIncrement n n' i = (b : ℝ) - a := by
  have h1 : ∑ i, n' (σ i) = ∑ i, n' i := Equiv.sum_comp σ n'
  have h2 : ∑ i, n' (σ i) = ∑ i, Function.update n k b i :=
    Finset.sum_congr rfl fun i _ => hσ i
  have hZ : ∑ i, n' i = ∑ i, n i - a + b := by
    rw [← h1, h2, sum_update_int, hk]
  have hZR : (∑ i, (n' i : ℝ)) = (∑ i, (n i : ℝ)) - a + b := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hZ
    push_cast at this
    exact this
  unfold labelIncrement
  rw [Finset.sum_sub_distrib, hZR]
  ring

/-- Increasing replacement `a < b`: every increment is nonnegative. -/
theorem labelIncrement_nonneg_of_increase {n n' : Fin N → ℤ} (hn : Monotone n)
    (hn' : Monotone n') {a b : ℤ} (hab : a < b) {k : Fin N} (hk : n k = a)
    {σ : Equiv.Perm (Fin N)} (hσ : ∀ i, n' (σ i) = Function.update n k b i) :
    ∀ i, 0 ≤ labelIncrement n n' i := by
  have hc : ∀ t, countLE n' t ≤ countLE n t := by
    intro t
    have h := countLE_of_perm hσ t
    rw [hk] at h
    split_ifs at h <;> omega
  intro i
  have h1 : n i ≤ n' i := le_of_countLE_le hn hn' hc i
  unfold labelIncrement
  have h2 : (n i : ℝ) ≤ n' i := by exact_mod_cast h1
  linarith

/-- Decreasing replacement `b < a`: every increment is nonpositive. -/
theorem labelIncrement_nonpos_of_decrease {n n' : Fin N → ℤ} (hn : Monotone n)
    (hn' : Monotone n') {a b : ℤ} (hab : b < a) {k : Fin N} (hk : n k = a)
    {σ : Equiv.Perm (Fin N)} (hσ : ∀ i, n' (σ i) = Function.update n k b i) :
    ∀ i, labelIncrement n n' i ≤ 0 := by
  have hc : ∀ t, countLE n t ≤ countLE n' t := by
    intro t
    have h := countLE_of_perm hσ t
    rw [hk] at h
    split_ifs at h <;> omega
  intro i
  have h1 : n' i ≤ n i := le_of_countLE_le hn' hn hc i
  unfold labelIncrement
  have h2 : (n' i : ℝ) ≤ n i := by exact_mod_cast h1
  linarith

/-- The interpolated labels stay sorted for `s ∈ [0,1]`: a convex combination of two sorted
tuples. -/
theorem labelAt_monotone {n n' : Fin N → ℤ} (hn : Monotone n) (hn' : Monotone n') {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    Monotone (labelAt (realLabels n) (labelIncrement n n') s) := by
  intro i j hij
  have h1 : (n i : ℝ) ≤ n j := by exact_mod_cast hn hij
  have h2 : (n' i : ℝ) ≤ n' j := by exact_mod_cast hn' hij
  obtain ⟨hs0, hs1⟩ := hs
  simp only [labelAt, labelIncrement, realLabels]
  nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr h1),
    mul_nonneg hs0 (sub_nonneg.mpr h2)]

/-! ### The displacement lemma -/

/-- `adj:lem:total-displacement`, case `a < b`. -/
theorem total_displacement_increase {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n n' : Fin N → ℤ} (hn : Monotone n) (hn' : Monotone n')
    {a b : ℤ} (hab : a < b) {k : Fin N} (hk : n k = a)
    (hrep : ∃ σ : Equiv.Perm (Fin N), ∀ i, n' (σ i) = Function.update n k b i) :
    (∀ i, 0 ≤ labelIncrement n n' i) ∧
    ∑ i, labelIncrement n n' i = (b : ℝ) - a ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1, Monotone (labelAt (realLabels n) (labelIncrement n n') s)) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ j,
      0 ≤ deriv (fracRoots L c (realLabels n) (labelIncrement n n')) s j) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∑ j, deriv (fracRoots L c (realLabels n) (labelIncrement n n')) s j =
        2 * Real.pi / L * ((b : ℝ) - a)) ∧
    ∑ j, |BetheSmooth.roots L n' c j - BetheSmooth.roots L n c j| =
      2 * Real.pi / L * ((b : ℝ) - a) := by
  obtain ⟨σ, hσ⟩ := hrep
  have hδ := labelIncrement_nonneg_of_increase hn hn' hab hk hσ
  have hsum := sum_labelIncrement hk hσ
  refine ⟨hδ, hsum, fun s hs => labelAt_monotone hn hn' hs,
    fun s _ j => fracRoots_deriv_nonneg hL hc _ _ hδ s j,
    fun s _ => by rw [sum_deriv_fracRoots hL hc, hsum], ?_⟩
  rw [← fracRoots_zero L c n (labelIncrement n n'), ← fracRoots_one L c n n']
  have hcoord : ∀ j, |fracRoots L c (realLabels n) (labelIncrement n n') 1 j -
      fracRoots L c (realLabels n) (labelIncrement n n') 0 j| =
      fracRoots L c (realLabels n) (labelIncrement n n') 1 j -
      fracRoots L c (realLabels n) (labelIncrement n n') 0 j := fun j =>
    abs_of_nonneg (sub_nonneg.mpr (fracRoots_mono_of_nonneg hL hc _ _ hδ j))
  rw [Finset.sum_congr rfl (fun j _ => hcoord j), sum_fracRoots_sub hL hc, hsum]

/-- `adj:lem:total-displacement`, case `a > b`: all signs reverse and the last identity has
`|b - a|` on its right side. -/
theorem total_displacement_decrease {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n n' : Fin N → ℤ} (hn : Monotone n) (hn' : Monotone n')
    {a b : ℤ} (hba : b < a) {k : Fin N} (hk : n k = a)
    (hrep : ∃ σ : Equiv.Perm (Fin N), ∀ i, n' (σ i) = Function.update n k b i) :
    (∀ i, labelIncrement n n' i ≤ 0) ∧
    ∑ i, labelIncrement n n' i = (b : ℝ) - a ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1, Monotone (labelAt (realLabels n) (labelIncrement n n') s)) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ j,
      deriv (fracRoots L c (realLabels n) (labelIncrement n n')) s j ≤ 0) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∑ j, deriv (fracRoots L c (realLabels n) (labelIncrement n n')) s j =
        2 * Real.pi / L * ((b : ℝ) - a)) ∧
    ∑ j, |BetheSmooth.roots L n' c j - BetheSmooth.roots L n c j| =
      2 * Real.pi / L * |(b : ℝ) - a| := by
  obtain ⟨σ, hσ⟩ := hrep
  have hδ := labelIncrement_nonpos_of_decrease hn hn' hba hk hσ
  have hsum := sum_labelIncrement hk hσ
  refine ⟨hδ, hsum, fun s hs => labelAt_monotone hn hn' hs,
    fun s _ j => fracRoots_deriv_nonpos hL hc _ _ hδ s j,
    fun s _ => by rw [sum_deriv_fracRoots hL hc, hsum], ?_⟩
  rw [← fracRoots_zero L c n (labelIncrement n n'), ← fracRoots_one L c n n']
  have hcoord : ∀ j, |fracRoots L c (realLabels n) (labelIncrement n n') 1 j -
      fracRoots L c (realLabels n) (labelIncrement n n') 0 j| =
      fracRoots L c (realLabels n) (labelIncrement n n') 0 j -
      fracRoots L c (realLabels n) (labelIncrement n n') 1 j := fun j => by
    rw [abs_sub_comm]
    exact abs_of_nonneg (sub_nonneg.mpr (fracRoots_mono_of_nonpos hL hc _ _ hδ j))
  have hneg : ∑ j, (fracRoots L c (realLabels n) (labelIncrement n n') 0 j -
      fracRoots L c (realLabels n) (labelIncrement n n') 1 j) =
      -∑ j, (fracRoots L c (realLabels n) (labelIncrement n n') 1 j -
        fracRoots L c (realLabels n) (labelIncrement n n') 0 j) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hba' : (b : ℝ) < a := by exact_mod_cast hba
  rw [Finset.sum_congr rfl (fun j _ => hcoord j), hneg, sum_fracRoots_sub hL hc, hsum,
    abs_of_neg (by linarith : (b : ℝ) - a < 0)]
  ring

end QuantumNLS.RootDisplacement

#print axioms QuantumNLS.RootDisplacement.logLabel
#print axioms QuantumNLS.RootDisplacement.fracRoots_zero
#print axioms QuantumNLS.RootDisplacement.fracRoots_one
#print axioms QuantumNLS.RootDisplacement.forcingPath_hasDerivAt
#print axioms QuantumNLS.RootDisplacement.root_contDiffAt_forcing
#print axioms QuantumNLS.RootDisplacement.gaudin_eq_Bmat
#print axioms QuantumNLS.RootDisplacement.Bmat_apply_eq_gaudin
#print axioms QuantumNLS.RootDisplacement.gaudin_deriv_eq
#print axioms QuantumNLS.RootDisplacement.printed_equation
#print axioms QuantumNLS.RootDisplacement.deriv_eq_Bmat_inv
#print axioms QuantumNLS.RootDisplacement.deriv_fracRoots_eq_inv
#print axioms QuantumNLS.RootDisplacement.gaudin_sum
#print axioms QuantumNLS.RootDisplacement.sum_deriv_fracRoots
#print axioms QuantumNLS.RootDisplacement.fracRoots_deriv_nonneg
#print axioms QuantumNLS.RootDisplacement.fracRoots_deriv_nonpos
#print axioms QuantumNLS.RootDisplacement.fracRoots_mono_of_nonneg
#print axioms QuantumNLS.RootDisplacement.fracRoots_mono_of_nonpos
#print axioms QuantumNLS.RootDisplacement.sum_fracRoots_sub
#print axioms QuantumNLS.RootDisplacement.le_of_countLE_le
#print axioms QuantumNLS.RootDisplacement.countLE_update
#print axioms QuantumNLS.RootDisplacement.sum_labelIncrement
#print axioms QuantumNLS.RootDisplacement.labelIncrement_nonneg_of_increase
#print axioms QuantumNLS.RootDisplacement.labelIncrement_nonpos_of_decrease
#print axioms QuantumNLS.RootDisplacement.labelAt_monotone
#print axioms QuantumNLS.RootDisplacement.total_displacement_increase
#print axioms QuantumNLS.RootDisplacement.total_displacement_decrease
