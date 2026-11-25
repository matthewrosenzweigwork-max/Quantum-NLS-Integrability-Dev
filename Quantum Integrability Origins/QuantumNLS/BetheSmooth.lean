import QuantumNLS.BetheRoots
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
Smooth positive-coupling Bethe roots (R-4C8D7C9E).
Report pin: 3b1f701a43a387dd5a779bad3ceb2c56c3c2a53f.
Frozen BetheRoots: 6e37db68702ad1adf1f85a0f65641734bb8af2a78de701a273a8eb5052a14fc4.
Sources: foundations/periodic_basis.tex:133--162; root_response/F02.tex:13--81.
The forcing is arbitrary and fixed. No spectral basis or completeness is assumed.
-/

noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter

namespace QuantumNLS.BetheSmooth
open BetheAdmission BetheRoots

/-- Select the unique solution whose existence was proved by minimization.
The value outside the physical positive quadrant is only a totalization. -/
def root {N : ℕ} (L : ℝ) (b : Fin N → ℝ) (c : ℝ) : Fin N → ℝ :=
  if h : 0 < L ∧ 0 < c then (logMap_surjective h.1 h.2 b).choose else 0

theorem root_solves {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (b : Fin N → ℝ) : logMap L c (root L b c) = b := by
  simp only [root, dite_eq_left (show 0 < L ∧ 0 < c from ⟨hL, hc⟩)]
  exact (logMap_surjective hL hc b).choose_spec

theorem eq_root {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {b q : Fin N → ℝ} (hq : logMap L c q = b) : q = root L b c :=
  logMap_injective hL hc (hq.trans (root_solves hL hc b).symm)

theorem gaudin_isInvertible {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (q : Fin N → ℝ) : (gaudin L c q).IsInvertible := by
  have hb := gaudin_bijective hL hc q
  exact ⟨ContinuousLinearEquiv.ofBijective (gaudin L c q)
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2), rfl⟩

/-- Joint smoothness is local only at nonzero coupling; it includes colliding
configurations, so no ordered-chamber hypothesis is concealed here. -/
theorem logMap_contDiffAt {N : ℕ} (L : ℝ) {c : ℝ} (hc : c ≠ 0)
    (q : Fin N → ℝ) :
    ContDiffAt ℝ ∞ (fun p : ℝ × (Fin N → ℝ) => logMap L p.1 p.2) (c, q) := by
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

/-- The partial derivative used by the implicit function theorem is the
proved, actual Gaudin map, rather than an assumed inverse-Jacobian field. -/
theorem logMap_partial_q {N : ℕ} (L : ℝ) {c : ℝ} (hc : 0 < c)
    (q : Fin N → ℝ) :
    fderiv ℝ (fun p : ℝ × (Fin N → ℝ) => logMap L p.1 p.2) (c, q) ∘L
      ContinuousLinearMap.inr ℝ ℝ (Fin N → ℝ) = gaudin L c q := by
  have hd := ((logMap_contDiffAt L hc.ne' q).differentiableAt (by simp)).hasFDerivAt
  have he : HasFDerivAt (fun x : Fin N → ℝ => (c, x))
      (ContinuousLinearMap.inr ℝ ℝ (Fin N → ℝ)) q := by
    convert (hasFDerivAt_const c q).prodMk (hasFDerivAt_id q) using 1 <;> ext <;> simp
  exact (hd.comp q he).unique (logMap_hasFDerivAt L hc q)

/-- Smooth dependence on all positive couplings of the globally unique roots.
Local implicit branches agree with the selected minimizer by uniqueness. -/
theorem root_contDiffAt {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (b : Fin N → ℝ) : ContDiffAt ℝ ∞ (root L b) c := by
  let q := root L b c
  let f := fun p : ℝ × (Fin N → ℝ) => logMap L p.1 p.2
  have hs : ContDiffAt ℝ ∞ f (c, q) := logMap_contDiffAt L hc.ne' q
  have hi : (fderiv ℝ f (c, q) ∘L ContinuousLinearMap.inr ℝ ℝ (Fin N → ℝ)).IsInvertible := by
    rw [logMap_partial_q L hc q]
    exact gaudin_isInvertible hL hc q
  let ψ := hs.implicitFunction (by simp) hi
  have he : root L b =ᶠ[𝓝 c] ψ := by
    filter_upwards [hs.eventually_apply_implicitFunction (by simp) hi,
      isOpen_Ioi.mem_nhds hc] with d hd hdpos
    exact (eq_root hL hdpos (hd.trans (root_solves hL hc b))).symm
  exact (hs.contDiffAt_implicitFunction (by simp) hi).congr_of_eventuallyEq he

theorem root_contDiffOn {N : ℕ} {L : ℝ} (hL : 0 < L) (b : Fin N → ℝ) :
    ContDiffOn ℝ ∞ (root L b) (Ioi 0) :=
  fun _c hc => (root_contDiffAt hL hc b).contDiffWithinAt

/-- Actual corrected-integer-label roots, in the increasing convention of
BetheAdmission. Reversing ranks gives the source's decreasing convention. -/
def roots {N : ℕ} (L : ℝ) (n : Fin N → ℤ) : ℝ → (Fin N → ℝ) :=
  root L (fun i => 2 * Real.pi * quantumNumbers n i)

theorem roots_solves {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (n : Fin N → ℤ) : Solves L c n (roots L n c) :=
  fun i => congrFun (root_solves hL hc _) i

theorem roots_contDiffOn {N : ℕ} {L : ℝ} (hL : 0 < L) (n : Fin N → ℤ) :
    ContDiffOn ℝ ∞ (roots L n) (Ioi 0) := root_contDiffOn hL _

/-- The positive-coupling derivative forcing, with the sign obtained by
moving the fixed-root coupling derivative to the right-hand side. -/
def couplingForce {N : ℕ} (c : ℝ) (q : Fin N → ℝ) : Fin N → ℝ :=
  fun i => ∑ j, 2 * (q i - q j) / (c^2 + (q i - q j)^2)

/-- Differentiate the literal equations along any differentiable root curve. -/
theorem logMap_curve_hasDerivAt {N : ℕ} (L : ℝ) {c : ℝ} (hc : 0 < c)
    {q : ℝ → (Fin N → ℝ)} {v : Fin N → ℝ} (hq : HasDerivAt q v c) :
    HasDerivAt (fun d => logMap L d (q d))
      (gaudin L c (q c) v - couplingForce c (q c)) c := by
  apply hasDerivAt_pi.mpr
  intro i
  have hi := hasDerivAt_pi.mp hq
  have hj (j : Fin N) : HasDerivAt
      (fun d => 2 * Real.arctan ((q d i - q d j) / d))
      (edgeWeight c (q c) i j * (v i - v j) -
        2 * (q c i - q c j) / (c^2 + (q c i - q c j)^2)) c := by
    convert! ((((hi i).sub (hi j)).div (hasDerivAt_id c) hc.ne').arctan).const_mul 2 using 1
    have hd : c^2 + (q c i - q c j)^2 ≠ 0 := by positivity
    have hd' : 1 + ((q c i - q c j) / c)^2 ≠ 0 := by positivity
    dsimp [edgeWeight]
    field_simp
  convert! ((hi i).const_mul L).add
    (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hj j)) using 1
  · funext d
    simp only [logMap, Finset.mul_sum, Pi.add_apply]
  · simp only [Pi.sub_apply, gaudin_apply, couplingForce, Finset.sum_sub_distrib]
    ring

/-- Differentiability is a consequence of proved smoothness. -/
theorem root_hasDerivAt {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (b : Fin N → ℝ) : HasDerivAt (root L b) (deriv (root L b) c) c :=
  ((root_contDiffAt hL hc b).differentiableAt (by simp)).hasDerivAt

/-- The actual differentiated fixed-label equation B q' = forcing. -/
theorem root_derivative_equation {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (b : Fin N → ℝ) :
    gaudin L c (root L b c) (deriv (root L b) c) = couplingForce c (root L b c) := by
  have hd := logMap_curve_hasDerivAt L hc (root_hasDerivAt hL hc b)
  have he : (fun d => logMap L d (root L b d)) =ᶠ[𝓝 c] (fun _ => b) := by
    filter_upwards [isOpen_Ioi.mem_nhds hc] with d hd
    exact root_solves hL hd b
  have hz := (hd.congr_of_eventuallyEq he.symm).unique (hasDerivAt_const c b)
  exact sub_eq_zero.mp hz

/-- Explicit inverse-Gaudin formula, with no assumed derivative. -/
theorem root_deriv_eq {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (b : Fin N → ℝ) :
    deriv (root L b) c =
      (gaudin L c (root L b c)).inverse (couplingForce c (root L b c)) := by
  rw [← root_derivative_equation hL hc b,
    (gaudin_isInvertible hL hc _).inverse_apply_self]

theorem couplingForce_scaled {N : ℕ} (L c : ℝ) (q : Fin N → ℝ) :
    c • couplingForce c q = gaudin L c q q - L • q := by
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, couplingForce, gaudin_apply, Pi.sub_apply,
    Finset.mul_sum, edgeWeight]
  rw [add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Source F02 derivative-identity, z = c ∂c q. -/
theorem root_scaled_derivative_equation {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (b : Fin N → ℝ) :
    gaudin L c (root L b c) (c • deriv (root L b) c) =
      gaudin L c (root L b c) (root L b c) - L • root L b c := by
  rw [map_smul, root_derivative_equation hL hc b, couplingForce_scaled]

/-- Source F02 inverse formula B⁻¹q = (q-cq')/L, without division. -/
theorem root_scaled_deriv_eq {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (b : Fin N → ℝ) :
    c • deriv (root L b) c = root L b c -
      L • (gaudin L c (root L b c)).inverse (root L b c) := by
  apply (gaudin_isInvertible hL hc _).injective
  rw [root_scaled_derivative_equation hL hc b, map_sub, map_smul,
    (gaudin_isInvertible hL hc _).self_apply_inverse]

/-- Entrywise nonnegativity of the actual inverse Gaudin map, proved by
the minimum-component argument in F01 (also valid for N=0). -/
theorem gaudin_inverse_nonneg {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (q : Fin N → ℝ) {b : Fin N → ℝ} (hb : ∀ i, 0 ≤ b i) :
    ∀ i, 0 ≤ (gaudin L c q).inverse b i := by
  let v := (gaudin L c q).inverse b
  have hv : gaudin L c q v = b := (gaudin_isInvertible hL hc q).self_apply_inverse b
  intro k
  by_contra hk
  have hk' : v k < 0 := lt_of_not_ge hk
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ v ⟨k, Finset.mem_univ k⟩
  have hvi : v i < 0 := lt_of_le_of_lt (hi k (Finset.mem_univ k)) hk'
  have hs : (∑ j, edgeWeight c q i j * (v i - v j)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    exact mul_nonpos_of_nonneg_of_nonpos (edgeWeight_pos hc q i j).le
      (sub_nonpos.mpr (hi j (Finset.mem_univ j)))
  have he := congrFun hv i
  rw [gaudin_apply] at he
  have := hb i
  have := mul_neg_of_pos_of_neg hL hvi
  linarith

/-- Inverse-Gaudin quadratic positivity and its sharp L⁻¹ upper bound.
This is proved from the quadratic lower bound, not assumed spectrally. -/
theorem gaudin_inverse_quadratic_bounds {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (q : Fin N → ℝ) :
    0 ≤ (∑ i, q i * (gaudin L c q).inverse q i) ∧
    L * (∑ i, q i * (gaudin L c q).inverse q i) ≤ ∑ i, (q i)^2 := by
  let v := (gaudin L c q).inverse q
  have hv : gaudin L c q v = q := (gaudin_isInvertible hL hc q).self_apply_inverse q
  have hl := gaudin_lower_bound L hc q v
  rw [hv] at hl
  have he : (∑ i, v i * q i) = ∑ i, q i * v i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at hl
  have hV : 0 ≤ ∑ i, (v i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  refine ⟨le_trans (mul_nonneg hL.le hV) hl, ?_⟩
  have hn : 0 ≤ ∑ i, (q i - L * v i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hn' : (∑ i, (q i - L * v i)^2) =
      (∑ i, (q i)^2) - 2 * L * (∑ i, q i * v i) + L^2 * ∑ i, (v i)^2 := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hn'] at hn
  have hmul := mul_le_mul_of_nonneg_left hl hL.le
  dsimp [v] at *
  nlinarith

/-- Unnormalized finite quadratic energy, with fixed forcing. -/
def energy {N : ℕ} (L : ℝ) (b : Fin N → ℝ) (c : ℝ) : ℝ :=
  ∑ i, (root L b c i)^2

theorem energy_hasDerivAt {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (b : Fin N → ℝ) :
    HasDerivAt (energy L b) (2 * ∑ i, root L b c i * deriv (root L b) c i) c := by
  have hi := hasDerivAt_pi.mp (root_hasDerivAt hL hc b)
  convert! HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hi i).pow 2) using 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp
  ring

/-- Actual finite energy response, source F07, before division by N. -/
theorem energy_scaled_deriv_eq {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (b : Fin N → ℝ) :
    c * deriv (energy L b) c = 2 * energy L b c -
      2 * L * ∑ i, root L b c i * (gaudin L c (root L b c)).inverse (root L b c) i := by
  rw [(energy_hasDerivAt hL hc b).deriv]
  have hz := root_scaled_deriv_eq hL hc b
  have he (i : Fin N) : c * deriv (root L b) c i = root L b c i -
      L * (gaudin L c (root L b c)).inverse (root L b c) i := by
    exact congrFun hz i
  unfold energy
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  linear_combination 2 * root L b c i * he i

/-- Repulsive fixed-label energy is nondecreasing, with the exact source
bound 0 ≤ c E' ≤ 2 E. Individual rapidity derivatives need not be positive. -/
theorem energy_scaled_deriv_bounds {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (b : Fin N → ℝ) :
    0 ≤ c * deriv (energy L b) c ∧ c * deriv (energy L b) c ≤ 2 * energy L b c := by
  rw [energy_scaled_deriv_eq hL hc b]
  have h := gaudin_inverse_quadratic_bounds hL hc (root L b c)
  change 0 ≤ 2 * energy L b c - 2 * L * _ ∧ _ ≤ 2 * energy L b c
  dsimp [energy]
  constructor <;> nlinarith [mul_nonneg hL.le h.1]

/-- The literal zero-based decreasing-rank correction in periodic_basis:
I_j = n_j + (N-1)/2 - j. -/
def sourceNumbers {N : ℕ} (n : Fin N → ℤ) (i : Fin N) : ℝ :=
  (n i : ℝ) + ((N : ℝ) - 1) / 2 - (i.val : ℝ)

/-- Source-normalized forcing and root curve for decreasing Bose labels. -/
def sourceRoots {N : ℕ} (L : ℝ) (n : Fin N → ℤ) : ℝ → (Fin N → ℝ) :=
  root L (fun i => 2 * Real.pi * sourceNumbers n i)

theorem sourceRoots_solves {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (n : Fin N → ℤ) :
    logMap L c (sourceRoots L n c) = fun i => 2 * Real.pi * sourceNumbers n i :=
  root_solves hL hc _

theorem sourceRoots_strictAnti {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin N → ℤ} (hn : Antitone n) : StrictAnti (sourceRoots L n c) := by
  intro i j hij
  have hn' : (n j : ℝ) ≤ n i := by exact_mod_cast hn hij.le
  have hi' : (i.val : ℝ) < j.val := by exact_mod_cast hij
  have hI : sourceNumbers n j < sourceNumbers n i := by
    unfold sourceNumbers
    linarith
  by_contra hq
  have hm := logMap_coordinate_mono hL.le hc (sourceRoots L n c) (le_of_not_gt hq)
  rw [sourceRoots_solves hL hc n] at hm
  exact (not_le_of_gt (mul_lt_mul_of_pos_left hI (by positivity : 0 < 2 * Real.pi))) hm

theorem sourceRoots_norm_bound {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (n : Fin N → ℤ) :
    Real.sqrt (∑ i, (sourceRoots L n c i)^2) ≤
      2 * Real.pi * Real.sqrt (∑ i, (sourceNumbers n i)^2) / L := by
  have hb := solution_sq_bound hL hc _ _ (sourceRoots_solves hL hc n)
  have hsum : (∑ i, (2 * Real.pi * sourceNumbers n i)^2) =
      (2 * Real.pi)^2 * ∑ i, (sourceNumbers n i)^2 := by
    simp only [mul_pow, Finset.mul_sum]
  rw [hsum] at hb
  have hQ : 0 ≤ ∑ i, (sourceRoots L n c i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hI : 0 ≤ ∑ i, (sourceNumbers n i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  apply (le_div_iff₀ hL).mpr
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hL.le)
    (mul_nonneg (by positivity) (Real.sqrt_nonneg _))).mp
  simpa only [mul_pow, Real.sq_sqrt hQ, Real.sq_sqrt hI, mul_comm] using hb

/-- The full R-4C8D7C9E root statement, in its printed decreasing convention.
The sum over all j equals the source's j≠i sum (`logMap_erase`). -/
theorem source_roots_spec {N : ℕ} {L : ℝ} (hL : 0 < L)
    {n : Fin N → ℤ} (hn : Antitone n) :
    ContDiffOn ℝ ∞ (sourceRoots L n) (Ioi 0) ∧
    ∀ c : ℝ, 0 < c →
      logMap L c (sourceRoots L n c) = (fun i => 2 * Real.pi * sourceNumbers n i) ∧
      StrictAnti (sourceRoots L n c) ∧
      Real.sqrt (∑ i, (sourceRoots L n c i)^2) ≤
        2 * Real.pi * Real.sqrt (∑ i, (sourceNumbers n i)^2) / L ∧
      ∀ q, logMap L c q = (fun i => 2 * Real.pi * sourceNumbers n i) →
        q = sourceRoots L n c := by
  refine ⟨root_contDiffOn hL _, fun c hc =>
    ⟨sourceRoots_solves hL hc n, sourceRoots_strictAnti hL hc hn,
      sourceRoots_norm_bound hL hc n, ?_⟩⟩
  intro q hq
  exact eq_root hL hc hq

end QuantumNLS.BetheSmooth

#print axioms QuantumNLS.BetheSmooth.root
#print axioms QuantumNLS.BetheSmooth.root_solves
#print axioms QuantumNLS.BetheSmooth.eq_root
#print axioms QuantumNLS.BetheSmooth.gaudin_isInvertible
#print axioms QuantumNLS.BetheSmooth.logMap_contDiffAt
#print axioms QuantumNLS.BetheSmooth.logMap_partial_q
#print axioms QuantumNLS.BetheSmooth.root_contDiffAt
#print axioms QuantumNLS.BetheSmooth.root_contDiffOn
#print axioms QuantumNLS.BetheSmooth.roots
#print axioms QuantumNLS.BetheSmooth.roots_solves
#print axioms QuantumNLS.BetheSmooth.roots_contDiffOn
#print axioms QuantumNLS.BetheSmooth.couplingForce
#print axioms QuantumNLS.BetheSmooth.logMap_curve_hasDerivAt
#print axioms QuantumNLS.BetheSmooth.root_hasDerivAt
#print axioms QuantumNLS.BetheSmooth.root_derivative_equation
#print axioms QuantumNLS.BetheSmooth.root_deriv_eq
#print axioms QuantumNLS.BetheSmooth.couplingForce_scaled
#print axioms QuantumNLS.BetheSmooth.root_scaled_derivative_equation
#print axioms QuantumNLS.BetheSmooth.root_scaled_deriv_eq
#print axioms QuantumNLS.BetheSmooth.gaudin_inverse_nonneg
#print axioms QuantumNLS.BetheSmooth.gaudin_inverse_quadratic_bounds
#print axioms QuantumNLS.BetheSmooth.energy
#print axioms QuantumNLS.BetheSmooth.energy_hasDerivAt
#print axioms QuantumNLS.BetheSmooth.energy_scaled_deriv_eq
#print axioms QuantumNLS.BetheSmooth.energy_scaled_deriv_bounds
#print axioms QuantumNLS.BetheSmooth.sourceNumbers
#print axioms QuantumNLS.BetheSmooth.sourceRoots
#print axioms QuantumNLS.BetheSmooth.sourceRoots_solves
#print axioms QuantumNLS.BetheSmooth.sourceRoots_strictAnti
#print axioms QuantumNLS.BetheSmooth.sourceRoots_norm_bound
#print axioms QuantumNLS.BetheSmooth.source_roots_spec
