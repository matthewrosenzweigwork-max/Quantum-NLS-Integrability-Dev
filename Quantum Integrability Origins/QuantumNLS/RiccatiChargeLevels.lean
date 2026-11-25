import Mathlib
import QuantumNLS.RiccatiResidualBound
import QuantumNLS.RiccatiSobolevS
import QuantumNLS.RiccatiDerivative

/-!
# R-3FEAD88B stage E4-3c: level-indexed charges and the bottom-level identity

Source: `source-text/chapters/foundations/riccati_expansion.tex` (proof of `values:prop:riccati`, residual `E_M`,
lines 25-38) and the charge recursion `w_{n+1} = -i ∂ w_n + κ v ∑_{a=1}^{n-1} w_a w_{n-a}`, with
`κ = κ_model = κ_phys / L`.

Model. An `Ell2` element `x` represents the field `toField L t x` at level `t`, and its norm is the periodic `H^t`
norm. `derCLM` (E4-1) sends level `t+1` to level `t` with norm ≤ 1; `iotaEll` (E4-0) sends a level `S` element to a
lower level `t ≤ S` with norm ≤ 1; `mulBil` (E3-pre) is the algebra product at a level `t > 1/2`.

Level clamp. `lv S M n = S - min(n, M) + 1`, so `lv S M n = S - n + 1` for `n ≤ M` (the review record's `t_n`). Clamping
keeps every level above `1/2`, so no proof obligation depends on `n` beyond the `n ≤ M` range used below.

Contents.
* `chg`: the level-indexed charges, with `chg 1 = u` and `chg (n+2) = -(i ∂ chg (n+1)) + κ v ∑ chg j chg (n+1-j)`
  (products at level `lv (n+2)`). Uniform bound `‖chg n‖ ≤ bnd n`, where `bnd` depends only on `|κ|`, `ρ` (bounding
  `‖u‖, ‖v‖ ≤ ρ`), `M` and `L`, not on `u, v` beyond `ρ`: this is the uniform bound on a bounded set.
* `dDom`, `dmulEll`, `exists_dext`: the coefficient multiplier `dSymb` on its domain, and a total linear extension `D`.
  Only values of `D` on `dDom` are used. The domain contains the bottom images below.
* `wAbs`, `wAbs_identity`: the bottom-level instance `(X, m, D) = (Ell2, mulLin_a, D)` at level `a`, with charges
  `wAbs n = lowT a (lv n) (chg n)` for `1 ≤ n ≤ M`. `resid_formula` and `resid_norm_le` apply to `wAbs` at level `a`.
* `‖D (wAbs M)‖ ≤ bnd M` (the KD hypothesis of `resid_norm_le`), `‖wAbs n‖ ≤ K` (the K hypothesis).

Standard axioms only. No sorry, admit, native_decide, or new axioms.
-/

set_option autoImplicit false
noncomputable section

open Complex Finset
open QuantumNLS.RiccatiSobolevE1 QuantumNLS.RiccatiSobolevE2b QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.RiccatiSobolevS QuantumNLS.RiccatiDerivative QuantumNLS.RiccatiCharges
open QuantumNLS.RiccatiResidualBound

namespace QuantumNLS.RiccatiChargeLevels

/-! ### 1. Generic history (structural replacement for non-structural recursion over sums) -/

/-- `hst z val m k`: the k-th entry after stage m; stage m+1 sets index m+1 to `val (m+1) (previous stage)`. -/
def hst {α : Type} (z : α) (val : ℕ → (ℕ → α) → α) : ℕ → ℕ → α
  | 0 => fun _ => z
  | m + 1 => fun k => if k = m + 1 then val (m + 1) (hst z val m) else hst z val m k

theorem hst_stab {α : Type} (z : α) (val : ℕ → (ℕ → α) → α) :
    ∀ m k : ℕ, k ≤ m → hst z val m k = hst z val k k := by
  intro m
  induction m with
  | zero =>
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    rfl
  | succ m ih =>
    intro k hk
    by_cases hkm : k = m + 1
    · subst hkm
      rfl
    · have hk' : k ≤ m := by omega
      show (if k = m + 1 then val (m + 1) (hst z val m) else hst z val m k) = hst z val k k
      rw [if_neg hkm]
      exact ih k hk'

theorem hst_succ_succ {α : Type} (z : α) (val : ℕ → (ℕ → α) → α) (n : ℕ)
    (hc : ∀ H H' : ℕ → α, (∀ j, j ≤ n + 1 → H j = H' j) → val (n + 2) H = val (n + 2) H') :
    hst z val (n + 2) (n + 2) = val (n + 2) (fun j => hst z val j j) := by
  have h1 : hst z val (n + 2) (n + 2) = val (n + 2) (hst z val (n + 1)) := by
    simp [hst]
  rw [h1]
  apply hc
  intro j hj
  exact hst_stab z val (n + 1) j hj

/-! ### 2. Levels -/

/-- Level of the n-th charge, clamped at M. -/
def lv (S : ℝ) (M n : ℕ) : ℝ := S - ((min n M : ℕ) : ℝ) + 1

theorem lv_eq {S : ℝ} {M n : ℕ} (hn : n ≤ M) : lv S M n = S - (n : ℝ) + 1 := by
  unfold lv
  rw [min_eq_left hn]

theorem lv_ge {a S : ℝ} {M : ℕ} (haS : a + (M : ℝ) + 1 ≤ S) (n : ℕ) : a + 2 ≤ lv S M n := by
  unfold lv
  have h1 : ((min n M : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast min_le_right n M
  linarith

theorem lv_ge_a {a S : ℝ} {M : ℕ} (haS : a + (M : ℝ) + 1 ≤ S) (n : ℕ) : a ≤ lv S M n := by
  linarith [lv_ge haS n]

theorem lv_pos {a S : ℝ} {M : ℕ} (ha : 1 / 2 < a) (haS : a + (M : ℝ) + 1 ≤ S) (n : ℕ) :
    1 / 2 < lv S M n := by
  linarith [lv_ge haS n]

theorem lv_le_top {S : ℝ} {M n : ℕ} (hM : 1 ≤ M) (hn : 1 ≤ n) : lv S M n ≤ S := by
  unfold lv
  have h1 : (1 : ℝ) ≤ ((min n M : ℕ) : ℝ) := by exact_mod_cast le_min hn hM
  linarith

theorem lv_one {S : ℝ} {M : ℕ} (hM : 1 ≤ M) : lv S M 1 = S := by
  rw [lv_eq hM]
  push_cast
  ring

theorem lv_succ {S : ℝ} {M n : ℕ} (hn : n + 1 ≤ M) : lv S M (n + 1) + 1 = lv S M n := by
  rw [lv_eq hn, lv_eq (Nat.le_of_succ_le hn)]
  push_cast
  ring

theorem lv_anti {S : ℝ} {M i j : ℕ} (hij : i ≤ j) (hjM : j ≤ M) : lv S M j ≤ lv S M i := by
  rw [lv_eq hjM, lv_eq (hij.trans hjM)]
  have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  linarith

/-! ### 3. Lowering the level (total wrapper over `iotaEll`) -/

/-- `lowT L p q x`: the element `x` (level `q`) viewed at level `p ≤ q`; the identity if `q < p`. -/
def lowT (L p q : ℝ) (x : Ell2) : Ell2 :=
  if h : p ≤ q then iotaEll (L := L) h x else x

theorem norm_lowT_le (L p q : ℝ) (x : Ell2) : ‖lowT L p q x‖ ≤ ‖x‖ := by
  unfold lowT
  split_ifs with h
  · exact norm_iotaEll_le h x
  · exact le_rfl

theorem toField_lowT {L p q : ℝ} (h : p ≤ q) (x : Ell2) :
    toField L p (lowT L p q x) = toField L q x := by
  unfold lowT
  rw [dif_pos h]
  exact toField_iota h x

theorem lowT_apply {L p q : ℝ} (h : p ≤ q) (x : Ell2) (k : ℤ) :
    ((lowT L p q x : Ell2) : ℤ → ℂ) k = ((incMult L p q k : ℝ) : ℂ) * x k := by
  unfold lowT
  rw [dif_pos h]
  rfl

/-! ### 4. Field-level bookkeeping -/

theorem toField_neg {L a : ℝ} (x : Ell2) : toField L a (-x) = fun k => -(toField L a x k) := by
  funext k
  simp [toField, neg_div]

theorem toField_sum {L a : ℝ} {ι : Type} (s : Finset ι) (f : ι → Ell2) :
    toField L a (∑ i ∈ s, f i) = ∑ i ∈ s, toField L a (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    funext k
    simp [toField]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, toField_add, ih]
    funext k
    simp

theorem toField_mulLin {L b : ℝ} (hL : 0 < L) (hb : 1 / 2 < b) (x y : Ell2) :
    toField L b (mulLin hL hb x y) = convC (toField L b x) (toField L b y) := by
  rw [show mulLin hL hb x y = mulEll hL hb x y from rfl]
  exact toField_mulEll hL hb x y

theorem toField_mulBil {L b : ℝ} (hL : 0 < L) (hb : 1 / 2 < b) (x y : Ell2) :
    toField L b (mulBil hL hb x y) = convC (toField L b x) (toField L b y) := by
  rw [mulBil_apply]
  exact toField_mulEll hL hb x y

theorem toField_inj {L a : ℝ} {x y : Ell2} (h : toField L a x = toField L a y) : x = y := by
  apply lp.ext
  funext k
  have hk := congrFun h k
  simp only [toField] at hk
  exact (div_left_inj' (pw_ne_zero L a k)).mp hk

theorem derCLM_apply (L : ℝ) (x : Ell2) : derCLM L x = derEll L x := rfl

/-! ### 5. The coefficient multiplier on its domain, and a total linear extension -/

/-- Elements whose coefficient multiplier `dSymb` stays in `ℓ²`. -/
def dDom (L : ℝ) : Submodule ℂ Ell2 where
  carrier := {y | Memℓp (fun k => dSymb L k * ((y : Ell2) : ℤ → ℂ) k) 2}
  add_mem' := by
    intro y z hy hz
    show Memℓp (fun k => dSymb L k * ((y + z : Ell2) : ℤ → ℂ) k) 2
    have h := Memℓp.add hy hz
    convert h using 1
    funext k
    simp [mul_add, Pi.add_apply]
  zero_mem' := by
    show Memℓp (fun k => dSymb L k * ((0 : Ell2) : ℤ → ℂ) k) 2
    have h0 : (fun k => dSymb L k * ((0 : Ell2) : ℤ → ℂ) k) = 0 := by
      funext k
      simp
    rw [h0]
    exact zero_memℓp
  smul_mem' := by
    intro c y hy
    show Memℓp (fun k => dSymb L k * ((c • y : Ell2) : ℤ → ℂ) k) 2
    have h := Memℓp.const_smul hy c
    convert h using 1
    funext k
    simp [mul_left_comm, Pi.smul_apply]

/-- The multiplier `dSymb` applied to an element of `dDom`. -/
def dmulEll (L : ℝ) (y : dDom L) : Ell2 :=
  ⟨fun k => dSymb L k * ((y : Ell2) : ℤ → ℂ) k, y.2⟩

theorem toField_dmulEll {L a : ℝ} (y : dDom L) :
    toField L a (dmulEll L y) = dField L (toField L a (y : Ell2)) := by
  funext k
  simp only [toField, dField, dmulEll]
  ring

def dmulLin (L : ℝ) : dDom L →ₗ[ℂ] Ell2 where
  toFun y := dmulEll L y
  map_add' y z := by
    apply lp.ext
    funext k
    exact mul_add _ _ _
  map_smul' c y := by
    apply lp.ext
    funext k
    exact mul_left_comm _ _ _

/-- A total linear extension `D` of the multiplier `dSymb` from `dDom`. Its values off `dDom` are arbitrary. -/
theorem exists_dext (L : ℝ) :
    ∃ D : Ell2 →ₗ[ℂ] Ell2, ∀ y : dDom L, D (y : Ell2) = dmulEll L y := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (dmulLin L)
  refine ⟨g, fun y => ?_⟩
  have h := LinearMap.congr_fun hg y
  simpa [dmulLin] using h

/-- The frequency bound `|freq_k| · pw_a/pw_p ≤ 1` for `p ≥ a + 1`. -/
theorem freq_incMult_le {L a p : ℝ} (hap : a + 1 ≤ p) (k : ℤ) :
    |freq L k| * incMult L a p k ≤ 1 := by
  unfold incMult
  have h1 : pw L (a + 1) k ≤ pw L p k := pw_le_pw hap k
  rw [pw_succ] at h1
  rw [← mul_div_assoc, div_le_one (pw_pos L p k)]
  nlinarith [abs_nonneg (freq L k), pw_pos L a k]

theorem dmul_lowT_pointwise {L a p : ℝ} (hap : a + 1 ≤ p) (x : Ell2) (k : ℤ) :
    ‖dSymb L k * ((lowT L a p x : Ell2) : ℤ → ℂ) k‖ ≤ ‖x k‖ := by
  have hap' : a ≤ p := by linarith
  rw [lowT_apply hap' x k, norm_mul, norm_mul, norm_dSymb, Complex.norm_real,
    Real.norm_of_nonneg (incMult_nonneg L a p k)]
  calc |freq L k| * (incMult L a p k * ‖x k‖)
      = (|freq L k| * incMult L a p k) * ‖x k‖ := by ring
    _ ≤ 1 * ‖x k‖ := mul_le_mul_of_nonneg_right (freq_incMult_le hap k) (norm_nonneg _)
    _ = ‖x k‖ := one_mul _

theorem lowT_mem_dDom {L a p : ℝ} (hap : a + 1 ≤ p) (x : Ell2) : lowT L a p x ∈ dDom L := by
  show Memℓp (fun k => dSymb L k * ((lowT L a p x : Ell2) : ℤ → ℂ) k) 2
  apply memℓp_gen
  rw [two_toReal]
  simp only [Real.rpow_two]
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) (summable_sq x)
  exact pow_le_pow_left₀ (norm_nonneg _) (dmul_lowT_pointwise hap x k) 2

theorem norm_dmulEll_le_of_lowT {L a p : ℝ} (hap : a + 1 ≤ p) (x : Ell2) :
    ‖dmulEll L ⟨lowT L a p x, lowT_mem_dDom hap x⟩‖ ≤ ‖x‖ := by
  have h := norm_le_of_pointwise (x := x) (y := dmulEll L ⟨lowT L a p x, lowT_mem_dDom hap x⟩)
    (C := 1) zero_le_one (fun k => by
      rw [one_mul]
      exact dmul_lowT_pointwise hap x k)
  rw [one_mul] at h
  exact h

/-! ### 6. Level-indexed charges -/

/-- The j-th summand of the product sum at stage `n + 2` (level `lv (n+2)`). -/
def termChg {a S : ℝ} {M : ℕ} (L : ℝ) (hL : 0 < L) (ha : 1 / 2 < a) (haS : a + (M : ℝ) + 1 ≤ S)
    (n : ℕ) (H : ℕ → Ell2) (j : ℕ) : Ell2 :=
  (mulBil hL (lv_pos ha haS (n + 2)))
    (lowT L (lv S M (n + 2)) (lv S M j) (H j))
    (lowT L (lv S M (n + 2)) (lv S M (n + 1 - j)) (H (n + 1 - j)))

/-- The recursion values: stage `N` given the history `H` of earlier charges. -/
def valChg {a S : ℝ} {M : ℕ} (L : ℝ) (hL : 0 < L) (ha : 1 / 2 < a) (haS : a + (M : ℝ) + 1 ≤ S)
    (κ : ℂ) (u v : Ell2) : ℕ → (ℕ → Ell2) → Ell2
  | 0, _ => 0
  | 1, _ => u
  | n + 2, H =>
    -(Complex.I • derCLM L (H (n + 1)))
      + κ • (mulBil hL (lv_pos ha haS (n + 2))) (lowT L (lv S M (n + 2)) S v)
        (∑ j ∈ Finset.Ico 1 (n + 1), termChg L hL ha haS n H j)

theorem valChg_congr {a S : ℝ} {M : ℕ} (L : ℝ) (hL : 0 < L) (ha : 1 / 2 < a)
    (haS : a + (M : ℝ) + 1 ≤ S) (κ : ℂ) (u v : Ell2) (n : ℕ) :
    ∀ H H' : ℕ → Ell2, (∀ j, j ≤ n + 1 → H j = H' j) →
      valChg L hL ha haS κ u v (n + 2) H = valChg L hL ha haS κ u v (n + 2) H' := by
  intro H H' h
  have hs : (∑ j ∈ Finset.Ico 1 (n + 1), termChg L hL ha haS n H j)
      = ∑ j ∈ Finset.Ico 1 (n + 1), termChg L hL ha haS n H' j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Ico] at hj
    unfold termChg
    rw [h j (by omega), h (n + 1 - j) (by omega)]
  show -(Complex.I • derCLM L (H (n + 1)))
      + κ • (mulBil hL (lv_pos ha haS (n + 2))) (lowT L (lv S M (n + 2)) S v)
        (∑ j ∈ Finset.Ico 1 (n + 1), termChg L hL ha haS n H j)
      = -(Complex.I • derCLM L (H' (n + 1)))
      + κ • (mulBil hL (lv_pos ha haS (n + 2))) (lowT L (lv S M (n + 2)) S v)
        (∑ j ∈ Finset.Ico 1 (n + 1), termChg L hL ha haS n H' j)
  rw [h (n + 1) le_rfl, hs]

/-- The level-indexed charges `chg N` (the charge `w_N` at level `lv S M N`). -/
def chg {a S : ℝ} {M : ℕ} (L : ℝ) (hL : 0 < L) (ha : 1 / 2 < a) (haS : a + (M : ℝ) + 1 ≤ S)
    (κ : ℂ) (u v : Ell2) (N : ℕ) : Ell2 :=
  hst 0 (valChg L hL ha haS κ u v) N N

theorem chg_one {a S : ℝ} {M : ℕ} (L : ℝ) (hL : 0 < L) (ha : 1 / 2 < a) (haS : a + (M : ℝ) + 1 ≤ S)
    (κ : ℂ) (u v : Ell2) : chg L hL ha haS κ u v 1 = u := by
  simp [chg, hst, valChg]

theorem chg_rec {a S : ℝ} {M : ℕ} (L : ℝ) (hL : 0 < L) (ha : 1 / 2 < a) (haS : a + (M : ℝ) + 1 ≤ S)
    (κ : ℂ) (u v : Ell2) (n : ℕ) :
    chg L hL ha haS κ u v (n + 2)
      = -(Complex.I • derCLM L (chg L hL ha haS κ u v (n + 1)))
        + κ • (mulBil hL (lv_pos ha haS (n + 2))) (lowT L (lv S M (n + 2)) S v)
          (∑ j ∈ Finset.Ico 1 (n + 1),
            (mulBil hL (lv_pos ha haS (n + 2)))
              (lowT L (lv S M (n + 2)) (lv S M j) (chg L hL ha haS κ u v j))
              (lowT L (lv S M (n + 2)) (lv S M (n + 1 - j)) (chg L hL ha haS κ u v (n + 1 - j)))) := by
  show hst 0 (valChg L hL ha haS κ u v) (n + 2) (n + 2) = _
  rw [hst_succ_succ 0 (valChg L hL ha haS κ u v) n (valChg_congr L hL ha haS κ u v n)]
  rfl

/-! ### 7. Uniform norm bounds -/

/-- Majorant recursion (real valued; `ρ` bounds `‖u‖, ‖v‖`). -/
def valBnd (L S : ℝ) (M : ℕ) (κ : ℂ) (ρ : ℝ) : ℕ → (ℕ → ℝ) → ℝ
  | 0, _ => 0
  | 1, _ => ρ
  | n + 2, H =>
    H (n + 1) + ‖κ‖ * (Cmul L (lv S M (n + 2))) ^ 2 * ρ
      * ∑ j ∈ Finset.Ico 1 (n + 1), H j * H (n + 1 - j)

theorem valBnd_congr (L S : ℝ) (M : ℕ) (κ : ℂ) (ρ : ℝ) (n : ℕ) :
    ∀ H H' : ℕ → ℝ, (∀ j, j ≤ n + 1 → H j = H' j) →
      valBnd L S M κ ρ (n + 2) H = valBnd L S M κ ρ (n + 2) H' := by
  intro H H' h
  have hs : (∑ j ∈ Finset.Ico 1 (n + 1), H j * H (n + 1 - j))
      = ∑ j ∈ Finset.Ico 1 (n + 1), H' j * H' (n + 1 - j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Ico] at hj
    rw [h j (by omega), h (n + 1 - j) (by omega)]
  show H (n + 1) + ‖κ‖ * (Cmul L (lv S M (n + 2))) ^ 2 * ρ
      * ∑ j ∈ Finset.Ico 1 (n + 1), H j * H (n + 1 - j)
      = H' (n + 1) + ‖κ‖ * (Cmul L (lv S M (n + 2))) ^ 2 * ρ
      * ∑ j ∈ Finset.Ico 1 (n + 1), H' j * H' (n + 1 - j)
  rw [h (n + 1) le_rfl, hs]

/-- The majorant `bnd N`. -/
def bnd (L S : ℝ) (M : ℕ) (κ : ℂ) (ρ : ℝ) (N : ℕ) : ℝ :=
  hst 0 (valBnd L S M κ ρ) N N

theorem bnd_rec (L S : ℝ) (M : ℕ) (κ : ℂ) (ρ : ℝ) (n : ℕ) :
    bnd L S M κ ρ (n + 2) = bnd L S M κ ρ (n + 1)
      + ‖κ‖ * (Cmul L (lv S M (n + 2))) ^ 2 * ρ
        * ∑ j ∈ Finset.Ico 1 (n + 1), bnd L S M κ ρ j * bnd L S M κ ρ (n + 1 - j) := by
  show hst 0 (valBnd L S M κ ρ) (n + 2) (n + 2) = _
  rw [hst_succ_succ 0 (valBnd L S M κ ρ) n (valBnd_congr L S M κ ρ n)]
  rfl

theorem bnd_props {a S : ℝ} {M : ℕ} (L : ℝ) (hL : 0 < L) (ha : 1 / 2 < a)
    (haS : a + (M : ℝ) + 1 ≤ S) (κ : ℂ) (u v : Ell2) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hu : ‖u‖ ≤ ρ) (hv : ‖v‖ ≤ ρ) :
    ∀ N : ℕ, 0 ≤ bnd L S M κ ρ N ∧ (1 ≤ N → ‖chg L hL ha haS κ u v N‖ ≤ bnd L S M κ ρ N) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases N with _ | _ | n
    · refine ⟨?_, fun h => absurd h (by norm_num)⟩
      show (0 : ℝ) ≤ hst 0 (valBnd L S M κ ρ) 0 0
      simp [hst]
    · refine ⟨?_, fun _ => ?_⟩
      · show (0 : ℝ) ≤ hst 0 (valBnd L S M κ ρ) 1 1
        simp [hst, valBnd, hρ]
      · rw [chg_one L hL ha haS κ u v]
        show ‖u‖ ≤ hst 0 (valBnd L S M κ ρ) 1 1
        simp [hst, valBnd, hu]
    · have hpre := ih (n + 1) (by omega)
      have hsum_nonneg : 0 ≤ ∑ j ∈ Finset.Ico 1 (n + 1), bnd L S M κ ρ j * bnd L S M κ ρ (n + 1 - j) := by
        apply Finset.sum_nonneg
        intro j hj
        rw [Finset.mem_Ico] at hj
        exact mul_nonneg (ih j (by omega)).1 (ih (n + 1 - j) (by omega)).1
      have hCm : 0 ≤ Cmul L (lv S M (n + 2)) := by
        unfold Cmul
        exact Real.sqrt_nonneg _
      have hnonneg : 0 ≤ bnd L S M κ ρ (n + 2) := by
        rw [bnd_rec]
        exact add_nonneg hpre.1
          (mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _)) hρ) hsum_nonneg)
      refine ⟨hnonneg, fun _ => ?_⟩
      rw [chg_rec, bnd_rec]
      have hvb : ‖lowT L (lv S M (n + 2)) S v‖ ≤ ρ := (norm_lowT_le _ _ _ _).trans hv
      have hS : ‖∑ j ∈ Finset.Ico 1 (n + 1),
            (mulBil hL (lv_pos ha haS (n + 2)))
              (lowT L (lv S M (n + 2)) (lv S M j) (chg L hL ha haS κ u v j))
              (lowT L (lv S M (n + 2)) (lv S M (n + 1 - j)) (chg L hL ha haS κ u v (n + 1 - j)))‖
          ≤ Cmul L (lv S M (n + 2)) * ∑ j ∈ Finset.Ico 1 (n + 1),
              bnd L S M κ ρ j * bnd L S M κ ρ (n + 1 - j) := by
        calc _ ≤ ∑ j ∈ Finset.Ico 1 (n + 1), ‖(mulBil hL (lv_pos ha haS (n + 2)))
              (lowT L (lv S M (n + 2)) (lv S M j) (chg L hL ha haS κ u v j))
              (lowT L (lv S M (n + 2)) (lv S M (n + 1 - j)) (chg L hL ha haS κ u v (n + 1 - j)))‖ :=
              norm_sum_le _ _
          _ ≤ ∑ j ∈ Finset.Ico 1 (n + 1), Cmul L (lv S M (n + 2))
                * (bnd L S M κ ρ j * bnd L S M κ ρ (n + 1 - j)) := by
              apply Finset.sum_le_sum
              intro j hj
              rw [Finset.mem_Ico] at hj
              have hx := (ih j (by omega)).2 (by omega)
              have hy := (ih (n + 1 - j) (by omega)).2 (by omega)
              have hx' := (norm_lowT_le L (lv S M (n + 2)) (lv S M j) (chg L hL ha haS κ u v j)).trans hx
              have hy' := (norm_lowT_le L (lv S M (n + 2)) (lv S M (n + 1 - j))
                (chg L hL ha haS κ u v (n + 1 - j))).trans hy
              have hb := norm_mulBil_le hL (lv_pos ha haS (n + 2))
                (lowT L (lv S M (n + 2)) (lv S M j) (chg L hL ha haS κ u v j))
                (lowT L (lv S M (n + 2)) (lv S M (n + 1 - j)) (chg L hL ha haS κ u v (n + 1 - j)))
              calc _ ≤ Cmul L (lv S M (n + 2)) * ‖lowT L (lv S M (n + 2)) (lv S M j) (chg L hL ha haS κ u v j)‖
                    * ‖lowT L (lv S M (n + 2)) (lv S M (n + 1 - j)) (chg L hL ha haS κ u v (n + 1 - j))‖ := hb
                _ ≤ Cmul L (lv S M (n + 2)) * bnd L S M κ ρ j * bnd L S M κ ρ (n + 1 - j) := by
                  apply mul_le_mul (mul_le_mul_of_nonneg_left hx' hCm) hy' (norm_nonneg _)
                  exact mul_nonneg hCm (ih j (by omega)).1
                _ = Cmul L (lv S M (n + 2)) * (bnd L S M κ ρ j * bnd L S M κ ρ (n + 1 - j)) := by ring
          _ = Cmul L (lv S M (n + 2)) * ∑ j ∈ Finset.Ico 1 (n + 1),
              bnd L S M κ ρ j * bnd L S M κ ρ (n + 1 - j) := (Finset.mul_sum _ _ _).symm
      have hY : ‖(mulBil hL (lv_pos ha haS (n + 2))) (lowT L (lv S M (n + 2)) S v)
            (∑ j ∈ Finset.Ico 1 (n + 1),
              (mulBil hL (lv_pos ha haS (n + 2)))
                (lowT L (lv S M (n + 2)) (lv S M j) (chg L hL ha haS κ u v j))
                (lowT L (lv S M (n + 2)) (lv S M (n + 1 - j)) (chg L hL ha haS κ u v (n + 1 - j))))‖
          ≤ Cmul L (lv S M (n + 2)) * ρ * (Cmul L (lv S M (n + 2)) * ∑ j ∈ Finset.Ico 1 (n + 1),
              bnd L S M κ ρ j * bnd L S M κ ρ (n + 1 - j)) := by
        refine (norm_mulBil_le hL (lv_pos ha haS (n + 2)) _ _).trans ?_
        have := mul_le_mul (mul_le_mul_of_nonneg_left hvb hCm) hS (norm_nonneg _) (mul_nonneg hCm hρ)
        calc _ ≤ Cmul L (lv S M (n + 2)) * ‖lowT L (lv S M (n + 2)) S v‖ * _ := le_rfl
          _ ≤ _ := this
      have hD : ‖-(Complex.I • derCLM L (chg L hL ha haS κ u v (n + 1)))‖
          ≤ bnd L S M κ ρ (n + 1) := by
        rw [norm_neg, norm_smul, Complex.norm_I, one_mul]
        exact (norm_derCLM_le L _).trans ((ih (n + 1) (by omega)).2 (by omega))
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul]
      have hK := mul_le_mul_of_nonneg_left hY (norm_nonneg κ)
      have hE : ‖κ‖ * (Cmul L (lv S M (n + 2)) * ρ * (Cmul L (lv S M (n + 2)) * ∑ j ∈ Finset.Ico 1 (n + 1),
              bnd L S M κ ρ j * bnd L S M κ ρ (n + 1 - j)))
          = ‖κ‖ * (Cmul L (lv S M (n + 2))) ^ 2 * ρ
            * ∑ j ∈ Finset.Ico 1 (n + 1), bnd L S M κ ρ j * bnd L S M κ ρ (n + 1 - j) := by ring
      linarith [hD, hK, hE]


/-! ### 8. The bottom-level instance at level `a` -/

/-- Bottom-level recursion for an abstract product `m` and derivative `D` (the shape of `resid_formula`). -/
def valAbs (m : Ell2 →ₗ[ℂ] Ell2 →ₗ[ℂ] Ell2) (D : Ell2 →ₗ[ℂ] Ell2) (vb ub : Ell2) (κ : ℂ) :
    ℕ → (ℕ → Ell2) → Ell2
  | 0, _ => 0
  | 1, _ => ub
  | n + 2, H =>
    -(Complex.I • D (H (n + 1)))
      + κ • m vb (∑ j ∈ Finset.Ico 1 (n + 1), m (H j) (H (n + 1 - j)))

theorem valAbs_congr (m : Ell2 →ₗ[ℂ] Ell2 →ₗ[ℂ] Ell2) (D : Ell2 →ₗ[ℂ] Ell2) (vb ub : Ell2) (κ : ℂ)
    (n : ℕ) : ∀ H H' : ℕ → Ell2, (∀ j, j ≤ n + 1 → H j = H' j) →
      valAbs m D vb ub κ (n + 2) H = valAbs m D vb ub κ (n + 2) H' := by
  intro H H' h
  have hs : (∑ j ∈ Finset.Ico 1 (n + 1), m (H j) (H (n + 1 - j)))
      = ∑ j ∈ Finset.Ico 1 (n + 1), m (H' j) (H' (n + 1 - j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Ico] at hj
    rw [h j (by omega), h (n + 1 - j) (by omega)]
  show -(Complex.I • D (H (n + 1))) + κ • m vb (∑ j ∈ Finset.Ico 1 (n + 1), m (H j) (H (n + 1 - j)))
      = -(Complex.I • D (H' (n + 1))) + κ • m vb (∑ j ∈ Finset.Ico 1 (n + 1), m (H' j) (H' (n + 1 - j)))
  rw [h (n + 1) le_rfl, hs]

/-- The bottom-level charges: `wAbs N = hst … N N`. -/
def wAbs (m : Ell2 →ₗ[ℂ] Ell2 →ₗ[ℂ] Ell2) (D : Ell2 →ₗ[ℂ] Ell2) (vb ub : Ell2) (κ : ℂ) (N : ℕ) : Ell2 :=
  hst 0 (valAbs m D vb ub κ) N N

theorem wAbs_one (m : Ell2 →ₗ[ℂ] Ell2 →ₗ[ℂ] Ell2) (D : Ell2 →ₗ[ℂ] Ell2) (vb ub : Ell2) (κ : ℂ) :
    wAbs m D vb ub κ 1 = ub := by
  simp [wAbs, hst, valAbs]

theorem wAbs_rec (m : Ell2 →ₗ[ℂ] Ell2 →ₗ[ℂ] Ell2) (D : Ell2 →ₗ[ℂ] Ell2) (vb ub : Ell2) (κ : ℂ)
    (n : ℕ) : wAbs m D vb ub κ (n + 2)
      = -(Complex.I • D (wAbs m D vb ub κ (n + 1)))
        + κ • m vb (∑ j ∈ Finset.Ico 1 (n + 1), m (wAbs m D vb ub κ j) (wAbs m D vb ub κ (n + 1 - j))) := by
  show hst 0 (valAbs m D vb ub κ) (n + 2) (n + 2) = _
  rw [hst_succ_succ 0 (valAbs m D vb ub κ) n (valAbs_congr m D vb ub κ n)]
  rfl

/-- Identity at the bottom level: `wAbs N = lowT a (lv N) (chg N)` for `1 ≤ N ≤ M`. -/
theorem wAbs_identity {a S : ℝ} {M : ℕ} (L : ℝ) (hL : 0 < L) (ha : 1 / 2 < a)
    (haS : a + (M : ℝ) + 1 ≤ S) (hM : 1 ≤ M) (κ : ℂ) (u v : Ell2)
    (D : Ell2 →ₗ[ℂ] Ell2) (hD : ∀ y : dDom L, D (y : Ell2) = dmulEll L y) :
    ∀ N : ℕ, 1 ≤ N → N ≤ M →
      wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) κ N
        = lowT L a (lv S M N) (chg L hL ha haS κ u v N) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro h1 hNM
    rcases N with _ | _ | n
    · omega
    · rw [wAbs_one, chg_one L hL ha haS κ u v, lv_one hM]
    · have hw : ∀ j, 1 ≤ j → j ≤ n + 1 →
          toField L a (wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) κ j)
            = toField L (lv S M j) (chg L hL ha haS κ u v j) := by
        intro j hj1 hj2
        rw [ih j (by omega) hj1 (by omega), toField_lowT (L := L) (lv_ge_a haS j)]
      have hDw : toField L a (D (wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) κ (n + 1)))
          = dField L (toField L (lv S M (n + 1)) (chg L hL ha haS κ u v (n + 1))) := by
        rw [ih (n + 1) (by omega) (by omega) (by omega)]
        have hmem := lowT_mem_dDom (L := L) (a := a) (p := lv S M (n + 1))
          (by linarith [lv_ge haS (n + 1)]) (chg L hL ha haS κ u v (n + 1))
        have hval := hD ⟨_, hmem⟩
        rw [show D (lowT L a (lv S M (n + 1)) (chg L hL ha haS κ u v (n + 1)))
            = dmulEll L ⟨_, hmem⟩ from hval]
        rw [toField_dmulEll]
        dsimp only
        rw [toField_lowT (L := L) (lv_ge_a haS (n + 1))]
      have hPL : toField L a (mulLin hL ha (lowT L a S v)
            (∑ j ∈ Finset.Ico 1 (n + 1), mulLin hL ha (wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) κ j)
              (wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) κ (n + 1 - j))))
          = convC (toField L S v) (∑ j ∈ Finset.Ico 1 (n + 1),
              convC (toField L (lv S M j) (chg L hL ha haS κ u v j))
                (toField L (lv S M (n + 1 - j)) (chg L hL ha haS κ u v (n + 1 - j)))) := by
        have hsum : toField L a (∑ j ∈ Finset.Ico 1 (n + 1),
              mulLin hL ha (wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) κ j)
                (wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) κ (n + 1 - j)))
            = ∑ j ∈ Finset.Ico 1 (n + 1),
              convC (toField L (lv S M j) (chg L hL ha haS κ u v j))
                (toField L (lv S M (n + 1 - j)) (chg L hL ha haS κ u v (n + 1 - j))) := by
          rw [toField_sum]
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mem_Ico] at hj
          rw [toField_mulLin hL ha, hw j (by omega) (by omega), hw (n + 1 - j) (by omega) (by omega)]
        rw [toField_mulLin hL ha, toField_lowT (L := L) (show a ≤ S by linarith), hsum]
      have hPR : toField L (lv S M (n + 2))
            ((mulBil hL (lv_pos ha haS (n + 2))) (lowT L (lv S M (n + 2)) S v)
              (∑ j ∈ Finset.Ico 1 (n + 1),
                (mulBil hL (lv_pos ha haS (n + 2)))
                  (lowT L (lv S M (n + 2)) (lv S M j) (chg L hL ha haS κ u v j))
                  (lowT L (lv S M (n + 2)) (lv S M (n + 1 - j)) (chg L hL ha haS κ u v (n + 1 - j)))))
          = convC (toField L S v) (∑ j ∈ Finset.Ico 1 (n + 1),
              convC (toField L (lv S M j) (chg L hL ha haS κ u v j))
                (toField L (lv S M (n + 1 - j)) (chg L hL ha haS κ u v (n + 1 - j)))) := by
        have hsum2 : toField L (lv S M (n + 2)) (∑ j ∈ Finset.Ico 1 (n + 1),
              (mulBil hL (lv_pos ha haS (n + 2)))
                (lowT L (lv S M (n + 2)) (lv S M j) (chg L hL ha haS κ u v j))
                (lowT L (lv S M (n + 2)) (lv S M (n + 1 - j)) (chg L hL ha haS κ u v (n + 1 - j))))
            = ∑ j ∈ Finset.Ico 1 (n + 1),
              convC (toField L (lv S M j) (chg L hL ha haS κ u v j))
                (toField L (lv S M (n + 1 - j)) (chg L hL ha haS κ u v (n + 1 - j))) := by
          rw [toField_sum]
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mem_Ico] at hj
          rw [toField_mulBil hL (lv_pos ha haS (n + 2)),
            toField_lowT (L := L) (lv_anti (S := S) (show j ≤ n + 2 by omega) (show n + 2 ≤ M by omega)),
            toField_lowT (L := L) (lv_anti (S := S) (show n + 1 - j ≤ n + 2 by omega) (show n + 2 ≤ M by omega))]
        rw [toField_mulBil hL (lv_pos ha haS (n + 2)),
          toField_lowT (L := L) (lv_le_top (S := S) (n := n + 2) hM (by omega)), hsum2]
      have hlv : lv S M (n + 2) + 1 = lv S M (n + 1) := lv_succ (show n + 2 ≤ M by omega)
      have hDR : toField L (lv S M (n + 2)) (derCLM L (chg L hL ha haS κ u v (n + 1)))
          = dField L (toField L (lv S M (n + 1)) (chg L hL ha haS κ u v (n + 1))) := by
        rw [derCLM_apply, toField_derEll, hlv]
      apply toField_inj
      rw [toField_lowT (L := L) (lv_ge_a haS (n + 2)), wAbs_rec, chg_rec]
      rw [toField_add, toField_add]
      funext k
      simp only [toField_neg, toField_smul]
      rw [hDw, hDR, hPL, hPR]

/-- Main statement of stage E4-3c. -/
theorem charge_levels_main {a S : ℝ} {M : ℕ} (L : ℝ) (hL : 0 < L) (ha : 1 / 2 < a)
    (haS : a + (M : ℝ) + 1 ≤ S) (hM : 1 ≤ M) (κ : ℂ) (u v : Ell2) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hu : ‖u‖ ≤ ρ) (hv : ‖v‖ ≤ ρ) :
    (∀ N : ℕ, 1 ≤ N → N ≤ M → ‖chg L hL ha haS κ u v N‖ ≤ bnd L S M κ ρ N) ∧
    (∀ D : Ell2 →ₗ[ℂ] Ell2, (∀ y : dDom L, D (y : Ell2) = dmulEll L y) →
      (∀ N : ℕ, 1 ≤ N → N ≤ M →
        wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) κ N
          = lowT L a (lv S M N) (chg L hL ha haS κ u v N)) ∧
      ‖D (wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) κ M)‖ ≤ bnd L S M κ ρ M) := by
  refine ⟨fun N h1 hNM => ((bnd_props L hL ha haS κ u v ρ hρ hu hv N).2 h1), fun D hD => ⟨fun N h1 hNM =>
    wAbs_identity L hL ha haS hM κ u v D hD N h1 hNM, ?_⟩⟩
  rw [wAbs_identity L hL ha haS hM κ u v D hD M (by omega) le_rfl]
  have hmem := lowT_mem_dDom (L := L) (a := a) (p := lv S M M)
    (by linarith [lv_ge haS M]) (chg L hL ha haS κ u v M)
  rw [show D (lowT L a (lv S M M) (chg L hL ha haS κ u v M)) = dmulEll L ⟨_, hmem⟩ from hD ⟨_, hmem⟩]
  exact (norm_dmulEll_le_of_lowT (L := L) (a := a) (p := lv S M M)
    (by linarith [lv_ge haS M]) (chg L hL ha haS κ u v M)).trans
    ((bnd_props L hL ha haS κ u v ρ hρ hu hv M).2 (by omega))

/-- Stage E4-3c conclusion: the residual of the bottom-level family at level `a` obeys `resid_norm_le`. -/
theorem resid_bottom {a S : ℝ} {M : ℕ} (L : ℝ) (hL : 0 < L) (ha : 1 / 2 < a)
    (haS : a + (M : ℝ) + 1 ≤ S) (hM : 1 ≤ M) (κ : ℂ) (u v : Ell2) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hu : ‖u‖ ≤ ρ) (hv : ‖v‖ ≤ ρ)
    (D : Ell2 →ₗ[ℂ] Ell2) (hD : ∀ y : dDom L, D (y : Ell2) = dmulEll L y)
    (z ζ : ℂ) (hzζ : z * ζ = 1) (hζ : ‖ζ‖ ≤ 1) :
    ‖resid (mulLin hL ha) D (lowT L a S v) (lowT L a S u) κ z ζ
        (wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) κ) M‖
      ≤ ‖ζ‖ ^ M * (bnd L S M κ ρ M + ‖κ‖ * (Cmul L a * ‖lowT L a S v‖)
          * ((M : ℝ) * ((M : ℝ) * (Cmul L a * (∑ N ∈ Finset.range (M + 1), bnd L S M κ ρ N) ^ 2)))) := by
  have hC : 0 ≤ Cmul L a := by
    unfold Cmul
    exact Real.sqrt_nonneg _
  have hm : ∀ x y : Ell2, ‖mulLin hL ha x y‖ ≤ Cmul L a * ‖x‖ * ‖y‖ := by
    intro x y
    have h := norm_mulBil_le hL ha x y
    rw [mulBil_apply] at h
    exact h
  have hrec : ∀ n : ℕ, 1 ≤ n → wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) κ (n + 1)
      = -(Complex.I • D (wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) κ n))
        + κ • mulLin hL ha (lowT L a S v)
          (∑ j ∈ Finset.Ico 1 n, mulLin hL ha (wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) κ j)
            (wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) κ (n - j))) := by
    intro n hn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    exact wAbs_rec (mulLin hL ha) D (lowT L a S v) (lowT L a S u) κ n'
  have hK : ∀ n : ℕ, 1 ≤ n → n ≤ M →
      ‖wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) κ n‖
        ≤ ∑ N ∈ Finset.range (M + 1), bnd L S M κ ρ N := by
    intro n hn hnM
    rw [wAbs_identity L hL ha haS hM κ u v D hD n hn hnM]
    refine (norm_lowT_le _ _ _ _).trans ((bnd_props L hL ha haS κ u v ρ hρ hu hv n).2 hn |>.trans ?_)
    exact Finset.single_le_sum (f := fun N => bnd L S M κ ρ N)
      (fun N _ => (bnd_props L hL ha haS κ u v ρ hρ hu hv N).1)
      (Finset.mem_range.mpr (by omega : n < M + 1))
  have hKD : ‖D (wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) κ M)‖ ≤ bnd L S M κ ρ M :=
    (charge_levels_main L hL ha haS hM κ u v ρ hρ hu hv).2 D hD |>.2
  have h := resid_norm_le (mulLin hL ha) D (lowT L a S v) (lowT L a S u) κ z ζ
    (wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) κ)
    (Cmul L a) (∑ N ∈ Finset.range (M + 1), bnd L S M κ ρ N) (bnd L S M κ ρ M)
    hzζ hζ hC (wAbs_one _ _ _ _ _) hrec hm M hM hK hKD
  exact h

end QuantumNLS.RiccatiChargeLevels

#print axioms QuantumNLS.RiccatiChargeLevels.hst_stab
#print axioms QuantumNLS.RiccatiChargeLevels.toField_inj
#print axioms QuantumNLS.RiccatiChargeLevels.exists_dext
#print axioms QuantumNLS.RiccatiChargeLevels.chg_rec
#print axioms QuantumNLS.RiccatiChargeLevels.bnd_props
#print axioms QuantumNLS.RiccatiChargeLevels.wAbs_identity
#print axioms QuantumNLS.RiccatiChargeLevels.charge_levels_main
#print axioms QuantumNLS.RiccatiChargeLevels.resid_bottom
