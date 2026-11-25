import Mathlib
import QuantumNLS.SmoothScalarMomentsPrerequisite
import QuantumNLS.RiccatiRemainder

/-!
# R-3FEAD88B blocker (1): analyticity of the Riccati coefficients in the parameter

For `1 ≤ n ≤ M` the coefficient `coeffs L a S κ hL ha D p n` equals the level-indexed charge
`lowT a (lv S M n) (chg κ/L p.1 p.2 n)`, by the frozen identity `wAbs_identity` (which uses only
`D y = dmulEll y` on `dDom`). Every `chg n` is built from continuous linear maps (`derCLM`, `lowT`),
continuous bilinear maps (`mulBil`), scalars and finite sums. Hence `p ↦ coeffs p n` is analytic on
all of `Ell2 × Ell2`. No continuity of the extension `D` is used.

Standard axioms only. No sorry, admit, native_decide, or new axioms.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex

namespace QuantumNLS.RiccatiCoeffAnalytic

open QuantumNLS.ComplexifiedSobolevField QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.RiccatiSobolevS QuantumNLS.RiccatiDerivative QuantumNLS.RiccatiRemainder
open QuantumNLS.RiccatiChargeLevels QuantumNLS.SmoothScalarMomentsPrerequisite

/-- Lowering the level `q` to `p ≤ q` is a continuous linear map, hence analytic. -/
theorem lowT_analyticAt {L p q : ℝ} (h : p ≤ q) (x0 : Ell2) :
    AnalyticAt ℂ (fun x : Ell2 => lowT L p q x) x0 := by
  have hfun : (fun x : Ell2 => lowT L p q x) = ⇑(iotaCLM L p q h) := by
    funext x
    unfold lowT
    rw [dif_pos h]
    rfl
  rw [hfun]
  exact (iotaCLM L p q h).analyticAt x0

/-- Composition of a level lowering with an analytic parameter map. -/
theorem analyticAt_lowT_comp {L p q : ℝ} (h : p ≤ q) {g : Ell2 × Ell2 → Ell2}
    {p0 : Ell2 × Ell2} (hg : AnalyticAt ℂ g p0) :
    AnalyticAt ℂ (fun x => lowT L p q (g x)) p0 :=
  (lowT_analyticAt h (g p0)).comp hg

/-- A continuous bilinear map applied to two analytic parameter maps is analytic. -/
theorem analyticAt_bil_comp {B : Ell2 →L[ℂ] Ell2 →L[ℂ] Ell2} {g h : Ell2 × Ell2 → Ell2}
    {p0 : Ell2 × Ell2} (hg : AnalyticAt ℂ g p0) (hh : AnalyticAt ℂ h p0) :
    AnalyticAt ℂ (fun q => B (g q) (h q)) p0 :=
  (ContinuousLinearMap.analyticAt_bilinear B (g p0, h p0)).comp₂ hg hh

/-- Monotonicity of the level clamp in the index (`lv` decreases as the index grows). -/
theorem lv_mono_index {S : ℝ} {M i j : ℕ} (hij : i ≤ j) : lv S M j ≤ lv S M i := by
  unfold lv
  have : ((min i M : ℕ) : ℝ) ≤ ((min j M : ℕ) : ℝ) := by
    exact_mod_cast min_le_min_right M hij
  linarith

/-- The level `lv S M n` lies below `S` when `1 ≤ n` and `1 ≤ M`. -/
theorem lv_le_S {S : ℝ} {M n : ℕ} (hM : 1 ≤ M) (hn : 1 ≤ n) : lv S M n ≤ S :=
  lv_le_top hM hn

/-- The charges are analytic in the pair `(u, v) = p` for every stage `N ≥ 1`. -/
theorem chg_analyticAt {a S : ℝ} {M : ℕ} (L : ℝ) (hL : 0 < L) (ha : 1 / 2 < a)
    (haS : a + (M : ℝ) + 1 ≤ S) (hM : 1 ≤ M) (κ : ℂ) :
    ∀ N : ℕ, 1 ≤ N → ∀ p0 : Ell2 × Ell2,
      AnalyticAt ℂ (fun q : Ell2 × Ell2 => chg L hL ha haS κ q.1 q.2 N) p0 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN p0
    by_cases h1 : N = 1
    · subst h1
      have hfun : (fun q : Ell2 × Ell2 => chg L hL ha haS κ q.1 q.2 1) = fun q => q.1 := by
        funext q
        exact chg_one L hL ha haS κ q.1 q.2
      rw [hfun]
      exact (ContinuousLinearMap.fst ℂ Ell2 Ell2).analyticAt p0
    · obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
      have hrec : (fun q : Ell2 × Ell2 => chg L hL ha haS κ q.1 q.2 (n + 2)) = fun q =>
          -(Complex.I • derCLM L (chg L hL ha haS κ q.1 q.2 (n + 1)))
            + κ • (mulBil hL (lv_pos ha haS (n + 2))) (lowT L (lv S M (n + 2)) S q.2)
              (∑ j ∈ Finset.Ico 1 (n + 1),
                (mulBil hL (lv_pos ha haS (n + 2)))
                  (lowT L (lv S M (n + 2)) (lv S M j) (chg L hL ha haS κ q.1 q.2 j))
                  (lowT L (lv S M (n + 2)) (lv S M (n + 1 - j))
                    (chg L hL ha haS κ q.1 q.2 (n + 1 - j)))) := by
        funext q
        exact chg_rec L hL ha haS κ q.1 q.2 n
      rw [hrec]
      -- the derivative term
      have hD1 : AnalyticAt ℂ (fun q : Ell2 × Ell2 => derCLM L (chg L hL ha haS κ q.1 q.2 (n + 1))) p0 :=
        AnalyticAt.comp (g := ⇑(derCLM L))
          (f := fun q : Ell2 × Ell2 => chg L hL ha haS κ q.1 q.2 (n + 1)) (x := p0)
          ((derCLM L).analyticAt (chg L hL ha haS κ p0.1 p0.2 (n + 1)))
          (ih (n + 1) (by omega) (by omega) p0)
      -- the product term with the parameter `v = q.2` lowered to level `lv (n+2)`
      have hlowS : AnalyticAt ℂ (fun q : Ell2 × Ell2 => lowT L (lv S M (n + 2)) S q.2) p0 :=
        analyticAt_lowT_comp (p := lv S M (n + 2)) (q := S) (lv_le_S hM (by omega))
          ((ContinuousLinearMap.snd ℂ Ell2 Ell2).analyticAt p0)
      have hsum : AnalyticAt ℂ (fun q : Ell2 × Ell2 => ∑ j ∈ Finset.Ico 1 (n + 1),
          (mulBil hL (lv_pos ha haS (n + 2)))
            (lowT L (lv S M (n + 2)) (lv S M j) (chg L hL ha haS κ q.1 q.2 j))
            (lowT L (lv S M (n + 2)) (lv S M (n + 1 - j)) (chg L hL ha haS κ q.1 q.2 (n + 1 - j)))) p0 := by
        apply Finset.analyticAt_fun_sum
        intro j hj
        rw [Finset.mem_Ico] at hj
        have hA : AnalyticAt ℂ (fun q : Ell2 × Ell2 => chg L hL ha haS κ q.1 q.2 j) p0 :=
          ih j (by omega) (by omega) p0
        have hB : AnalyticAt ℂ (fun q : Ell2 × Ell2 => chg L hL ha haS κ q.1 q.2 (n + 1 - j)) p0 :=
          ih (n + 1 - j) (by omega) (by omega) p0
        have hA' : AnalyticAt ℂ (fun q : Ell2 × Ell2 =>
            lowT L (lv S M (n + 2)) (lv S M j) (chg L hL ha haS κ q.1 q.2 j)) p0 :=
          analyticAt_lowT_comp (lv_mono_index (by omega : j ≤ n + 2)) hA
        have hB' : AnalyticAt ℂ (fun q : Ell2 × Ell2 =>
            lowT L (lv S M (n + 2)) (lv S M (n + 1 - j)) (chg L hL ha haS κ q.1 q.2 (n + 1 - j))) p0 :=
          analyticAt_lowT_comp (lv_mono_index (by omega : n + 1 - j ≤ n + 2)) hB
        exact analyticAt_bil_comp (B := mulBil hL (lv_pos ha haS (n + 2))) hA' hB'
      have hY : AnalyticAt ℂ (fun q : Ell2 × Ell2 =>
          (mulBil hL (lv_pos ha haS (n + 2))) (lowT L (lv S M (n + 2)) S q.2)
            (∑ j ∈ Finset.Ico 1 (n + 1),
              (mulBil hL (lv_pos ha haS (n + 2)))
                (lowT L (lv S M (n + 2)) (lv S M j) (chg L hL ha haS κ q.1 q.2 j))
                (lowT L (lv S M (n + 2)) (lv S M (n + 1 - j))
                  (chg L hL ha haS κ q.1 q.2 (n + 1 - j))))) p0 :=
        analyticAt_bil_comp (B := mulBil hL (lv_pos ha haS (n + 2))) hlowS hsum
      exact ((((analyticAt_const : AnalyticAt ℂ (fun _ : Ell2 × Ell2 => Complex.I) p0).smul hD1)).neg).add
        ((analyticAt_const : AnalyticAt ℂ (fun _ : Ell2 × Ell2 => κ) p0).smul hY)

/-- The coefficients equal the level-indexed charges for `1 ≤ n ≤ M` (frozen `wAbs_identity`). -/
theorem coeffs_eq_chg (L : ℝ) [Fact (0 < L)] {a S : ℝ} {M : ℕ} (hL : 0 < L) (ha : 1 / 2 < a)
    (haS : a + (M : ℝ) + 1 ≤ S) (hM : 1 ≤ M) (κ : ℝ) (D : Ell2 →ₗ[ℂ] Ell2)
    (hD : ∀ y : dDom L, D (y : Ell2) = dmulEll L y) (p : Ell2 × Ell2) (n : ℕ)
    (hn : 1 ≤ n) (hnM : n ≤ M) :
    coeffs L a S κ hL ha D p n
      = lowT L a (lv S M n) (chg L hL ha haS ((κ / L : ℝ) : ℂ) p.1 p.2 n) := by
  unfold coeffs
  exact wAbs_identity L hL ha haS hM _ p.1 p.2 D hD n hn hnM

/-- Analyticity of `p ↦ coeffs p n` on all of `Ell2 × Ell2`, for `1 ≤ n ≤ M`. -/
theorem coeffs_analyticAt (L : ℝ) [Fact (0 < L)] {a S : ℝ} {M : ℕ} (hL : 0 < L) (ha : 1 / 2 < a)
    (haS : a + (M : ℝ) + 1 ≤ S) (hM : 1 ≤ M) (κ : ℝ) (D : Ell2 →ₗ[ℂ] Ell2)
    (hD : ∀ y : dDom L, D (y : Ell2) = dmulEll L y) (n : ℕ) (hn : 1 ≤ n) (hnM : n ≤ M)
    (p0 : Ell2 × Ell2) :
    AnalyticAt ℂ (fun p : Ell2 × Ell2 => coeffs L a S κ hL ha D p n) p0 := by
  have hfun : (fun p : Ell2 × Ell2 => coeffs L a S κ hL ha D p n)
      = fun p => lowT L a (lv S M n) (chg L hL ha haS ((κ / L : ℝ) : ℂ) p.1 p.2 n) := by
    funext p
    exact coeffs_eq_chg L hL ha haS hM κ D hD p n hn hnM
  rw [hfun]
  exact analyticAt_lowT_comp (lv_ge_a haS n)
    (chg_analyticAt L hL ha haS hM ((κ / L : ℝ) : ℂ) n hn p0)

/-- The truncated sum `rMsum` of the coefficients is analytic in the parameter. -/
theorem rMsum_coeffs_analyticAt (L : ℝ) [Fact (0 < L)] {a S : ℝ} {M : ℕ} (hL : 0 < L) (ha : 1 / 2 < a)
    (haS : a + (M : ℝ) + 1 ≤ S) (hM : 1 ≤ M) (κ : ℝ) (D : Ell2 →ₗ[ℂ] Ell2)
    (hD : ∀ y : dDom L, D (y : Ell2) = dmulEll L y) (ζ : ℂ) (p0 : Ell2 × Ell2) :
    AnalyticAt ℂ (fun p : Ell2 × Ell2 => rMsum (fun n => coeffs L a S κ hL ha D p n) ζ M) p0 := by
  unfold rMsum
  have hsum : AnalyticAt ℂ (fun p : Ell2 × Ell2 =>
      ∑ n ∈ Finset.Icc 1 M, ζ ^ n • coeffs L a S κ hL ha D p n) p0 := by
    apply Finset.analyticAt_fun_sum
    intro n hn
    rw [Finset.mem_Icc] at hn
    exact ((analyticAt_const : AnalyticAt ℂ (fun _ : Ell2 × Ell2 => ζ ^ n) p0).smul
      (coeffs_analyticAt L hL ha haS hM κ D hD n hn.1 hn.2 p0))
  exact ((analyticAt_const : AnalyticAt ℂ (fun _ : Ell2 × Ell2 => Complex.I) p0).smul hsum)

end QuantumNLS.RiccatiCoeffAnalytic
