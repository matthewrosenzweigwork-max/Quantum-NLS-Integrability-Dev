import QuantumNLS.Q07ChargeAnalyticR24
import QuantumNLS.GP05AcceptedBridgeR16

/-! Uniform value and Hessian bounds for the actual finite charge polynomials. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
open Set Metric Filter Topology
open scoped ContDiff
namespace QuantumNLS.Q07ChargeBoundsR24
open RiccatiSobolevBanach RiccatiSobolevE2b RiccatiSobolevS RiccatiDerivative
open Q07ChargeLevelsR24 Q07ChargeAnalyticR24 RiccatiExpansions
open ComplexifiedSobolevField ClassicalCharges RiccatiPointwiseDisc
variable {L S : ℝ} [Fact (0 < L)] {M : ℕ}

def cxCharge (hS : 1 + (M : ℝ) ≤ S) (κ : ℝ) (n : ℕ) (p : Ell2 × Ell2) : ℂ :=
  modeCoef L 1 (lowT L 1 S p.2)
    (lowT L 1 (lv S M n) (chg L Fact.out (by norm_num) hS ((κ/L : ℝ) : ℂ) p.1 p.2 n))

lemma cxCharge_analytic (hS : 1 + (M : ℝ) ≤ S) (hM : 1 ≤ M) (κ : ℝ)
    (n : ℕ) (hn : 1 ≤ n) (p : Ell2 × Ell2) :
    AnalyticAt ℂ (cxCharge (L := L) hS κ n) p := by
  exact RiccatiModeAnalytic.modeCoef_analyticAt Fact.out (by norm_num)
    (analyticAt_lowT_comp (by linarith) ((ContinuousLinearMap.snd ℂ Ell2 Ell2).analyticAt p))
    (analyticAt_lowT_comp (lv_ge_a hS n)
      (chg_analyticAt L Fact.out (by norm_num) hS hM ((κ/L : ℝ) : ℂ) n hn p))

def majorant (S : ℝ) (M : ℕ) (κ ρ : ℝ) (n : ℕ) : ℝ :=
  L * ((physK L 1 * ρ) * (physK L 1 * bnd L S M ((κ/L : ℝ) : ℂ) ρ n))

lemma majorant_nonneg (hS : 1 + (M : ℝ) ≤ S) (κ : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) (n : ℕ) :
    0 ≤ majorant (L := L) S M κ ρ n := by
  have hb := (bnd_props L Fact.out (by norm_num) hS ((κ/L : ℝ) : ℂ) 0 0 ρ hρ
    (by simpa) (by simpa) n).1
  have hk := physK_nonneg (L := L) (a := (1 : ℝ)) (by norm_num)
  exact mul_nonneg (Fact.out : 0 < L).le (mul_nonneg (mul_nonneg hk hρ) (mul_nonneg hk hb))

lemma cxCharge_bound (hS : 1 + (M : ℝ) ≤ S) (κ : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (n : ℕ) (hn : 1 ≤ n) (p : Ell2 × Ell2) (hp : ‖p‖ ≤ ρ) :
    ‖cxCharge (L := L) hS κ n p‖ ≤ majorant (L := L) S M κ ρ n := by
  have hp1 : ‖p.1‖ ≤ ρ := (norm_fst_le p).trans hp
  have hp2 : ‖p.2‖ ≤ ρ := (norm_snd_le p).trans hp
  have hb := (bnd_props L Fact.out (by norm_num) hS ((κ/L : ℝ) : ℂ) p.1 p.2 ρ hρ hp1 hp2 n).2 hn
  have hlow1 := (norm_lowT_le L 1 S p.2).trans hp2
  have hlow2 := (norm_lowT_le L 1 (lv S M n) _).trans hb
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  have hk := physK_nonneg (L := L) (a := (1 : ℝ)) (by norm_num)
  exact (RiccatiValueBounds.norm_modeCoef_le Fact.out (by norm_num) _ _).trans
    (by dsimp [majorant]; gcongr)

/-- The full real slice has norm one, including radial directions. -/
def slice : Ell2 →L[ℝ] (Ell2 × Ell2) :=
  LinearMap.mkContinuous
    { toFun := fun u => (u,jEll u)
      map_add' := by
        intro u v
        exact Prod.ext rfl (ellConj.J.map_add u v)
      map_smul' := by
        intro c u
        change (c • u,jEll (c • u)) = (c • u,c • jEll u)
        refine Prod.ext rfl ?_
        ext k
        change (starRingEnd ℂ) ((c : ℂ)*u (-k)) = (c : ℂ)*(starRingEnd ℂ) (u (-k))
        simp }
    1 (fun u => by simp [Prod.norm_def, norm_jEll])

@[simp] lemma slice_apply (u : Ell2) : slice u = (u,jEll u) := rfl
@[simp] lemma norm_slice (u : Ell2) : ‖slice u‖ = ‖u‖ := by simp [Prod.norm_def,norm_jEll]

def realCharge (hS : 1 + (M : ℝ) ≤ S) (κ : ℝ) (n : ℕ) (u : Ell2) : ℝ :=
  (cxCharge (L := L) hS κ n (slice u)).re

lemma realCharge_contDiff (hS : 1 + (M : ℝ) ≤ S) (hM : 1 ≤ M) (κ : ℝ)
    (n : ℕ) (hn : 1 ≤ n) : ContDiff ℝ ∞ (realCharge (L := L) hS κ n) := by
  have hc : ContDiff ℂ ∞ (cxCharge (L := L) hS κ n) :=
    contDiff_iff_contDiffAt.mpr (fun p => (cxCharge_analytic hS hM κ n hn p).contDiffAt)
  exact Complex.reCLM.contDiff.comp ((hc.restrict_scalars ℝ).comp slice.contDiff)

lemma physical_charge (hS : 1 + (M : ℝ) ≤ S) (hM : 1 ≤ M) (κ : ℝ)
    (n : ℕ) (hn : 1 ≤ n) (hnM : n ≤ M) (u : Ell2) {f : ℝ → ℂ}
    (hrep : physRep L 1 (lowT L 1 S u) = f) :
    realCharge (L := L) hS κ n u = (charge L κ f n).re := by
  obtain ⟨D,hD⟩ := exists_dext L
  have hi := wAbs_identity L Fact.out (by norm_num) hS hM ((κ/L : ℝ) : ℂ)
    u (jEll u) D hD n hn hnM
  have hp := physical_coefficients (L := L) Fact.out (by norm_num) hS hM κ u D hD hrep
    n (Finset.mem_Icc.mpr ⟨hn,hnM⟩)
  apply congrArg Complex.re
  change modeCoef L 1 (lowT L 1 S (jEll u))
    (lowT L 1 (lv S M n) (chg L Fact.out (by norm_num) hS ((κ/L : ℝ) : ℂ) u (jEll u) n)) = _
  rw [← hi]
  have hj : lowT L 1 S (jEll u) = jEll (lowT L 1 S u) := RiccatiExpansions.lowT_jEll L 1 S u
  rw [hj]
  simpa only [Q07ChargeAnalyticR24.Wc,hj] using hp

end QuantumNLS.Q07ChargeBoundsR24
