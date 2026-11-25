import NlsGge.GK38.XiSqFullEstimates
import NlsGge.GK38.XiSqRealPositive

set_option autoImplicit false
open NlsGge.Pilot
open Set Filter Topology Metric
namespace NlsGge.GK38
noncomputable section

/-- The canonical normalized action coordinate, chosen ONLY after actual analytic existence. -/
def xiSq38 (n : ℤ) : PotPair → ℂ := Classical.choose (a5XiSqExists38 n)

theorem xiSq38_spec (n : ℤ) : XiSqSpec38 n (xiSq38 n) :=
  (Classical.choose_spec (a5XiSqExists38 n)).1

theorem xiSq38_unique (n : ℤ) (g : PotPair → ℂ) (hg : XiSqSpec38 n g) :
    EqOn (xiSq38 n) g gkW :=
  (Classical.choose_spec (a5XiSqExists38 n)).2 g hg

theorem xiSq38_analytic (n : ℤ) : AnalyticOnNhd ℂ (xiSq38 n) gkW := (xiSq38_spec n).1

theorem xiSq38_multiplied (n : ℤ) (φ : PotPair) (hφ : φ ∈ gkW) :
    gamma2 φ n*xiSq38 n φ = 4*gkActionC38 φ n :=
  xiSqCandidate_multiplied38 n (xiSq38 n) (xiSq38_spec n) φ hφ

theorem xiSq38_eq_quotient (n : ℤ) (φ : PotPair) (hφ : φ ∈ gkW)
    (hne : gamma2 φ n ≠ 0) : xiSq38 n φ = 4*gkActionC38 φ n/gamma2 φ n := by
  apply (eq_div_iff hne).mpr
  simpa only [mul_comm] using xiSq38_multiplied n φ hφ

/-- The principal square root is defined on all potentials; analyticity has its true guarded locus. -/
def xiN38 (n : ℤ) (φ : PotPair) : ℂ := Complex.sqrt (xiSq38 n φ)

theorem xiN38_sq (n : ℤ) (φ : PotPair) : xiN38 n φ^2=xiSq38 n φ := Lib.sqrt_sq _

theorem xiN38_analytic (n : ℤ) : AnalyticOnNhd ℂ (xiN38 n)
    {φ : PotPair | φ ∈ gkW ∧ xiSq38 n φ ∈ Complex.slitPlane} :=
  xiSqrtCandidate_analytic38 n (xiSq38 n) (xiSq38_spec n)

theorem xiSq38_near_one (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ∃ U : Set PotPair,U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧ ∃ N : ℕ,
      ∀ φ ∈ U,∀ n : ℤ,N<n.natAbs →
        xiSq38 n φ ∈ Complex.slitPlane ∧ ‖xiSq38 n φ-1‖<(1/2:ℝ) :=
  xiSqNearOne38_proved xiSq38 xiSq38_spec φ₀ hφ₀

theorem xiN38_l2_near_one (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    IsLocUnifL2Seq (fun φ n => xiN38 n φ-1) φ₀ :=
  xiSqrtL2NearOne38_proved xiSq38 xiSq38_spec φ₀ hφ₀

theorem xiSq38_real_ge_one (u : PhysicalL2) (n : ℤ) :
    (xiSq38 n (realSlice u)).im=0 ∧ 1≤(xiSq38 n (realSlice u)).re :=
  xiSqCandidate_real_ge_one38 n (xiSq38 n) (xiSq38_spec n) u

/-- Strict real positivity is retained at EVERY actual collapsed gap, for the principal root too. -/
theorem xiN38_real_ge_one (u : PhysicalL2) (n : ℤ) :
    (xiN38 n (realSlice u)).im=0 ∧ 1≤(xiN38 n (realSlice u)).re := by
  let q := xiN38 n (realSlice u)
  have hs := xiN38_sq n (realSlice u)
  have hg := xiSq38_real_ge_one u n
  have hqr : 0 ≤ q.re := Lib.re_sqrt_nonneg _
  have hsqre : q.re^2-q.im^2=(xiSq38 n (realSlice u)).re := by
    simpa only [pow_two,Complex.mul_re] using congrArg Complex.re hs
  have hsqim : 2*q.re*q.im=0 := by
    have h := congrArg Complex.im hs
    simp only [pow_two,Complex.mul_im,hg.1] at h
    change q.re*q.im+q.im*q.re=0 at h
    nlinarith
  have hpos : 0<q.re := by nlinarith [sq_nonneg q.im]
  have hmul : q.re*q.im=0 := by nlinarith
  have him : q.im=0 := (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hpos)
  refine ⟨him,?_⟩
  rw [him] at hsqre
  nlinarith

theorem actionXiN38_identity (n : ℤ) (φ : PotPair) (hφ : φ ∈ gkW) :
    gkActionC38 φ n=xiN38 n φ^2*gamma2 φ n/4 :=
  actionXiCandidate_identity38 n (xiSq38 n) (xiSq38_spec n) φ hφ

/-- Every proposition in the exact A5 preparation packet now has an actual proof. -/
theorem a5AllContracts38 : XiSqExistence38 ∧ XiSqIdentity38 ∧ OpenGapNonempty38 ∧
    XiSqNearOne38 ∧ XiSqrtL2NearOne38 ∧ XiSqrtAnalytic38 ∧ XiSqRealPositive38 ∧ ActionXiIdentity38 :=
  ⟨a5XiSqExistence38,a5XiSqIdentity38,a5OpenGapNonemptyContract38,
    xiSqNearOne38_proved,xiSqrtL2NearOne38_proved,xiSqrtCandidate_analytic38,
    a5XiSqRealPositive38,actionXiCandidate_identity38⟩

end
end NlsGge.GK38
