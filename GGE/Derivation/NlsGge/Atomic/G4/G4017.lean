import Mathlib
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.Atomic.G2.G2046
import NlsGge.GK38.DirichletRealBridge
import NlsGge.GK38.StdRootBranchesProducts
import NlsGge.GK38.StdRootBranchesConvergence
import NlsGge.GK38.StdRootBranchesDomain
import NlsGge.GK38.AngleDirichletAnalytic
import NlsGge.GK38.DirichletLabels
import NlsGge.GK38.RealTypeSpectrum
import NlsGge.GK38.DirichletRealGapIndex
import NlsGge.GK38.IsolatingDistance
import NlsGge.GK38.GradFundamentalDefs

/- G4-017 (proof development, AUTHOR; not self-reviewed).  Head from followup2 STATEMENTS/G4.md G4-017 verbatim; offGapSet and sheetSign verbatim from DEFINITIONS/G4.lean.md
   (namespace NlsGge.GKDefinitionDesign); sourceBetaW from the SourceFamilyBasic host (X-006 family).  Route: the isolating certificate of phi in gkW makes the n-th
   Dirichlet root avoid every other gap segment (balls disjoint), so on sourceBetaW  "mu_n not in segment_n"  is  "(phi, mu_n) in rootDomain38";
   rootDomain38 is open and phi |-> mu_n, antiDiscrim, canonRoot38 are analytic/continuous there; antiDiscrim^2 = perChar = canonRoot^2 at the Dirichlet root
   (dirichlet_perChar_eq_anti_sq38, muSeq_root38, canonRoot_sq38) gives sheetSign = ±1; a continuous ±1-valued function is locally constant;
   real slice: gkMu u n lies in the closed real gap and lamMinus/lamPlus of realSlice u are the real gap endpoints (lamPlus_real). -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

def offGapSet (n : ℤ) : Set PotPair :=
  {φ | φ ∈ sourceBetaW ∧ muSeq φ n ∉ gapSegment φ n}

/-- Only used on offGapSet, where its denominator is nonzero. -/
def sheetSign (n : ℤ) (φ : PotPair) : ℂ :=
  antiDiscrim φ (muSeq φ n) / canonRoot38 φ (muSeq φ n)

namespace G4017Aux

theorem sourceBetaW_gkW : sourceBetaW ⊆ gkW := fun φ hφ =>
  sourceFamily.W_gk (sourceFamily.V_W hφ)

theorem sourceBetaW_open : IsOpen sourceBetaW := sourceFamily.V_open

/-- The n-th Dirichlet root avoids every gap segment as soon as it avoids the n-th one. -/
theorem avoids_all (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ)
    (h : muSeq φ n ∉ segment ℝ (lamMinus φ n) (lamPlus φ n)) :
    muSeq φ n ∉ gapSegments38 φ := by
  obtain ⟨u, ρ0, hcert, hmem⟩ := hφ
  obtain ⟨hρ0, C, R, c, N, hgeom, hall⟩ := hcert
  have hsp := hall φ hmem
  intro hz
  obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hz
  by_cases hmn : m = n
  · subst hmn; exact h hm
  · have h1 := (hsp.1 m).1 hm
    have h2 := (hsp.1 n).2.1
    have hd := (hgeom.2.2.2.1 m n hmn).1
    have hpos : 0 < ballDistance38 (C m) (C n) (R m) (R n) := by
      have hc1 : 1 ≤ c := hgeom.2.2.1
      have hd1 : (1 : ℝ) ≤ |((m - n : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hmn)
      have : 0 < c⁻¹ * |((m - n : ℤ) : ℝ)| := by
        have hc0 : 0 < c := by linarith
        positivity
      exact lt_of_lt_of_le this hd
    have hle := ballDistance38_le_pair (C m) (C n) (R m) (R n) h1 h2
    rw [dist_self] at hle
    linarith

theorem mem_offGap_iff (n : ℤ) (φ : PotPair) (hφ : φ ∈ sourceBetaW) :
    φ ∈ offGapSet n ↔ (φ, muSeq φ n) ∈ rootDomain38 := by
  constructor
  · intro h
    exact ⟨sourceBetaW_gkW hφ, avoids_all φ (sourceBetaW_gkW hφ) n h.2⟩
  · intro h
    refine ⟨hφ, fun hs => h.2 (Set.mem_iUnion.2 ⟨n, hs⟩)⟩

theorem offGap_open (n : ℤ) : IsOpen (offGapSet n) := by
  rw [isOpen_iff_mem_nhds]
  intro φ hφ
  have hVφ := hφ.1
  have hgk := sourceBetaW_gkW hVφ
  have hmu : ContinuousAt (fun ψ : PotPair => muSeq ψ n) φ :=
    ((analyticOnNhd_muSeq_complex38 n) φ hgk).continuousAt
  have hg : ContinuousAt (fun ψ : PotPair => (ψ, muSeq ψ n)) φ :=
    continuousAt_id.prodMk hmu
  have hroot : (φ, muSeq φ n) ∈ rootDomain38 := (mem_offGap_iff n φ hVφ).1 hφ
  have h1 : {ψ : PotPair | (ψ, muSeq ψ n) ∈ rootDomain38} ∈ 𝓝 φ :=
    hg.preimage_mem_nhds (isOpen_rootDomain38.mem_nhds hroot)
  have h2 : sourceBetaW ∈ 𝓝 φ := sourceBetaW_open.mem_nhds hVφ
  filter_upwards [h1, h2] with ψ hψ1 hψ2
  exact (mem_offGap_iff n ψ hψ2).2 hψ1

theorem sheetSign_sq (n : ℤ) (φ : PotPair) (hφ : φ ∈ offGapSet n) :
    sheetSign n φ ^ 2 = 1 := by
  have hgk := sourceBetaW_gkW hφ.1
  have hav := avoids_all φ hgk n hφ.2
  have hne := canonRoot_ne_zero38 φ hgk _ hav
  have hA := dirichlet_perChar_eq_anti_sq38 φ _ (muSeq_root38 φ n)
  have hC := canonRoot_sq38 φ hgk _ hav
  unfold sheetSign
  rw [div_pow, ← hA, ← hC]
  exact div_self (pow_ne_zero 2 hne)

theorem sheetSign_continuousAt (n : ℤ) (φ : PotPair) (hφ : φ ∈ offGapSet n) :
    ContinuousAt (sheetSign n) φ := by
  have hgk := sourceBetaW_gkW hφ.1
  have hroot : (φ, muSeq φ n) ∈ rootDomain38 := (mem_offGap_iff n φ hφ.1).1 hφ
  have hmu : ContinuousAt (fun ψ : PotPair => muSeq ψ n) φ :=
    ((analyticOnNhd_muSeq_complex38 n) φ hgk).continuousAt
  have hg : ContinuousAt (fun ψ : PotPair => (ψ, muSeq ψ n)) φ :=
    continuousAt_id.prodMk hmu
  have hA : ContinuousAt (fun p : PotPair × ℂ => antiDiscrim p.1 p.2) (φ, muSeq φ n) :=
    (analyticOnNhd_antiDiscrim _ (Set.mem_univ _)).continuousAt
  have hCr : ContinuousAt (fun p : PotPair × ℂ => canonRoot38 p.1 p.2) (φ, muSeq φ n) :=
    (canonRoot_analytic38 _ hroot).continuousAt
  have hne : canonRoot38 φ (muSeq φ n) ≠ 0 :=
    canonRoot_ne_zero38 φ hgk _ (avoids_all φ hgk n hφ.2)
  have hA' : ContinuousAt (fun ψ : PotPair => antiDiscrim ψ (muSeq ψ n)) φ :=
    ContinuousAt.comp (g := fun p : PotPair × ℂ => antiDiscrim p.1 p.2)
      (f := fun ψ : PotPair => (ψ, muSeq ψ n)) hA hg
  have hC' : ContinuousAt (fun ψ : PotPair => canonRoot38 ψ (muSeq ψ n)) φ :=
    ContinuousAt.comp (g := fun p : PotPair × ℂ => canonRoot38 p.1 p.2)
      (f := fun ψ : PotPair => (ψ, muSeq ψ n)) hCr hg
  exact hA'.div hC' hne

end G4017Aux

theorem G4017 (n : ℤ) :
  IsOpen (offGapSet n) ∧ Disjoint (offGapSet n) (Set.range realSlice) ∧
  ContinuousOn (sheetSign n) (offGapSet n) ∧
  ∀ φ ∈ offGapSet n,
    canonRoot38 φ (muSeq φ n) ≠ 0 ∧
    (sheetSign n φ = 1 ∨ sheetSign n φ = -1) ∧
    ∃ V : Set PotPair, V ∈ 𝓝 φ ∧ V ⊆ offGapSet n ∧
      ∀ ψ ∈ V, sheetSign n ψ = sheetSign n φ := by
  have hopen := G4017Aux.offGap_open n
  refine ⟨hopen, ?_, fun φ hφ => (G4017Aux.sheetSign_continuousAt n φ hφ).continuousWithinAt, ?_⟩
  · rw [Set.disjoint_left]
    rintro φ hφ ⟨u, rfl⟩
    apply hφ.2
    have hlo := (lamPlus_real u n).2
    have hhi := (lamPlus_real u n).1
    have hmu := muSeq_eq_gkMu38 u n
    have hg := gkMu_mem_gap38 u n
    unfold gapSegment
    rw [hlo, hhi, hmu]
    have hseg : segment ℝ (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) =
        Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) :=
      segment_eq_Icc (hg.1.trans hg.2)
    have hmemseg : gkMu u n ∈ segment ℝ (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) := by
      rw [hseg]; exact hg
    obtain ⟨a, b, ha, hb, hab, hmu'⟩ := hmemseg
    refine ⟨a, b, ha, hb, hab, ?_⟩
    rw [← hmu']
    simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_add, Complex.ofReal_mul]
  · intro φ hφ
    have hgk := G4017Aux.sourceBetaW_gkW hφ.1
    have hav := G4017Aux.avoids_all φ hgk n hφ.2
    have hne := canonRoot_ne_zero38 φ hgk _ hav
    have hsq := G4017Aux.sheetSign_sq n φ hφ
    have hpm : sheetSign n φ = 1 ∨ sheetSign n φ = -1 := by
      have : (sheetSign n φ - 1) * (sheetSign n φ + 1) = 0 := by linear_combination hsq
      rcases mul_eq_zero.1 this with h | h
      · left; linear_combination h
      · right; linear_combination h
    refine ⟨hne, hpm, ?_⟩
    have hcont := G4017Aux.sheetSign_continuousAt n φ hφ
    have hnb : {ψ : PotPair | ‖sheetSign n ψ - sheetSign n φ‖ < 1} ∈ 𝓝 φ := by
      have := hcont.eventually (Metric.ball_mem_nhds (sheetSign n φ) one_pos)
      filter_upwards [this] with ψ hψ
      show ‖sheetSign n ψ - sheetSign n φ‖ < 1
      rw [← dist_eq_norm]
      exact hψ
    refine ⟨{ψ | ‖sheetSign n ψ - sheetSign n φ‖ < 1} ∩ offGapSet n,
      Filter.inter_mem hnb (hopen.mem_nhds hφ), Set.inter_subset_right, ?_⟩
    rintro ψ ⟨hψ1, hψ2⟩
    have hsψ := G4017Aux.sheetSign_sq n ψ hψ2
    have hpmψ : sheetSign n ψ = 1 ∨ sheetSign n ψ = -1 := by
      have : (sheetSign n ψ - 1) * (sheetSign n ψ + 1) = 0 := by linear_combination hsψ
      rcases mul_eq_zero.1 this with h | h
      · left; linear_combination h
      · right; linear_combination h
    have hψ1' : ‖sheetSign n ψ - sheetSign n φ‖ < 1 := hψ1
    rcases hpm with h | h <;> rcases hpmψ with h' | h'
    · rw [h, h']
    · rw [h, h'] at hψ1'; norm_num at hψ1'
    · rw [h, h'] at hψ1'; norm_num at hψ1'
    · rw [h, h']

end
end NlsGge.GKDefinitionDesign
