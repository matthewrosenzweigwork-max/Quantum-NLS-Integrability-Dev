import Mathlib
import NlsGge.Atomic.I.I011
import NlsGge.Spectral.ActualGapHeightHolderE02_38
import NlsGge.Spectral.ActualGapActionAllNE02_38
import NlsGge.ThirdConsultation.I.SymmetricKernel

/- I-012 PRODUCTION01 (proof development, AUTHOR; target NlsGge/Atomic/I/I012.lean, namespace NlsGge.ThirdConsultation.I as landed I045/I046).
   Head verbatim from followup2 STATEMENTS/I.md I-012; symmetricKernel is the SymmetricKernel-host definition (DEFINITIONS/I.lean.md:126).
   Route: closed gap = level set {p = n pi} (actualGapLevelSet_eq_Icc), so p is constant on each closed gap and distinct closed gaps are disjoint
   intervals; finitely many such give a positive separation delta (filter 𝓝[>] 0). v x <> 0 puts x in an open gap (actualGapHeight_mem_gap_of_ne_zero),
   hence for |x-t| <= eps < delta both lie in the same gap and the kernel vanishes. Integrability: K equals the landed I-011 truncated symmetrized kernel. -/
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff
open NlsGge.Pilot NlsGge.Schur NlsGge.Analysis
open NlsGge.SpectralFoundations

namespace NlsGge.ThirdConsultation.I
noncomputable section
namespace I012Aux

theorem level_eq (u : PhysicalL2) (n : ℤ) (x : ℝ)
    (hx : x ∈ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n)) :
    actualQuasimomentumRealPartE02_38 u x = (n : ℝ) * Real.pi := by
  have h := (actualGapLevelSet_eq_Icc_E02_38 u n).2
  rw [← h] at hx
  exact hx

theorem sep_pair (u : PhysicalL2) (n m : ℤ) (hnm : n ≠ m)
    (hn : actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n)
    (hm : actualGapLowerAllE02_38 u m < actualGapUpperAllE02_38 u m) :
    ∃ d : ℝ, 0 < d ∧ ∀ x ∈ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
      ∀ t ∈ Icc (actualGapLowerAllE02_38 u m) (actualGapUpperAllE02_38 u m), d ≤ |x - t| := by
  set a := actualGapLowerAllE02_38 u n
  set b := actualGapUpperAllE02_38 u n
  set c := actualGapLowerAllE02_38 u m
  set e := actualGapUpperAllE02_38 u m
  have hdisj : b < c ∨ e < a := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hz1 : max a c ∈ Icc a b := ⟨le_max_left _ _, max_le hn.le h1⟩
    have hz2 : max a c ∈ Icc c e := ⟨le_max_right _ _, max_le h2 hm.le⟩
    have p1 := level_eq u n _ hz1
    have p2 := level_eq u m _ hz2
    have : (n : ℝ) * Real.pi = (m : ℝ) * Real.pi := p1.symm.trans p2
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have : (n : ℝ) = m := mul_right_cancel₀ hpi this
    exact hnm (by exact_mod_cast this)
  rcases hdisj with h | h
  · refine ⟨c - b, by linarith, fun x hx t ht => ?_⟩
    have : x - t ≤ -(c - b) := by linarith [hx.2, ht.1]
    have := neg_le_abs (x - t)
    linarith [neg_le_abs (x - t)]
  · refine ⟨a - e, by linarith, fun x hx t ht => ?_⟩
    have : a - e ≤ x - t := by linarith [hx.1, ht.2]
    exact this.trans (le_abs_self _)

end I012Aux

open I012Aux in
theorem i012 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (hfin : {n : ℤ | actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n}.Finite)
    (W : ℝ → ℝ) (hW : ContDiff ℝ 2 W) (hc : ConvexOn ℝ Set.univ W) :
    let v := actualGapHeightE02_38 u
    let p := actualQuasimomentumRealPartE02_38 u
    let f := fun x : ℝ => W (2 * x)
    let K := symmetricKernel f p v
    Integrable K ∧
    (∀ n : ℤ, ∀ x ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
      ∀ t ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
        deriv f (p x) - deriv f (p t) = 0) ∧
    ∃ δ : ℝ, 0 < δ ∧
      (∀ n ∈ hfin.toFinset, ∀ m ∈ hfin.toFinset, n ≠ m →
        ∀ x ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
        ∀ t ∈ Set.Icc (actualGapLowerAllE02_38 u m) (actualGapUpperAllE02_38 u m),
          δ ≤ |x - t|) ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
        ({q : ℝ × ℝ | ε < |q.1 - q.2|}.indicator K) = K := by
  intro v p f K
  have hconst : ∀ n : ℤ, ∀ x ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
      ∀ t ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
        deriv f (p x) - deriv f (p t) = 0 := by
    intro n x hx t ht
    have h1 : p x = (n : ℝ) * Real.pi := level_eq u n x hx
    have h2 : p t = (n : ℝ) * Real.pi := level_eq u n t ht
    rw [h1, h2, sub_self]
  have hpair : ∀ n ∈ hfin.toFinset, ∀ m ∈ hfin.toFinset, ∀ᶠ δ in 𝓝[>] (0 : ℝ), n ≠ m →
      ∀ x ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
      ∀ t ∈ Set.Icc (actualGapLowerAllE02_38 u m) (actualGapUpperAllE02_38 u m), δ ≤ |x - t| := by
    intro n hn m hm
    by_cases hnm : n = m
    · exact Filter.Eventually.of_forall (fun δ h => absurd hnm h)
    · have hn' := hfin.mem_toFinset.1 hn
      have hm' := hfin.mem_toFinset.1 hm
      obtain ⟨d, hd, hdd⟩ := sep_pair u n m hnm hn' hm'
      filter_upwards [Ioo_mem_nhdsGT hd] with δ hδ _ x hx t ht
      exact hδ.2.le.trans (hdd x hx t ht)
  have hall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ n ∈ hfin.toFinset, ∀ m ∈ hfin.toFinset, n ≠ m →
      ∀ x ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
      ∀ t ∈ Set.Icc (actualGapLowerAllE02_38 u m) (actualGapUpperAllE02_38 u m), δ ≤ |x - t| := by
    rw [Filter.eventually_all_finset]
    intro n hn
    rw [Filter.eventually_all_finset]
    intro m hm
    exact hpair n hn m hm
  obtain ⟨δ, hδ0, hδ⟩ := (eventually_mem_nhdsWithin.and hall).exists
  have hδpos : 0 < δ := hδ0
  have key : ∀ ε : ℝ, ε < δ → ∀ q : ℝ × ℝ, |q.1 - q.2| ≤ ε → K q = 0 := by
    intro ε hεδ q hq
    by_cases h1 : v q.1 = 0
    · show (deriv f (p q.1) - deriv f (p q.2)) / (q.1 - q.2) * v q.1 * v q.2 = 0
      rw [h1]; simp
    by_cases h2 : v q.2 = 0
    · show (deriv f (p q.1) - deriv f (p q.2)) / (q.1 - q.2) * v q.1 * v q.2 = 0
      rw [h2]; simp
    obtain ⟨n, hn⟩ := actualGapHeight_mem_gap_of_ne_zero_E02_38 u q.1 h1
    obtain ⟨m, hm⟩ := actualGapHeight_mem_gap_of_ne_zero_E02_38 u q.2 h2
    have hnS : n ∈ hfin.toFinset := hfin.mem_toFinset.2 (hn.1.trans hn.2)
    have hmS : m ∈ hfin.toFinset := hfin.mem_toFinset.2 (hm.1.trans hm.2)
    by_cases hnm : n = m
    · subst hnm
      have hz := hconst n q.1 ⟨hn.1.le, hn.2.le⟩ q.2 ⟨hm.1.le, hm.2.le⟩
      show (deriv f (p q.1) - deriv f (p q.2)) / (q.1 - q.2) * v q.1 * v q.2 = 0
      rw [hz]; simp
    · exfalso
      have := hδ n hnS m hmS hnm q.1 ⟨hn.1.le, hn.2.le⟩ q.2 ⟨hm.1.le, hm.2.le⟩
      linarith
  have hKeq : K = fun q : ℝ × ℝ =>
      (deriv (fun y : ℝ => W (2 * y)) (actualQuasimomentumRealPartE02_38 u q.1) -
        deriv (fun y : ℝ => W (2 * y)) (actualQuasimomentumRealPartE02_38 u q.2)) *
        truncKernelE02_38 (actualGapHeightE02_38 u) (δ / 2) q := by
    funext q
    by_cases h : δ / 2 < |q.2 - q.1|
    · simp only [truncKernelE02_38]
      rw [Set.indicator_of_mem (show q ∈ {q : ℝ × ℝ | δ / 2 < |q.2 - q.1|} from h)]
      show (deriv f (p q.1) - deriv f (p q.2)) / (q.1 - q.2) * v q.1 * v q.2 = _
      ring
    · have h0 : K q = 0 := key (δ / 2) (by linarith) q (by
        rw [abs_sub_comm]; exact not_lt.1 h)
      rw [h0]
      simp only [truncKernelE02_38]
      rw [Set.indicator_of_notMem (show q ∉ {q : ℝ × ℝ | δ / 2 < |q.2 - q.1|} from h)]
      simp
  have hI : Integrable (fun q : ℝ × ℝ =>
      (deriv (fun y : ℝ => W (2 * y)) (actualQuasimomentumRealPartE02_38 u q.1) -
        deriv (fun y : ℝ => W (2 * y)) (actualQuasimomentumRealPartE02_38 u q.2)) *
        truncKernelE02_38 (actualGapHeightE02_38 u) (δ / 2) q) :=
    (NlsGge.Atomic.I011.truncatedHilbert_symmetrization u hu hfin W hW hc (δ / 2)
      (by linarith)).2.1
  refine ⟨hKeq ▸ hI, hconst, δ, hδpos, hδ, ?_⟩
  intro ε hε hεδ
  funext q
  by_cases h : ε < |q.1 - q.2|
  · exact Set.indicator_of_mem (show q ∈ {q : ℝ × ℝ | ε < |q.1 - q.2|} from h) _
  · rw [Set.indicator_of_notMem (show q ∉ {q : ℝ × ℝ | ε < |q.1 - q.2|} from h)]
    exact (key ε hεδ q (not_lt.1 h)).symm

end
end NlsGge.ThirdConsultation.I
