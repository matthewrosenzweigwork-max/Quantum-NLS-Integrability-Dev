import QuantumNLS.Q07TensorCoefficientsR15
import QuantumNLS.HighMomentsTransfer

/-! Normal convergence in full physical operator norms. The local calculus
lemma is applied to the actual transfer polynomials and their proved kernel
majorant, with no convergence or derivative conclusion supplied. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Set Filter Topology Metric
namespace QuantumNLS.Q07NormalSeriesR15

section LocalSeries
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Local C1 normal convergence in Banach operator norm. -/
theorem c1_series {f : ℕ → E → F} {R : ℝ} (hR : 0 < R)
    (hf : ∀ i, ContDiff ℝ 1 (f i)) (M0 M1 : ℕ → ℝ)
    (h0 : Summable M0) (h1 : Summable M1)
    (hb0 : ∀ i u, u ∈ ball (0:E) R → ‖f i u‖ ≤ M0 i)
    (hb1 : ∀ i u, u ∈ ball (0:E) R → ‖fderiv ℝ (f i) u‖ ≤ M1 i) :
    ContDiffOn ℝ 1 (fun u => ∑' i, f i u) (ball (0:E) R) ∧
      ∀ u ∈ ball (0:E) R,
        fderiv ℝ (fun v => ∑' i, f i v) u = ∑' i, fderiv ℝ (f i) u := by
  have hsum0 : Summable (fun i => f i (0:E)) :=
    .of_norm_bounded h0 (fun i => hb0 i 0 (mem_ball_self hR))
  have hdiff : ∀ u ∈ ball (0:E) R,
      HasFDerivAt (fun v => ∑' i, f i v) (∑' i, fderiv ℝ (f i) u) u := by
    intro u hu
    exact hasFDerivAt_tsum_of_isPreconnected h1 isOpen_ball (convex_ball _ _).isPreconnected
      (fun i v _ => ((hf i).differentiable one_ne_zero v).hasFDerivAt)
      hb1 (mem_ball_self hR) hsum0 hu
  have heq : ∀ u ∈ ball (0:E) R,
      fderiv ℝ (fun v => ∑' i, f i v) u = ∑' i, fderiv ℝ (f i) u :=
    fun u hu => (hdiff u hu).fderiv
  refine ⟨?_, heq⟩
  have hc : ContinuousOn (fun u => ∑' i, fderiv ℝ (f i) u) (ball (0:E) R) :=
    continuousOn_tsum (fun i => ((hf i).continuous_fderiv one_ne_zero).continuousOn) h1 hb1
  apply (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℝ) (n := 0) isOpen_ball).mpr
  refine ⟨fun u hu => (hdiff u hu).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · intro hn; simp at hn
  · exact contDiffOn_zero.mpr (hc.congr heq)

/-- Second-order local normal convergence, including the full nested
operator-valued derivative identity. -/
theorem c2_series {f : ℕ → E → F} {R : ℝ} (hR : 0 < R)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (M0 M1 M2 : ℕ → ℝ)
    (h0 : Summable M0) (h1 : Summable M1) (h2 : Summable M2)
    (hb0 : ∀ i u, u ∈ ball (0:E) R → ‖f i u‖ ≤ M0 i)
    (hb1 : ∀ i u, u ∈ ball (0:E) R → ‖fderiv ℝ (f i) u‖ ≤ M1 i)
    (hb2 : ∀ i u, u ∈ ball (0:E) R → ‖fderiv ℝ (fderiv ℝ (f i)) u‖ ≤ M2 i) :
    ContDiffOn ℝ 2 (fun u => ∑' i, f i u) (ball (0:E) R) ∧
      (∀ u ∈ ball (0:E) R,
        fderiv ℝ (fun v => ∑' i, f i v) u = ∑' i, fderiv ℝ (f i) u) ∧
      ∀ u ∈ ball (0:E) R,
        fderiv ℝ (fderiv ℝ (fun v => ∑' i, f i v)) u =
          ∑' i, fderiv ℝ (fderiv ℝ (f i)) u := by
  obtain ⟨hc1, heq⟩ := c1_series hR (fun i => (hf i).of_le (by norm_num)) M0 M1 h0 h1 hb0 hb1
  obtain ⟨hgc1, hgeq⟩ := c1_series (F := E →L[ℝ] F) hR
    (fun i => (hf i).fderiv_right (by norm_num)) M1 M2 h1 h2 hb1 hb2
  refine ⟨?_, heq, ?_⟩
  · apply (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℝ) (n := 1) isOpen_ball).mpr
    refine ⟨hc1.differentiableOn one_ne_zero, ?_, hgc1.congr heq⟩
    intro hn; simp at hn
  · intro u hu
    have hev : fderiv ℝ (fun v => ∑' i, f i v) =ᶠ[𝓝 u]
        fun v => ∑' i, fderiv ℝ (f i) v :=
      by
        filter_upwards [isOpen_ball.mem_nhds hu] with v hv
        exact heq v hv
    rw [hev.fderiv_eq]
    exact hgeq u hu
end LocalSeries


open Q07TensorCoefficientsR15 QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements
  QuantumNLS.NormalizedTransfer QuantumNLS.PhysicalTensor QuantumNLS.KernelDefinition
  QuantumNLS.RootOverlapLimit QuantumNLS.RootOverlapCommutator

variable {L : ℝ} [Fact (0 < L)]

/-- A single summable bound, independent of the real part of z and of the
profile on the full physical ball. -/
def majorant (κ R b : ℝ) (k j : ℕ) : ℝ :=
  (2^(k+1) * Real.exp (b*L)) * HighMomentsTransfer.Mterm L (|κ| * R^2) k j

theorem summable_majorant (κ R b : ℝ) (k : ℕ) :
    Summable (majorant (L := L) κ R b k) := by
  have hL : 0 < L := Fact.out
  exact (HighMomentsTransfer.summable_Mterm L (|κ| * R^2)
    (by positivity : 0 ≤ |κ| * R^2*L) k).mul_left _

theorem term_contDiff (κ : ℝ) (z : ℂ) (n : ℕ) (N : WithTop ℕ∞) :
    ContDiff ℝ N (fun u : L2T L => symbolTerm L κ u z n) := by
  let A := extendSymKernel (orderedKernel L n z)
  have he : (fun u : L2T L => symbolTerm L κ u z n) =
      fun u => ((κ^n : ℝ) : ℂ) • RootSymbolFrechet.symFun n A u := by
    funext u
    simp only [symbolTerm, RootSymbolFrechet.symFun, kernelProductSymbol,
      smul_eq_mul, A, extend_htpow]
  rw [he]
  have hc : ContDiff ℝ N (RootSymbolFrechet.symFun n A) := by
    simpa +instances only [NormedSpace.complexToReal, NormedSpace.restrictScalars_eq] using contDiff_symFun_all n A N
  exact hc.const_smul _

theorem term_majorant (κ : ℝ) {R b : ℝ} (hR : 1 ≤ R) (hb : 0 ≤ b)
    (z : ℂ) (hz : -b ≤ z.im) (k j : ℕ) (u : L2T L) (hu : ‖u‖ ≤ R) :
    ‖iteratedFDeriv ℝ k (fun v => symbolTerm L κ v z (j+1)) u‖ ≤
      majorant (L := L) κ R b k j := by
  have hL : 0 < L := Fact.out
  let n := j+1
  let A := extendSymKernel (orderedKernel L n z)
  have he : (fun v : L2T L => symbolTerm L κ v z n) =
      fun v => ((κ^n : ℝ) : ℂ) • RootSymbolFrechet.symFun n A v := by
    funext v
    have hv := RootSymbolFrechet.symbolTerm_eq_symFun L κ z j v
    simpa only [RootSymbolFrechet.physW, RootSymbolFrechet.physA, n, A,
      smul_eq_mul] using hv
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hAn : ‖A‖ ≤ 2*(Real.exp (b*L)*(L/(n:ℝ))^n) :=
    (norm_extendSymKernel_le _).trans (HighMomentsTransfer.norm_physicalKernel_strip hb z hz)
  have hdesc : ((n+n).descFactorial k : ℝ) ≤ (2:ℝ)^k*(n:ℝ)^k := by
    have hh : ((n+n).descFactorial k : ℝ) ≤ (((n+n:ℕ):ℝ))^k := by
      exact_mod_cast (Nat.descFactorial_le_pow (n+n) k)
    convert hh using 1
    push_cast
    rw [← mul_pow]
    congr 1
    ring
  have hpow : ‖u‖^(n+n-k) ≤ (R^2)^n := by
    calc
      _ ≤ R^(n+n-k) := pow_le_pow_left₀ (norm_nonneg _) hu _
      _ ≤ R^(n+n) := pow_le_pow_right₀ hR (Nat.sub_le _ _)
      _ = (R^2)^n := by rw [← pow_mul]; congr 1; omega
  change ‖iteratedFDeriv ℝ k (fun v => symbolTerm L κ v z n) u‖ ≤ _
  have hc : ContDiff ℝ k (RootSymbolFrechet.symFun n A) := by
    simpa +instances only [NormedSpace.complexToReal, NormedSpace.restrictScalars_eq] using contDiff_symFun_all n A k
  rw [he, iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (i := k) (x := u)
    (f := RootSymbolFrechet.symFun n A) (a := ((κ^n : ℝ) : ℂ)) hc.contDiffAt,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_pow]
  have hd : ‖iteratedFDeriv ℝ k (RootSymbolFrechet.symFun n A) u‖ ≤
      ((n+n).descFactorial k : ℝ) * ‖A‖ * ‖u‖^(n+n-k) := by
    let nsR : NormedSpace ℝ (L2T L) := by
      letI : NormedSpace ℂ (L2T L) := (inferInstance : InnerProductSpace ℂ (L2T L)).toNormedSpace
      exact NormedSpace.complexToReal
    let P (s : NormedSpace ℝ (L2T L)) : Prop := by
      letI : NormedSpace ℝ (L2T L) := s
      letI : Module ℝ (L2T L) := s.toModule
      exact ‖iteratedFDeriv ℝ k (RootSymbolFrechet.symFun n A) u‖ ≤
        ((n+n).descFactorial k : ℝ) * ‖A‖ * ‖u‖^(n+n-k)
    have hs : P nsR := norm_iterated_symFun_le n k A u
    have hn : nsR = (inferInstance : NormedSpace ℝ (L2T L)) := by
      let : NormedSpace ℂ (L2T L) := (inferInstance : InnerProductSpace ℂ (L2T L)).toNormedSpace
      exact NormedSpace.restrictScalars_eq ℝ ℂ
    exact Eq.mp (congrArg P hn) hs
  calc
    _ ≤ |κ|^n * (((n+n).descFactorial k : ℝ)*‖A‖*‖u‖^(n+n-k)) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ ≤ |κ|^n * (((2:ℝ)^k*(n:ℝ)^k)*
        (2*(Real.exp (b*L)*(L/(n:ℝ))^n))*(R^2)^n) := by gcongr
    _ = majorant (L := L) κ R b k j := by
      dsimp [majorant, HighMomentsTransfer.Mterm, n]
      simp only [mul_pow, div_pow, pow_add, pow_one]
      ring

/-- Actual product symbol is C2 on every physical L2 ball. The enclosing
radius is arbitrary; the strip restriction supplies the common bound. -/
theorem transfer_tail_data (κ : ℝ) {R b : ℝ} (hR : 1 ≤ R) (hb : 0 ≤ b)
    (z : ℂ) (hz : -b ≤ z.im) :
    ContDiffOn ℝ 2 (fun u : L2T L => ∑' j, symbolTerm L κ u z (j+1)) (ball 0 R) ∧
      (∀ u ∈ ball (0:L2T L) R,
        fderiv ℝ (fun v => ∑' j, symbolTerm L κ v z (j+1)) u =
          ∑' j, fderiv ℝ (fun v => symbolTerm L κ v z (j+1)) u) ∧
      ∀ u ∈ ball (0:L2T L) R,
        fderiv ℝ (fderiv ℝ (fun v => ∑' j, symbolTerm L κ v z (j+1))) u =
          ∑' j, fderiv ℝ (fderiv ℝ (fun v => symbolTerm L κ v z (j+1))) u := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let f := fun j (u : L2T L) => symbolTerm L κ u z (j+1)
  have h0 : ∀ j u, u ∈ ball (0:L2T L) R → ‖f j u‖ ≤ majorant (L := L) κ R b 0 j := by
    intro j u hu
    simpa only [norm_iteratedFDeriv_zero] using
      term_majorant (L := L) κ hR hb z hz 0 j u (mem_ball_zero_iff.mp hu).le
  have h1 : ∀ j u, u ∈ ball (0:L2T L) R → ‖fderiv ℝ (f j) u‖ ≤ majorant (L := L) κ R b 1 j := by
    intro j u hu
    simpa only [norm_iteratedFDeriv_one] using
      term_majorant (L := L) κ hR hb z hz 1 j u (mem_ball_zero_iff.mp hu).le
  have h2 : ∀ j u, u ∈ ball (0:L2T L) R →
      ‖fderiv ℝ (fderiv ℝ (f j)) u‖ ≤ majorant (L := L) κ R b 2 j := by
    intro j u hu
    have hh := term_majorant (L := L) κ hR hb z hz 2 j u (mem_ball_zero_iff.mp hu).le
    have he : ‖iteratedFDeriv ℝ 1 (fderiv ℝ (f j)) u‖ = ‖iteratedFDeriv ℝ 2 (f j) u‖ :=
      norm_iteratedFDeriv_fderiv
    rw [norm_iteratedFDeriv_one] at he
    rw [← he] at hh
    exact hh
  have hc := (c2_series hRp (fun j => term_contDiff κ z (j+1) 2)
    (majorant (L := L) κ R b 0) (majorant (L := L) κ R b 1) (majorant (L := L) κ R b 2)
    (summable_majorant (L := L) κ R b 0) (summable_majorant (L := L) κ R b 1) (summable_majorant (L := L) κ R b 2)
    h0 h1 h2)
  exact hc


theorem transfer_contDiffOn (κ : ℝ) {R b : ℝ} (hR : 1 ≤ R) (hb : 0 ≤ b)
    (z : ℂ) (hz : -b ≤ z.im) :
    ContDiffOn ℝ 2 (fun u : L2T L => productSymbol L κ u z) (ball 0 R) :=
  contDiffOn_const.add (transfer_tail_data (L := L) κ hR hb z hz).1

/-- Uniform full first and second physical Hilbert differential bounds for
the actual classical transfer, including radial directions. -/
theorem transfer_uniform_differentials (κ : ℝ) {R b : ℝ} (hR : 1 ≤ R) (hb : 0 ≤ b) :
    ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ ∀ z : ℂ, -b ≤ z.im →
      ∀ u ∈ ball (0:L2T L) R,
        ‖fderiv ℝ (fun v => productSymbol L κ v z) u‖ ≤ C1 ∧
        ‖fderiv ℝ (fderiv ℝ (fun v => productSymbol L κ v z)) u‖ ≤ C2 := by
  have hL : 0 < L := Fact.out
  refine ⟨∑' j, majorant (L := L) κ R b 1 j,
    ∑' j, majorant (L := L) κ R b 2 j, ?_, ?_, ?_⟩
  · exact tsum_nonneg (fun j => by unfold majorant HighMomentsTransfer.Mterm; positivity)
  · exact tsum_nonneg (fun j => by unfold majorant HighMomentsTransfer.Mterm; positivity)
  · intro z hz u hu
    obtain ⟨-, h1, h2⟩ := transfer_tail_data (L := L) κ hR hb z hz
    let S : L2T L → ℂ := fun v => ∑' j, symbolTerm L κ v z (j+1)
    have heD : fderiv ℝ (fun v : L2T L => productSymbol L κ v z) = fderiv ℝ S := by
      funext v
      exact fderiv_const_add _
    simp only [heD]
    rw [h1 u hu, h2 u hu]
    constructor
    · apply tsum_of_norm_bounded (summable_majorant (L := L) κ R b 1).hasSum
      intro j
      simpa only [norm_iteratedFDeriv_one] using
        term_majorant (L := L) κ hR hb z hz 1 j u (mem_ball_zero_iff.mp hu).le
    · apply tsum_of_norm_bounded
        (f := fun j : ℕ => fderiv ℝ (fderiv ℝ (fun v : L2T L => symbolTerm L κ v z (j+1))) u)
        (summable_majorant (L := L) κ R b 2).hasSum
      intro j
      have hh := term_majorant (L := L) κ hR hb z hz 2 j u (mem_ball_zero_iff.mp hu).le
      have he : ‖iteratedFDeriv ℝ 1 (fderiv ℝ (fun v => symbolTerm L κ v z (j+1))) u‖ =
          ‖iteratedFDeriv ℝ 2 (fun v => symbolTerm L κ v z (j+1)) u‖ := norm_iteratedFDeriv_fderiv
      rw [norm_iteratedFDeriv_one] at he
      rw [← he] at hh
      exact hh

end QuantumNLS.Q07NormalSeriesR15
