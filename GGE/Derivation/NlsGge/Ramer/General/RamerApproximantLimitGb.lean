import NlsGge.Ramer.General.RamerApproximantLimitGa

/-!
# Convergence of Ramer's approximants `a_n(G) → η` in `L²(γ)`, general source law (GB5, part b)

Limits as the level tends to infinity, the tail terms, and the main results
`tendsto_eLpNorm_ramerA`, `ramerA_congr_of_eqOn`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal RealInnerProductSpace

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer

variable (S : NlsGge.Ramer.General.RamerSetting)

/-! ### Limits as the level `N → ∞` -/

/-- The limit of the field part: `P_n G(ξ) - G(ξ)`. -/
def fieldLim  (n : ℕ)
    (G : S.E → S.H) (z : ℤ → ℂ) : S.H :=
  ((S.cmTrunc n (G (S.R z)) :
      S.head n) : S.H) - G (S.R z)

/-- The limit of the `p`-th column: `(P_n - I) DG(ξ)(i b_p)`. -/
def colLim  (n : ℕ)
    (G : S.E → S.H) (z : ℤ → ℂ) (p : ℤ × Fin 2) : S.H :=
  ((S.cmTrunc n (fderiv ℝ G (S.R z)
      (S.incl (weightedRealHilbertBasis S.cmWeight p))) :
      S.head n) : S.H) -
    fderiv ℝ G (S.R z)
      (S.incl (weightedRealHilbertBasis S.cmWeight p))

theorem norm_fieldD_le  (n N : ℕ)
    (G : S.E → S.H) (B : ℝ) (hB : ∀ x, ‖G x‖ ≤ B)
    (v : S.head N) : ‖S.fieldD n N G v‖ ≤ 2 * B := by
  unfold fieldD
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖((S.cmTrunc n (G (S.headToE N v)) : S.head n) : S.H)‖ ≤ B :=
    (S.norm_cmTrunc_le n _).trans (hB _)
  have h2 : ‖((S.cmTrunc N (G (S.headToE N v)) : S.head N) : S.H)‖ ≤ B :=
    (S.norm_cmTrunc_le N _).trans (hB _)
  linarith

theorem norm_colD_le  (n N : ℕ)
    (G : S.E → S.H) (B : ℝ) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B)
    (v : S.head N) (p : ℤ × Fin 2) :
    ‖S.colD n N G v p‖ ≤
      2 * B * ‖S.incl (weightedRealHilbertBasis S.cmWeight p)‖ := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hDB 0)
  have hw : ‖fderiv ℝ G (S.headToE N v) (S.colArg N p)‖ ≤
      B * ‖S.incl (weightedRealHilbertBasis S.cmWeight p)‖ :=
    ((fderiv ℝ G _).le_opNorm _).trans
      (mul_le_mul (hDB _) (S.norm_colArg_le N p) (norm_nonneg _) hB0)
  unfold colD
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖((S.cmTrunc n (fderiv ℝ G (S.headToE N v) (S.colArg N p)) :
      S.head n) : S.H)‖ ≤ _ := (S.norm_cmTrunc_le n _).trans hw
  have h2 : ‖((S.cmTrunc N (fderiv ℝ G (S.headToE N v) (S.colArg N p)) :
      S.head N) : S.H)‖ ≤ _ := (S.norm_cmTrunc_le N _).trans hw
  linarith

theorem measurable_fieldD_headPt  (n N : ℕ)
    (G : S.E → S.H) (hG : Continuous G) :
    Measurable (fun z => ‖S.fieldD n N G (S.headPt N z)‖ ^ 2) := by
  have hc : Continuous (fun v : S.head N => ‖S.fieldD n N G v‖ ^ 2) := by
    unfold fieldD
    refine Continuous.pow (Continuous.norm (Continuous.sub ?_ ?_)) 2
    · exact continuous_subtype_val.comp ((S.cmTrunc n).continuous.comp
        (hG.comp (S.headToE N).continuous))
    · exact continuous_subtype_val.comp ((S.cmTrunc N).continuous.comp
        (hG.comp (S.headToE N).continuous))
  exact hc.measurable.comp (S.measurable_headPt N)

theorem measurable_colD_headPt 
    (n N : ℕ) (G : S.E → S.H) (hG : ContDiff ℝ 1 G)
    (p : ℤ × Fin 2) :
    Measurable (fun z => ‖S.colD n N G (S.headPt N z) p‖ ^ 2) := by
  have hD : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  have hc : Continuous (fun v : S.head N => ‖S.colD n N G v p‖ ^ 2) := by
    unfold colD
    have hc0 : Continuous (fun v : S.head N =>
        fderiv ℝ G (S.headToE N v) (S.colArg N p)) :=
      (hD.comp (S.headToE N).continuous).clm_apply continuous_const
    refine Continuous.pow (Continuous.norm (Continuous.sub ?_ ?_)) 2
    · exact continuous_subtype_val.comp ((S.cmTrunc n).continuous.comp hc0)
    · exact continuous_subtype_val.comp ((S.cmTrunc N).continuous.comp hc0)
  exact hc.measurable.comp (S.measurable_headPt N)

theorem tendsto_lintegral_fieldD  (n : ℕ) (G : S.E → S.H)
    (hG : Continuous G) (B : ℝ) (hB : ∀ x, ‖G x‖ ≤ B) :
    Tendsto (fun N : ℕ => ∫⁻ z, ENNReal.ofReal (‖S.fieldD n (N + n) G (S.headPt (N + n) z)‖ ^ 2)
        ∂(S.γ)) atTop
      (𝓝 (∫⁻ z, ENNReal.ofReal (‖S.fieldLim n G z‖ ^ 2)
        ∂(S.γ))) := by
  set γ := S.γ with hγ
  refine NlsGge.Ramer.ApproxLimit.tendsto_lintegral_ofReal_of_dominated (μ := γ)
    (fun N z => ‖S.fieldD n (N + n) G (S.headPt (N + n) z)‖ ^ 2)
    (fun z => ‖S.fieldLim n G z‖ ^ 2) ((2 * B) ^ 2)
    (fun N => S.measurable_fieldD_headPt n (N + n) G hG) ?_ ?_
  · intro N z
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (S.norm_fieldD_le n (N + n) G B hB _) 2
  · filter_upwards [S.coord_R_ae] with z hz
    have h1 := S.tendsto_headToE_headPt z hz
    have h2 := h1.comp (tendsto_add_atTop_nat n)
    have hcont : Continuous (fun y : S.E =>
        ((S.cmTrunc n (G y) : S.head n) : S.H)) :=
      continuous_subtype_val.comp ((S.cmTrunc n).continuous.comp hG)
    have t1 := (hcont.tendsto _).comp h2
    have t2 := (S.tendsto_cmTrunc_comp G hG _ _ h1).comp (tendsto_add_atTop_nat n)
    exact (t1.sub t2).norm.pow 2

theorem tendsto_lintegral_colD  (n : ℕ) (G : S.E → S.H)
    (hG : ContDiff ℝ 1 G) (B : ℝ) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) :
    Tendsto (fun N : ℕ => ∫⁻ z, ∑' p : ℤ × Fin 2,
        ENNReal.ofReal (‖S.colD n (N + n) G (S.headPt (N + n) z) p‖ ^ 2)
        ∂(S.γ)) atTop
      (𝓝 (∫⁻ z, ∑' p : ℤ × Fin 2, ENNReal.ofReal (‖S.colLim n G z p‖ ^ 2)
        ∂(S.γ))) := by
  set γ := S.γ with hγ
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hDB 0)
  have hD : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  set b := weightedRealHilbertBasis S.cmWeight with hb
  set i := S.incl with hi
  have hσ : Summable (fun p : ℤ × Fin 2 => 4 * B ^ 2 * ‖i (b p)‖ ^ 2) :=
    (S.incl_hs b).mul_left _
  refine NlsGge.Ramer.ApproxLimit.tendsto_lintegral_tsum_ofReal_of_dominated (μ := γ)
    (fun N z p => ‖S.colD n (N + n) G (S.headPt (N + n) z) p‖ ^ 2)
    (fun z p => ‖S.colLim n G z p‖ ^ 2) _ hσ
    (fun N z p => sq_nonneg _) ?_
    (fun N p => S.measurable_colD_headPt n (N + n) G hG p) ?_
  · intro N z p
    calc ‖S.colD n (N + n) G (S.headPt (N + n) z) p‖ ^ 2
        ≤ (2 * B * ‖i (b p)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (S.norm_colD_le n (N + n) G B hDB _ p) 2
      _ = 4 * B ^ 2 * ‖i (b p)‖ ^ 2 := by ring
  · filter_upwards [S.coord_R_ae] with z hz p
    have h1 := S.tendsto_headToE_headPt z hz
    have h2 := h1.comp (tendsto_add_atTop_nat n)
    -- `P_N`-part: the previously proved convergence of the truncated derivative
    have t2 := (S.tendsto_truncatedDeriv_apply_basis G hG z hz p).comp
      (tendsto_add_atTop_nat n)
    -- the untruncated part: `DG(y_N)(i P_N b_p) → DG(ξ)(i b_p)`
    have hcont : Continuous (fun x : S.E => fderiv ℝ G x (i (b p))) :=
      hD.clm_apply continuous_const
    have t0 : Tendsto (fun N : ℕ => fderiv ℝ G (S.headToE (N + n) (S.headPt (N + n) z))
        (S.colArg (N + n) p)) atTop
        (𝓝 (fderiv ℝ G (S.R z) (i (b p)))) := by
      refine ((hcont.tendsto _).comp h2).congr' ?_
      filter_upwards [(tendsto_add_atTop_nat n).eventually
        (S.eventually_colArg_eq p)] with N hN
      rw [hN]
      rfl
    have t1 := ((continuous_subtype_val.comp (S.cmTrunc n).continuous).tendsto _).comp t0
    exact (t1.sub t2).norm.pow 2


/-! ### The tail terms tend to `0` as `n → ∞` -/

theorem measurable_fieldLim_sq  (n : ℕ)
    (G : S.E → S.H) (hG : Continuous G) :
    Measurable (fun z => ‖S.fieldLim n G z‖ ^ 2) := by
  let _ : MeasurableSpace (S.H) := borel _
  have _ : BorelSpace (S.H) := ⟨rfl⟩
  have hRm := S.measurable_R
  have h1 : Measurable (fun z => ((S.cmTrunc n
      (G (S.R z)) : S.head n) :
        S.H)) :=
    (continuous_subtype_val.comp ((S.cmTrunc n).continuous.comp hG)).measurable.comp hRm
  have h2 : Measurable (fun z => G (S.R z)) :=
    hG.measurable.comp hRm
  exact (h1.sub h2).norm.pow_const 2

theorem measurable_colLim_sq  (n : ℕ)
    (G : S.E → S.H) (hG : ContDiff ℝ 1 G) (p : ℤ × Fin 2) :
    Measurable (fun z => ‖S.colLim n G z p‖ ^ 2) := by
  let _ : MeasurableSpace (S.H) := borel _
  have _ : BorelSpace (S.H) := ⟨rfl⟩
  have hRm := S.measurable_R
  have hD : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  have hc : Continuous (fun x : S.E =>
      fderiv ℝ G x (S.incl (weightedRealHilbertBasis S.cmWeight p))) :=
    hD.clm_apply continuous_const
  have h1 := (continuous_subtype_val.comp ((S.cmTrunc n).continuous.comp hc)).measurable.comp hRm
  have h2 := hc.measurable.comp hRm
  exact (h1.sub h2).norm.pow_const 2

theorem tendsto_lintegral_fieldLim_zero 
    (G : S.E → S.H) (hG : Continuous G) (B : ℝ)
    (hB : ∀ x, ‖G x‖ ≤ B) :
    Tendsto (fun n : ℕ => ∫⁻ z, ENNReal.ofReal (‖S.fieldLim n G z‖ ^ 2)
        ∂(S.γ)) atTop (𝓝 0) := by
  have h := NlsGge.Ramer.ApproxLimit.tendsto_lintegral_ofReal_of_dominated
    (μ := S.γ)
    (fun n z => ‖S.fieldLim n G z‖ ^ 2) (fun _ => (0 : ℝ)) ((2 * B) ^ 2)
    (fun n => S.measurable_fieldLim_sq n G hG) ?_ ?_
  · simpa using h
  · intro n z
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    unfold fieldLim
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖((S.cmTrunc n (G (S.R z)) :
        S.head n) : S.H)‖ ≤ B := (S.norm_cmTrunc_le n _).trans (hB _)
    linarith [hB (S.R z)]
  · refine Eventually.of_forall fun z => ?_
    have h1 := S.tendsto_cmTrunc_self (G (S.R z))
    have h2 := (h1.sub_const (G (S.R z))).norm.pow 2
    simpa [fieldLim] using h2

theorem tendsto_lintegral_colLim_zero  (G : S.E → S.H)
    (hG : ContDiff ℝ 1 G) (B : ℝ) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) :
    Tendsto (fun n : ℕ => ∫⁻ z, ∑' p : ℤ × Fin 2, ENNReal.ofReal (‖S.colLim n G z p‖ ^ 2)
        ∂(S.γ)) atTop (𝓝 0) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hDB 0)
  set b := weightedRealHilbertBasis S.cmWeight with hb
  set i := S.incl with hi
  have hσ : Summable (fun p : ℤ × Fin 2 => 4 * B ^ 2 * ‖i (b p)‖ ^ 2) :=
    (S.incl_hs b).mul_left _
  have h := NlsGge.Ramer.ApproxLimit.tendsto_lintegral_tsum_ofReal_of_dominated
    (μ := S.γ)
    (fun n z p => ‖S.colLim n G z p‖ ^ 2) (fun _ _ => (0 : ℝ)) _ hσ
    (fun N z p => sq_nonneg _) ?_ (fun n p => S.measurable_colLim_sq n G hG p) ?_
  · simpa using h
  · intro n z p
    have hw : ‖fderiv ℝ G (S.R z) (i (b p))‖ ≤
        B * ‖i (b p)‖ :=
      ((fderiv ℝ G _).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hDB _) (norm_nonneg _))
    have h3 : ‖S.colLim n G z p‖ ≤ 2 * B * ‖i (b p)‖ := by
      unfold colLim
      refine (norm_sub_le _ _).trans ?_
      have h1 := (S.norm_cmTrunc_le n
        (fderiv ℝ G (S.R z) (i (b p)))).trans hw
      have h1' : ‖((S.cmTrunc n
        (fderiv ℝ G (S.R z) (i (b p))) :
          S.head n) : S.H)‖ ≤ B * ‖i (b p)‖ := h1
      linarith
    calc ‖S.colLim n G z p‖ ^ 2 ≤ (2 * B * ‖i (b p)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h3 2
      _ = 4 * B ^ 2 * ‖i (b p)‖ ^ 2 := by ring
  · refine Eventually.of_forall fun z p => ?_
    have h1 := S.tendsto_cmTrunc_self
      (fderiv ℝ G (S.R z) (i (b p)))
    have h2 := (h1.sub_const
      (fderiv ℝ G (S.R z) (i (b p)))).norm.pow 2
    simpa [colLim] using h2


/-! ### The bound for fixed `n` -/

/-- For each `n`, `‖a_n(G) - η‖_{L²(γ)}` is bounded by the square root of the `n`-th tail
`E‖(P_n - I) G(ξ)‖² + E ∑_p ‖(P_n - I) DG(ξ)(i b_p)‖²`, provided the divergences of the truncated
fields converge to `η` in `L²(γ)`. -/
theorem eLpNorm_ramerA_sub_le  (n : ℕ) (G : S.E → S.H)
    (hG : ContDiff ℝ 2 G) (B : ℝ) (hB : ∀ x, ‖G x‖ ≤ B) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B)
    (η : (ℤ → ℂ) → ℝ)
    (hηlim : Tendsto (fun N : ℕ => eLpNorm (fun z =>
        S.cylDiv N (fun v => S.cmTrunc N (G (S.headToE N v))) z - η z) 2
        (S.γ)) atTop (𝓝 0)) :
    eLpNorm (fun z => S.ramerA n G z - η z) 2
        (S.γ) ≤
      ((∫⁻ z, ENNReal.ofReal (‖S.fieldLim n G z‖ ^ 2)
          ∂(S.γ)) +
        ∫⁻ z, ∑' p : ℤ × Fin 2,
          ENNReal.ofReal (‖S.colLim n G z p‖ ^ 2)
          ∂(S.γ)) ^ (1 / (2 : ℝ)) := by
  set γ := S.γ with hγ
  have hG1 : ContDiff ℝ 1 G := hG.of_le (by norm_num)
  -- the three terms
  let a : ℕ → ℝ≥0∞ := fun N => eLpNorm (fun z =>
    S.cylDiv (N + n) (S.gRamer (Nat.le_add_left n N) G) z -
      S.ramerA n G z) 2 γ
  let Q : ℕ → ℝ≥0∞ := fun N =>
    (∫⁻ z, ENNReal.ofReal (‖S.fieldD n (N + n) G (S.headPt (N + n) z)‖ ^ 2) ∂γ) +
      ∫⁻ z, ∑' p : ℤ × Fin 2,
        ENNReal.ofReal (‖S.colD n (N + n) G (S.headPt (N + n) z) p‖ ^ 2) ∂γ
  let t : ℕ → ℝ≥0∞ := fun N => eLpNorm (fun z =>
    S.cylDiv (N + n) (fun v => S.cmTrunc (N + n) (G (S.headToE (N + n) v))) z - η z) 2 γ
  have hbound : ∀ N : ℕ, eLpNorm (fun z => S.ramerA n G z - η z) 2 γ ≤
      a N + (Q N) ^ (1 / (2 : ℝ)) + t N := by
    intro N
    have h := Nat.le_add_left n N
    have e : (fun z => S.ramerA n G z - η z) =
        (-(fun z => S.cylDiv (N + n) (S.gRamer h G) z - S.ramerA n G z) +
          (fun z => S.cylDiv (N + n) (S.deltaF h G) z)) +
        (fun z => S.cylDiv (N + n) (fun v => S.cmTrunc (N + n) (G (S.headToE (N + n) v))) z
          - η z) := by
      funext z
      simp only [Pi.add_apply, Pi.neg_apply]
      rw [S.cylDiv_deltaF h G hG]
      change _ = -(S.cylDiv (N + n) (S.gRamer h G) z - S.ramerA n G z) +
        (S.cylDiv (N + n) (S.gRamer h G) z - S.cylDiv (N + n) (S.truncF G (N + n)) z) +
        (S.cylDiv (N + n) (S.truncF G (N + n)) z - η z)
      ring
    rw [e]
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    refine add_le_add ((eLpNorm_add_le (by norm_num)).trans ?_) le_rfl
    refine add_le_add ?_ ?_
    · rw [eLpNorm_neg]
    · exact S.eLpNorm_cylDiv_deltaF_le n (N + n) h G hG B hB hDB
  have ha : Tendsto a atTop (𝓝 0) :=
    S.tendsto_eLpNorm_cylDiv_gRamer n G hG1 B hB hDB
  have ht : Tendsto t atTop (𝓝 0) := hηlim.comp (tendsto_add_atTop_nat n)
  have hQ : Tendsto Q atTop (𝓝 ((∫⁻ z, ENNReal.ofReal (‖S.fieldLim n G z‖ ^ 2) ∂γ) +
      ∫⁻ z, ∑' p : ℤ × Fin 2,
        ENNReal.ofReal (‖S.colLim n G z p‖ ^ 2) ∂γ)) :=
    (S.tendsto_lintegral_fieldD n G hG1.continuous B hB).add
      (S.tendsto_lintegral_colD n G hG1 B hDB)
  have hQ' := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto _).comp hQ
  have hT := (ha.add hQ').add ht
  rw [zero_add, add_zero] at hT
  exact ge_of_tendsto' hT hbound

/-- The tail `n ↦ E‖(P_n - I) G(ξ)‖² + E ∑_p ‖(P_n - I) DG(ξ)(i b_p)‖²` tends to `0`. -/
theorem tendsto_tail_zero  (G : S.E → S.H)
    (hG : ContDiff ℝ 1 G) (B : ℝ) (hB : ∀ x, ‖G x‖ ≤ B) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) :
    Tendsto (fun n : ℕ =>
      ((∫⁻ z, ENNReal.ofReal (‖S.fieldLim n G z‖ ^ 2)
          ∂(S.γ)) +
        ∫⁻ z, ∑' p : ℤ × Fin 2,
          ENNReal.ofReal (‖S.colLim n G z p‖ ^ 2)
          ∂(S.γ)) ^ (1 / (2 : ℝ))) atTop (𝓝 0) := by
  have h := (S.tendsto_lintegral_fieldLim_zero G hG.continuous B hB).add
    (S.tendsto_lintegral_colLim_zero G hG B hDB)
  rw [add_zero] at h
  have h' := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp h
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h'
  exact h'


/-! ### Main results -/

/-- **H2: Ramer's approximants converge in `L²(γ)`.** If `G : E_s → H` is `C²` with `G`, `DG`
bounded by `B`, and the divergences `δ_cyl(P_N G(P_N ·))` of the truncated fields converge to `η`
in `L²(γ)`, then Ramer's approximants `a_n(G) = ⟨P_n G, x_n⟩ - tr(P_n DG)` converge to `η` in
`L²(γ)`. -/
theorem tendsto_eLpNorm_ramerA 
    
    (G : S.E → S.H)
    (hG : ContDiff ℝ 2 G) (B : ℝ) (hB : ∀ x, ‖G x‖ ≤ B) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B)
    (η : (ℤ → ℂ) → ℝ)
    (hη : MemLp η 2 (S.γ))
    (hηlim : Tendsto (fun N : ℕ => eLpNorm (fun z =>
        S.cylDiv N (fun v => S.cmTrunc N (G (S.headToE N v))) z - η z) 2
        (S.γ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => eLpNorm (fun z =>
        S.ramerA n G z - η z) 2
        (S.γ)) atTop (𝓝 0) := by
  -- `hη` is not needed: `eLpNorm_add_le` carries no measurability hypothesis.
  have _ := hη
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (S.tendsto_tail_zero G (hG.of_le (by norm_num)) B hB hDB)
    (fun _ => zero_le)
    (fun n => S.eLpNorm_ramerA_sub_le n G hG B hB hDB η hηlim)

/-- **H3: locality of Ramer's approximant.** If two fields agree on an open set `U` of `E_s`,
then `a_n(G)` and `a_n(K)` agree at every sample whose realization lies in `U`. -/
theorem ramerA_congr_of_eqOn  
    (G K : S.E → S.H)
    {U : Set (S.E)} (hU : IsOpen U) (h : Set.EqOn G K U)
    (n : ℕ) (z : ℤ → ℂ)
    (hz : S.R z ∈ U) :
    S.ramerA n G z = S.ramerA n K z := by
  have hev : G =ᶠ[𝓝 (S.R z)] K :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hz) h
  have hd : fderiv ℝ G (S.R z) =
      fderiv ℝ K (S.R z) := hev.fderiv_eq
  unfold ramerA
  rw [h hz, hd]
end NlsGge.Ramer.General.RamerSetting
