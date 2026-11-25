import QuantumNLS.Q07ContourApplicationR16
import QuantumNLS.Q07IntegratedHessiansR16

/-! Actual full real Frechet differentiation of the four rectangular sides.
The side fields are canonical derivatives of the actual Cauchy logarithm. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Metric Filter Topology MeasureTheory
namespace QuantumNLS.Q07WindowDifferentiationR16
open PhysicalTensor (L2T)
open Q07LogDifferentialsR16 Q07ContourDifferentiationR16 Q07ContourApplicationR16
open ResolventNeighborhood (GammaN)

section Linear
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite scalar combination preserves both actual Frechet derivatives. -/
theorem sum_twice {ι : Type*} [Fintype ι] {U : Set E} (hU : IsOpen U)
    (c : ι → ℂ) (f : ι → E → ℂ) (D1 : ι → E → E →L[ℝ] ℂ)
    (D2 : ι → E →L[ℝ] (E →L[ℝ] ℂ)) {x : E} (hx : x ∈ U)
    (h1 : ∀ i y, y ∈ U → HasFDerivAt (f i) (D1 i y) y)
    (h2 : ∀ i, HasFDerivAt (D1 i) (D2 i) x) :
    (∀ y ∈ U, HasFDerivAt (fun z => ∑ i, c i*f i z) (∑ i, c i • D1 i y) y) ∧
    HasFDerivAt (fderiv ℝ (fun z => ∑ i, c i*f i z)) (∑ i, c i • D2 i) x := by
  have hf : ∀ y ∈ U, HasFDerivAt (fun z => ∑ i, c i*f i z) (∑ i, c i • D1 i y) y := by
    intro y hy
    exact HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => (h1 i y hy).const_mul (c i))
  have hd : HasFDerivAt (fun y => ∑ i, c i • D1 i y) (∑ i, c i • D2 i) x :=
    HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => (h2 i).const_smul (c i))
  have he : fderiv ℝ (fun z => ∑ i, c i*f i z) =ᶠ[𝓝 x] (fun y => ∑ i, c i • D1 i y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hf y hy).fderiv
  exact ⟨hf,hd.congr_of_eventuallyEq he⟩

/-- A bounded real-linear postcomposition preserves the second derivative. -/
theorem post_twice {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (P : ℂ →L[ℝ] G) {U : Set E} (hU : IsOpen U) {f : E → ℂ} {x : E} (hx : x ∈ U)
    (hf : ∀ y ∈ U, DifferentiableAt ℝ f y)
    {D2 : E →L[ℝ] (E →L[ℝ] ℂ)} (h2 : HasFDerivAt (fderiv ℝ f) D2 x) :
    HasFDerivAt (fderiv ℝ (fun y => P (f y)))
      ((ContinuousLinearMap.compL ℝ E ℂ G P).comp D2) x := by
  let A := ContinuousLinearMap.compL ℝ E ℂ G P
  have hd := A.hasFDerivAt.comp x h2
  have he : fderiv ℝ (fun y => P (f y)) =ᶠ[𝓝 x] (fun y => A (fderiv ℝ f y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (P.hasFDerivAt.comp y (hf y hy).hasFDerivAt).fderiv
  exact hd.congr_of_eventuallyEq he
end Linear

variable {L κ : ℝ} [Fact (0 < L)]

def side (a h : ℝ) (i : Fin 4) (t : ℝ) : ℂ :=
  if i = 0 then (t : ℂ)-(h : ℂ)*Complex.I
  else if i = 1 then (a : ℂ)+(t : ℂ)*Complex.I
  else if i = 2 then (t : ℂ)+(h : ℂ)*Complex.I
  else ((-a : ℝ) : ℂ)+(t : ℂ)*Complex.I
def lo (a h : ℝ) (i : Fin 4) : ℝ := if i = 0 then -a else if i = 1 then -h else if i = 2 then -a else -h
def hi (a h : ℝ) (i : Fin 4) : ℝ := if i = 0 then a else if i = 1 then h else if i = 2 then a else h
def coefficient (i : Fin 4) : ℂ := if i = 0 then 1 else if i = 1 then Complex.I else if i = 2 then -1 else -Complex.I

theorem side_mem {a h : ℝ} (i : Fin 4) {t : ℝ} (ht : t ∈ Icc (lo a h i) (hi a h i)) :
    side a h i t ∈ GammaN a h := by
  fin_cases i
  · simpa [side,lo,hi] using (ContourPrefactor.bottom_mem (a := a) (h := h) (by simpa [lo,hi] using ht))
  · simpa [side,lo,hi] using (ContourPrefactor.right_mem (a := a) (h := h) (by simpa [lo,hi] using ht))
  · simpa [side,lo,hi] using (ContourPrefactor.top_mem (a := a) (h := h) (by simpa [lo,hi] using ht))
  · simpa [side,lo,hi] using (ContourPrefactor.left_mem (a := a) (h := h) (by simpa [lo,hi] using ht))

theorem rect_sum (a h : ℝ) (F : ℂ → ℂ) :
    PropagationContour.rectContour a h F =
      ∑ i : Fin 4, coefficient i*(∫ t in lo a h i..hi a h i, F (side a h i t)) := by
  simp [Fin.sum_univ_four,coefficient,side,lo,hi,PropagationContour.rectContour,
    intervalIntegral.integral_mul_const]
  all_goals ring

/-- Full real second differentiation of the literal source window contour.
The denominator and field bounds are inputs only to this local assembly
lemma; the physical Sobolev-class theorem discharges them. -/
theorem window_second (hκ : 0 < κ) (r : ℕ) {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h)
    {U : Set (L2T L)} (hU : IsOpen U) {A1 A2 : ℝ} (h2 : 0 ≤ A2)
    (hreg : ∀ v ∈ U, ∀ z ∈ GammaN a h, RootCauchyJointR9.Regular κ (v,z))
    (hB1 : ∀ v ∈ U, ∀ z ∈ GammaN a h, ‖fderiv ℝ (logarithm hκ z) v‖ ≤ A1)
    (hB2 : ∀ v ∈ U, ∀ z ∈ GammaN a h, ‖fderiv ℝ (fderiv ℝ (logarithm hκ z)) v‖ ≤ A2)
    {u : L2T L} (hu : u ∈ U) :
    DifferentiableAt ℝ (Q07IntegratedHessiansR16.windowContour hκ r a h) u ∧
    DifferentiableAt ℝ (fderiv ℝ (Q07IntegratedHessiansR16.windowContour hκ r a h)) u ∧
      ∀ v w : L2T L,
        |((fderiv ℝ (fderiv ℝ (Q07IntegratedHessiansR16.windowContour hκ r a h)) u) v) w| ≤
          (1/(2*Real.pi*κ))*(4*(a+h)*((a+h)^r*A2))*‖v‖*‖w‖ := by
  let F : Fin 4 → L2T L × ℝ → ℂ := fun i p =>
    (side a h i p.2)^r*logarithm hκ (side a h i p.2) p.1
  let J : Fin 4 → L2T L → ℂ := fun i v => ∫ t in lo a h i..hi a h i, F i (v,t)
  let D1 : Fin 4 → L2T L → L2T L →L[ℝ] ℂ := fun i v =>
    ∫ t in lo a h i..hi a h i, fieldPartial (F i) (v,t)
  let D2 : Fin 4 → L2T L →L[ℝ] (L2T L →L[ℝ] ℂ) := fun i =>
    ∫ t in lo a h i..hi a h i, fieldPartial (fieldPartial (F i)) (u,t)
  have hab : ∀ i : Fin 4, lo a h i ≤ hi a h i := by
    intro i
    fin_cases i <;> simp [lo,hi] <;> linarith
  have hside : ∀ i : Fin 4, ∀ v ∈ U,
      HasFDerivAt (J i) (D1 i v) v ∧ HasFDerivAt (fderiv ℝ (J i))
        (∫ t in lo a h i..hi a h i, fieldPartial (fieldPartial (F i)) (v,t)) v := by
    intro i v hv
    apply weighted_side hκ r (side a h i) hU (hab i) (Z := a+h) (by linarith)
    · intro t _
      have hr : AnalyticAt ℝ (fun x : ℝ => (x : ℂ)) t := Complex.ofRealCLM.analyticAt t
      fin_cases i
      · change AnalyticAt ℝ (fun x : ℝ => (x : ℂ)-(h : ℂ)*Complex.I) t
        exact hr.sub analyticAt_const
      · change AnalyticAt ℝ (fun x : ℝ => (a : ℂ)+(x : ℂ)*Complex.I) t
        exact analyticAt_const.add (hr.mul analyticAt_const)
      · change AnalyticAt ℝ (fun x : ℝ => (x : ℂ)+(h : ℂ)*Complex.I) t
        exact hr.add analyticAt_const
      · change AnalyticAt ℝ (fun x : ℝ => ((-a : ℝ) : ℂ)+(x : ℂ)*Complex.I) t
        exact analyticAt_const.add (hr.mul analyticAt_const)
    · intro t ht
      exact Q07IntegratedHessiansR16.norm_le_of_GammaN ha hh.le (side_mem i ht)
    · exact fun x hx t ht => hreg x hx _ (side_mem i ht)
    · exact fun x hx t ht => hB1 x hx _ (side_mem i ht)
    · exact fun x hx t ht => hB2 x hx _ (side_mem i ht)
    · exact hv
  have hD1 : ∀ i, HasFDerivAt (D1 i) (D2 i) u := by
    intro i
    have he : D1 i =ᶠ[𝓝 u] fderiv ℝ (J i) := by
      filter_upwards [hU.mem_nhds hu] with v hv
      exact (hside i v hv).1.fderiv.symm
    exact (hside i u hu).2.congr_of_eventuallyEq he
  obtain ⟨hsum,hsum2⟩ := sum_twice hU coefficient J D1 D2 hu
    (fun i v hv => (hside i v hv).1) hD1
  let S : L2T L → ℂ := fun v => ∑ i : Fin 4, coefficient i*J i v
  let T : L2T L →L[ℝ] (L2T L →L[ℝ] ℂ) := ∑ i : Fin 4, coefficient i • D2 i
  let P : ℂ →L[ℝ] ℝ := (-(1/(2*Real.pi*κ))) • Complex.reCLM
  have hw : Q07IntegratedHessiansR16.windowContour hκ r a h = fun v => P (S v) := by
    funext v
    change -(1/(2*Real.pi*κ))*(PropagationContour.rectContour a h
      (fun z => z^r*logarithm hκ z v)).re = _
    rw [rect_sum]
    rfl
  have hdS : ∀ v ∈ U, DifferentiableAt ℝ S v := fun v hv => (hsum v hv).differentiableAt
  have hdW : DifferentiableAt ℝ (fun v => P (S v)) u := P.differentiableAt.comp u (hdS u hu)
  have hdW2 := post_twice P hU hu hdS hsum2
  rw [hw]
  refine ⟨hdW,hdW2.differentiableAt,?_⟩
  let M := (a+h)^r*A2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hTi : ∀ i : Fin 4, ‖D2 i‖ ≤ M*|hi a h i-lo a h i| := by
    intro i
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [uIoc_of_le (hab i)] at ht
    have ht' : t ∈ Icc (lo a h i) (hi a h i) := ⟨ht.1.le,ht.2⟩
    change ‖fieldPartial (fieldPartial (fun p : L2T L × ℝ =>
      (side a h i p.2)^r*logarithm hκ (side a h i p.2) p.1)) (u,t)‖ ≤ M
    rw [weighted_second hκ r (side a h i) (hreg u hu _ (side_mem i ht')), norm_smul, norm_pow]
    apply mul_le_mul
      (pow_le_pow_left₀ (norm_nonneg _) (Q07IntegratedHessiansR16.norm_le_of_GammaN ha hh.le (side_mem i ht')) r)
      (hB2 u hu _ (side_mem i ht'))
      (ContinuousLinearMap.opNorm_nonneg _) (by positivity)
  have hlen : (∑ i : Fin 4, |hi a h i-lo a h i|) = 4*(a+h) := by
    simp_rw [abs_of_nonneg (sub_nonneg.mpr (hab _))]
    simp [Fin.sum_univ_four,lo,hi]
    ring
  have hci : ∀ i : Fin 4, ‖coefficient i‖ = 1 := by intro i; fin_cases i <;> simp [coefficient]
  have hT : ‖T‖ ≤ M*(4*(a+h)) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    simp only [T,_root_.sum_apply,smul_apply,smul_eq_mul]
    calc
      _ ≤ ∑ i : Fin 4, ‖coefficient i*(D2 i v w)‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 4, (M*|hi a h i-lo a h i|)*‖v‖*‖w‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul,hci i,one_mul]
        have hv := (D2 i).le_opNorm v
        have hw := (D2 i v).le_opNorm w
        calc
          _ ≤ ‖D2 i v‖*‖w‖ := hw
          _ ≤ (‖D2 i‖*‖v‖)*‖w‖ := by gcongr
          _ ≤ _ := by gcongr; exact hTi i
      _ = _ := by rw [← Finset.sum_mul,← Finset.sum_mul,← Finset.mul_sum,hlen]
  have hpref : 0 ≤ 1/(2*Real.pi*κ) := by positivity
  have hP : ∀ z : ℂ, |P z| ≤ (1/(2*Real.pi*κ))*‖z‖ := by
    intro z
    change |(-(1/(2*Real.pi*κ)))*z.re| ≤ _
    rw [abs_mul,abs_neg,abs_of_nonneg hpref]
    exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) hpref
  intro v w
  rw [hdW2.fderiv]
  change |P (T v w)| ≤ _
  refine (hP _).trans ?_
  have hv := T.le_opNorm v
  have hw' := (T v).le_opNorm w
  have hval : ‖T v w‖ ≤ (M*(4*(a+h)))*‖v‖*‖w‖ := by
    calc
      _ ≤ ‖T v‖*‖w‖ := hw'
      _ ≤ (‖T‖*‖v‖)*‖w‖ := by gcongr
      _ ≤ _ := by gcongr
  calc
    _ ≤ (1/(2*Real.pi*κ))*((M*(4*(a+h)))*‖v‖*‖w‖) :=
      mul_le_mul_of_nonneg_left hval hpref
    _ = _ := by dsimp [M]; ring

end QuantumNLS.Q07WindowDifferentiationR16
