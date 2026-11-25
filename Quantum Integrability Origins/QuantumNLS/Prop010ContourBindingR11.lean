import QuantumNLS.Round10ScalarReconstructionBatch
import QuantumNLS.BoundedBetheTransfer
import QuantumNLS.MixedQuadratures
import QuantumNLS.CartesianOccupationTransfer

/-! Concrete bounded diagonal contour operators for PROP-010.
No reconstruction estimate is assumed in these definitions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
open Set Filter Topology Complex MeasureTheory
open scoped InnerProductSpace BigOperators ContDiff
namespace QuantumNLS.Prop010ContourBindingR11

section Diagonal
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

def diagonal (b : HilbertBasis ι ℂ E) (a : ι → ℂ) (M : ℝ)
    (hM : 0 ≤ M) (ha : ∀ i, ‖a i‖ ≤ M) : E →L[ℂ] E :=
  (HilbertDiagOp.diag_exists b a M ha hM).choose

lemma diagonal_coord (b : HilbertBasis ι ℂ E) (a : ι → ℂ) (M : ℝ)
    (hM : 0 ≤ M) (ha : ∀ i, ‖a i‖ ≤ M) (i : ι) (v : E) :
    ⟪b i, diagonal b a M hM ha v⟫_ℂ = a i * ⟪b i,v⟫_ℂ :=
  (HilbertDiagOp.diag_exists b a M ha hM).choose_spec.1 i v

lemma diagonal_norm (b : HilbertBasis ι ℂ E) (a : ι → ℂ) (M : ℝ)
    (hM : 0 ≤ M) (ha : ∀ i, ‖a i‖ ≤ M) : ‖diagonal b a M hM ha‖ ≤ M :=
  (HilbertDiagOp.diag_exists b a M ha hM).choose_spec.2

lemma diagonal_basis (b : HilbertBasis ι ℂ E) (a : ι → ℂ) (M : ℝ)
    (hM : 0 ≤ M) (ha : ∀ i, ‖a i‖ ≤ M) (i : ι) :
    diagonal b a M hM ha (b i) = a i • b i := by
  apply b.repr.injective
  ext j
  simp only [HilbertBasis.repr_apply_apply,diagonal_coord,inner_smul_right]
  by_cases hj : j = i
  · subst j; rfl
  · rw [b.orthonormal.inner_eq_zero hj,mul_zero,mul_zero]

/-- Operator real part, exactly `(T+T*)/2`. -/
def realPart (T : E →L[ℂ] E) : E →L[ℂ] E := (2:ℂ)⁻¹ • (T+T.adjoint)

lemma realPart_basis (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E)
    (a : ι → ℂ) (hT : ∀ i,T (b i)=a i • b i) (i : ι) :
    realPart T (b i) = ((a i).re:ℂ) • b i := by
  rw [realPart,smul_apply,add_apply,hT,
    BoundedBetheTransfer.adjoint_basis b T a hT,← add_smul,smul_smul]
  congr 1
  apply Complex.ext
  · simp [Complex.inv_re,Complex.inv_im]; ring
  · simp [Complex.inv_re,Complex.inv_im]

lemma realPart_selfAdjoint (T : E →L[ℂ] E) : IsSelfAdjoint (realPart T) := by
  change (realPart T).adjoint = realPart T
  have hc : (starRingEnd ℂ) ((2:ℂ)⁻¹) = (2:ℂ)⁻¹ := by
    change star ((2:ℂ)⁻¹)=(2:ℂ)⁻¹
    rw [star_inv₀,star_ofNat]
  rw [realPart,map_smulₛₗ,hc,map_add,ContinuousLinearMap.adjoint_adjoint,add_comm]

lemma realPart_norm (T : E →L[ℂ] E) : ‖realPart T‖ ≤ ‖T‖ := by
  calc ‖realPart T‖ = (1/2:ℝ)*‖T+T.adjoint‖ := by rw [realPart,norm_smul]; norm_num
       _ ≤ (1/2:ℝ)*(‖T‖+‖T.adjoint‖) := by gcongr; exact norm_add_le _ _
       _ = ‖T‖ := by rw [ContinuousLinearMap.adjoint.norm_map]; ring

/-- The operator-norm Bochner boundary integral of the source rectangle. -/
def rectOp (F : ℂ → E →L[ℂ] E) (a b h : ℝ) : E →L[ℂ] E :=
  (∫ x in a..b,F (x+((-h:ℝ):ℂ)*I)) - (∫ x in a..b,F (x+h*I)) +
    I • (∫ y in (-h)..h,F (b+y*I)) - I • (∫ y in (-h)..h,F (a+y*I))

lemma rectOp_basis (b0 : HilbertBasis ι ℂ E) (F : ℂ → E →L[ℂ] E)
    (f : ℂ → ι → ℂ) {a b h : ℝ} (hab : a ≤ b) (hh : 0 ≤ h)
    (hc : ∀ z ∈ PeriodReconstruction.Gam a b h,ContinuousAt F z)
    (he : ∀ z i,F z (b0 i)=f z i • b0 i) (i : ι) :
    rectOp F a b h (b0 i) = LabelExactPeriod.rectIntegral (fun z => f z i) a b h • b0 i := by
  have ih (y : ℝ) (hy : ∀ x ∈ uIcc a b,(x:ℂ)+y*I ∈ PeriodReconstruction.Gam a b h) :
      IntervalIntegrable (fun x : ℝ => F (x+y*I)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    exact ((hc _ (hy x hx)).comp_of_eq (by fun_prop : ContinuousAt (fun x : ℝ => (x:ℂ)+y*I) x) rfl).continuousWithinAt
  have iv (x : ℝ) (hx : ∀ y ∈ uIcc (-h) h,(x:ℂ)+y*I ∈ PeriodReconstruction.Gam a b h) :
      IntervalIntegrable (fun y : ℝ => F (x+y*I)) volume (-h) h := by
    apply ContinuousOn.intervalIntegrable
    intro y hy
    exact ((hc _ (hx y hy)).comp_of_eq (by fun_prop : ContinuousAt (fun y : ℝ => (x:ℂ)+y*I) y) rfl).continuousWithinAt
  simp only [rectOp,sub_apply,add_apply,smul_apply,
    ContinuousLinearMap.intervalIntegral_apply (ih (-h) (fun _ hx => PeriodTwoTerm.bot_mem hab hx)),
    ContinuousLinearMap.intervalIntegral_apply (ih h (fun _ hx => PeriodTwoTerm.top_mem hab hx)),
    ContinuousLinearMap.intervalIntegral_apply (iv b (fun _ hy => PeriodTwoTerm.right_mem hh hy)),
    ContinuousLinearMap.intervalIntegral_apply (iv a (fun _ hy => PeriodTwoTerm.left_mem hh hy)),he,
    intervalIntegral.integral_smul_const,LabelExactPeriod.rectIntegral,
    sub_smul,add_smul,smul_smul]
  rfl

end Diagonal

/-- A declared globally bounded, Lipschitz scalar extension. Smooth compactly
supported extensions supply this regularity; no period/error bound is a field. -/
structure Extension (X : Type*) [PseudoMetricSpace X] where
  value : X → ℂ
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  value_bound : ∀ x, ‖value x‖ ≤ bound
  constant : NNReal
  lipschitz : LipschitzWith constant value

section Lift
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def lift (b : HilbertBasis ι ℂ E) (a : ℂ → ι → ℂ) (f : Extension (ℂ × ℂ))
    (z : ℂ) : E →L[ℂ] E :=
  diagonal b (fun i => f.value (z,a z i)) f.bound f.bound_nonneg (fun _i => f.value_bound _)

lemma lift_basis (b : HilbertBasis ι ℂ E) (a : ℂ → ι → ℂ) (f : Extension (ℂ × ℂ))
    (z : ℂ) (i : ι) : lift b a f z (b i)=f.value (z,a z i) • b i :=
  diagonal_basis b _ _ _ _ i

lemma eigen_sub_norm (b : HilbertBasis ι ℂ E) (A B : E →L[ℂ] E) (a d : ι → ℂ)
    (hA : ∀ i,A (b i)=a i • b i) (hB : ∀ i,B (b i)=d i • b i) (i : ι) :
    ‖a i-d i‖ ≤ ‖A-B‖ := by
  have he : (A-B) (b i)=(a i-d i) • b i := by rw [sub_apply,hA,hB,sub_smul]
  have hn := (A-B).le_opNorm (b i)
  rw [he,norm_smul,b.orthonormal.1 i,mul_one,mul_one] at hn
  exact hn

lemma lift_sub_norm (b : HilbertBasis ι ℂ E) (A : ℂ → E →L[ℂ] E)
    (a : ℂ → ι → ℂ) (hA : ∀ z i,A z (b i)=a z i • b i)
    (f : Extension (ℂ × ℂ)) (z w : ℂ) :
    ‖lift b a f z-lift b a f w‖ ≤ f.constant * max ‖z-w‖ ‖A z-A w‖ := by
  apply BoundedBetheTransfer.diagonal_norm_le b _
    (fun i => f.value (z,a z i)-f.value (w,a w i))
    (fun i => by rw [sub_apply,lift_basis,lift_basis,sub_smul]) (by positivity)
  intro i
  have hl := f.lipschitz.dist_le_mul (z,a z i) (w,a w i)
  rw [Prod.dist_eq,dist_eq_norm,dist_eq_norm,dist_eq_norm] at hl
  exact hl.trans (mul_le_mul_of_nonneg_left
    (max_le_max le_rfl (eigen_sub_norm b _ _ _ _ (hA z) (hA w) i)) f.constant.coe_nonneg)

lemma continuousAt_lift (b : HilbertBasis ι ℂ E) (A : ℂ → E →L[ℂ] E)
    (a : ℂ → ι → ℂ) (hA : ∀ z i,A z (b i)=a z i • b i)
    (f : Extension (ℂ × ℂ)) (z : ℂ) (hc : ContinuousAt A z) :
    ContinuousAt (lift b a f) z := by
  have hn : Tendsto (fun w => f.constant * max ‖w-z‖ ‖A w-A z‖) (𝓝 z) (𝓝 0) := by
    have h1 : Tendsto (fun w : ℂ => ‖w-z‖) (𝓝 z) (𝓝 0) := by
      simpa only [sub_self,norm_zero] using
      (show Tendsto (fun w : ℂ => ‖w-z‖) (𝓝 z) (𝓝 ‖z-z‖) from
        ((continuousAt_id : ContinuousAt (fun w : ℂ => w) z).sub continuousAt_const).norm)
    have h2 : Tendsto (fun w => ‖A w-A z‖) (𝓝 z) (𝓝 0) := by
      simpa only [sub_self,norm_zero] using
      (show Tendsto (fun w => ‖A w-A z‖) (𝓝 z) (𝓝 ‖A z-A z‖) from
        (hc.sub continuousAt_const).norm)
    simpa using (h1.max h2).const_mul (f.constant:ℝ)
  have ht : Tendsto (fun w => lift b a f w-lift b a f z) (𝓝 z) (𝓝 0) :=
    squeeze_zero_norm (fun w => lift_sub_norm b A a hA f w z) hn
  have hh := ht.add_const (lift b a f z)
  change Tendsto (lift b a f) (𝓝 z) (𝓝 (lift b a f z))
  simpa using hh

/-- Joint extension of the transfer and its first derivative. -/
def liftJoint (b : HilbertBasis ι ℂ E) (a d : ℂ → ι → ℂ)
    (g : Extension (ℂ × (ℂ × ℂ))) (z : ℂ) : E →L[ℂ] E :=
  diagonal b (fun i => g.value (z,(a z i,d z i))) g.bound g.bound_nonneg
    (fun _i => g.value_bound _)

lemma liftJoint_basis (b : HilbertBasis ι ℂ E) (a d : ℂ → ι → ℂ)
    (g : Extension (ℂ × (ℂ × ℂ))) (z : ℂ) (i : ι) :
    liftJoint b a d g z (b i)=g.value (z,(a z i,d z i)) • b i :=
  diagonal_basis b _ _ _ _ i

lemma liftJoint_sub_norm (b : HilbertBasis ι ℂ E) (A D : ℂ → E →L[ℂ] E)
    (a d : ℂ → ι → ℂ) (hA : ∀ z i,A z (b i)=a z i • b i)
    (hD : ∀ z i,D z (b i)=d z i • b i)
    (g : Extension (ℂ × (ℂ × ℂ))) (z w : ℂ) :
    ‖liftJoint b a d g z-liftJoint b a d g w‖ ≤
      g.constant * max ‖z-w‖ (max ‖A z-A w‖ ‖D z-D w‖) := by
  apply BoundedBetheTransfer.diagonal_norm_le b _
    (fun i => g.value (z,(a z i,d z i))-g.value (w,(a w i,d w i)))
    (fun i => by rw [sub_apply,liftJoint_basis,liftJoint_basis,sub_smul]) (by positivity)
  intro i
  have hl := g.lipschitz.dist_le_mul (z,(a z i,d z i)) (w,(a w i,d w i))
  simp only [dist_eq_norm] at hl
  exact hl.trans (mul_le_mul_of_nonneg_left (max_le_max le_rfl
    (max_le_max (eigen_sub_norm b _ _ _ _ (hA z) (hA w) i)
      (eigen_sub_norm b _ _ _ _ (hD z) (hD w) i))) g.constant.coe_nonneg)

lemma continuousAt_liftJoint (b : HilbertBasis ι ℂ E) (A D : ℂ → E →L[ℂ] E)
    (a d : ℂ → ι → ℂ) (hA : ∀ z i,A z (b i)=a z i • b i)
    (hD : ∀ z i,D z (b i)=d z i • b i)
    (g : Extension (ℂ × (ℂ × ℂ))) (z : ℂ) (hc : ContinuousAt A z) (hd : ContinuousAt D z) :
    ContinuousAt (liftJoint b a d g) z := by
  have h1 : Tendsto (fun w : ℂ => ‖w-z‖) (𝓝 z) (𝓝 0) := by
    simpa only [sub_self,norm_zero] using
      (show Tendsto (fun w : ℂ => ‖w-z‖) (𝓝 z) (𝓝 ‖z-z‖) from
        ((continuousAt_id : ContinuousAt (fun w : ℂ => w) z).sub continuousAt_const).norm)
  have h2 : Tendsto (fun w => ‖A w-A z‖) (𝓝 z) (𝓝 0) := by
    simpa only [sub_self,norm_zero] using
      (show Tendsto (fun w => ‖A w-A z‖) (𝓝 z) (𝓝 ‖A z-A z‖) from
        (hc.sub continuousAt_const).norm)
  have h3 : Tendsto (fun w => ‖D w-D z‖) (𝓝 z) (𝓝 0) := by
    simpa only [sub_self,norm_zero] using
      (show Tendsto (fun w => ‖D w-D z‖) (𝓝 z) (𝓝 ‖D z-D z‖) from
        (hd.sub continuousAt_const).norm)
  have hn : Tendsto (fun w => g.constant * max ‖w-z‖ (max ‖A w-A z‖ ‖D w-D z‖))
      (𝓝 z) (𝓝 0) := by simpa using (h1.max (h2.max h3)).const_mul (g.constant:ℝ)
  have ht : Tendsto (fun w => liftJoint b a d g w-liftJoint b a d g z) (𝓝 z) (𝓝 0) :=
    squeeze_zero_norm (fun w => liftJoint_sub_norm b A D a d hA hD g w z) hn
  change Tendsto (liftJoint b a d g) (𝓝 z) (𝓝 (liftJoint b a d g z))
  simpa using ht.add_const (liftJoint b a d g z)
end Lift

section Correction
open PeriodReconstructionCore
/-- Literal root from eq:B4-local-functions, expressed in the fixed scalar background. -/
def localRoot (L κ : ℝ) (G : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (w+Df L κ G z*(1+(w^2-sf L κ G z^2)/Df L κ G z^2)^((2:ℂ)⁻¹))/2

def localLog (L κ : ℝ) (G : ℂ → ℂ) (z w : ℂ) : ℂ :=
  I*κ*G z+log (localRoot L κ G z w/Af κ G z)

/-- The precise correction, including its derivative variable. -/
def localCorrection (L κ : ℝ) (G : ℂ → ℂ) (z w v : ℂ) : ℂ :=
  ef L z*(localRoot L κ G z w*v-I*L*ef L z)/
    (localRoot L κ G z w^2*(2*localRoot L κ G z w-w)^2)

lemma localRoot_sN (L κ c : ℝ) (G : ℂ → ℂ) {N : ℕ} (q : Fin N → ℝ) (z : ℂ) :
    localRoot L κ G z (sNf L c q z)=aNf L κ c G q z := rfl

lemma localLog_sN (L κ c : ℝ) (G : ℂ → ℂ) {N : ℕ} (q : Fin N → ℝ) (z : ℂ) :
    localLog L κ G z (sNf L c q z)=logaNf L κ c G q z := rfl

/-- Source quadratic-derivative equation for the actual scalar transfer. -/
theorem quadratic_derivative (L κ c : ℝ) (G : ℂ → ℂ) {N : ℕ} (q : Fin N → ℝ) {z : ℂ}
    (hG : DifferentiableAt ℂ G z) (hD : ∀ᶠ w in 𝓝 z,Df L κ G w ≠ 0)
    (hz : ∀ j,2*|c|<‖z-q j‖) (hW : 1+Wf L κ c G q z ∈ slitPlane) :
    deriv (aNf L κ c G q) z*DNf L κ c G q z =
      aNf L κ c G q z*deriv (sNf L c q) z-I*L*ef L z := by
  have hd := deriv_aN_mul_DN L κ c hG hD hz hW
  rw [← (hasDerivAt_sN L hz).deriv] at hd
  simpa only [mul_comm] using hd

/-- No correction eigenvalue agreement is assumed: substitution and the
quadratic derivative prove the source correction exactly. -/
theorem correction_sN (L κ c : ℝ) (G : ℂ → ℂ) {N : ℕ} (q : Fin N → ℝ) {z : ℂ}
    (hG : DifferentiableAt ℂ G z) (hD : ∀ᶠ w in 𝓝 z,Df L κ G w ≠ 0)
    (hz : ∀ j,2*|c|<‖z-q j‖) (hW : 1+Wf L κ c G q z ∈ slitPlane)
    (ha : aNf L κ c G q z ≠ 0) (hd : DNf L κ c G q z ≠ 0) :
    localCorrection L κ G z (sNf L c q z) (deriv (sNf L c q) z) =
      PeriodTwoTerm.corrf L κ c G q z := by
  have he := quadratic_derivative L κ c G q hG hD hz hW
  rw [localCorrection,localRoot_sN,← DN_eq,← he,
    PeriodTwoTerm.corrf,← aD L κ c G q hD.self_of_nhds]
  field_simp
end Correction


section Physical
open PhysicalTensor (L2T)
open BetheCoefficientTransform (HN)
variable (L : ℝ) {κ : ℝ} [Fact (0 < L)]

abbrev basis (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) :=
  UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ

def ev (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (z : ℂ) (i : BetheLabels.MArr N) : ℂ :=
  NormalityBridge.eigen (L := L) κ hκ hN i z

def dev (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (z : ℂ) (i : BetheLabels.MArr N) : ℂ :=
  deriv (NormalityBridge.eigen (L := L) κ hκ hN i) z

lemma ev_basis (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (z : ℂ) (i : BetheLabels.MArr N) :
    NormalizedTransfer.normalizedTransfer L κ N z (basis L hκ hN i)=ev L hκ hN z i • basis L hκ hN i :=
  UnconditionalBetheBasis.transfer_physicalBasis hκ hN z i

lemma dev_basis (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (z : ℂ) (i : BetheLabels.MArr N) :
    deriv (NormalizedTransfer.normalizedTransfer L κ N) z (basis L hκ hN i)=
      dev L hκ hN z i • basis L hκ hN i := by
  simpa only [iteratedDeriv_one,basis,dev] using NormalityBridge.deriv_basis hκ hN
    (UnconditionalBetheBasis.meanField_isBetheBasis hκ hN) 1 z i

/-- `f_z(S_N(z))` in the actual common complete Bethe resolution. -/
def Fop (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (f : Extension (ℂ × ℂ)) (z : ℂ) : HN L N →L[ℂ] HN L N :=
  lift (basis L hκ hN) (ev L hκ hN) f z

/-- `g_z(S_N(z),S_N'(z))` in that same resolution. -/
def Gop (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (g : Extension (ℂ × (ℂ × ℂ))) (z : ℂ) : HN L N →L[ℂ] HN L N :=
  liftJoint (basis L hκ hN) (ev L hκ hN) (dev L hκ hN) g z

lemma Fop_continuous (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (f : Extension (ℂ × ℂ)) :
    Continuous (Fop L hκ hN f) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact continuousAt_lift _ (NormalizedTransfer.normalizedTransfer L κ N) _ (ev_basis L hκ hN) f z
    (NormalityBridge.differentiable_normalizedTransfer (L := L) (κ := κ) (N := N)).continuous.continuousAt

lemma Gop_continuous (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (g : Extension (ℂ × (ℂ × ℂ))) :
    Continuous (Gop L hκ hN g) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hc := NormalityBridge.differentiable_normalizedTransfer (L := L) (κ := κ) (N := N)
  exact continuousAt_liftJoint _ (NormalizedTransfer.normalizedTransfer L κ N)
    (deriv (NormalizedTransfer.normalizedTransfer L κ N)) _ _ (ev_basis L hκ hN) (dev_basis L hκ hN) g z
    hc.continuous.continuousAt hc.contDiff.continuous_deriv_one.continuousAt

/-- Eq:B4-global-action-operators, leading term, as a norm integral. -/
def C0 (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (f : Extension (ℂ × ℂ)) (a b h : ℝ) : HN L N →L[ℂ] HN L N :=
  (-(2*Real.pi*κ)⁻¹ : ℂ) • realPart (rectOp (Fop L hκ hN f) a b h)

/-- Eq:B4-global-action-operators, correction term, as a norm integral. -/
def C1 (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (g : Extension (ℂ × (ℂ × ℂ))) (a b h : ℝ) : HN L N →L[ℂ] HN L N :=
  realPart ((I/(2*Real.pi):ℂ) • rectOp (Gop L hκ hN g) a b h)

/-- The source's particular `C_N = C0_N + N^-1 C1_N`. -/
def C (hκ : 0 < κ) {N : ℕ} (hN : 0 < N)
    (f : Extension (ℂ × ℂ)) (g : Extension (ℂ × (ℂ × ℂ))) (a b h : ℝ) : HN L N →L[ℂ] HN L N :=
  C0 L hκ hN f a b h+((N:ℂ)⁻¹) • C1 L hκ hN g a b h

def c0 (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (f : Extension (ℂ × ℂ))
    (a b h : ℝ) (i : BetheLabels.MArr N) : ℝ :=
  -(2*Real.pi*κ)⁻¹*(LabelExactPeriod.rectIntegral (fun z => f.value (z,ev L hκ hN z i)) a b h).re

def c1 (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (g : Extension (ℂ × (ℂ × ℂ)))
    (a b h : ℝ) (i : BetheLabels.MArr N) : ℝ :=
  ((I/(2*Real.pi):ℂ)*LabelExactPeriod.rectIntegral (fun z => g.value (z,(ev L hκ hN z i,dev L hκ hN z i))) a b h).re

lemma C0_basis (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (f : Extension (ℂ × ℂ))
    {a b h : ℝ} (hab : a ≤ b) (hh : 0 ≤ h) (i : BetheLabels.MArr N) :
    C0 L hκ hN f a b h (basis L hκ hN i)=((c0 L hκ hN f a b h i):ℂ) • basis L hκ hN i := by
  have he := rectOp_basis (basis L hκ hN) (Fop L hκ hN f) (fun z i => f.value (z,ev L hκ hN z i))
    hab hh (fun _ _ => (Fop_continuous L hκ hN f).continuousAt) (lift_basis _ _ f) 
  rw [C0,smul_apply,realPart_basis _ _ _ he,smul_smul]
  simp only [c0,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_inv,Complex.ofReal_ofNat]

lemma C1_basis (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (g : Extension (ℂ × (ℂ × ℂ)))
    {a b h : ℝ} (hab : a ≤ b) (hh : 0 ≤ h) (i : BetheLabels.MArr N) :
    C1 L hκ hN g a b h (basis L hκ hN i)=((c1 L hκ hN g a b h i):ℂ) • basis L hκ hN i := by
  have he := rectOp_basis (basis L hκ hN) (Gop L hκ hN g)
    (fun z i => g.value (z,(ev L hκ hN z i,dev L hκ hN z i)))
    hab hh (fun _ _ => (Gop_continuous L hκ hN g).continuousAt) (liftJoint_basis _ _ _ g)
  apply realPart_basis (basis L hκ hN) _ (fun i => (I/(2*Real.pi):ℂ)*
    LabelExactPeriod.rectIntegral (fun z => g.value (z,(ev L hκ hN z i,dev L hκ hN z i))) a b h) _ i
  intro j
  rw [smul_apply,he,smul_smul]

lemma C_basis (hκ : 0 < κ) {N : ℕ} (hN : 0 < N)
    (f : Extension (ℂ × ℂ)) (g : Extension (ℂ × (ℂ × ℂ)))
    {a b h : ℝ} (hab : a ≤ b) (hh : 0 ≤ h) (i : BetheLabels.MArr N) :
    C L hκ hN f g a b h (basis L hκ hN i)=
      ((c0 L hκ hN f a b h i+(N:ℝ)⁻¹*c1 L hκ hN g a b h i:ℝ):ℂ) • basis L hκ hN i := by
  rw [C,add_apply,smul_apply,C0_basis L hκ hN f hab hh,C1_basis L hκ hN g hab hh,smul_smul,← add_smul]
  push_cast
  rfl

lemma selfAdjoint_of_real_basis {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E) (r : ι → ℝ)
    (he : ∀ i,T (b i)=(r i:ℂ) • b i) : IsSelfAdjoint T := by
  change T.adjoint=T
  apply NormalityBridge.clm_ext_basis b
  intro i
  rw [BoundedBetheTransfer.adjoint_basis b T (fun i => (r i:ℂ)) he,he,Complex.conj_ofReal]

/-- Explicit uniform bound independent of the particle number. -/
def K (κ a b h : ℝ) (f : Extension (ℂ × ℂ)) (g : Extension (ℂ × (ℂ × ℂ))) : ℝ :=
  |(2*Real.pi*κ)⁻¹| *(2*(b-a)+4*h)*f.bound+
    (2*Real.pi)⁻¹*(2*(b-a)+4*h)*g.bound

lemma c0_bound (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (f : Extension (ℂ × ℂ))
    {a b h : ℝ} (hab : a ≤ b) (hh : 0 ≤ h) (i : BetheLabels.MArr N) :
    |c0 L hκ hN f a b h i| ≤ |(2*Real.pi*κ)⁻¹| *(2*(b-a)+4*h)*f.bound := by
  rw [c0,abs_mul,abs_neg]
  have hb := (Complex.abs_re_le_norm _).trans
    (PeriodTwoTerm.norm_rectIntegral_le hab hh (fun z _ => f.value_bound (z,ev L hκ hN z i)))
  calc _ ≤ |(2*Real.pi*κ)⁻¹| *((2*(b-a)+4*h)*f.bound) :=
        mul_le_mul_of_nonneg_left hb (abs_nonneg _)
       _ = _ := by ring

lemma c1_bound (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (g : Extension (ℂ × (ℂ × ℂ)))
    {a b h : ℝ} (hab : a ≤ b) (hh : 0 ≤ h) (i : BetheLabels.MArr N) :
    |c1 L hκ hN g a b h i| ≤ (2*Real.pi)⁻¹*(2*(b-a)+4*h)*g.bound := by
  unfold c1
  apply (Complex.abs_re_le_norm _).trans
  rw [norm_mul]
  have hn : ‖(I/(2*Real.pi):ℂ)‖=(2*Real.pi)⁻¹ := by
    simp only [norm_div,Complex.norm_I,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,one_div]
  rw [hn]
  have hb := PeriodTwoTerm.norm_rectIntegral_le hab hh
    (fun z _ => g.value_bound (z,(ev L hκ hN z i,dev L hκ hN z i)))
  exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (by ring)

/-- One named binding theorem: the literal norm-integral C0/C1/C, their
actual Bethe spectra, self-adjointness and a bound uniform in N. It does
not assert the still separate condensate reconstruction norm estimate. -/
theorem condensate_reconstruction_operator_binding (hκ : 0 < κ) {N : ℕ} (hN : 0 < N)
    (f : Extension (ℂ × ℂ)) (g : Extension (ℂ × (ℂ × ℂ)))
    {a b h : ℝ} (hab : a ≤ b) (hh : 0 ≤ h) :
    IsSelfAdjoint (C0 L hκ hN f a b h) ∧ IsSelfAdjoint (C1 L hκ hN g a b h) ∧
    IsSelfAdjoint (C L hκ hN f g a b h) ∧
    (∀ i,C L hκ hN f g a b h (basis L hκ hN i)=
      ((c0 L hκ hN f a b h i+(N:ℝ)⁻¹*c1 L hκ hN g a b h i:ℝ):ℂ) • basis L hκ hN i) ∧
    ‖C L hκ hN f g a b h‖ ≤ K κ a b h f g := by
  have hf0 := f.bound_nonneg
  have hg0 := g.bound_nonneg
  have h0 := C0_basis L hκ hN f hab hh
  have h1 := C1_basis L hκ hN g hab hh
  have he := C_basis L hκ hN f g hab hh
  refine ⟨selfAdjoint_of_real_basis _ _ _ h0,selfAdjoint_of_real_basis _ _ _ h1,
    selfAdjoint_of_real_basis _ _ _ he,he,?_⟩
  apply BoundedBetheTransfer.diagonal_norm_le (basis L hκ hN) _ _ he (by unfold K; positivity)
  intro i
  rw [Complex.norm_real,Real.norm_eq_abs]
  have hNi : (N:ℝ)⁻¹ ≤ 1 := (inv_le_one₀ (by exact_mod_cast hN)).mpr (by exact_mod_cast hN)
  have hNi0 : 0 ≤ (N:ℝ)⁻¹ := by positivity
  have hB1 : 0 ≤ (2*Real.pi)⁻¹*(2*(b-a)+4*h)*g.bound := by positivity
  calc |c0 L hκ hN f a b h i+(N:ℝ)⁻¹*c1 L hκ hN g a b h i|
      ≤ |c0 L hκ hN f a b h i|+(N:ℝ)⁻¹*|c1 L hκ hN g a b h i| := by
        simpa [abs_mul,abs_of_nonneg hNi0] using abs_add_le (c0 L hκ hN f a b h i) ((N:ℝ)⁻¹*c1 L hκ hN g a b h i)
    _ ≤ K κ a b h f g := by
      unfold K
      have hc1 := mul_le_mul_of_nonneg_left (c1_bound L hκ hN g hab hh i) hNi0
      have hc2 := mul_le_mul_of_nonneg_right hNi hB1
      linarith [c0_bound L hκ hN f hab hh i]
end Physical


section ScalarProbes
open IndexedScalarMeasure IndexedScalarMeasureCuts LabelJointLimit LabelJointWeak LabelBlock
open PeriodReconstructionCore PeriodReconstruction PeriodTwoTerm
open RootMeasureComplex (HighHalf)

/-- Conditions used in the exact correction proof, with the source transfer
inside the prescribed scalar cutoff tube. -/
def LocalGood (L κ : ℝ) (G : ℂ → ℂ) (r : ℝ) {N : ℕ}
    (B : OnShellBethe L κ N) (z : ℂ) : Prop :=
  ‖sNf L (κ/N) B.q z-sf L κ G z‖<r ∧
  DifferentiableAt ℂ G z ∧ (∀ᶠ w in 𝓝 z,Df L κ G w ≠ 0) ∧
  (∀ j,2*|κ/(N:ℝ)|<‖z-B.q j‖) ∧
  1+Wf L κ (κ/N) G B.q z ∈ slitPlane ∧
  aNf L κ (κ/N) G B.q z ≠ 0 ∧ DNf L κ (κ/N) G B.q z ≠ 0

/-- The finite probe set forces both cutoff activation and the actual
scalar two-term remainder. No B-C error or condensate estimate is a premise. -/
theorem cutoff_probes {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ)
    {n : ℤ} {a b h r : ℝ} (ha : a ∈ S.cuts) (hb : b ∈ S.cuts) (hab : a<b)
    (hh : 0<h) (hr : 0<r)
    (h1 : 2*Real.pi*(n-1)<exteriorForce L κ S.μ a)
    (h2 : exteriorForce L κ S.μ a<2*Real.pi*n)
    (h3 : 2*Real.pi*n<exteriorForce L κ S.μ b)
    (h4 : exteriorForce L κ S.μ b<2*Real.pi*(n+1)) :
    ∃ m : ℕ,∃ z : Fin m → ℂ,(∀ j,HighHalf L κ (z j)) ∧ ∃ ε>0,∃ N₀ : ℕ,∃ C≥0,
      ∀ (N : ℕ) (_hN : 0<N),N₀≤N → ∀ B : OnShellBethe L κ N,
        (∀ j,‖sNf L (κ/N) B.q (z j)-sf L κ (EmpiricalRapidity.cauchyTransform S.μ) (z j)‖<ε) →
        (∀ w ∈ Gam a b h,LocalGood L κ (EmpiricalRapidity.cauchyTransform S.μ) r B w) ∧
        ‖twoTermErr L κ (EmpiricalRapidity.cauchyTransform S.μ) B n a b h‖≤C*((N:ℝ)⁻¹)^2 := by
  let G := EmpiricalRapidity.cauchyTransform S.μ
  let P : ℕ → ∀ N : ℕ,OnShellBethe L κ N → Prop := fun t N B =>
    (∀ w ∈ Gam a b h,LocalGood L κ G r B w) ∧
    ‖twoTermErr L κ G B n a b h‖≤(t:ℝ)*((N:ℝ)⁻¹)^2
  have hmono : ∀ t t' N (B : OnShellBethe L κ N),t≤t' → P t N B → P t' N B := by
    intro t t' N B htt hp
    exact ⟨hp.1,hp.2.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast htt) (sq_nonneg _))⟩
  have hseq : ∀ (N : ℕ → ℕ) (hN : ∀ k,0<N k) (B : ∀ k,OnShellBethe L κ (N k)),
      Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 (⟨S.μ,S.isProb⟩:ProbabilityMeasure ℝ)) →
      Tendsto N atTop atTop → ∃ t,∀ᶠ k in atTop,P t (N k) (B k) := by
    intro N hN B hc hNt
    obtain ⟨d,hd,d0,hd0,M,η,hM,hη,hroot,hsupp,hU,hGd,hD,hbounds⟩ :=
      setup S (μ := ⟨S.μ,S.isProb⟩) rfl hc hNt ha hb hab hh h1 h2 h3 h4
    have hsdev := Prop009ProbeDev.unif_sdev S.hL S.hκ hc hNt (isCompact_Gam a b h)
      (d1 := min d d0) (by positivity) (fun z hz => Gam_abs_im hh hz)
      (fun z hz t ht => (min_le_right _ _).trans (hsupp z hz t ht))
      (hroot.mono fun k hk z hz j => (min_le_left _ _).trans (hk z hz j)) hr
    have hprops := Filter.eventually_prod_principal_iff.mp
      (eventual_props S.hκ hN hNt hd hroot hU hGd hD hM hη hbounds)
    obtain ⟨C,hC⟩ := two_term_period S (μ := ⟨S.μ,S.isProb⟩) rfl hc hNt ha hb hab hh h1 h2 h3 h4
    refine ⟨⌈C⌉₊,?_⟩
    filter_upwards [hsdev,hprops,hC] with k hsk hpk hCk
    refine ⟨fun z hz => ?_,hCk.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (sq_nonneg _))⟩
    obtain ⟨hR,hW,haN,hDN,_⟩ := hpk z hz
    have hslit : 1+Wf L κ (κ/N k) G (B k).q z ∈ slitPlane := by
      left
      have habs := Complex.abs_re_le_norm (Wf L κ (κ/N k) G (B k).q z)
      simp only [add_re,one_re]
      have hneg := neg_abs_le (Wf L κ (κ/N k) G (B k).q z).re
      change ‖Wf L κ (κ/N k) G (B k).q z‖≤1/2 at hW
      linarith
    refine ⟨hsk z hz,hGd z hz,hD z hz,hR,hslit,?_,?_⟩
    · intro he
      rw [he,norm_zero] at haN
      have hpos : 0<1/(2*M) := by positivity
      linarith
    · intro he
      rw [he,norm_zero] at hDN
      linarith
  obtain ⟨m,z,hz,ε,hε,N₀,t,ht⟩ := Prop009ProbeDev.probes_generic S P hmono hseq
  exact ⟨m,z,hz,ε,hε,N₀,(t:ℝ),Nat.cast_nonneg t,ht⟩

/-- Scalar reconstruction using declared cutoff extensions and the actual
transfer derivative. The only derivative bound is the source cutoff range. -/
theorem scalar_cutoff_error {L κ : ℝ} (G : ℂ → ℂ) {N : ℕ}
    (B : OnShellBethe L κ N) (n : ℤ) {a b h r V : ℝ}
    (hab : a≤b) (hh : 0≤h) (f : Extension (ℂ × ℂ)) (g : Extension (ℂ × (ℂ × ℂ)))
    (hf : ∀ z ∈ Gam a b h,∀ w,‖w-sf L κ G z‖<r → f.value (z,w)=localLog L κ G z w)
    (hg : ∀ z ∈ Gam a b h,∀ w v,‖w-sf L κ G z‖<r → ‖v‖≤V →
      g.value (z,(w,v))=localCorrection L κ G z w v)
    (hl : ∀ z ∈ Gam a b h,LocalGood L κ G r B z)
    (hv : ∀ z ∈ Gam a b h,‖deriv (sNf L (κ/N) B.q) z‖≤V) :
    |((Finset.univ.filter fun j => B.n j=n).card:ℝ)/N -
      (-(2*Real.pi*κ)⁻¹*(LabelExactPeriod.rectIntegral (fun z => f.value (z,sNf L (κ/N) B.q z)) a b h).re+
       (N:ℝ)⁻¹*((I/(2*Real.pi):ℂ)*LabelExactPeriod.rectIntegral
         (fun z => g.value (z,(sNf L (κ/N) B.q z,deriv (sNf L (κ/N) B.q) z))) a b h).re)| ≤
      ‖twoTermErr L κ G B n a b h‖ := by
  have hfe : ∀ z ∈ Gam a b h,f.value (z,sNf L (κ/N) B.q z)=logaNf L κ (κ/N) G B.q z := by
    intro z hz
    rw [hf z hz _ (hl z hz).1,localLog_sN]
  have hge : ∀ z ∈ Gam a b h,g.value (z,(sNf L (κ/N) B.q z,deriv (sNf L (κ/N) B.q) z))=
      corrf L κ (κ/N) G B.q z := by
    intro z hz
    obtain ⟨ht,hG,hD,hR,hW,ha,hDN⟩ := hl z hz
    rw [hg z hz _ _ ht (hv z hz)]
    exact correction_sN L κ (κ/N) G B.q hG hD hR hW ha hDN
  have hfi := LabelExactPeriod.rectIntegral_congr
    (f := fun z => f.value (z,sNf L (κ/N) B.q z)) (g := logaNf L κ (κ/N) G B.q)
    (fun _ hx => hfe _ (bot_mem hab hx)) (fun _ hx => hfe _ (top_mem hab hx))
    (fun _ hx => hfe _ (right_mem hh hx)) (fun _ hx => hfe _ (left_mem hh hx))
  have hgi := LabelExactPeriod.rectIntegral_congr
    (f := fun z => g.value (z,(sNf L (κ/N) B.q z,deriv (sNf L (κ/N) B.q) z))) (g := corrf L κ (κ/N) G B.q)
    (fun _ hx => hge _ (bot_mem hab hx)) (fun _ hx => hge _ (top_mem hab hx))
    (fun _ hx => hge _ (right_mem hh hx)) (fun _ hx => hge _ (left_mem hh hx))
  rw [hfi,hgi]
  have he : (twoTermErr L κ G B n a b h).re =
      ((Finset.univ.filter fun j => B.n j=n).card:ℝ)/N -
      (-(2*Real.pi*κ)⁻¹*(LabelExactPeriod.rectIntegral (logaNf L κ (κ/N) G B.q) a b h).re+
       (N:ℝ)⁻¹*((I/(2*Real.pi):ℂ)*LabelExactPeriod.rectIntegral (corrf L κ (κ/N) G B.q) a b h).re) := by
    unfold twoTermErr
    simp only [Complex.sub_re,Complex.add_re,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.div_re,Complex.div_im,
      Complex.neg_re,Complex.neg_im,Complex.one_re,Complex.one_im,Complex.I_re,Complex.I_im]
    simp
    field_simp
  rw [← he]
  exact Complex.abs_re_le_norm _
end ScalarProbes


section PhysicalRate
open PhysicalTensor (L2T)
open BetheCoefficientTransform (HN)
open LabelJointLimit LabelJointWeak LabelBlock
open PeriodReconstructionCore PeriodReconstruction PeriodTwoTerm
open BetheLabels BetheAdmission RootContraction BetheSmooth
variable (L : ℝ) [Fact (0<L)] {κ : ℝ}

/-- Canonical on-shell configuration with its exact occupation label, rather
than an existential configuration with unspecified labels. -/
theorem configuration_exists (hκ : 0<κ) {N : ℕ} (hN : 0<N) (m : MArr N) :
    ∃ B : OnShellBethe L κ N,B.q=arrRoots L (κ/N) m ∧
      B.n=correctedInt (labelsEquivArr.symm m) := by
  have hL : 0<L := Fact.out
  have hc : 0<κ/(N:ℝ) := div_pos hκ (by exact_mod_cast hN)
  let ℓ := labelsEquivArr.symm m
  have hs := roots_solves hL hc (correctedInt ℓ)
  have hq := roots_strictMono_labels hL hc ℓ
  have hb : BoseBethe L (κ/N) (correctedInt ℓ) (roots L (correctedInt ℓ) (κ/N)) := by
    apply (boseBethe_iff_log (L := L) hc hq (correctedInt ℓ)).2
    intro j
    have h1 := hs j
    have h2 : Tmap L (κ/N) (roots L (correctedInt ℓ) (κ/N)) j=
        logMap L (κ/N) (roots L (correctedInt ℓ) (κ/N)) j := by rw [logMap_erase]; rfl
    rw [h2,h1]
    unfold quantumNumbers
    ring
  exact ⟨⟨roots L (correctedInt ℓ) (κ/N),correctedInt ℓ,hq,correctedInt_monotone ℓ,hb⟩,rfl,rfl⟩

def configuration (hκ : 0<κ) {N : ℕ} (hN : 0<N) (m : MArr N) : OnShellBethe L κ N :=
  (configuration_exists L hκ hN m).choose

lemma configuration_q (hκ : 0<κ) {N : ℕ} (hN : 0<N) (m : MArr N) :
    (configuration L hκ hN m).q=arrRoots L (κ/N) m :=
  (configuration_exists L hκ hN m).choose_spec.1

lemma configuration_n (hκ : 0<κ) {N : ℕ} (hN : 0<N) (m : MArr N) :
    (configuration L hκ hN m).n=correctedInt (labelsEquivArr.symm m) :=
  (configuration_exists L hκ hN m).choose_spec.2

lemma configuration_count (hκ : 0<κ) {N : ℕ} (hN : 0<N) (m : MArr N) (n : ℤ) :
    (Finset.univ.filter fun j => (configuration L hκ hN m).n j=n).card=m.1 n := by
  rw [configuration_n,← labelsEquivArr_apply,Equiv.apply_symm_apply]

lemma ev_configuration (hκ : 0<κ) {N : ℕ} (hN : 0<N) (m : MArr N) (z : ℂ)
    (hz : ∀ j,z≠((configuration L hκ hN m).q j:ℂ)) :
    ev L hκ hN z m=sNf L (κ/N) (configuration L hκ hN m).q z := by
  have hL : 0<L := Fact.out
  have hc := NormalityBridge.cpos hκ hN
  have hroot : ∀ i,sourceRoots L (NormalityBridge.label m).1 (κ/N) i=
      arrRoots L (κ/N) m (Fin.rev i) := by
    intro i
    rw [RootMeasureTransfer.label_val]
    exact sourceRoots_eq_roots_rev hL hc _ i
  unfold ev NormalityBridge.eigen
  rw [BetheSpectralContinuity.spectralValue_nonpole L hc (NormalityBridge.label m).2 z (by
    intro i
    rw [hroot i,← configuration_q L hκ hN m]
    exact hz _)]
  unfold TransferSeparation.sFun sNf ANf
  simp only [hroot,configuration_q]
  have p1 := Equiv.prod_comp Fin.revPerm
    (fun j => 1+I*((κ/(N:ℝ):ℝ):ℂ)/(z-(arrRoots L (κ/N) m j:ℂ)))
  have p2 := Equiv.prod_comp Fin.revPerm
    (fun j => 1-I*((κ/(N:ℝ):ℝ):ℂ)/(z-(arrRoots L (κ/N) m j:ℂ)))
  simp only [Fin.revPerm_apply] at p1 p2
  rw [p1]
  simp only [Complex.ofReal_neg,mul_neg,neg_div,← sub_eq_add_neg]
  rw [p2]
  rfl

lemma dev_configuration (hκ : 0<κ) {N : ℕ} (hN : 0<N) (m : MArr N) (z : ℂ)
    (hz : ∀ j,z≠((configuration L hκ hN m).q j:ℂ)) :
    dev L hκ hN z m=deriv (sNf L (κ/N) (configuration L hκ hN m).q) z := by
  have hn : ∀ᶠ w in 𝓝 z,∀ j,w≠((configuration L hκ hN m).q j:ℂ) :=
    Filter.eventually_all.mpr (fun j => continuousAt_id.eventually_ne (hz j))
  have he : (fun w => ev L hκ hN w m) =ᶠ[𝓝 z] sNf L (κ/N) (configuration L hκ hN m).q :=
    hn.mono fun w hw => ev_configuration L hκ hN m w hw
  exact he.deriv_eq

lemma massFraction_bound {N : ℕ} (hN : 0<N) (m : MArr N) (n : ℤ) :
    ‖(((m.1 n:ℝ)/N:ℝ):ℂ)‖≤1 := by
  rw [Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  simpa [Occupation.coef_diag] using (Occupation.sum_diag_coef_le_one (m := m.1) m.2 hN {n})

/-- Actual normalized occupation, with exactly the source m_n/N spectrum. -/
def B (hκ : 0<κ) {N : ℕ} (hN : 0<N) (n : ℤ) : HN L N →L[ℂ] HN L N :=
  diagonal (basis L hκ hN) (fun m => (((m.1 n:ℝ)/N:ℝ):ℂ)) 1 zero_le_one
    (fun m => massFraction_bound hN m n)

lemma B_basis (hκ : 0<κ) {N : ℕ} (hN : 0<N) (n : ℤ) (m : MArr N) :
    B L hκ hN n (basis L hκ hN m)=(((m.1 n:ℝ)/N:ℝ):ℂ) • basis L hκ hN m :=
  diagonal_basis _ _ _ _ _ m
end PhysicalRate


section FinalRate
open IndexedScalarMeasure IndexedScalarMeasureCuts
open PhysicalTensor (L2T)
open BetheCoefficientTransform (HN)
open LabelJointLimit LabelJointWeak LabelBlock
open PeriodReconstructionCore PeriodReconstruction PeriodTwoTerm
variable (L : ℝ) [Fact (0<L)] {κ : ℝ}

/-- A uniform cutoff bound for the actual transfer derivative, obtained
from the whole-plane transfer norm bound and radius-one Cauchy estimate. -/
theorem derivative_cutoff_bound (hκ : 0<κ) {N : ℕ} (hN : 0<N) (m : BetheLabels.MArr N)
    {h : ℝ} (z : ℂ) (hz : |z.im|≤h) :
    ‖dev L hκ hN z m‖≤MixedQuadratures.Rbd L κ (h+1) := by
  have hn (w : ℂ) (hw : w ∈ Metric.sphere z 1) :
      ‖NormalityBridge.eigen (L := L) κ hκ hN m w‖≤MixedQuadratures.Rbd L κ (h+1) := by
    have hnorm : ‖w-z‖=1 := by simpa [Metric.mem_sphere,dist_eq_norm] using hw
    have him := Complex.abs_im_le_norm (w-z)
    have htri : |w.im|≤|(w-z).im|+|z.im| := by
      simpa using abs_add_le (w-z).im z.im
    have hb : |w.im|≤h+1 := by rw [hnorm] at him; linarith
    have he := ev_basis L hκ hN w m
    have hop := (NormalizedTransfer.normalizedTransfer L κ N w).le_opNorm (basis L hκ hN m)
    rw [he,norm_smul,(basis L hκ hN).orthonormal.1 m,mul_one,mul_one] at hop
    exact hop.trans (MixedQuadratures.norm_normalizedTransfer_le L κ N w (h+1) hb)
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (c := z) (R := 1) (f := NormalityBridge.eigen (L := L) κ hκ hN m) 1 one_pos
    (NormalityBridge.eigen_differentiable κ hκ hN m).diffContOnCl hn
  simpa [dev,iteratedDeriv_one] using hc

/-- Physical PROP-010 norm clause for declared scalar extensions with their
printed cutoff agreement. No diagonal/error estimate is a premise.
The existence/construction of the scalar extension pair is a separate obligation. -/
theorem condensate_reconstruction (hκ : 0<κ) (u : L2T L) (hu : ‖u‖=1) (n : ℤ)
    {h r : ℝ} (hh : 0<h) (hr : 0<r)
    (f : Extension (ℂ × ℂ)) (g : Extension (ℂ × (ℂ × ℂ)))
    (hf : ∀ z ∈ Gam (RootScalarPeriodR8.cut hκ u (n-1)) (RootScalarPeriodR8.cut hκ u n) h,
      ∀ w,‖w-sf L κ (EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)) z‖<r →
      f.value (z,w)=localLog L κ (EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)) z w)
    (hg : ∀ z ∈ Gam (RootScalarPeriodR8.cut hκ u (n-1)) (RootScalarPeriodR8.cut hκ u n) h,
      ∀ w v,‖w-sf L κ (EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)) z‖<r →
      ‖v‖≤MixedQuadratures.Rbd L κ (h+1) →
      g.value (z,(w,v))=localCorrection L κ (EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)) z w v) :
    ∃ D≥0,∃ N₀ : ℕ,∀ (N : ℕ) (hN : 0<N),N₀≤N →
      ‖(B L hκ hN n-C L hκ hN f g (RootScalarPeriodR8.cut hκ u (n-1))
        (RootScalarPeriodR8.cut hκ u n) h) (HighMomentsOps.wvec N u)‖≤D*((N:ℝ)⁻¹)^2 := by
  let S := Prop026Bound.scalarCuts hκ u hu
  let a := RootScalarPeriodR8.cut hκ u (n-1)
  let b := RootScalarPeriodR8.cut hκ u n
  let G := EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)
  have hne : u≠0 := by intro he; rw [he,norm_zero] at hu; norm_num at hu
  have hcut (k : ℤ) : RootScalarPeriodR8.cut hκ u k ∈ S.cuts :=
    (DEF014Phase.facts ((⟨κ,hκ⟩,u):DEF014Phase.Param L)).separator_in_band k
  have hforce (k : ℤ) : exteriorForce L κ S.μ (RootScalarPeriodR8.cut hκ u k)=
      2*((k:ℝ)+1/2)*Real.pi := by
    change exteriorForce L κ (Prop026Bound.M hκ u) _ = _
    rw [Prop026Bound.force_eq hκ hne (hcut k)]
    have hp := (PhysicalSourceFinal.sourceFacts hκ u).phase.separator_spec k
    change Prop026Bound.theta hκ u (RootScalarPeriodR8.cut hκ u k)=((k:ℝ)+1/2)*Real.pi at hp
    rw [hp]
    ring
  have hab : a<b := (DEF014Phase.facts ((⟨κ,hκ⟩,u):DEF014Phase.Param L)).phase.separator_strictMono (by omega)
  have h1 : 2*Real.pi*(n-1)<exteriorForce L κ S.μ a := by dsimp [a]; rw [hforce]; push_cast; nlinarith [Real.pi_pos]
  have h2 : exteriorForce L κ S.μ a<2*Real.pi*n := by dsimp [a]; rw [hforce]; push_cast; nlinarith [Real.pi_pos]
  have h3 : 2*Real.pi*n<exteriorForce L κ S.μ b := by dsimp [b]; rw [hforce]; nlinarith [Real.pi_pos]
  have h4 : exteriorForce L κ S.μ b<2*Real.pi*(n+1) := by dsimp [b]; rw [hforce]; nlinarith [Real.pi_pos]
  obtain ⟨m,z,hz,ε,hε,N₀,Cs,hCs,hprobes⟩ := cutoff_probes S (hcut (n-1)) (hcut n) hab hh hr h1 h2 h3 h4
  let K0 := 1+K κ a b h f g
  let D := Real.sqrt (Cs^2+K0^2*ε⁻¹^8*∑ _j : Fin m,max 0 (HighMomentsTransfer.Cunif L κ 0 4))
  refine ⟨D,Real.sqrt_nonneg _,N₀,?_⟩
  intro N hN hN0
  let R := B L hκ hN n-C L hκ hN f g a b h
  let re : BetheLabels.MArr N → ℂ := fun i =>
    (((i.1 n:ℝ)/N:ℝ):ℂ)-((c0 L hκ hN f a b h i+(N:ℝ)⁻¹*c1 L hκ hN g a b h i:ℝ):ℂ)
  have hR : ∀ i,R (basis L hκ hN i)=re i • basis L hκ hN i := by
    intro i
    dsimp [R,re]
    rw [sub_apply,B_basis,C_basis L hκ hN f g hab.le hh.le]
    exact (sub_smul _ _ _).symm
  have hbound : ∀ i,‖re i‖≤K0 := by
    intro i
    have hC := (condensate_reconstruction_operator_binding L hκ hN f g hab.le hh.le).2.2.2.2
    have hc := (C L hκ hN f g a b h).le_opNorm (basis L hκ hN i)
    rw [C_basis L hκ hN f g hab.le hh.le,norm_smul,(basis L hκ hN).orthonormal.1 i,mul_one,mul_one] at hc
    calc ‖re i‖ ≤ ‖(((i.1 n:ℝ)/N:ℝ):ℂ)‖+‖((c0 L hκ hN f a b h i+(N:ℝ)⁻¹*c1 L hκ hN g a b h i:ℝ):ℂ)‖ := by
            dsimp [re]; push_cast; exact norm_sub_le _ _
         _ ≤ K0 := add_le_add (massFraction_bound hN i n) (hc.trans hC)
  have hgood : ∀ i,(∀ j,‖ev L hκ hN (z j) i-NormalizedTransfer.productSymbol L κ u (z j)‖<ε) →
      ‖re i‖≤Cs*((N:ℝ)⁻¹)^2 := by
    intro i hi
    let Bc := configuration L hκ hN i
    have hprobe : ∀ j,‖sNf L (κ/N) Bc.q (z j)-sf L κ G (z j)‖<ε := by
      intro j
      have hroot : ∀ k,z j≠(Bc.q k:ℂ) := by
        intro k he
        have hhj := (hz j).1
        have him := congrArg Complex.im he
        simp only [Complex.ofReal_im] at him
        linarith
      rw [← ev_configuration L hκ hN i (z j) hroot]
      have hs := RootScalarPeriodR10.transfer_identity hκ u (z j) (Or.inl (ne_of_gt (show 0<(z j).im by have hj := (hz j).1; linarith)))
      have hs' : NormalizedTransfer.productSymbol L κ u (z j)=sf L κ G (z j) := by
        simpa [RootScalarPeriodR10.symbol,ScalarLogBranchR10.transfer,RootScalarPeriodR10.exponential,
          RootScalarPeriodR10.exponent,RootCauchyFullBracketR8.G,sf,Af,ef,G,mul_assoc,mul_left_comm,mul_comm] using hs
      rw [← hs']
      exact hi j
    obtain ⟨hl,herr⟩ := hprobes N hN hN0 Bc hprobe
    have hroot (w : ℂ) (hw : w ∈ Gam a b h) : ∀ k,w≠(Bc.q k:ℂ) := by
      intro k he
      have hn := (hl w hw).2.2.2.1 k
      rw [he,sub_self,norm_zero] at hn
      linarith [abs_nonneg (κ/(N:ℝ))]
    have hv : ∀ w ∈ Gam a b h,‖deriv (sNf L (κ/N) Bc.q) w‖≤MixedQuadratures.Rbd L κ (h+1) := by
      intro w hw
      rw [← dev_configuration L hκ hN i w (hroot w hw)]
      exact derivative_cutoff_bound L hκ hN i w (Gam_abs_im hh hw)
    have hs := scalar_cutoff_error G Bc n hab.le hh.le f g hf hg hl hv
    have heq : |((Finset.univ.filter fun j => Bc.n j=n).card:ℝ)/N -
        (-(2*Real.pi*κ)⁻¹*(LabelExactPeriod.rectIntegral (fun z => f.value (z,sNf L (κ/N) Bc.q z)) a b h).re+
         (N:ℝ)⁻¹*((I/(2*Real.pi):ℂ)*LabelExactPeriod.rectIntegral
           (fun z => g.value (z,(sNf L (κ/N) Bc.q z,deriv (sNf L (κ/N) Bc.q) z))) a b h).re)| = ‖re i‖ := by
      have hef := LabelExactPeriod.rectIntegral_congr
        (f := fun w => f.value (w,sNf L (κ/N) Bc.q w)) (g := fun w => f.value (w,ev L hκ hN w i))
        (fun w hw => by rw [ev_configuration L hκ hN i _ (hroot _ (bot_mem hab.le hw))])
        (fun w hw => by rw [ev_configuration L hκ hN i _ (hroot _ (top_mem hab.le hw))])
        (fun w hw => by rw [ev_configuration L hκ hN i _ (hroot _ (right_mem hh.le hw))])
        (fun w hw => by rw [ev_configuration L hκ hN i _ (hroot _ (left_mem hh.le hw))])
      have heg := LabelExactPeriod.rectIntegral_congr
        (f := fun w => g.value (w,(sNf L (κ/N) Bc.q w,deriv (sNf L (κ/N) Bc.q) w)))
        (g := fun w => g.value (w,(ev L hκ hN w i,dev L hκ hN w i)))
        (fun w hw => by rw [ev_configuration L hκ hN i _ (hroot _ (bot_mem hab.le hw)),dev_configuration L hκ hN i _ (hroot _ (bot_mem hab.le hw))])
        (fun w hw => by rw [ev_configuration L hκ hN i _ (hroot _ (top_mem hab.le hw)),dev_configuration L hκ hN i _ (hroot _ (top_mem hab.le hw))])
        (fun w hw => by rw [ev_configuration L hκ hN i _ (hroot _ (right_mem hh.le hw)),dev_configuration L hκ hN i _ (hroot _ (right_mem hh.le hw))])
        (fun w hw => by rw [ev_configuration L hκ hN i _ (hroot _ (left_mem hh.le hw)),dev_configuration L hκ hN i _ (hroot _ (left_mem hh.le hw))])
      rw [hef,heg,configuration_count]
      simp only [re,← Complex.ofReal_sub,c0,c1,Complex.norm_real,Real.norm_eq_abs]
    rw [heq] at hs
    exact hs.trans herr
  exact CondensateLocalizationR10.physical_error_rate hκ u hu hN z hz R re hR hε hbound hgood
end FinalRate


section SmoothExtensions
/-- Smooth compactly supported source functions furnish all numerical
bounds and norm-continuity data used by the concrete operator definition. -/
def Extension.ofSmooth {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (F : X → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) : Extension X := by
  let M := (hc.exists_bound_of_continuous hF.continuous).choose
  have hM := (hc.exists_bound_of_continuous hF.continuous).choose_spec
  let K := (ContDiff.lipschitzWith_of_hasCompactSupport hc hF (by norm_num)).choose
  have hK := (ContDiff.lipschitzWith_of_hasCompactSupport hc hF (by norm_num)).choose_spec
  exact ⟨F,max 0 M,le_max_left _ _,fun x => (hM x).trans (le_max_right _ _),K,hK⟩

lemma Extension.ofSmooth_value {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (F : X → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    (Extension.ofSmooth F hF hc).value=F := by
  rfl

open PhysicalTensor (L2T)
open PeriodReconstructionCore PeriodReconstruction
variable (L : ℝ) [Fact (0<L)] {κ : ℝ}

/-- PROP-010 condensate norm clause as one named theorem for the source's
explicitly declared smooth extensions. All extension, tube and derivative
cutoff hypotheses are printed; there is no assumed norm error estimate. -/
theorem condensate_reconstruction_smooth (hκ : 0<κ) (u : L2T L) (hu : ‖u‖=1) (n : ℤ)
    {h r : ℝ} (hh : 0<h) (hr : 0<r)
    (F : ℂ × ℂ → ℂ) (H : ℂ × (ℂ × ℂ) → ℂ)
    (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hH : ContDiff ℝ ∞ H) (hHc : HasCompactSupport H)
    (hf : ∀ z ∈ Gam (RootScalarPeriodR8.cut hκ u (n-1)) (RootScalarPeriodR8.cut hκ u n) h,
      ∀ w,‖w-sf L κ (EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)) z‖<r →
      F (z,w)=localLog L κ (EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)) z w)
    (hg : ∀ z ∈ Gam (RootScalarPeriodR8.cut hκ u (n-1)) (RootScalarPeriodR8.cut hκ u n) h,
      ∀ w v,‖w-sf L κ (EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)) z‖<r →
      ‖v‖≤MixedQuadratures.Rbd L κ (h+1) →
      H (z,(w,v))=localCorrection L κ (EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)) z w v) :
    let f := Extension.ofSmooth F hF hFc
    let g := Extension.ofSmooth H hH hHc
    ∃ D≥0,∃ N₀ : ℕ,∀ (N : ℕ) (hN : 0<N),N₀≤N →
      IsSelfAdjoint (C L hκ hN f g (RootScalarPeriodR8.cut hκ u (n-1)) (RootScalarPeriodR8.cut hκ u n) h) ∧
      ‖C L hκ hN f g (RootScalarPeriodR8.cut hκ u (n-1)) (RootScalarPeriodR8.cut hκ u n) h‖≤
        K κ (RootScalarPeriodR8.cut hκ u (n-1)) (RootScalarPeriodR8.cut hκ u n) h f g ∧
      ‖(B L hκ hN n-C L hκ hN f g (RootScalarPeriodR8.cut hκ u (n-1))
        (RootScalarPeriodR8.cut hκ u n) h) (HighMomentsOps.wvec N u)‖≤D*((N:ℝ)⁻¹)^2 := by
  dsimp only
  let f := Extension.ofSmooth F hF hFc
  let g := Extension.ofSmooth H hH hHc
  have hf' : ∀ z ∈ Gam (RootScalarPeriodR8.cut hκ u (n-1)) (RootScalarPeriodR8.cut hκ u n) h,
      ∀ w,‖w-sf L κ (EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)) z‖<r →
      f.value (z,w)=localLog L κ (EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)) z w := by
    simpa only [f,Extension.ofSmooth_value] using hf
  have hg' : ∀ z ∈ Gam (RootScalarPeriodR8.cut hκ u (n-1)) (RootScalarPeriodR8.cut hκ u n) h,
      ∀ w v,‖w-sf L κ (EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)) z‖<r →
      ‖v‖≤MixedQuadratures.Rbd L κ (h+1) →
      g.value (z,(w,v))=localCorrection L κ (EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)) z w v := by
    simpa only [g,Extension.ofSmooth_value] using hg
  obtain ⟨D,hD,N₀,hest⟩ := condensate_reconstruction L hκ u hu n hh hr f g hf' hg'
  refine ⟨D,hD,N₀,fun N hN hN0 => ?_⟩
  have hab : RootScalarPeriodR8.cut hκ u (n-1)≤RootScalarPeriodR8.cut hκ u n :=
    ((DEF014Phase.facts ((⟨κ,hκ⟩,u):DEF014Phase.Param L)).phase.separator_strictMono (by omega)).le
  have hop := condensate_reconstruction_operator_binding L hκ hN f g hab hh.le
  exact ⟨hop.2.2.1,hop.2.2.2.2,hest N hN hN0⟩
end SmoothExtensions


section OccupationIdentity
open BetheOccupationGauge BetheCoefficientTransform
variable (L : ℝ) [Fact (0<L)] {κ : ℝ}
/-- The source occupation in the estimate is the inherited actual physical
occupation operator, not a new operator with a postulated spectrum. -/
theorem B_eq_physical (hκ : 0<κ) {N : ℕ} (hN : 0<N) (n : ℤ) :
    B L hκ hN n=CartesianOccupationTransfer.physical (basis L hκ hN) identityGauge n n := by
  apply NormalityBridge.clm_ext_basis (basis L hκ hN)
  intro i
  have hg : gaugedBasis (basis L hκ hN) identityGauge i=basis L hκ hN i := by
    rw [gaugedBasis_apply]
    simp [identityGauge]
  have he := CartesianOccupationTransfer.physical_diag (basis L hκ hN) identityGauge n i
  rw [hg] at he
  rw [B_basis]
  exact he.symm
end OccupationIdentity

end QuantumNLS.Prop010ContourBindingR11


#print axioms QuantumNLS.Prop010ContourBindingR11.condensate_reconstruction
#print axioms QuantumNLS.Prop010ContourBindingR11.condensate_reconstruction_smooth
#print axioms QuantumNLS.Prop010ContourBindingR11.condensate_reconstruction_operator_binding
#print axioms QuantumNLS.Prop010ContourBindingR11.correction_sN
#check @QuantumNLS.Prop010ContourBindingR11.condensate_reconstruction
#check @QuantumNLS.Prop010ContourBindingR11.condensate_reconstruction_smooth
#check @QuantumNLS.Prop010ContourBindingR11.condensate_reconstruction_operator_binding
#check @QuantumNLS.Prop010ContourBindingR11.Extension.ofSmooth

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop010ContourBindingR11." ||
        n.toString.startsWith "_private.QuantumNLS.Prop010ContourBindingR11." then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"Prop010ContourBindingR11 audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
