import QuantumNLS.DynamicGaugeEdgesR34m
import QuantumNLS.ReconstructionInputsR33m
import QuantumNLS.UniformStaticR31m
import QuantumNLS.RetargetStageR48b

/-! Compare the printed gauge operators and literal physical operators in
the original Bethe coefficient space. Diagonal charge evolution preserves
the moduli of all these coefficients. -/

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option linter.unusedSectionVars false
noncomputable section

open Filter Topology
open scoped ComplexConjugate InnerProductSpace Classical

namespace QuantumNLS.DynamicGaugePhysicalR34m

open Occupation OccupationHilbert FullOccupationAffinity FiniteCellGauge
open FiniteCellSupport (phase_conj_mul)
open BetheCoefficientTransform BetheOccupationGauge BetheLabels
open Def033HierarchyR24m PhysicalTensor
open RetargetEdgeR48b (J J_basis inCoefficients inCoefficients_apply inCoefficients_adjoint
  residual_inCoefficients single_classical)

variable {L κ : ℝ} [Fact (0 < L)] {N : ℕ}

abbrev basisAt (hκ : 0 < κ) (N : ℕ) (hN : 0 < N) :=
  UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ

abbrev productAt (u : Smooth L) (N : ℕ) : HN L N :=
  HighMomentsOps.wvec N (physical u)

abbrev UAt (hκ : 0 < κ) (R : Finset ℕ) (t : ℕ → ℝ) (N : ℕ) (hN : 0 < N) :=
  HierarchyFlow.quantumFlow (basisAt (L := L) hκ N hN) κ R t

abbrev EAt (hκ : 0 < κ) (g : Gauge) (N : ℕ) (hN : 0 < N) (a b : ℤ) :=
  CartesianOccupationTransfer.physical (basisAt (L := L) hκ N hN) g a b

abbrev WAt (hκ : 0 < κ) (g : Gauge) (N : ℕ) (hN : 0 < N) (a b : ℤ) :=
  UnitPhaseTransfer.physical (basisAt (L := L) hκ N hN) g a b

abbrev basis (hκ : 0 < κ) (n : ℕ) : BetheBasis L (n+1) := basisAt hκ (n+1) (Nat.succ_pos n)
abbrev product (u : Smooth L) (n : ℕ) := productAt u (n+1)
abbrev U (hκ : 0 < κ) (R : Finset ℕ) (t : ℕ → ℝ) (n : ℕ) :=
  UAt (L := L) hκ R t (n+1) (Nat.succ_pos n)
abbrev E (hκ : 0 < κ) (g : Gauge) (n : ℕ) (a b : ℤ) :=
  EAt (L := L) hκ g (n+1) (Nat.succ_pos n) a b
abbrev W (hκ : 0 < κ) (g : Gauge) (n : ℕ) (a b : ℤ) :=
  WAt (L := L) hκ g (n+1) (Nat.succ_pos n) a b

theorem U_inactive (hκ : 0 < κ) (R : Finset ℕ) (t s : ℕ → ℝ)
    (h : ∀ r ∈ R, t r = s r) (n : ℕ) :
    U (L := L) hκ R t n = U hκ R s n := by
  unfold U UAt HierarchyFlow.quantumFlow HierarchyFlow.jointSymbol
  congr 1
  funext m
  exact Finset.sum_congr rfl (fun r hr => by rw [h r hr])

/-- The rephasing of a basis vector is the conjugate of the source array
phase, so the resulting edge coefficient is q(source) times conj(q(target)). -/
def physicalGauge (q : UniformStaticR31m.FullGauge) : Gauge
  | 0, _ => phaseOne
  | n+1, m => ⟨conj (q n (marrArr (n+1) m)).1, by rw [Complex.norm_conj, (q n _).2]⟩

private theorem transfer_inCoefficients_single (B : BetheBasis L N) (g : Gauge)
    (q : Arr N → Phase) (h : ∀ d, conj (g N ((marrArr N).symm d)).1 = (q d).1)
    (T : HN L N →L[ℂ] HN L N) (a b : ℤ) (c : Arr N → ℂ)
    (hT : ∀ i : MArr N, T (gaugedBasis B g i) =
      if hd : DonorOK a (marrArr N i).1 then
        c (marrArr N i) • gaugedBasis B g
          ((marrArr N).symm (shiftArr a b (marrArr N i) hd))
      else 0)
    (m : Arr N) :
    inCoefficients B T (lp.single 2 m 1) =
      if hd : DonorOK a m.1 then lp.single 2 (shiftArr a b m hd)
        ((q m).1 * conj (q (shiftArr a b m hd)).1 * c m) else 0 := by
  obtain ⟨i, rfl⟩ := (marrArr N).surjective m
  have hq (i : MArr N) : conj (g N i).1 = (q (marrArr N i)).1 := by
    simpa only [Equiv.symm_apply_apply] using h (marrArr N i)
  have hn (i : MArr N) : (g N i).1 = conj (q (marrArr N i)).1 := by
    rw [← hq i, starRingEnd_self_apply]
  have hbg : B i = (q (marrArr N i)).1 • gaugedBasis B g i := by
    have hg : conj (g N i).1 * (g N i).1 = 1 := phase_conj_mul (g N i)
    rw [gaugedBasis_apply, ← hq i, smul_smul, hg, one_smul]
  rw [← J_basis B i, inCoefficients_apply, LinearIsometryEquiv.symm_apply_apply]
  rw [hbg, map_smul, hT i]
  split_ifs with hd
  · let d := shiftArr a b (marrArr N i) hd
    let k := (marrArr N).symm d
    change J B ((q (marrArr N i)).1 • c (marrArr N i) • gaugedBasis B g k) =
      lp.single 2 d ((q (marrArr N i)).1 * conj (q d).1 * c (marrArr N i))
    have hk : marrArr N k = d := (marrArr N).apply_symm_apply d
    rw [gaugedBasis_apply, hn k, hk]
    simp only [map_smul, J_basis, hk, smul_smul]
    rw [← lp.single_smul]
    congr 1
    simp only [smul_eq_mul, mul_one]
    ring
  · simp

private theorem cartesian_inCoefficients (B : BetheBasis L N) (g : Gauge) (q : Arr N → Phase)
    (h : ∀ d, conj (g N ((marrArr N).symm d)).1 = (q d).1) (a b : ℤ) :
    inCoefficients B (CartesianOccupationTransfer.physical B g a b) =
      RetargetWeightsR48b.cartesian q a b := by
  apply ExactShiftResidual.ext_single
  intro m
  have hT (i : MArr N) : CartesianOccupationTransfer.physical B g a b (gaugedBasis B g i) =
      if hd : DonorOK a (marrArr N i).1 then
        (coef N a b (marrArr N i).1 : ℂ) •
          gaugedBasis B g ((marrArr N).symm (shiftArr a b (marrArr N i) hd))
      else 0 := by
    have hs := CartesianOccupationTransfer.physical_basis B g a b i
    by_cases hd : DonorOK a (marrArr N i).1
    · simpa only [dite_eq_left hd] using hs
    · simpa only [dite_eq_right hd] using hs
  have hl := transfer_inCoefficients_single B g q h (CartesianOccupationTransfer.physical B g a b)
    a b (fun d => (coef N a b d.1 : ℂ)) hT m
  have hn (d : Arr N) : Complex.normSq (q d).1 = 1 := by
    rw [Complex.normSq_eq_norm_sq, (q d).2]
    norm_num
  have hr := sectorEq_single N (fun d => (q d).1) hn a b m 1
  by_cases hd : DonorOK a m.1
  · simp only [dite_eq_left hd, mul_one, single_classical] at hl hr ⊢
    exact hl.trans hr.symm
  · simp only [dite_eq_right hd, single_classical] at hl hr ⊢
    exact hl.trans hr.symm

private theorem phase_inCoefficients (B : BetheBasis L N) (g : Gauge) (q : Arr N → Phase)
    (h : ∀ d, conj (g N ((marrArr N).symm d)).1 = (q d).1) (a b : ℤ) :
    inCoefficients B (UnitPhaseTransfer.physical B g a b) = FiniteCellGauge.W q a b := by
  apply ExactShiftResidual.ext_single
  intro m
  have hT (i : MArr N) : UnitPhaseTransfer.physical B g a b (gaugedBasis B g i) =
      if hd : DonorOK a (marrArr N i).1 then
        (1 : ℂ) • gaugedBasis B g ((marrArr N).symm (shiftArr a b (marrArr N i) hd))
      else 0 := by
    rw [UnitPhaseTransfer.physical_basis]
    split_ifs <;> simp
  have hl := transfer_inCoefficients_single B g q h (UnitPhaseTransfer.physical B g a b)
    a b (fun _ => (1 : ℂ)) hT m
  have hr := W_basis q a b m
  by_cases hd : DonorOK a m.1
  · simp only [dite_eq_left hd, mul_one, single_classical] at hl hr ⊢
    letI : DecidableEq (Arr N) := Classical.decEq _
    rw [← lp.single_smul] at hr
    simp only [smul_eq_mul, mul_one, FiniteCellGauge.ratio] at hr
    exact hl.trans hr.symm
  · simp only [dite_eq_right hd, single_classical] at hl hr ⊢
    exact hl.trans hr.symm

private theorem physicalGauge_value (q : UniformStaticR31m.FullGauge) (n : ℕ) (d : Arr (n+1)) :
    conj (physicalGauge q (n+1) ((marrArr (n+1)).symm d)).1 = (q n d).1 := by
  change conj (conj (q n (marrArr (n+1) ((marrArr (n+1)).symm d))).1) = _
  rw [Equiv.apply_symm_apply, starRingEnd_self_apply]

theorem E_coordinates (hκ : 0 < κ) (n : ℕ) (q : UniformStaticR31m.FullGauge) (a b : ℤ) :
    inCoefficients (basis (L := L) hκ n) (E hκ (physicalGauge q) n a b) =
      RetargetWeightsR48b.cartesian (q n) a b :=
  cartesian_inCoefficients (basis hκ n) (physicalGauge q) (q n) (physicalGauge_value q n) a b

theorem W_coordinates (hκ : 0 < κ) (n : ℕ) (q : UniformStaticR31m.FullGauge) (a b : ℤ) :
    inCoefficients (basis (L := L) hκ n) (W hκ (physicalGauge q) n a b) =
      FiniteCellGauge.W (q n) a b :=
  phase_inCoefficients (basis hκ n) (physicalGauge q) (q n) (physicalGauge_value q n) a b

theorem W_eq_static (hκ : 0 < κ) (n : ℕ) (q : UniformStaticR31m.FullGauge) (a b : ℤ) :
    W (L := L) hκ (physicalGauge q) n a b =
      UniformStaticR31m.W hκ q n (a, b) := by
  let J₀ := J (basis (L := L) hκ n)
  apply J₀.conjStarAlgEquiv.injective
  change inCoefficients (basis (L := L) hκ n) _ = _
  rw [W_coordinates]
  exact (J₀.conjStarAlgEquiv.apply_symm_apply (FiniteCellGauge.W (q n) a b)).symm

theorem quantum_moduli (hκ : 0 < κ) (R : Finset ℕ) (t : ℕ → ℝ) (n : ℕ)
    (v : HN L (n+1)) (m : Arr (n+1)) :
    ‖J (basis hκ n) (U hκ R t n v) m‖ = ‖J (basis hκ n) v m‖ := by
  obtain ⟨i, rfl⟩ := (marrArr (n+1)).surjective m
  rw [occupationCoefficient_apply, occupationCoefficient_apply, HierarchyFlow.quantumFlow_coord,
    norm_mul, Complex.norm_exp]
  simp

theorem count_residual_eq_of_moduli (a : ℤ) (A : ℂ) (x y : H N) (h : ∀ m, ‖x m‖ = ‖y m‖) :
    ‖OccupationHilbert.E N a a x - A • x‖ = ‖OccupationHilbert.E N a a y - A • y‖ := by
  apply le_antisymm
  · apply lp.norm_mono (by norm_num)
    intro m
    simp only [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      OccupationHilbert.E_diag_apply, ← sub_mul, norm_mul, h]
    exact le_rfl
  · apply lp.norm_mono (by norm_num)
    intro m
    simp only [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      OccupationHilbert.E_diag_apply, ← sub_mul, norm_mul, h]
    exact le_rfl

theorem smooth_profile_ball (u : Smooth L) (hu : ‖physical u‖ = 1) :
    ∃ S : ℝ, 0 < S ∧ physical u ∈ UniformStaticR31m.unitBall (L := L) S ∧
      physical u ∈ R52CFCompact.profileClass L S := by
  let v : Sobolev.H02 L 1 := Sobolev.WField.mk (physical u)
    (RB7.memHs_of_smooth u.property 1)
  refine ⟨‖v‖ + 1, by positivity, ⟨hu, ⟨v, rfl, by linarith⟩⟩,
    ⟨⟨u.val, u.property, rfl⟩, hu, ?_⟩⟩
  have hv : ‖v‖ ^ 2 = Fourier.hsNormSq L 1 (fun n => Fourier.fourierL2 L (physical u) n) := by
    exact Sobolev.H02.norm_sq_eq v
  rw [← hv]
  nlinarith [norm_nonneg v]

end QuantumNLS.DynamicGaugePhysicalR34m
