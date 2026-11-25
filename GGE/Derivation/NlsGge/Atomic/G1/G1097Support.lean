import Mathlib
import NlsGge.Atomic.G1.G1096
import NlsGge.Atomic.G1.G1068
import NlsGge.Atomic.G1.G1057

/- G1-097 SUPPORT01 (proof development, AUTHOR; not reviewed). Supporting lemmas for the canonical mixed-bracket theorem
   G1_097 (Pro head, root/gpt6pro_followup7 STATEMENTS/G1.md section G1-097). Namespace NlsGge.GKDefinitionDesign.
   Contents: wedge/solution algebra; endpoint values of Dirichlet and terminal solutions; the four-solution integral
   (from production G1_068 by absolutely continuous FTC); pointwise kernel rewritings for mixedKernel false/true;
   injectivity of the Dirichlet labels for a fixed real potential (simple roots, production dir_simple). No hypothesis
   beyond production facts. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonMixed38
open scoped BigOperators Matrix

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G1097_wedge_mulVec (M : PairMat38) (x y : PairVec38) :
    wedge (M *ᵥ x) (M *ᵥ y) = M.det * wedge x y := by
  unfold wedge
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

theorem G1097_wedge_solution_const (φ : PotPair) (z : ℂ) (x y : PairVec38) (s : ℝ) :
    wedge (solution φ z x s) (solution φ z y s) = wedge x y := by
  have hdet : (Set.IccExtend zero_le_one (fundPair φ z) s).det = 1 :=
    NlsGge.GK38.det_fundPair38 φ z (Set.projIcc (0:ℝ) 1 zero_le_one s)
  unfold solution
  rw [G1097_wedge_mulVec, hdet, one_mul]

theorem G1097_dir_end1 (φ : PotPair) (z : ℂ) (hd : dirichletChar φ z = 0) :
    solution φ z ![1, 1] 1 = ![normingFactor φ z, normingFactor φ z] := by
  rw [G1096_solution_one, G1096_dir_one φ z hd]

theorem G1097_term_end1 (φ : PotPair) (z : ℂ) :
    solution φ z (terminalSeed φ z) 1 = ![1, -1] := by
  rw [G1096_solution_one, G1096_term_one φ z]

theorem G1097_wedge_dd_one (φ : PotPair) (μ ν : ℂ) (hμ : dirichletChar φ μ = 0)
    (hν : dirichletChar φ ν = 0) :
    wedge (solution φ μ ![1, 1] 1) (solution φ ν ![1, 1] 1) = 0 := by
  rw [G1097_dir_end1 φ μ hμ, G1097_dir_end1 φ ν hν]
  simp [wedge]

theorem G1097_wedge_dd_zero (φ : PotPair) (μ ν : ℂ) :
    wedge (solution φ μ ![1, 1] 0) (solution φ ν ![1, 1] 0) = 0 := by
  simp only [G1096_solution_zero]
  simp [wedge]

/-- Dirichlet seed at `μ` against terminal seed at `ν`, upper endpoint. -/
theorem G1097_E1 (φ : PotPair) (μ ν : ℂ) (hμ : dirichletChar φ μ = 0) :
    wedge (solution φ μ ![1, 1] 1) (solution φ ν (terminalSeed φ ν) 1) =
      -2 * normingFactor φ μ := by
  rw [G1097_dir_end1 φ μ hμ, G1097_term_end1 φ ν]
  simp only [wedge, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

/-- Terminal seed at `μ` against Dirichlet seed at `ν`, upper endpoint. -/
theorem G1097_E2 (φ : PotPair) (μ ν : ℂ) (hν : dirichletChar φ ν = 0) :
    wedge (solution φ μ (terminalSeed φ μ) 1) (solution φ ν ![1, 1] 1) =
      2 * normingFactor φ ν := by
  rw [G1097_dir_end1 φ ν hν, G1097_term_end1 φ μ]
  simp only [wedge, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

/-- Dirichlet seed at `μ` against terminal seed at `ν`, lower endpoint. -/
theorem G1097_E3 (φ : PotPair) (μ ν : ℂ) :
    wedge (solution φ μ ![1, 1] 0) (solution φ ν (terminalSeed φ ν) 0) =
      -2 * normingFactor φ ν := by
  simp only [G1096_solution_zero]
  simp only [wedge, terminalSeed, normingFactor, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  ring

/-- Terminal seed at `μ` against Dirichlet seed at `ν`, lower endpoint. -/
theorem G1097_E4 (φ : PotPair) (μ ν : ℂ) :
    wedge (solution φ μ (terminalSeed φ μ) 0) (solution φ ν ![1, 1] 0) =
      2 * normingFactor φ μ := by
  simp only [G1096_solution_zero]
  simp only [wedge, terminalSeed, normingFactor, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  ring

/-- Integrand of the four-solution integral. -/
def G1097_W (φ ψ : PotPair) (μ ν : ℂ) (a b c d : PairVec38) (s : ℝ) : ℂ :=
  wedge (starProd38 (solution φ μ a s) (solution ψ μ c s))
    (starProd38 (solution φ ν b s) (solution ψ ν d s))

/-- Four-solution integral (production G1_068 plus absolutely continuous FTC on [0,1]). -/
theorem G1097_four (φ ψ : PotPair) (μ ν : ℂ) (hμν : μ ≠ ν) (a b c d : PairVec38) :
    IntervalIntegrable (G1097_W φ ψ μ ν a b c d) volume 0 1 ∧
    (∫ s in (0 : ℝ)..1, G1097_W φ ψ μ ν a b c d s) =
      (wedge (solution φ μ a 1) (solution φ ν b 1) * wedge (solution ψ μ c 1) (solution ψ ν d 1) -
        wedge (solution φ μ a 0) (solution φ ν b 0) * wedge (solution ψ μ c 0) (solution ψ ν d 0)) /
        (2 * Complex.I * (μ - ν)) := by
  have hc : (2 * Complex.I * (μ - ν)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) (sub_ne_zero.2 hμν)
  have hG := G1_068 φ ψ μ ν hμν a b c d
  have hR : ∀ s : ℝ, fourSolutionWronskianRhs φ ψ μ ν a b c d s =
      (2 * Complex.I * (μ - ν)) * G1097_W φ ψ μ ν a b c d s := fun s => rfl
  have hWfun : G1097_W φ ψ μ ν a b c d = fun s : ℝ =>
      (2 * Complex.I * (μ - ν))⁻¹ * fourSolutionWronskianRhs φ ψ μ ν a b c d s := by
    funext s
    rw [hR s, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  have hint : IntervalIntegrable (G1097_W φ ψ μ ν a b c d) volume 0 1 := by
    rw [hWfun]
    exact hG.1.const_mul _
  refine ⟨hint, ?_⟩
  have hac : AbsolutelyContinuousOnInterval (fun s : ℝ =>
      wedge (solution φ μ a s) (solution φ ν b s) *
        wedge (solution ψ μ c s) (solution ψ ν d s)) 0 1 :=
    (ac_pairBracket38 (G1096_isPairSolution φ μ a).1 (G1096_isPairSolution φ ν b).1).smul
      (ac_pairBracket38 (G1096_isPairSolution ψ μ c).1 (G1096_isPairSolution ψ ν d).1)
  have hd : ∀ᵐ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
      HasDerivAt (fun s : ℝ => wedge (solution φ μ a s) (solution φ ν b s) *
        wedge (solution ψ μ c s) (solution ψ ν d s))
        (fourSolutionWronskianRhs φ ψ μ ν a b c d x) x := by
    have h1 := (ae_restrict_iff' measurableSet_Ioo).1 hG.2
    have hcount : ({0, 1} : Set ℝ).Countable := (Set.toFinite ({0, 1} : Set ℝ)).countable
    have hae : ∀ᵐ s : ℝ, s ∉ ({0, 1} : Set ℝ) :=
      measure_eq_zero_iff_ae_notMem.1 (Set.Countable.measure_zero hcount volume)
    filter_upwards [h1, hae] with x hx hx0 hIcc
    have hIoo : x ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hIcc.1 (fun h => hx0 (by rw [← h]; simp)),
        lt_of_le_of_ne hIcc.2 (fun h => hx0 (by rw [h]; simp))⟩
    exact hx hIoo
  have key := ac_integral_eq_sub38 hac hG.1 hd t1
  have key' : (∫ s in (0 : ℝ)..1, fourSolutionWronskianRhs φ ψ μ ν a b c d s) =
      wedge (solution φ μ a 1) (solution φ ν b 1) * wedge (solution ψ μ c 1) (solution ψ ν d 1) -
        wedge (solution φ μ a 0) (solution φ ν b 0) * wedge (solution ψ μ c 0) (solution ψ ν d 0) :=
    key
  have hI : (∫ s in (0 : ℝ)..1, G1097_W φ ψ μ ν a b c d s) =
      (2 * Complex.I * (μ - ν))⁻¹ * ∫ s in (0 : ℝ)..1, fourSolutionWronskianRhs φ ψ μ ν a b c d s := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    show G1097_W φ ψ μ ν a b c d s =
      (2 * Complex.I * (μ - ν))⁻¹ * fourSolutionWronskianRhs φ ψ μ ν a b c d s
    rw [hR s, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [hI, key', div_eq_inv_mul]

/-- Kernel wedge is the wedge of the values. -/
theorem G1097_kw_eq (g h : PairKernelCont38) (s : ℝ) :
    kernelWedge38 g h s = wedge (pairKernelExt38 g s) (pairKernelExt38 h s) := rfl

theorem G1097_kw_self (g : PairKernelCont38) :
    (∫ t in (0 : ℝ)..1, kernelWedge38 g g t) = 0 := by
  have h0 : ∀ t : ℝ, kernelWedge38 g g t = 0 := fun t => by
    unfold kernelWedge38
    ring
  simp only [h0, intervalIntegral.integral_zero]

theorem G1097_dirPt (u : PhysicalL2) (m : ℤ) (s : ℝ) :
    pairKernelExt38 (dirState u m) s = solution (realSlice u) (gkMu u m : ℂ) ![1, 1] s :=
  (G1096_solution_eq_state (realSlice u) (gkMu u m : ℂ) ![1, 1] s).symm

theorem G1097_dirPtV (u v : PhysicalL2) (m : ℤ) (h : gkMu v m = gkMu u m) (s : ℝ) :
    pairKernelExt38 (dirState v m) s = solution (realSlice v) (gkMu u m : ℂ) ![1, 1] s := by
  have e : dirState v m = state (realSlice v) (gkMu u m : ℂ) ![1, 1] := by
    unfold dirState
    rw [h]
  rw [e]
  exact (G1096_solution_eq_state (realSlice v) (gkMu u m : ℂ) ![1, 1] s).symm

theorem G1097_termPtV (u v : PhysicalL2) (m : ℤ) (h : gkMu v m = gkMu u m) (s : ℝ) :
    pairKernelExt38 (terminalState v m) s =
      solution (realSlice v) (gkMu u m : ℂ) (terminalSeed (realSlice v) (gkMu u m : ℂ)) s := by
  have e : terminalState v m = state (realSlice v) (gkMu u m : ℂ)
      (terminalSeed (realSlice v) (gkMu u m : ℂ)) := by
    unfold terminalState
    rw [h]
  rw [e]
  exact (G1096_solution_eq_state _ _ _ s).symm

theorem G1097_termPt (u : PhysicalL2) (m : ℤ) (s : ℝ) :
    pairKernelExt38 (terminalState u m) s =
      solution (realSlice u) (gkMu u m : ℂ) (terminalSeed (realSlice u) (gkMu u m : ℂ)) s :=
  (G1096_solution_eq_state _ _ _ s).symm

theorem G1097_plus_pt (u v : PhysicalL2) (m : ℤ) (h : gkMu v m = gkMu u m) (s : ℝ) :
    pairKernelExt38 (mixedKernel u v m false) s =
      starProd38 (solution (realSlice u) (gkMu u m : ℂ) ![1, 1] s)
        (solution (realSlice v) (gkMu u m : ℂ) ![1, 1] s) := by
  show starProd38 (pairKernelExt38 (dirState u m) s) (pairKernelExt38 (dirState v m) s) = _
  rw [G1097_dirPt u m s, G1097_dirPtV u v m h s]

theorem G1097_minus_pt (u v : PhysicalL2) (m : ℤ) (h : gkMu v m = gkMu u m) (s : ℝ) :
    pairKernelExt38 (mixedKernel u v m true) s =
      Complex.I • (starProd38 (solution (realSlice u) (gkMu u m : ℂ) ![1, 1] s)
          (solution (realSlice v) (gkMu u m : ℂ) (terminalSeed (realSlice v) (gkMu u m : ℂ)) s) +
        starProd38 (solution (realSlice v) (gkMu u m : ℂ) ![1, 1] s)
          (solution (realSlice u) (gkMu u m : ℂ) (terminalSeed (realSlice u) (gkMu u m : ℂ)) s)) := by
  show Complex.I • (starProd38 (pairKernelExt38 (dirState u m) s)
      (pairKernelExt38 (terminalState v m) s) +
    starProd38 (pairKernelExt38 (dirState v m) s) (pairKernelExt38 (terminalState u m) s)) = _
  rw [G1097_dirPt u m s, G1097_termPtV u v m h s, G1097_dirPtV u v m h s, G1097_termPt u m s]

theorem G1097_wedge_I_sum (x y x' y' : PairVec38) :
    wedge (Complex.I • (x + y)) (Complex.I • (x' + y')) =
      -(wedge x x' + wedge x y' + wedge y x' + wedge y y') := by
  unfold wedge
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  linear_combination ((x 0 + y 0) * (x' 1 + y' 1) - (x 1 + y 1) * (x' 0 + y' 0)) * Complex.I_mul_I

theorem G1097_wedge_I_right (p x y : PairVec38) :
    wedge p (Complex.I • (x + y)) = Complex.I * (wedge p x + wedge p y) := by
  unfold wedge
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

theorem G1097_starProd_comm (g h : PairVec38) : starProd38 g h = starProd38 h g := by
  funext i
  fin_cases i
  · simp [starProd38, mul_comm]
  · simp [starProd38, mul_comm]

theorem G1097_alg1 (a c T : PairVec38) :
    wedge (starProd38 a c) (starProd38 a T) = -(a 0 * a 1) * wedge c T := by
  simp only [wedge, starProd38, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

theorem G1097_alg2 (a c T : PairVec38) :
    wedge (starProd38 a c) (starProd38 c T) = -(c 0 * c 1) * wedge a T := by
  simp only [wedge, starProd38, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

/-- Dirichlet labels of one real potential are distinct: simple roots (production dir_simple). -/
theorem G1097_gkMu_ne (u : PhysicalL2) (m n : ℤ) (hmn : m ≠ n) :
    (gkMu u m : ℂ) ≠ (gkMu u n : ℂ) := by
  intro heq
  have hm := muSeq_eq_gkMu38 u m
  have hn := muSeq_eq_gkMu38 u n
  have heq' : muSeq (realSlice u) m = muSeq (realSlice u) n := by
    rw [hm, hn, heq]
  have hroot : dirichletChar (realSlice u) (muSeq (realSlice u) m) = 0 := muSeq_root38 (realSlice u) m
  have hord := NlsGge.Atomic.G1057S3.dir_simple u (muSeq (realSlice u) m) hroot
  have hcard : Set.encard {k : ℤ | muSeq (realSlice u) k = muSeq (realSlice u) m} = 1 := by
    rw [((muSeq_enumeration38 (realSlice u)).2.2 (muSeq (realSlice u) m)).2]
    exact hord
  obtain ⟨x, hx⟩ := Set.encard_eq_one.1 hcard
  have hm' : m ∈ {k : ℤ | muSeq (realSlice u) k = muSeq (realSlice u) m} := rfl
  have hn' : n ∈ {k : ℤ | muSeq (realSlice u) k = muSeq (realSlice u) m} := heq'.symm
  rw [hx] at hm' hn'
  exact hmn (Set.mem_singleton_iff.1 hm' |>.trans (Set.mem_singleton_iff.1 hn').symm)

end
end NlsGge.GKDefinitionDesign
