import NlsGge.GK38.AngleActualPsiPeriodsQuadraticMass
import NlsGge.GK38.AbelianFreeSolutionFiber

/-! HELD SOURCE ONLY. Final exposed GK Theorem 14.1 clauses, REUSING existing K4 assembly.
The SAME already constructed normalized analytic inverse branch F is used for its product,
periods, real gap placement and locally uniform quadratic root mass.
No new compiler/query, production claim or quotient analyticity is asserted. -/
set_option autoImplicit false
open Set Metric SummationFilter
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p6PsiNumerator_literal_product38 (n : ℤ)
    (F : PotPair → P2Space38 n) (φ : PotPair) (z : ℂ) :
    p6PsiNumerator38 n F φ z = (-2 / (Lib.piN n : ℂ)) *
      ∏'[symmetricIcc ℤ] k : ℤ,
        (if k=n then 1 else Lib.prodFactor (Lib.sigmaOf (p2Extend38 n (F φ))) z k) := by
  unfold p6PsiNumerator38 p2Numerator38 p2FullNumerator38 Lib.omitProd
  simp only [div_eq_mul_inv,one_mul]
  ring

theorem p6PsiNumerator_exact_roots38 (n : ℤ)
    (F : PotPair → P2Space38 n) (φ : PotPair) (z : ℂ) :
    p6PsiNumerator38 n F φ z=0 ↔
      ∃ m : P2Index38 n, countingCenter38 m.1+F φ m=z := by
  have hscalar : (-2 : ℂ) ≠ 0 := by norm_num
  change (-2 : ℂ)*Lib.omitProd n (p2Extend38 n (F φ)) z=0 ↔ _
  rw [mul_eq_zero]
  simp only [hscalar,false_or]
  rw [Lib.omitProd_eq_zero_iff]
  constructor
  · rintro ⟨m,hm,hz⟩
    refine ⟨⟨m,hm⟩,?_⟩
    have hext : p2Extend38 n (F φ) m=F φ (⟨m,hm⟩ : P2Index38 n) :=
      p2Extend_at38 n (F φ) (⟨m,hm⟩ : P2Index38 n)
    simpa only [Lib.sigmaOf,countingCenter38,hext] using hz
  · rintro ⟨m,hm⟩
    refine ⟨m.1,m.2,?_⟩
    simpa only [Lib.sigmaOf,countingCenter38,p2Extend_at38] using hm

theorem p6Actual_psi_theorem141_same_family38 :
    ∃ W : Set PotPair, IsOpen W ∧ range realSlice ⊆ W ∧ W ⊆ gkW ∧
      ∃ F : (n : ℤ) → PotPair → P2Space38 n,
        (∀ n : ℤ, AnalyticOnNhd ℂ (F n) W) ∧
        (∀ n : ℤ, AnalyticOnNhd ℂ
          (fun p : PotPair × ℂ => p6PsiNumerator38 n (F n) p.1 p.2)
          (W ×ˢ (univ : Set ℂ))) ∧
        (∀ (n : ℤ) (m : P2Index38 n), AnalyticOnNhd ℂ
          (fun φ : PotPair => countingCenter38 m.1+F n φ m) W) ∧
        (∀ (n : ℤ) (φ : PotPair), φ ∈ W →
          p2Fn38 n (φ,F n φ)=0 ∧
          (fderiv ℂ (fun y : P2Space38 n => p2Fn38 n (φ,y)) (F n φ)).IsInvertible ∧
          AnalyticOnNhd ℂ (p6PsiNumerator38 n (F n) φ) univ ∧
          (∀ m : ℤ, CircleIntegrable
            (fun z => p6PsiNumerator38 n (F n) φ z/canonRoot38 φ z)
            (discC φ m) (discR φ m)) ∧
          (∀ m : ℤ, abelianPeriod38 m φ (p6PsiNumerator38 n (F n) φ)=
            if m=n then 2*(Real.pi : ℂ) else 0) ∧
          (∀ z : ℂ, p6PsiNumerator38 n (F n) φ z=0 ↔
            ∃ m : P2Index38 n, countingCenter38 m.1+F n φ m=z) ∧
          (∀ z : ℂ, p6PsiNumerator38 n (F n) φ z = (-2 / (Lib.piN n : ℂ)) *
            ∏'[symmetricIcc ℤ] k : ℤ,
              (if k=n then 1 else
                Lib.prodFactor (Lib.sigmaOf (p2Extend38 n (F n φ))) z k))) ∧
        (∀ (n : ℤ) (u : PhysicalL2), ∃ t : P3RealSpace38 n,
          t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t=0 ∧
          F n (realSlice u)=p3RealInclude38 n t ∧
          ∀ m : P2Index38 n, countingCenter38 m.1+F n (realSlice u) m ∈
            segment ℝ (lamMinus (realSlice u) m.1) (lamPlus (realSlice u) m.1)) ∧
        (∀ n : ℤ, F n (realSlice (0 : PhysicalL2))=0) ∧
        (∀ φ : PotPair, φ ∈ W → ∃ V : Set PotPair, ∃ B : ℝ,
          IsOpen V ∧ φ ∈ V ∧ V ⊆ W ∧ 0 < B ∧
          ∀ (n : ℤ) (ψ : PotPair), ψ ∈ V → ∃ A : P2Space38 n,
            (∀ m : P2Index38 n,
              A m=(countingCenter38 m.1+F n ψ m-tauN ψ m.1)/gamma2 ψ m.1) ∧
            Summable (fun m : P2Index38 n => ‖A m‖^2) ∧
            (∑' m : P2Index38 n,‖A m‖^2) ≤ B ∧
            ∀ m : P2Index38 n,
              countingCenter38 m.1+F n ψ m=tauN ψ m.1+gamma2 ψ m.1*A m) := by
  obtain ⟨W,hW,hreal,hWW,F,hFa,hFspec,hjoint,hperiod,hFreal,hMass,_hcollapsed⟩ :=
    angleActual_same_psi_periods_quadratic_mass_collapsed_nodes38
  refine ⟨W,hW,hreal,hWW,F,hFa,hjoint,?_,?_,?_,?_,?_⟩
  · intro n m φ hφ
    have heval : AnalyticAt ℂ (fun ψ : PotPair => F n ψ m) φ :=
      AnalyticAt.comp
        (g := lp.evalCLM ℂ (fun _ : P2Index38 n => ℂ) 2 m) (f := F n)
        ((lp.evalCLM ℂ (fun _ : P2Index38 n => ℂ) 2 m).analyticAt (F n φ))
        (hFa n φ hφ)
    exact analyticAt_const.add heval
  · intro n φ hφ
    obtain ⟨hz,hi⟩ := hFspec n φ hφ
    refine ⟨hz,hi,p6PsiNumerator_entire38 n (F n) φ,
      fun m => (hperiod n φ hφ m).1,
      fun m => (hperiod n φ hφ m).2,
      fun z => p6PsiNumerator_exact_roots38 n (F n) φ z,
      fun z => p6PsiNumerator_literal_product38 n (F n) φ z⟩
  · intro n u
    obtain ⟨t,ht,hzero,hbase⟩ := hFreal n u
    refine ⟨t,ht,hzero,hbase,?_⟩
    intro m
    rw [hbase,p3RealInclude_apply38]
    exact ht m
  · intro n
    obtain ⟨t,ht,_hz,hbase⟩ := hFreal n (0 : PhysicalL2)
    have ht0 := p5RealGapCube_free_unique38 n t ht
    rw [hbase,ht0,map_zero]
  · intro φ hφ
    obtain ⟨r,B,hr,hB,hsub,hbound⟩ := hMass φ hφ
    refine ⟨ball φ r,B,isOpen_ball,mem_ball_self hr,hsub,hB,?_⟩
    intro n ψ hψ
    exact hbound ψ hψ n

theorem p6Psi_family_free_root_of_free_value38
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hfree : ∀ n : ℤ, F n (realSlice (0 : PhysicalL2))=0)
    (n : ℤ) (m : P2Index38 n) :
    countingCenter38 m.1+F n (realSlice (0 : PhysicalL2)) m=
      (m.1 : ℂ)*(Real.pi : ℂ) := by
  rw [hfree n]
  change countingCenter38 m.1+(0 : ℂ)=(m.1 : ℂ)*(Real.pi : ℂ)
  simp only [add_zero,countingCenter38]

end
end NlsGge.GK38
