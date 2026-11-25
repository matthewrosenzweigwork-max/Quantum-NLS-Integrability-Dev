import NlsGge.GK38.GradEigenPeriodicGradient
import NlsGge.GK38.GradEigenPeriodicConst
import NlsGge.GK38.RealTypeSpectrumProbe
import NlsGge.GK38.GradEigenRealState
import NlsGge.GK38.EigenvalueCompactnessStrong
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem real_root_label_analyticAt (f : PhysicalL2 × ℝ → ℝ) (r : PhysicalL2 → ℝ)
    (u : PhysicalL2) (hA : AnalyticAt ℝ f (u,r u)) (hr : ContinuousAt r u)
    (hroot : ∀ v : PhysicalL2, f (v,r v)=0)
    (hpartial : (fderiv ℝ f (u,r u)) (0,1) ≠ 0) : AnalyticAt ℝ r u := by
  let F : PhysicalL2 × ℝ → PhysicalL2 × ℝ := fun p => (p.1,f p)
  have hF : AnalyticAt ℝ F (u,r u) := (analyticAt_fst (𝕜 := ℝ)).prod hA
  have hd : fderiv ℝ F (u,r u) =
      (ContinuousLinearMap.fst ℝ PhysicalL2 ℝ).prod (fderiv ℝ f (u,r u)) :=
    (hasFDerivAt_fst.prodMk hA.differentiableAt.hasFDerivAt).fderiv
  have hinv : (fderiv ℝ F (u,r u)).IsInvertible := by
    rw [hd]
    exact dirichlet_triangular_invertible38 _ hpartial
  obtain ⟨e,he,hEF,han⟩ := Lib.exists_analytic_chart hF hinv
  have hvalue : F (u,r u)=(u,0) := by
    apply Prod.ext
    · rfl
    · exact hroot u
  rw [hvalue] at han
  have hinverse : AnalyticAt ℝ (fun v : PhysicalL2 => e.symm (v,(0 : ℝ))) u := by
    have hcomp := AnalyticAt.comp (g := fun p : PhysicalL2 × ℝ => e.symm p)
      (f := fun v : PhysicalL2 => (v,(0 : ℝ))) han
      ((analyticAt_id (𝕜 := ℝ)).prod (analyticAt_const (v := (0 : ℝ))))
    simpa only [Function.comp_def] using hcomp
  have hbranch : AnalyticAt ℝ (fun v : PhysicalL2 => (e.symm (v,0)).2) u := by
    have hcomp := AnalyticAt.comp (g := fun p : PhysicalL2 × ℝ => p.2)
      (f := fun v : PhysicalL2 => e.symm (v,(0 : ℝ))) (analyticAt_snd (𝕜 := ℝ)) hinverse
    simpa only [Function.comp_def] using hcomp
  apply hbranch.congr
  have hgraph : ContinuousAt (fun v : PhysicalL2 => (v,r v)) u :=
    continuous_id.continuousAt.prodMk hr
  have hsource : ∀ᶠ v in 𝓝 u, (v,r v) ∈ e.source :=
    hgraph.preimage_mem_nhds (e.open_source.mem_nhds he)
  filter_upwards [hsource] with v hv
  have hev : e (v,r v)=(v,0) := by
    rw [hEF]
    apply Prod.ext
    · rfl
    · exact hroot v
  have hi := e.left_inv hv
  rw [hev] at hi
  exact congrArg Prod.snd hi

theorem periodic_eigenvector_exists (M : PairMat38) (c : ℂ)
    (hc : c^2=1) (hd : M 0 0*M 1 1-M 0 1*M 1 0=1)
    (hs : M 0 0+M 1 1=2*c) :
    ∃ a : PairVec38, a ≠ 0 ∧ Matrix.mulVec M a=c • a := by
  have hdet : (M-c • (1 : PairMat38)).det=0 := by
    simp [Matrix.det_fin_two,Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply]
    linear_combination hd-c*hs-hc
  obtain ⟨a,ha,he⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨a,ha,?_⟩
  rw [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec] at he
  exact sub_eq_zero.mp he

theorem real_symmetric_eigenvector_exists (M : PairMat38) (c : ℂ)
    (hM : ∀ i j : Fin 2, star (M i j)=M i.rev j.rev) (hc : star c=c)
    (hex : ∃ a : PairVec38, a ≠ 0 ∧ Matrix.mulVec M a=c • a) :
    ∃ a : PairVec38, a ≠ 0 ∧ a 1=star (a 0) ∧ Matrix.mulVec M a=c • a := by
  obtain ⟨a,ha,he⟩ := hex
  let b : PairVec38 := ![star (a 1),star (a 0)]
  have hb : Matrix.mulVec M b=c • b := by
    have h0 := congrArg star (congrFun he 0)
    have h1 := congrArg star (congrFun he 1)
    simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two,Pi.smul_apply,smul_eq_mul,
      star_add,star_mul,hM,hc] at h0 h1
    ext i
    fin_cases i
    · simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two,b,Matrix.cons_val_zero,
        Matrix.cons_val_one,Pi.smul_apply,smul_eq_mul]
      change M 0 0*star (a 1)+M 0 1*star (a 0)=c*star (a 1)
      change star (a 0)*M 1 1+star (a 1)*M 1 0=star (a 0)*c at h0
      change star (a 0)*M 0 1+star (a 1)*M 0 0=star (a 1)*c at h1
      linear_combination h1
    · simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two,b,Matrix.cons_val_zero,
        Matrix.cons_val_one,Pi.smul_apply,smul_eq_mul]
      change M 1 0*star (a 1)+M 1 1*star (a 0)=c*star (a 0)
      change star (a 0)*M 1 1+star (a 1)*M 1 0=star (a 0)*c at h0
      linear_combination h0
  by_cases hsum : a+b=0
  · have hrel : a 1= -star (a 0) := by
      have hv := congrFun hsum 1
      change a 1+star (a 0)=0 at hv
      exact eq_neg_of_add_eq_zero_left hv
    refine ⟨Complex.I • a,smul_ne_zero Complex.I_ne_zero ha,?_,?_⟩
    · change Complex.I*a 1=star (Complex.I*a 0)
      rw [hrel,star_mul]
      have hI : star Complex.I= -Complex.I := by simp
      rw [hI]
      ring
    · rw [Matrix.mulVec_smul,he,smul_smul,smul_smul,mul_comm]
  · refine ⟨a+b,hsum,?_,?_⟩
    · change a 1+star (a 0)=star (a 0+star (a 1))
      simp only [star_add,star_star]
      ring
    · rw [Matrix.mulVec_add,he,hb,smul_add]

end
end NlsGge.GK38.GradEigen38
