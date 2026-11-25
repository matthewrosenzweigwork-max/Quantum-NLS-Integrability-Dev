import Mathlib
import NlsGge.Atomic.F.F012
import NlsGge.Atomic.F.F012Sup1
import NlsGge.Atomic.F.F012Core
import NlsGge.ThirdConsultation.F.F013Core
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing

                                                                                                                   
                                                                                                                    
                                                                                                                        
                                                                          
                                                                                                           
                                                                                                                      
                                                                        
                                                                                                               
                                                                                            
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Measure

namespace NlsGge.ThirdConsultation.F

/-- The coefficients of `finiteT` are the actual `T` of the coefficients. -/
theorem finiteT_coe_actualT (m : ℕ) (hm : 2 ≤ m) (x : Hm1 m) (n : ℤ) :
    NlsGge.ThirdConsultation.F013X.co _ (finiteT m x) n =
      NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38.T
        (NlsGge.ThirdConsultation.F013X.co _ x) n := by
  have h1 := NlsGge.ThirdConsultation.F012Aux.finiteT_coe m hm x n
  change sobolevCoe _ (finiteT m x) n = _
  rw [h1]
  set u : PhysicalL2 := sobolevToL2_38 (m - 1) (FinvH38 m x) with hu
  have hfs : fourierSeq38 u = NlsGge.ThirdConsultation.F013X.co _ x := by
    funext k
    rw [fourierSeq38_apply, hu, sobolevToL2_38_fourier]
    change -(sobolevCoe _ (FinvH38 m x) (-k)) = sobolevCoe _ x k
    rw [NlsGge.ThirdConsultation.F012Aux.coe_FinvH, neg_neg, neg_neg]
  have hPhi := NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38_Phi u n
  calc NlsGge.GKDefinitionDesign.physicalBirkhoff u n
      = NlsGge.ThirdConsultation.Common.actualPhi u n := rfl
    _ = NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38.Φ u n := hPhi.symm
    _ = NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38.T (fourierSeq38 u) n := rfl
    _ = NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38.T
          (NlsGge.ThirdConsultation.F013X.co _ x) n := by rw [hfs]; rfl

theorem f013 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ)
    (hβ : ∀ j ≤ m, 0 < β j) :
    ∃ K : Hm1 m → SobolevHilbert (m : ℝ),
      Continuous K ∧
      (∀ x : Hm1 m, lowerSobolev m (K x) = finiteT m x - x) ∧
      ∀ x : Hm1 m,
        Tendsto (fun N => K (truncSobolev38 _ N x)) atTop (nhds (K x)) ∧
        (∀ N : ℕ,
          Summable (fun n : ℤ => finiteHierarchyRate38 m β n *
            ‖sobolevCoe _ (lowerSobolev m (K (truncSobolev38 _ N x)) -
              truncSobolev38 _ N (lowerSobolev m (K (truncSobolev38 _ N x)))) n‖ ^ 2) ∧
          finiteA m β (truncSobolev38 _ N (finiteT m (truncSobolev38 _ N x))) -
            finiteA m β (truncSobolev38 _ N x) =
          finiteD m β (truncSobolev38 _ N x) -
            finiteA m β (lowerSobolev m (K (truncSobolev38 _ N x)) -
              truncSobolev38 _ N (lowerSobolev m (K (truncSobolev38 _ N x))))) ∧
        Tendsto (fun N => finiteA m β
          (lowerSobolev m (K (truncSobolev38 _ N x)) -
            truncSobolev38 _ N (lowerSobolev m (K (truncSobolev38 _ N x)))))
          atTop (nhds 0) ∧
        Tendsto (fun N =>
          finiteA m β (truncSobolev38 _ N (finiteT m (truncSobolev38 _ N x))) -
            finiteA m β (truncSobolev38 _ N x)) atTop (nhds (finiteD m β x)) := by
  have h12 := f012 m hm β hβ
  exact NlsGge.ThirdConsultation.F013X.core m hm β hβ
    NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38
    NlsGge.ThirdConsultation.PDE.actualOneSmoothingInput38
    (lowerSobolev m) (fun y n => NlsGge.ThirdConsultation.F012Aux.coe_lower m y n)
    (finiteT m) (finiteT_coe_actualT m hm)
    (finiteD m β) h12.1 (fun h => ⟨(h12.2 h).1, (h12.2 h).2.2⟩)

end NlsGge.ThirdConsultation.F
