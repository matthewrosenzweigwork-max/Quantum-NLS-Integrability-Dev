import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W11Equivalence38f
import NlsGge.Birkhoff.W11Equivalence38c
import NlsGge.Birkhoff.W10Localized38i
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport
import NlsGge.ThirdConsultation.R.R109Host
import NlsGge.ThirdConsultation.R.R110Host
import NlsGge.ThirdConsultation.R.R142Host

                                                                                                  
                                                                                                                    
                                                                                                                         
                                                                                                                        
                                                                                                                         
                                                                                                                    
                                                                                                                    
                                                                                                                      
                                                                                                                  
                                                                                                                   
                                                                                                                     
                                                                                                                       
                                                                                                                     
                                                                                                                      
                                                                                                                     
                                                                                                                     
                                                                                    
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
open NlsGge.HierarchyRiccati.Core
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem actual_W11 {lo up : ℝ} (c : BoundedCoefficients lo up) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    let hs1 : s ≤ 1 := by linarith
    List.TFAE [
      Tendsto (fun N : ℕ => relativePartition38 c N) atTop (𝓝 ((B).ZW38 c.val)),
      L1Converges (fullWeightedSequenceGaussian c s)
        (fun N : ℕ => fN38 c s N) (actualRamerDensity c s hs hs1),
      UniformIntegrable (fun N : ℕ => fN38 c s N) 1 (fullWeightedSequenceGaussian c s),
      W11Weak38 B c s,
      W11Tight38 c] := by
  intro hs1
  have hδ : RamerDivergence38 c s
      (PDE.actualBirkhoffInput38.KW06_38 PDE.actualOneSmoothingInput38 c
        (le_one_of_lt_three_quarters_W06_38 hs')) (canonicalDelta c s hs hs1) :=
    canonicalDelta_spec c s hs hs1
  have h := ((B).W11_38 O c hs hs').2 _ hδ
  have hW := (B).weight_W11 O c hs hs' _ hδ
  have hb : L1Converges (fullWeightedSequenceGaussian c s)
      (fun N : ℕ => fN38 c s N) (actualRamerDensity c s hs hs1) ↔
      Tendsto (fun N : ℕ => ∫ x, |fN38 c s N x -
          fW06_38 c s hs ((B).KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs'))
            (canonicalDelta c s hs hs1) x| ∂(fullWeightedSequenceGaussian c s)) atTop (𝓝 0) :=
    (tendsto_l1_iff_eLpNorm_W11 (μ := fullWeightedSequenceGaussian c s)
      (fn := fun N x => fN38 c s N x)
      (f := fW06_38 c s hs ((B).KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs'))
        (canonicalDelta c s hs hs1))
      (fun N => BirkhoffInput38.integrable_fN38 c hs N) hW.integrable).symm
  tfae_have 1 ↔ 2 := (h.out 1 2).trans hb.symm
  tfae_have 2 ↔ 3 := hb.trans (h.out 2 3)
  tfae_have 3 ↔ 4 := h.out 3 4
  tfae_have 4 ↔ 5 := h.out 4 5
  tfae_finish

end NlsGge.ThirdConsultation.R
