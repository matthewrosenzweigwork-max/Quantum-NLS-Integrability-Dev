import Mathlib
import NlsGge.Composition.Weight

                                                                                                                                                                                 
                                                                                  
                                                                                                  
                                                                                                         
                                                                                                          
                                                                                                        
                                                                                     
                                                                                                              

set_option autoImplicit false

namespace NlsGge.Atomic.R082

theorem srcWeight_ratio (a b : ℝ) (k l : ℤ) (ha : 0 ≤ a) (hkl : |l| ≤ |k|) :
    NlsGge.Composition.srcWeight a b (k + l) ≤
      NlsGge.Composition.srcWeight a b k * NlsGge.Composition.srcWeight a b l *
        NlsGge.Composition.ratioMajorant a b l :=
  (NlsGge.Composition.srcWeight_ratio ha b k l hkl).trans_eq (by ring)


end NlsGge.Atomic.R082
