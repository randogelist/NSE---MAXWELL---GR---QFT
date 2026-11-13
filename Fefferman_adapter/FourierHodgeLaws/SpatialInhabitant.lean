import FourierHodgeLaws.SpatialMultiplier
import FourierHodgeLaws.PoissonFromCoefficients
import FourierHodgeLaws.ElectricHodge

/-! Native discharge of the spatial inverse-Laplacian record and H1, H2, H4. -/

set_option autoImplicit false

namespace NSEMaxwell.HodgeProof

open NSEMaxwell.Classical NSEMaxwell.Bridge

noncomputable section

theorem spatialInverseLaplacianLaws : SpatialInverseLaplacianLaws where
  vector_smooth := vectorL_smooth
  curl_commute := curl_vectorL_commute
  divergence_commute := divergence_vectorL_commute
  poisson := neg_laplacian_vectorL

theorem h1_reconstruct_velocity (a : Field) (ha : Data a) :
    U (spatialMean a) (spatialCurl a) = a :=
  spatialInverseLaplacianLaws.reconstruct_velocity a ha

theorem h2_reconstruct_curl (m : Vec) (B : Field) (hB : MagneticData B) :
    spatialCurl (U m B) = B :=
  spatialInverseLaplacianLaws.reconstruct_curl m B hB

theorem h4_electric_hodge (ν : ℝ) (m : Vec) (B : Field) (hB : MagneticData B) :
    G ν m B + NSEMaxwell.Classical.gradient (headPotential ν m B) =
      K (spatialCurl (G ν m B)) :=
  spatialInverseLaplacianLaws.electric_hodge ν m B hB

end

end NSEMaxwell.HodgeProof
