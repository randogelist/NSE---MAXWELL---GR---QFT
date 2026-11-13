import NSEMaxwell.AnalyticReduction

/-!
The spatial algebraic assembly for the frozen Fourier operators.

`SpatialInverseLaplacianLaws` records four explicit analytic premises. The
lemmas below prove their exact consequences; this module supplies no inhabitant
of that record and makes no unconditional Hodge-convergence claim.
-/

set_option autoImplicit false

namespace NSEMaxwell.HodgeProof

open NSEMaxwell.Classical NSEMaxwell.FourierPeriodic
open scoped ContDiff

noncomputable section

theorem coordinateDerivative_const_add (m : Vec) (a : Field) (i : Fin 3) :
    coordinateDerivative (fun x => m + a x) i = coordinateDerivative a i := by
  funext x
  simp only [coordinateDerivative, fderiv_const_add]

theorem divergence_const_add (m : Vec) (a : Field) :
    NSEMaxwell.Classical.divergence (fun x => m + a x) =
      NSEMaxwell.Classical.divergence a := by
  funext x
  simp only [NSEMaxwell.Classical.divergence, coordinateDerivative_const_add]

theorem spatialCurl_const_add (m : Vec) (a : Field) :
    spatialCurl (fun x => m + a x) = spatialCurl a := by
  funext x
  simp only [spatialCurl, coordinateDerivative_const_add]

structure SpatialInverseLaplacianLaws : Prop where
  vector_smooth : ∀ (F : Field), ContDiff ℝ ∞ F → SpatialPeriodic F →
    ContDiff ℝ ∞ (vectorL F)
  curl_commute : ∀ (F : Field), ContDiff ℝ ∞ F → SpatialPeriodic F →
    spatialCurl (vectorL F) = vectorL (spatialCurl F)
  divergence_commute : ∀ (F : Field), ContDiff ℝ ∞ F → SpatialPeriodic F →
    NSEMaxwell.Classical.divergence (vectorL F) =
      scalarL (NSEMaxwell.Classical.divergence F)
  poisson : ∀ (F : Field), ContDiff ℝ ∞ F → SpatialPeriodic F →
    -NSEMaxwell.Classical.laplacian (vectorL F) = F - (fun _ => spatialMean F)

theorem SpatialInverseLaplacianLaws.K_smooth
    (laws : SpatialInverseLaplacianLaws) (F : Field)
    (hF : ContDiff ℝ ∞ F) (hp : SpatialPeriodic F) : ContDiff ℝ ∞ (K F) :=
  NSEMaxwell.CurlCurl.spatialCurl_smooth (laws.vector_smooth F hF hp)

theorem SpatialInverseLaplacianLaws.U_smooth
    (laws : SpatialInverseLaplacianLaws) (m : Vec) (F : Field)
    (hF : ContDiff ℝ ∞ F) (hp : SpatialPeriodic F) : ContDiff ℝ ∞ (U m F) :=
  contDiff_const.add (laws.K_smooth F hF hp)

theorem SpatialInverseLaplacianLaws.divergence_K
    (laws : SpatialInverseLaplacianLaws) (F : Field)
    (hF : ContDiff ℝ ∞ F) (hp : SpatialPeriodic F) :
    NSEMaxwell.Classical.divergence (K F) = 0 :=
  NSEMaxwell.CurlCurl.divergence_curl (laws.vector_smooth F hF hp)

theorem SpatialInverseLaplacianLaws.spatialMean_K
    (laws : SpatialInverseLaplacianLaws) (F : Field)
    (hF : ContDiff ℝ ∞ F) (hp : SpatialPeriodic F) : spatialMean (K F) = 0 :=
  NSEMaxwell.PeriodicIntegration.spatialMean_curl_zero
    (laws.vector_smooth F hF hp) (vectorL_periodic F)

theorem SpatialInverseLaplacianLaws.curl_K
    (laws : SpatialInverseLaplacianLaws) (F : Field)
    (hF : ContDiff ℝ ∞ F) (hp : SpatialPeriodic F) :
    spatialCurl (K F) = F - (fun _ => spatialMean F) +
      NSEMaxwell.Classical.gradient (scalarL (NSEMaxwell.Classical.divergence F)) := by
  unfold K
  rw [NSEMaxwell.CurlCurl.curl_curl (laws.vector_smooth F hF hp),
    laws.divergence_commute F hF hp, sub_eq_add_neg, laws.poisson F hF hp]
  abel

theorem SpatialInverseLaplacianLaws.K_curl
    (laws : SpatialInverseLaplacianLaws) (F : Field)
    (hF : ContDiff ℝ ∞ F) (hp : SpatialPeriodic F) :
    K (spatialCurl F) = F - (fun _ => spatialMean F) +
      NSEMaxwell.Classical.gradient (scalarL (NSEMaxwell.Classical.divergence F)) := by
  have hcomm : K (spatialCurl F) = spatialCurl (K F) := by
    unfold K
    rw [← laws.curl_commute F hF hp]
  rw [hcomm]
  exact laws.curl_K F hF hp

theorem SpatialInverseLaplacianLaws.reconstruct_velocity
    (laws : SpatialInverseLaplacianLaws) (a : Field) (ha : Data a) :
    U (spatialMean a) (spatialCurl a) = a := by
  have hdiv : NSEMaxwell.Classical.divergence a = 0 := by
    funext x
    exact ha.divergence_free x
  have hK := laws.K_curl a ha.smooth ha.periodic
  rw [hdiv, scalarL_zero, gradient_zero, add_zero] at hK
  funext x
  change spatialMean a + K (spatialCurl a) x = a x
  rw [hK]
  change spatialMean a + (a x - spatialMean a) = a x
  abel

theorem SpatialInverseLaplacianLaws.reconstruct_curl
    (laws : SpatialInverseLaplacianLaws) (m : Vec) (B : Field)
    (hB : MagneticData B) : spatialCurl (U m B) = B := by
  have hdiv : NSEMaxwell.Classical.divergence B = 0 := by
    funext x
    exact hB.divergence_free x
  have hK := laws.curl_K B hB.smooth hB.periodic
  rw [hdiv, scalarL_zero, gradient_zero, add_zero, hB.mean_zero] at hK
  change spatialCurl (fun x => m + K B x) = B
  rw [spatialCurl_const_add]
  have hz : (fun _ : Vec => (0 : Vec)) = (0 : Field) := rfl
  rw [hz, sub_zero] at hK
  exact hK

theorem SpatialInverseLaplacianLaws.reconstruction_data
    (laws : SpatialInverseLaplacianLaws) (m : Vec) (B : Field)
    (hB : MagneticData B) : Data (U m B) := by
  refine ⟨laws.U_smooth m B hB.smooth hB.periodic, U_periodic m B, ?_⟩
  intro x
  have h := laws.divergence_K B hB.smooth hB.periodic
  change NSEMaxwell.Classical.divergence (fun y => m + K B y) x = 0
  rw [divergence_const_add]
  exact congrFun h x

theorem SpatialInverseLaplacianLaws.reconstruct_mean
    (laws : SpatialInverseLaplacianLaws) (m : Vec) (B : Field)
    (hB : MagneticData B) : spatialMean (U m B) = m := by
  have h := laws.reconstruct_velocity (U m B) (laws.reconstruction_data m B hB)
  rw [laws.reconstruct_curl m B hB] at h
  have hx := congrFun h (0 : Vec)
  change spatialMean (U m B) + K B 0 = m + K B 0 at hx
  exact add_right_cancel hx

end

end NSEMaxwell.HodgeProof
