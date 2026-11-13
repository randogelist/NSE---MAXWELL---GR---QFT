import FourierHodgeLaws.SpatialHodge

/-!
The electric mean-zero calculation is proved from actual smoothness,
periodicity, divergence, and curl reconstruction. The final H4 assembly
retains the explicit spatial inverse-Laplacian record until it is instantiated.
-/

set_option autoImplicit false

namespace NSEMaxwell.HodgeProof

open NSEMaxwell.Classical NSEMaxwell.Bridge
open NSEMaxwell.PeriodicIntegration NSEMaxwell.FourierPeriodic
open MeasureTheory
open scoped ContDiff

noncomputable section

theorem spatialMean_lamb_zero (u : Field) (hu : Data u) :
    spatialMean (fun x => cross (spatialCurl u x) (u x)) = 0 := by
  have he : ContDiff ℝ ∞ (fun x : Vec => ‖u x‖ ^ 2 / 2) :=
    (hu.smooth.norm_sq ℝ).div_const 2
  have hep : SpatialPeriodic (fun x : Vec => ‖u x‖ ^ 2 / 2) := by
    intro x i
    change ‖u (x + unitVector i)‖ ^ 2 / 2 = ‖u x‖ ^ 2 / 2
    rw [hu.periodic x i]
  have hc : (fun x => cross (spatialCurl u x) (u x)) =
      convection u - NSEMaxwell.Classical.gradient (fun x => ‖u x‖ ^ 2 / 2) := by
    apply eq_sub_iff_add_eq.mpr
    exact (NSEMaxwell.Lamb.lamb_identity_of_data hu).symm
  rw [hc]
  change (∫ x in unitCube, convection u x -
    NSEMaxwell.Classical.gradient (fun y => ‖u y‖ ^ 2 / 2) x) = 0
  rw [integral_sub
    (integrableOn_unitCube_of_continuous (convection_smooth hu.smooth).continuous)
    (integrableOn_unitCube_of_continuous (gradient_smooth he).continuous)]
  change spatialMean (convection u) -
    spatialMean (NSEMaxwell.Classical.gradient (fun y => ‖u y‖ ^ 2 / 2)) = 0
  rw [spatialMean_convection_zero hu.smooth hu.periodic hu.divergence_free,
    spatialMean_gradient_zero he hep]
  exact sub_self 0

theorem G_smooth_of_velocity_smooth
    (ν : ℝ) (m : Vec) (B : Field)
    (hB : ContDiff ℝ ∞ B) (hU : ContDiff ℝ ∞ (U m B)) :
    ContDiff ℝ ∞ (G ν m B) :=
  (NSEMaxwell.LocalEvolution.cross_smooth hB hU).add
    ((NSEMaxwell.CurlCurl.spatialCurl_smooth hB).const_smul ν)

theorem spatialMean_G_of_reconstruction
    (ν : ℝ) (m : Vec) (B : Field)
    (hB : ContDiff ℝ ∞ B) (hp : SpatialPeriodic B)
    (hU : Data (U m B)) (hcurl : spatialCurl (U m B) = B) :
    spatialMean (G ν m B) = 0 := by
  have hlamb := spatialMean_lamb_zero (U m B) hU
  rw [hcurl] at hlamb
  have hc : IntegrableOn (fun x => cross (B x) (U m B x)) unitCube :=
    integrableOn_unitCube_of_continuous
      (NSEMaxwell.LocalEvolution.cross_smooth hB hU.smooth).continuous
  have hw : IntegrableOn (fun x => ν • spatialCurl B x) unitCube :=
    integrableOn_unitCube_of_continuous
      ((NSEMaxwell.CurlCurl.spatialCurl_smooth hB).const_smul ν).continuous
  change (∫ x in unitCube, cross (B x) (U m B x) + ν • spatialCurl B x) = 0
  rw [integral_add hc hw, integral_smul]
  change spatialMean (fun x => cross (B x) (U m B x)) +
    ν • spatialMean (spatialCurl B) = 0
  rw [hlamb, spatialMean_curl_zero hB hp]
  simp

theorem SpatialInverseLaplacianLaws.G_smooth
    (laws : SpatialInverseLaplacianLaws) (ν : ℝ) (m : Vec) (B : Field)
    (hB : MagneticData B) : ContDiff ℝ ∞ (G ν m B) :=
  G_smooth_of_velocity_smooth ν m B hB.smooth
    (laws.U_smooth m B hB.smooth hB.periodic)

theorem SpatialInverseLaplacianLaws.spatialMean_G
    (laws : SpatialInverseLaplacianLaws) (ν : ℝ) (m : Vec) (B : Field)
    (hB : MagneticData B) : spatialMean (G ν m B) = 0 :=
  spatialMean_G_of_reconstruction ν m B hB.smooth hB.periodic
    (laws.reconstruction_data m B hB) (laws.reconstruct_curl m B hB)

theorem SpatialInverseLaplacianLaws.electric_hodge
    (laws : SpatialInverseLaplacianLaws) (ν : ℝ) (m : Vec) (B : Field)
    (hB : MagneticData B) :
    G ν m B + NSEMaxwell.Classical.gradient (headPotential ν m B) =
      K (spatialCurl (G ν m B)) := by
  have h := laws.K_curl (G ν m B) (laws.G_smooth ν m B hB)
    (G_periodic ν m hB.periodic)
  rw [laws.spatialMean_G ν m B hB] at h
  have hz : (fun _ : Vec => (0 : Vec)) = (0 : Field) := rfl
  rw [hz, sub_zero] at h
  exact h.symm

end

end NSEMaxwell.HodgeProof
