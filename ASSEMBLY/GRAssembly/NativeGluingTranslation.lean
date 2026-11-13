import GRAssembly.ScalarJet
import GRAssembly.NativeGluingAtlas
import GRAdapter.GaussianUniqueness

/-! Literal affine translation of the actual scalar and metric derivatives. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius

namespace NSEGR.Assembly
noncomputable section

theorem spatialPeriodic_sub_integer {Y : Type*} {f : Vec → Y}
    (hf : SpatialPeriodic f) (n : Frequency) (x : Vec) :
    f (x - integerSpatialShift n) = f x := by
  simpa only [sub_add_cancel] using
    (spatialPeriodic_integerSpatialShift hf n (x - integerSpatialShift n)).symm

theorem fderiv_spatialPeriodic_sub_integer {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : Vec → Y}
    (hf : SpatialPeriodic f) (n : Frequency) (x : Vec) :
    fderiv ℝ f (x - integerSpatialShift n) = fderiv ℝ f x := by
  have he : (fun y => f (y - integerSpatialShift n)) = f :=
    funext (spatialPeriodic_sub_integer hf n)
  rw [← fderiv_comp_sub (integerSpatialShift n), he]

theorem scalarCompletionUpper_spatial_sub (ψ : Pressure) (c : Vec) (t : ℝ) (x : Vec) :
    scalarCompletionUpper (fun s y => ψ s (y - c)) t x =
      scalarCompletionUpper ψ t (x - c) := by
  have hH : scalarHessian (fun y => ψ t (y - c)) x = scalarHessian (ψ t) (x - c) := by
    ext i j
    simp only [scalarHessian, fderiv_comp_sub]
    exact congrArg (fun L : Vec →L[ℝ] ℝ => L (unitVector i))
      (fderiv_comp_sub (𝕜 := ℝ)
        (f := fun y => fderiv ℝ (ψ t) y (unitVector j)) (x := x) c)
  have hD : scalarLaplacian (fun y => ψ t (y - c)) x = scalarLaplacian (ψ t) (x - c) := by
    rw [← trace3_scalarHessian, hH, trace3_scalarHessian]
  have hG : gradient (scalarLocalTimeDerivative (fun s y => ψ s (y - c)) t) x =
      gradient (scalarLocalTimeDerivative ψ t) (x - c) := by
    ext i
    exact congrArg (fun L : Vec →L[ℝ] ℝ => L (unitVector i))
      (fderiv_comp_sub (𝕜 := ℝ) (f := scalarLocalTimeDerivative ψ t) (x := x) c)
  simp only [scalarCompletionUpper, hH, hD, hG]
  rfl

theorem conservedSourceUpper_periodic_sub {ν ρ : ℝ} {u : Velocity} {p : Pressure}
    {t : ℝ} (hu : SpatialPeriodic (u t)) (hp : SpatialPeriodic (p t))
    (n : Frequency) (x : Vec) :
    conservedSourceUpper ν ρ u p t (x - integerSpatialShift n) =
      conservedSourceUpper ν ρ u p t x := by
  simp only [conservedSourceUpper, strain, spatialPartial,
    spatialPeriodic_sub_integer hu n x, spatialPeriodic_sub_integer hp n x,
    fderiv_spatialPeriodic_sub_integer hu n x]

theorem completedBoundary_spatial_sub {ν ρ : ℝ} {u : Velocity} {p ψ : Pressure}
    {t : ℝ} (hu : SpatialPeriodic (u t)) (hp : SpatialPeriodic (p t))
    (n : Frequency) (x : Vec) :
    completedBoundary ν ρ u p (fun s y => ψ s (y - integerSpatialShift n)) t x =
      completedBoundary ν ρ u p ψ t (x - integerSpatialShift n) := by
  unfold completedBoundary
  rw [scalarCompletionUpper_spatial_sub, conservedSourceUpper_periodic_sub hu hp]

theorem scalarCompletionUpper_joint_congr {f g : ℝ × Vec → ℝ} {z : ℝ × Vec}
    (h : f =ᶠ[𝓝 z] g) :
    scalarCompletionUpper (fun t x => f (t, x)) z.1 z.2 =
      scalarCompletionUpper (fun t x => g (t, x)) z.1 z.2 := by
  have ht := jointTime_congr_germ h
  have htt := jointTime_congr ht
  have hs (i j : Fin 3) :=
    jointSpace_congr (jointSpace_congr_germ h j) i
  have hm (i : Fin 3) := jointSpace_congr ht i
  have hH : scalarHessian (fun x => f (z.1, x)) z.2 =
      scalarHessian (fun x => g (z.1, x)) z.2 := by
    ext i j
    exact hs i j
  have hD : scalarLaplacian (fun x => f (z.1, x)) z.2 =
      scalarLaplacian (fun x => g (z.1, x)) z.2 := by
    unfold scalarLaplacian
    exact Finset.sum_congr rfl (fun i _ => hs i i)
  have hG : gradient (scalarLocalTimeDerivative (fun t x => f (t, x)) z.1) z.2 =
      gradient (scalarLocalTimeDerivative (fun t x => g (t, x)) z.1) z.2 := by
    ext i
    exact hm i
  simp only [scalarCompletionUpper, hH, hD, hG]
  change boundaryBlock _ _ (fun i j => _ + (jointTime (jointTime f) z - _) * _) =
    boundaryBlock _ _ (fun i j => _ + (jointTime (jointTime g) z - _) * _)
  rw [htt]

theorem completedBoundary_joint_congr {ν ρ : ℝ} {u : Velocity} {p : Pressure}
    {f g : ℝ × Vec → ℝ} {z : ℝ × Vec} (h : f =ᶠ[𝓝 z] g) :
    completedBoundary ν ρ u p (fun t x => f (t, x)) z.1 z.2 =
      completedBoundary ν ρ u p (fun t x => g (t, x)) z.1 z.2 := by
  unfold completedBoundary
  rw [scalarCompletionUpper_joint_congr h]

theorem boundaryHamiltonian_joint_congr {ν ρ : ℝ} {u : Velocity} {p : Pressure}
    {f g : ℝ × Vec → ℝ} {z : ℝ × Vec} (h : f =ᶠ[𝓝 z] g) :
    boundaryHamiltonian (completedBoundary ν ρ u p (fun t x => f (t, x))) z.1 z.2 =
      boundaryHamiltonian (completedBoundary ν ρ u p (fun t x => g (t, x))) z.1 z.2 := by
  unfold boundaryHamiltonian
  rw [completedBoundary_joint_congr h]

theorem bulkPartial_comp_sub (f : Bulk → ℝ) (c : Bulk) (i : Fin 5) (z : Bulk) :
    bulkPartial (fun y => f (y - c)) i z = bulkPartial f i (z - c) := by
  simp only [bulkPartial, fderiv_comp_sub]

theorem christoffel_comp_sub (g : Metric) (c z : Bulk) (a b d : Fin 5) :
    christoffel (fun y => g (y - c)) z a b d = christoffel g (z - c) a b d := by
  have hd (i j k : Fin 5) :
      bulkPartial (fun y => g (y - c) i j) k z =
        bulkPartial (fun y => g y i j) k (z - c) :=
    bulkPartial_comp_sub (fun y => g y i j) c k z
  simp only [christoffel, inverseMetric, hd]

theorem ricci_comp_sub (g : Metric) (c z : Bulk) :
    ricci (fun y => g (y - c)) z = ricci g (z - c) := by
  have hd (i j k l : Fin 5) :
      bulkPartial (fun y => christoffel g (y - c) i j k) l z =
        bulkPartial (fun y => christoffel g y i j k) l (z - c) :=
    bulkPartial_comp_sub (fun y => christoffel g y i j k) c l z
  ext a b
  simp only [ricci, christoffel_comp_sub, hd]

theorem bulkPoint_sub_spatial (r t : ℝ) (x c : Vec) :
    bulkPoint r t x - bulkPoint 0 0 c = bulkPoint r t (x - c) := by
  ext i
  fin_cases i
  · change r - 0 = r
    exact sub_zero r
  · change t - 0 = t
    exact sub_zero t
  · rfl
  · rfl
  · rfl

theorem boundaryK_comp_spatial_sub (g : Metric) (c : Vec) (t : ℝ) (x : Vec) :
    boundaryK (fun z => g (z - bulkPoint 0 0 c)) t x = boundaryK g t (x - c) := by
  ext a b
  unfold boundaryK
  rw [bulkPartial_comp_sub
    (fun y => g y (boundaryIndex a) (boundaryIndex b)) (bulkPoint 0 0 c) 0 (bulkPoint 0 t x),
    bulkPoint_sub_spatial]

end
end NSEGR.Assembly
