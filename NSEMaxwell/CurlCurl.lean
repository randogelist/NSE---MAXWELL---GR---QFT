import NSEMaxwell.Kinematics

/-!
# Concrete curl-curl and viscosity identities

The second-coordinate derivatives are actual derivatives of the Frechet
derivative. Their symmetry follows from Mathlib's symmetry theorem for second
derivatives, applied to a smooth real vector field. The curl-curl identity is
then proved from the specified coordinate definitions.

No Fourier, Hodge, curl-curl, or Hessian-symmetry premise is postulated.
Compilation evidence is supplied by the external native Windows runner.
No local Lean or Lake execution is performed.
-/

set_option autoImplicit false

namespace NSEMaxwell.CurlCurl

open NSEMaxwell.Classical
open scoped ContDiff

noncomputable section

/-- Ordered second coordinate derivative: outer direction i, inner direction j. -/
def secondCoordinate (a : Field) (i j : Fin 3) (x : Vec) : Vec :=
  fderiv ℝ (fderiv ℝ a) x (unitVector i) (unitVector j)

theorem coordinateDerivative_smooth
    {a : Field} (ha : ContDiff ℝ ∞ a) (i : Fin 3) :
    ContDiff ℝ ∞ (coordinateDerivative a i) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ a) := ha.fderiv_right (by simp)
  change ContDiff ℝ ∞ (fun x : Vec => (fderiv ℝ a x) (unitVector i))
  exact hd.clm_apply
    (show ContDiff ℝ ∞ (fun _ : Vec => unitVector i) from contDiff_const)

theorem coordinate_component_smooth
    {a : Field} (ha : ContDiff ℝ ∞ a) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun x : Vec => coordinateDerivative a i x j) :=
  (contDiff_piLp 2).mp (coordinateDerivative_smooth ha i) j

/-- Differentiation commutes with the fixed coordinate projection. -/
theorem fderiv_component_apply
    {a : Field} {x : Vec} (ha : DifferentiableAt ℝ a x)
    (v : Vec) (j : Fin 3) :
    fderiv ℝ (fun y : Vec => a y j) x v = (fderiv ℝ a x v) j := by
  have hp := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (a x) j).comp x ha.hasFDerivAt
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L v) hp.fderiv

theorem coordinateDerivative_coordinateDerivative
    {a : Field} (ha : ContDiff ℝ ∞ a) (i j : Fin 3) (x : Vec) :
    coordinateDerivative (coordinateDerivative a j) i x =
      secondCoordinate a i j x := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ a) := ha.fderiv_right (by simp)
  have hdx := (hd.differentiable (by simp) x).hasFDerivAt
  have h := hdx.clm_apply (hasFDerivAt_const (unitVector j) x)
  have he := congrArg (fun L : Vec →L[ℝ] Vec => L (unitVector i)) h.fderiv
  change (fderiv ℝ (coordinateDerivative a j) x) (unitVector i) =
    (fderiv ℝ (fderiv ℝ a) x) (unitVector i) (unitVector j)
  have hfunction : coordinateDerivative a j =
      (fun y : Vec => (fderiv ℝ a y) (unitVector j)) := rfl
  rw [hfunction]
  simpa [ContinuousLinearMap.flip_apply] using he

/-- Symmetry is a consequence of the actual smoothness hypothesis. -/
theorem secondCoordinate_symm
    {a : Field} (ha : ContDiff ℝ ∞ a) (i j : Fin 3) (x : Vec) :
    secondCoordinate a i j x = secondCoordinate a j i x := by
  exact (ha.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    decide)) (unitVector i) (unitVector j)

theorem second_coordinate_component
    {a : Field} (ha : ContDiff ℝ ∞ a) (i j k : Fin 3) (x : Vec) :
    fderiv ℝ (fun y : Vec => coordinateDerivative a j y k) x (unitVector i) =
      secondCoordinate a i j x k := by
  calc
    fderiv ℝ (fun y : Vec => coordinateDerivative a j y k) x (unitVector i) =
        coordinateDerivative (coordinateDerivative a j) i x k :=
      fderiv_component_apply
        ((coordinateDerivative_smooth ha j).differentiable (by simp) x) (unitVector i) k
    _ = secondCoordinate a i j x k :=
      congrArg (fun v : Vec => v k) (coordinateDerivative_coordinateDerivative ha i j x)

theorem coordinate_component_sub_derivative
    {a : Field} (ha : ContDiff ℝ ∞ a) (i j k l r : Fin 3) (x : Vec) :
    fderiv ℝ
        (fun y : Vec => coordinateDerivative a j y k - coordinateDerivative a l y r)
        x (unitVector i) =
      secondCoordinate a i j x k - secondCoordinate a i l x r := by
  rw [fderiv_fun_sub
    ((coordinate_component_smooth ha j k).differentiable (by simp) x)
    ((coordinate_component_smooth ha l r).differentiable (by simp) x)]
  simp only [ContinuousLinearMap.sub_apply]
  rw [second_coordinate_component ha i j k x, second_coordinate_component ha i l r x]

theorem spatialCurl_smooth
    {a : Field} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (spatialCurl a) := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · simpa [spatialCurl, PiLp.toLp_apply] using
      (coordinate_component_smooth ha 1 2).sub (coordinate_component_smooth ha 2 1)
  · simpa [spatialCurl, PiLp.toLp_apply] using
      (coordinate_component_smooth ha 2 0).sub (coordinate_component_smooth ha 0 2)
  · simpa [spatialCurl, PiLp.toLp_apply] using
      (coordinate_component_smooth ha 0 1).sub (coordinate_component_smooth ha 1 0)

theorem coordinateDerivative_curl_zero
    {a : Field} (ha : ContDiff ℝ ∞ a) (i : Fin 3) (x : Vec) :
    coordinateDerivative (spatialCurl a) i x 0 =
      secondCoordinate a i 1 x 2 - secondCoordinate a i 2 x 1 := by
  calc
    coordinateDerivative (spatialCurl a) i x 0 =
        fderiv ℝ (fun y : Vec => spatialCurl a y 0) x (unitVector i) :=
      (fderiv_component_apply
        ((spatialCurl_smooth ha).differentiable (by simp) x) (unitVector i) 0).symm
    _ = secondCoordinate a i 1 x 2 - secondCoordinate a i 2 x 1 := by
      simpa [spatialCurl, PiLp.toLp_apply] using
        coordinate_component_sub_derivative ha i 1 2 2 1 x

theorem coordinateDerivative_curl_one
    {a : Field} (ha : ContDiff ℝ ∞ a) (i : Fin 3) (x : Vec) :
    coordinateDerivative (spatialCurl a) i x 1 =
      secondCoordinate a i 2 x 0 - secondCoordinate a i 0 x 2 := by
  calc
    coordinateDerivative (spatialCurl a) i x 1 =
        fderiv ℝ (fun y : Vec => spatialCurl a y 1) x (unitVector i) :=
      (fderiv_component_apply
        ((spatialCurl_smooth ha).differentiable (by simp) x) (unitVector i) 1).symm
    _ = secondCoordinate a i 2 x 0 - secondCoordinate a i 0 x 2 := by
      simpa [spatialCurl, PiLp.toLp_apply] using
        coordinate_component_sub_derivative ha i 2 0 0 2 x

theorem coordinateDerivative_curl_two
    {a : Field} (ha : ContDiff ℝ ∞ a) (i : Fin 3) (x : Vec) :
    coordinateDerivative (spatialCurl a) i x 2 =
      secondCoordinate a i 0 x 1 - secondCoordinate a i 1 x 0 := by
  calc
    coordinateDerivative (spatialCurl a) i x 2 =
        fderiv ℝ (fun y : Vec => spatialCurl a y 2) x (unitVector i) :=
      (fderiv_component_apply
        ((spatialCurl_smooth ha).differentiable (by simp) x) (unitVector i) 2).symm
    _ = secondCoordinate a i 0 x 1 - secondCoordinate a i 1 x 0 := by
      simpa [spatialCurl, PiLp.toLp_apply] using
        coordinate_component_sub_derivative ha i 0 1 1 0 x

/-- The NSEMaxwell.Classical.divergence of the actual curl vanishes for every smooth vector field. -/
theorem divergence_curl
    {a : Field} (ha : ContDiff ℝ ∞ a) :
    NSEMaxwell.Classical.divergence (spatialCurl a) = 0 := by
  funext x
  have htrace : NSEMaxwell.Classical.divergence (spatialCurl a) x =
      coordinateDerivative (spatialCurl a) 0 x 0 +
        coordinateDerivative (spatialCurl a) 1 x 1 +
        coordinateDerivative (spatialCurl a) 2 x 2 := by
    simp [NSEMaxwell.Classical.divergence, Fin.sum_univ_succ, add_assoc]
  change NSEMaxwell.Classical.divergence (spatialCurl a) x = 0
  rw [htrace, coordinateDerivative_curl_zero ha 0 x,
    coordinateDerivative_curl_one ha 1 x, coordinateDerivative_curl_two ha 2 x,
    secondCoordinate_symm ha 1 0 x, secondCoordinate_symm ha 2 0 x,
    secondCoordinate_symm ha 2 1 x]
  abel

theorem gradient_divergence_coordinate
    {a : Field} (ha : ContDiff ℝ ∞ a) (i : Fin 3) (x : Vec) :
    NSEMaxwell.Classical.gradient (NSEMaxwell.Classical.divergence a) x i =
      secondCoordinate a i 0 x 0 + secondCoordinate a i 1 x 1 +
        secondCoordinate a i 2 x 2 := by
  have hdiv : NSEMaxwell.Classical.divergence a =
      (fun y : Vec => coordinateDerivative a 0 y 0 +
        coordinateDerivative a 1 y 1 + coordinateDerivative a 2 y 2) := by
    funext y
    simp [NSEMaxwell.Classical.divergence, Fin.sum_univ_succ, add_assoc]
  have h0 := (coordinate_component_smooth ha 0 0).differentiable (by simp) x
  have h1 := (coordinate_component_smooth ha 1 1).differentiable (by simp) x
  have h2 := (coordinate_component_smooth ha 2 2).differentiable (by simp) x
  have hsum := (h0.hasFDerivAt.add h1.hasFDerivAt).add h2.hasFDerivAt
  change HasFDerivAt
      (fun y : Vec => coordinateDerivative a 0 y 0 +
        coordinateDerivative a 1 y 1 + coordinateDerivative a 2 y 2)
      (fderiv ℝ (fun y : Vec => coordinateDerivative a 0 y 0) x +
        fderiv ℝ (fun y : Vec => coordinateDerivative a 1 y 1) x +
        fderiv ℝ (fun y : Vec => coordinateDerivative a 2 y 2) x) x at hsum
  change fderiv ℝ (NSEMaxwell.Classical.divergence a) x (unitVector i) = _
  rw [hdiv, hsum.fderiv]
  simp only [ContinuousLinearMap.add_apply]
  rw [second_coordinate_component ha i 0 0 x,
    second_coordinate_component ha i 1 1 x, second_coordinate_component ha i 2 2 x]

theorem laplacian_coordinate
    {a : Field} (ha : ContDiff ℝ ∞ a) (x : Vec) (i : Fin 3) :
    NSEMaxwell.Classical.laplacian a x i =
      secondCoordinate a 0 0 x i + secondCoordinate a 1 1 x i +
        secondCoordinate a 2 2 x i := by
  have hsec (j : Fin 3) :
      fderiv ℝ (coordinateDerivative a j) x (unitVector j) =
        secondCoordinate a j j x :=
    coordinateDerivative_coordinateDerivative ha j j x
  simp [NSEMaxwell.Classical.laplacian, hsec, Fin.sum_univ_succ, add_assoc]

/-- Curl curl a = grad div a - Laplacian a, using the actual derivatives. -/
theorem curl_curl_at
    {a : Field} (ha : ContDiff ℝ ∞ a) (x : Vec) :
    spatialCurl (spatialCurl a) x = NSEMaxwell.Classical.gradient (NSEMaxwell.Classical.divergence a) x - NSEMaxwell.Classical.laplacian a x := by
  apply PiLp.ext
  intro i
  rw [PiLp.sub_apply]
  fin_cases i
  · change coordinateDerivative (spatialCurl a) 1 x 2 -
        coordinateDerivative (spatialCurl a) 2 x 1 =
      NSEMaxwell.Classical.gradient (NSEMaxwell.Classical.divergence a) x 0 - NSEMaxwell.Classical.laplacian a x 0
    rw [coordinateDerivative_curl_two ha 1 x, coordinateDerivative_curl_one ha 2 x,
      gradient_divergence_coordinate ha 0 x, laplacian_coordinate ha x 0,
      secondCoordinate_symm ha 1 0 x, secondCoordinate_symm ha 2 0 x]
    abel
  · change coordinateDerivative (spatialCurl a) 2 x 0 -
        coordinateDerivative (spatialCurl a) 0 x 2 =
      NSEMaxwell.Classical.gradient (NSEMaxwell.Classical.divergence a) x 1 - NSEMaxwell.Classical.laplacian a x 1
    rw [coordinateDerivative_curl_zero ha 2 x, coordinateDerivative_curl_two ha 0 x,
      gradient_divergence_coordinate ha 1 x, laplacian_coordinate ha x 1,
      secondCoordinate_symm ha 1 0 x, secondCoordinate_symm ha 2 1 x]
    abel
  · change coordinateDerivative (spatialCurl a) 0 x 1 -
        coordinateDerivative (spatialCurl a) 1 x 0 =
      NSEMaxwell.Classical.gradient (NSEMaxwell.Classical.divergence a) x 2 - NSEMaxwell.Classical.laplacian a x 2
    rw [coordinateDerivative_curl_one ha 0 x, coordinateDerivative_curl_zero ha 1 x,
      gradient_divergence_coordinate ha 2 x, laplacian_coordinate ha x 2,
      secondCoordinate_symm ha 2 0 x, secondCoordinate_symm ha 2 1 x]
    abel

theorem curl_curl
    {a : Field} (ha : ContDiff ℝ ∞ a) :
    spatialCurl (spatialCurl a) = NSEMaxwell.Classical.gradient (NSEMaxwell.Classical.divergence a) - NSEMaxwell.Classical.laplacian a := by
  funext x
  exact curl_curl_at ha x

theorem curl_curl_of_divergence_zero
    {a : Field} (ha : ContDiff ℝ ∞ a) (hDiv : NSEMaxwell.Classical.divergence a = 0) :
    spatialCurl (spatialCurl a) = -NSEMaxwell.Classical.laplacian a := by
  rw [curl_curl ha, hDiv, gradient_zero, zero_sub]

theorem viscosity_identity_of_curl
    (ν : ℝ) (a B : Field)
    (ha : ContDiff ℝ ∞ a) (hDiv : NSEMaxwell.Classical.divergence a = 0)
    (hCurl : spatialCurl a = B) :
    ν • NSEMaxwell.Classical.laplacian a = -(ν • spatialCurl B) := by
  have h := curl_curl_of_divergence_zero ha hDiv
  rw [hCurl] at h
  have hLap : NSEMaxwell.Classical.laplacian a = -spatialCurl B := by
    simpa only [neg_neg] using (congrArg (fun v : Field => -v) h).symm
  rw [hLap, smul_neg]

theorem viscosity_identity_of_data
    (ν : ℝ) (a B : Field) (ha : Data a) (hCurl : spatialCurl a = B) :
    ν • NSEMaxwell.Classical.laplacian a = -(ν • spatialCurl B) := by
  apply viscosity_identity_of_curl ν a B ha.smooth
  · funext x
    exact ha.divergence_free x
  · exact hCurl

theorem reconstructed_viscosity_identity
    (ν : ℝ) (m : Vec) (B : Field)
    (hData : Data (U m B))
    (hCurl : spatialCurl (U m B) = B) :
    ν • NSEMaxwell.Classical.laplacian (U m B) = -(ν • spatialCurl B) :=
  viscosity_identity_of_data ν (U m B) B hData hCurl

end

end NSEMaxwell.CurlCurl

