import NSEMaxwell.Spacetime
import NSEMaxwell.Lamb

/-!
# Local differential identities for the exact constrained Maxwell system

The vorticity residual is a consequence of actual smooth differential calculus.
The electric chain rule follows from that calculus and the separately stated
reconstruction time identity. No new analytic axiom is declared.
-/

set_option autoImplicit false

namespace NSEMaxwell.LocalEvolution

open NSEMaxwell.Classical NSEMaxwell.Spacetime NSEMaxwell.CurlCurl Set
open scoped ContDiff

noncomputable section

theorem cross_smooth {a b : Field}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (fun x => cross (a x) (b x)) := by
  apply (contDiff_piLp 2).mpr
  intro i
  have ha' (j : Fin 3) := (contDiff_piLp 2).mp ha j
  have hb' (j : Fin 3) := (contDiff_piLp 2).mp hb j
  fin_cases i
  · simpa [cross, PiLp.toLp_apply] using (ha' 1 |>.mul (hb' 2)).sub (ha' 2 |>.mul (hb' 1))
  · simpa [cross, PiLp.toLp_apply] using (ha' 2 |>.mul (hb' 0)).sub (ha' 0 |>.mul (hb' 2))
  · simpa [cross, PiLp.toLp_apply] using (ha' 0 |>.mul (hb' 1)).sub (ha' 1 |>.mul (hb' 0))

theorem cross_trajectory_smooth {u v : Velocity}
    (hu : SmoothVelocity u) (hv : SmoothVelocity v) :
    SmoothVelocity (fun t x => cross (u t x) (v t x)) := by
  apply (contDiffOn_piLp 2).mpr
  intro i
  have hu' (j : Fin 3) := (contDiffOn_piLp 2).mp hu j
  have hv' (j : Fin 3) := (contDiffOn_piLp 2).mp hv j
  fin_cases i
  · simpa [cross, PiLp.toLp_apply] using (hu' 1 |>.mul (hv' 2)).sub (hu' 2 |>.mul (hv' 1))
  · simpa [cross, PiLp.toLp_apply] using (hu' 2 |>.mul (hv' 0)).sub (hu' 0 |>.mul (hv' 2))
  · simpa [cross, PiLp.toLp_apply] using (hu' 0 |>.mul (hv' 1)).sub (hu' 1 |>.mul (hv' 0))

theorem timeDerivative_cross {u v : Velocity}
    (hu : SmoothVelocity u) (hv : SmoothVelocity v) {t : ℝ} (ht : 0 ≤ t) :
    timeDerivative (fun s x => cross (u s x) (v s x)) t =
      fun x => cross (timeDerivative u t x) (v t x) +
        cross (u t x) (timeDerivative v t x) := by
  have hs (x : Vec) (i j k l : Fin 3) :
      derivWithin (fun s : ℝ => u s x i * v s x j - u s x k * v s x l) (Ici 0) t =
      (timeDerivative u t x i * v t x j + u t x i * timeDerivative v t x j) -
        (timeDerivative u t x k * v t x l + u t x k * timeDerivative v t x l) := by
    simpa only [Pi.sub_def, Pi.mul_def] using
      (((time_component_hasDerivWithinAt hu ht x i).mul
      (time_component_hasDerivWithinAt hv ht x j)).sub
      ((time_component_hasDerivWithinAt hu ht x k).mul
      (time_component_hasDerivWithinAt hv ht x l))).derivWithin
        (uniqueDiffOn_Ici 0 t ht)
  funext x
  apply PiLp.ext
  intro i
  rw [← timeDerivative_component (cross_trajectory_smooth hu hv) ht x i]
  fin_cases i
  · convert hs x 1 2 2 1 using 1 <;> simp [cross, PiLp.toLp_apply] <;> ring
  · convert hs x 2 0 0 2 using 1 <;> simp [cross, PiLp.toLp_apply] <;> ring
  · convert hs x 0 1 1 0 using 1 <;> simp [cross, PiLp.toLp_apply] <;> ring

/-- The constitutive time chain has no independent nonlinear analytic premise. -/
theorem electric_time_chain_of_reconstruction
    (ν : ℝ) (m : Vec) (B : Velocity)
    (hB : SmoothVelocity B) (hU : SmoothVelocity (canonicalVelocity m B))
    {t : ℝ} (ht : 0 ≤ t)
    (hRecon : timeDerivative (canonicalVelocity m B) t = K (timeDerivative B t)) :
    timeDerivative (canonicalElectric ν m B) t = DG ν m (B t) (timeDerivative B t) := by
  have hC := cross_trajectory_smooth hB hU
  have hW := curl_trajectory_smooth hB
  funext x
  have h := ((time_slice_hasDerivWithinAt hC ht x).add
    ((time_slice_hasDerivWithinAt hW ht x).const_smul ν)).derivWithin
      (uniqueDiffOn_Ici 0 t ht)
  have hcross := congrFun (timeDerivative_cross hB hU ht) x
  have hcurl := congrFun (timeDerivative_curl_commute hB ht) x
  rw [hcross, hcurl, hRecon] at h
  simpa only [Pi.add_def, Pi.smul_def, canonicalElectric, G,
    timeDerivative, DG, canonicalVelocity] using h

theorem gradient_smooth {f : ScalarField} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (NSEMaxwell.Classical.gradient f) := by
  apply (contDiff_piLp 2).mpr
  intro i
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem spatialCurl_add {a b : Field}
    (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    spatialCurl (a + b) = spatialCurl a + spatialCurl b := by
  have hd (i : Fin 3) (x : Vec) :
      coordinateDerivative (a + b) i x = coordinateDerivative a i x + coordinateDerivative b i x := by
    change fderiv ℝ (a + b) x (unitVector i) = _
    rw [fderiv_add (ha x) (hb x)]
    rfl
  funext x
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [spatialCurl, PiLp.toLp_apply, hd] <;> ring

theorem spatialCurl_gradient {f : ScalarField} (hf : ContDiff ℝ ∞ f) :
    spatialCurl (NSEMaxwell.Classical.gradient f) = 0 := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hcomp (i j : Fin 3) (x : Vec) :
      coordinateDerivative (NSEMaxwell.Classical.gradient f) i x j =
        fderiv ℝ (fderiv ℝ f) x (unitVector i) (unitVector j) := by
    have h := ((hd.differentiable (by simp) x).hasFDerivAt.clm_apply
      (hasFDerivAt_const (unitVector j) x)).fderiv
    have he := congrArg (fun L : Vec →L[ℝ] ℝ => L (unitVector i)) h
    calc
      coordinateDerivative (NSEMaxwell.Classical.gradient f) i x j =
          fderiv ℝ (fun y : Vec => NSEMaxwell.Classical.gradient f y j)
            x (unitVector i) :=
        (fderiv_component_apply ((gradient_smooth hf).differentiable (by simp) x)
          (unitVector i) j).symm
      _ = fderiv ℝ (fderiv ℝ f) x (unitVector i) (unitVector j) := by
        simpa [NSEMaxwell.Classical.gradient, PiLp.toLp_apply,
          ContinuousLinearMap.flip_apply] using he
  have hsym (i j : Fin 3) (x : Vec) :
      coordinateDerivative (NSEMaxwell.Classical.gradient f) i x j =
        coordinateDerivative (NSEMaxwell.Classical.gradient f) j x i := by
    rw [hcomp, hcomp]
    exact hf.contDiffAt.isSymmSndFDerivAt
      (by simp only [minSmoothness_of_isRCLikeNormedField]; decide)
      (unitVector i) (unitVector j)
  funext x
  apply PiLp.ext
  intro i
  fin_cases i
  · change coordinateDerivative (NSEMaxwell.Classical.gradient f) 1 x 2 -
      coordinateDerivative (NSEMaxwell.Classical.gradient f) 2 x 1 = 0
    rw [hsym 1 2, sub_self]
  · change coordinateDerivative (NSEMaxwell.Classical.gradient f) 2 x 0 -
      coordinateDerivative (NSEMaxwell.Classical.gradient f) 0 x 2 = 0
    rw [hsym 2 0, sub_self]
  · change coordinateDerivative (NSEMaxwell.Classical.gradient f) 0 x 1 -
      coordinateDerivative (NSEMaxwell.Classical.gradient f) 1 x 0 = 0
    rw [hsym 0 1, sub_self]

/-- Curl of the momentum residual is exactly the vorticity residual. -/
theorem vorticity_residual
    (ν : ℝ) (u : Velocity) (p : Pressure)
    (hu : SmoothVelocity u) (hp : SmoothPressure p)
    (hDiv : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec, NSEMaxwell.Classical.divergence (u t) x = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    spatialCurl (timeDerivative u t + convection (u t) +
      NSEMaxwell.Classical.gradient (p t) - ν • NSEMaxwell.Classical.laplacian (u t)) =
      timeDerivative (fun s => spatialCurl (u s)) t +
        spatialCurl (fun x => cross (spatialCurl (u t) x) (u t x) +
          ν • spatialCurl (spatialCurl (u t)) x) := by
  have hs := velocity_slice_smooth hu ht
  have hps := pressure_slice_smooth hp ht
  have hdt := velocity_slice_smooth (timeDerivative_smooth hu) ht
  have hK : ContDiff ℝ ∞ (fun x : Vec => ‖u t x‖ ^ 2 / 2) :=
    (hs.norm_sq ℝ).div_const 2
  have hL := NSEMaxwell.Lamb.lamb_identity (hs.differentiable (by simp))
  have hVis := viscosity_identity_of_curl ν (u t) (spatialCurl (u t)) hs
    (funext (hDiv t ht)) rfl
  let A : Field := fun x => cross (spatialCurl (u t) x) (u t x) +
    ν • spatialCurl (spatialCurl (u t)) x
  have hA : ContDiff ℝ ∞ A :=
    (cross_smooth (spatialCurl_smooth hs) hs).add
      ((spatialCurl_smooth (spatialCurl_smooth hs)).const_smul ν)
  have hsplit : timeDerivative u t + convection (u t) +
      NSEMaxwell.Classical.gradient (p t) - ν • NSEMaxwell.Classical.laplacian (u t) =
      ((timeDerivative u t + A) +
        NSEMaxwell.Classical.gradient (fun x : Vec => ‖u t x‖ ^ 2 / 2)) +
        NSEMaxwell.Classical.gradient (p t) := by
    rw [hL, hVis]
    change timeDerivative u t +
        ((fun x => cross (spatialCurl (u t) x) (u t x)) +
          NSEMaxwell.Classical.gradient (fun x : Vec => ‖u t x‖ ^ 2 / 2)) +
        NSEMaxwell.Classical.gradient (p t) - -(ν • spatialCurl (spatialCurl (u t))) = _
    change _ = ((timeDerivative u t +
      ((fun x => cross (spatialCurl (u t) x) (u t x)) +
        ν • spatialCurl (spatialCurl (u t)))) +
      NSEMaxwell.Classical.gradient (fun x : Vec => ‖u t x‖ ^ 2 / 2)) +
      NSEMaxwell.Classical.gradient (p t)
    abel
  rw [hsplit,
    spatialCurl_add (((hdt.add hA).add (gradient_smooth hK)).differentiable (by simp))
      ((gradient_smooth hps).differentiable (by simp)),
    spatialCurl_add ((hdt.add hA).differentiable (by simp))
      ((gradient_smooth hK).differentiable (by simp)),
    spatialCurl_add (hdt.differentiable (by simp)) (hA.differentiable (by simp)),
    spatialCurl_gradient hK, spatialCurl_gradient hps, add_zero, add_zero,
    ← timeDerivative_curl_commute hu ht]

end

end NSEMaxwell.LocalEvolution
