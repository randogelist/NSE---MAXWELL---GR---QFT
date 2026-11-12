import NSEMaxwell.CurlCurl

/-!
# Differential calculus on the closed forward spacetime domain

All derivatives are the derivatives fixed in `Classical.lean`. The half-space
has unique derivatives, and every boundary point belongs to the closure of its
interior. Consequently the second within derivative is symmetric at t = 0 as
well as at positive times. No extension of the velocity to negative times is
assumed.
-/

set_option autoImplicit false

namespace NSEMaxwell.Spacetime

open NSEMaxwell.Classical Set Filter
open scoped ContDiff Topology

noncomputable section

theorem forwardSpacetime_eq_prod :
    forwardSpacetime = Ici (0 : ℝ) ×ˢ (univ : Set Vec) := by
  ext z
  simp [forwardSpacetime]

theorem uniqueDiffOn_forwardSpacetime : UniqueDiffOn ℝ forwardSpacetime := by
  rw [forwardSpacetime_eq_prod]
  exact (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ

theorem closure_interior_forwardSpacetime :
    closure (interior forwardSpacetime) = forwardSpacetime := by
  rw [forwardSpacetime_eq_prod, interior_prod_eq, closure_prod_eq]
  simp

section GeneralCodomain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Spatial restriction of the genuine within Frechet derivative. -/
theorem spatial_restriction_fderiv
    {f : ℝ × Vec → E} (hf : ContDiffOn ℝ ∞ f forwardSpacetime)
    {t : ℝ} (ht : 0 ≤ t) (x v : Vec) :
    fderiv ℝ (fun y : Vec => f (t, y)) x v =
      fderivWithin ℝ f forwardSpacetime (t, x) (0, v) := by
  have hd := (hf.differentiableOn (by simp) (t, x) ht).hasFDerivWithinAt
  have he := (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have hc := hd.comp_hasFDerivAt x he (Filter.Eventually.of_forall (fun _ => ht))
  have hv := congrArg (fun L : Vec →L[ℝ] E => L v) hc.fderiv
  simpa [Function.comp_def] using hv

/-- One-sided temporal derivative obtained by restriction of the same derivative. -/
theorem time_restriction_hasDerivWithinAt
    {f : ℝ × Vec → E} (hf : ContDiffOn ℝ ∞ f forwardSpacetime)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    HasDerivWithinAt (fun s : ℝ => f (s, x))
      (fderivWithin ℝ f forwardSpacetime (t, x) (1, 0)) (Ici 0) t := by
  have hd := (hf.differentiableOn (by simp) (t, x) ht).hasFDerivWithinAt
  have he := ((hasDerivAt_id t).prodMk (hasDerivAt_const t x)).hasDerivWithinAt
  exact hd.comp_hasDerivWithinAt t he (fun _ hs => hs)

theorem time_restriction_derivWithin
    {f : ℝ × Vec → E} (hf : ContDiffOn ℝ ∞ f forwardSpacetime)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    derivWithin (fun s : ℝ => f (s, x)) (Ici 0) t =
      fderivWithin ℝ f forwardSpacetime (t, x) (1, 0) :=
  (time_restriction_hasDerivWithinAt hf ht x).derivWithin
    (uniqueDiffOn_Ici 0 t ht)

theorem directional_smooth
    {f : ℝ × Vec → E} (hf : ContDiffOn ℝ ∞ f forwardSpacetime)
    (v : ℝ × Vec) :
    ContDiffOn ℝ ∞ (fun z => fderivWithin ℝ f forwardSpacetime z v)
      forwardSpacetime := by
  exact (hf.fderivWithin uniqueDiffOn_forwardSpacetime (by simp)).clm_apply
    contDiffOn_const

theorem directional_fderivWithin_apply
    {f : ℝ × Vec → E} (hf : ContDiffOn ℝ ∞ f forwardSpacetime)
    {z : ℝ × Vec} (hz : z ∈ forwardSpacetime) (v w : ℝ × Vec) :
    fderivWithin ℝ (fun y => fderivWithin ℝ f forwardSpacetime y v)
        forwardSpacetime z w =
      fderivWithin ℝ (fderivWithin ℝ f forwardSpacetime)
        forwardSpacetime z w v := by
  have hd := ((hf.fderivWithin uniqueDiffOn_forwardSpacetime (by simp)).differentiableOn
    (by simp) z hz).hasFDerivWithinAt
  have hc := hd.clm_apply (hasFDerivWithinAt_const v z forwardSpacetime)
  have he := congrArg (fun L : (ℝ × Vec) →L[ℝ] E => L w)
    (hc.fderivWithin (uniqueDiffOn_forwardSpacetime z hz))
  simpa [ContinuousLinearMap.flip_apply] using he

end GeneralCodomain

theorem time_slice_hasDerivWithinAt
    {u : Velocity} (hu : SmoothVelocity u) {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    HasDerivWithinAt (fun s : ℝ => u s x) (timeDerivative u t x) (Ici 0) t := by
  have h := time_restriction_hasDerivWithinAt hu ht x
  rw [← time_restriction_derivWithin hu ht x] at h
  exact h

theorem coordinateDerivative_eq_joint
    {u : Velocity} (hu : SmoothVelocity u) {t : ℝ} (ht : 0 ≤ t)
    (i : Fin 3) (x : Vec) :
    coordinateDerivative (u t) i x =
      fderivWithin ℝ (fun z : ℝ × Vec => u z.1 z.2)
        forwardSpacetime (t, x) (0, unitVector i) :=
  spatial_restriction_fderiv hu ht x (unitVector i)

theorem coordinateDerivative_trajectory_smooth
    {u : Velocity} (hu : SmoothVelocity u) (i : Fin 3) :
    SmoothVelocity (fun t => coordinateDerivative (u t) i) := by
  apply (directional_smooth hu (0, unitVector i)).congr
  intro z hz
  exact coordinateDerivative_eq_joint hu hz i z.2

theorem timeDerivative_smooth
    {u : Velocity} (hu : SmoothVelocity u) :
    SmoothVelocity (fun t => timeDerivative u t) := by
  apply (directional_smooth hu (1, 0)).congr
  intro z hz
  exact time_restriction_derivWithin hu hz z.2

theorem curl_trajectory_smooth
    {u : Velocity} (hu : SmoothVelocity u) :
    SmoothVelocity (fun t => spatialCurl (u t)) := by
  apply (contDiffOn_piLp 2).mpr
  intro i
  have hc (j k : Fin 3) :
      ContDiffOn ℝ ∞ (fun z : ℝ × Vec => coordinateDerivative (u z.1) j z.2 k)
        forwardSpacetime :=
    (contDiffOn_piLp 2).mp (coordinateDerivative_trajectory_smooth hu j) k
  fin_cases i
  · simpa [spatialCurl, PiLp.toLp_apply] using (hc 1 2).sub (hc 2 1)
  · simpa [spatialCurl, PiLp.toLp_apply] using (hc 2 0).sub (hc 0 2)
  · simpa [spatialCurl, PiLp.toLp_apply] using (hc 0 1).sub (hc 1 0)

/-- Mixed partials commute on the entire closed half-space. -/
theorem timeDerivative_coordinateDerivative
    {u : Velocity} (hu : SmoothVelocity u) {t : ℝ} (ht : 0 ≤ t)
    (i : Fin 3) :
    timeDerivative (fun s => coordinateDerivative (u s) i) t =
      coordinateDerivative (timeDerivative u t) i := by
  let f : ℝ × Vec → Vec := fun z => u z.1 z.2
  let d (v : ℝ × Vec) : ℝ × Vec → Vec :=
    fun z => fderivWithin ℝ f forwardSpacetime z v
  have hf : ContDiffOn ℝ ∞ f forwardSpacetime := hu
  have hd (v : ℝ × Vec) : ContDiffOn ℝ ∞ (d v) forwardSpacetime :=
    directional_smooth hf v
  funext x
  have hleft :
      timeDerivative (fun s => coordinateDerivative (u s) i) t x =
        derivWithin (fun s : ℝ => d (0, unitVector i) (s, x)) (Ici 0) t := by
    apply derivWithin_congr
    · intro s hs
      exact coordinateDerivative_eq_joint hu hs i x
    · exact coordinateDerivative_eq_joint hu ht i x
  have hright : timeDerivative u t = fun y => d (1, 0) (t, y) := by
    funext y
    exact time_restriction_derivWithin hf ht y
  rw [hleft, hright]
  change derivWithin (fun s : ℝ => d (0, unitVector i) (s, x)) (Ici 0) t =
    fderiv ℝ (fun y : Vec => d (1, 0) (t, y)) x (unitVector i)
  rw [time_restriction_derivWithin (hd (0, unitVector i)) ht x,
    spatial_restriction_fderiv (hd (1, 0)) ht x (unitVector i)]
  rw [directional_fderivWithin_apply hf ht (0, unitVector i) (1, 0),
    directional_fderivWithin_apply hf ht (1, 0) (0, unitVector i)]
  exact (hf (t, x) ht).isSymmSndFDerivWithinAt
    (by simp only [minSmoothness_of_isRCLikeNormedField]; decide)
    uniqueDiffOn_forwardSpacetime
    (by rw [closure_interior_forwardSpacetime]; exact ht) ht
    (1, 0) (0, unitVector i)

theorem time_component_hasDerivWithinAt
    {u : Velocity} (hu : SmoothVelocity u) {t : ℝ} (ht : 0 ≤ t)
    (x : Vec) (i : Fin 3) :
    HasDerivWithinAt (fun s : ℝ => u s x i) (timeDerivative u t x i) (Ici 0) t := by
  exact (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (u t x) i).comp_hasDerivWithinAt t
    (time_slice_hasDerivWithinAt hu ht x)

theorem timeDerivative_component
    {u : Velocity} (hu : SmoothVelocity u) {t : ℝ} (ht : 0 ≤ t)
    (x : Vec) (i : Fin 3) :
    derivWithin (fun s : ℝ => u s x i) (Ici 0) t = timeDerivative u t x i :=
  (time_component_hasDerivWithinAt hu ht x i).derivWithin (uniqueDiffOn_Ici 0 t ht)

/-- Curl commutes with the specified right time derivative, including t = 0. -/
theorem timeDerivative_curl_commute
    {u : Velocity} (hu : SmoothVelocity u) {t : ℝ} (ht : 0 ≤ t) :
    timeDerivative (fun s => spatialCurl (u s)) t = spatialCurl (timeDerivative u t) := by
  have hd (j k : Fin 3) (x : Vec) :=
    time_component_hasDerivWithinAt (coordinateDerivative_trajectory_smooth hu j) ht x k
  have hs (j k l r : Fin 3) (x : Vec) :
      derivWithin (fun s : ℝ => coordinateDerivative (u s) j x k -
        coordinateDerivative (u s) l x r) (Ici 0) t =
      coordinateDerivative (timeDerivative u t) j x k -
        coordinateDerivative (timeDerivative u t) l x r := by
    have h := ((hd j k x).sub (hd l r x)).derivWithin (uniqueDiffOn_Ici 0 t ht)
    simpa only [timeDerivative_coordinateDerivative hu ht] using h
  funext x
  apply PiLp.ext
  intro i
  rw [← timeDerivative_component (curl_trajectory_smooth hu) ht x i]
  fin_cases i
  · simpa [spatialCurl, PiLp.toLp_apply] using hs 1 2 2 1 x
  · simpa [spatialCurl, PiLp.toLp_apply] using hs 2 0 0 2 x
  · simpa [spatialCurl, PiLp.toLp_apply] using hs 0 1 1 0 x

theorem timeDerivative_periodic
    {u : Velocity} (hu : PeriodicVelocity u) :
    PeriodicVelocity (fun t => timeDerivative u t) := by
  intro t ht x i
  apply derivWithin_congr
  · intro s hs
    exact hu s hs x i
  · exact hu t ht x i

/-- Incompressibility is preserved by the actual right time derivative. -/
theorem timeDerivative_divergence_zero
    {u : Velocity} (hu : SmoothVelocity u)
    (hDiv : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec, NSEMaxwell.Classical.divergence (u t) x = 0)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    NSEMaxwell.Classical.divergence (timeDerivative u t) x = 0 := by
  have hd (i : Fin 3) :
      HasDerivWithinAt (fun s : ℝ => coordinateDerivative (u s) i x i)
        (coordinateDerivative (timeDerivative u t) i x i) (Ici 0) t := by
    have h := time_component_hasDerivWithinAt
      (coordinateDerivative_trajectory_smooth hu i) ht x i
    simpa only [timeDerivative_coordinateDerivative hu ht] using h
  have hsum := ((hd 0).add (hd 1)).add (hd 2)
  have hzero : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ))
      (coordinateDerivative (timeDerivative u t) 0 x 0 +
        coordinateDerivative (timeDerivative u t) 1 x 1 +
        coordinateDerivative (timeDerivative u t) 2 x 2) (Ici 0) t := by
    apply hsum.congr_of_mem
    · intro s hs
      have h := hDiv s hs x
      simpa [NSEMaxwell.Classical.divergence, Fin.sum_univ_succ, add_assoc] using h.symm
    · exact ht
  have he := hzero.derivWithin (uniqueDiffOn_Ici 0 t ht)
  simpa [NSEMaxwell.Classical.divergence, Fin.sum_univ_succ, add_assoc] using he.symm

end

end NSEMaxwell.Spacetime
