import FourierHodgeLaws.ParameterIntegral
import FourierHodgeLaws.TargetPrimitives

/-!
Actual cube-integral coefficient derivatives on the closed time half-line.
All parameter derivatives are within derivatives; no negative-time extension
is assumed. The generic integral lemmas apply in particular to complex values.
-/

set_option autoImplicit false

namespace NSEMaxwell.HodgeProof

open NSEMaxwell.Classical NSEMaxwell.Spacetime NSEMaxwell.PeriodicIntegration
open Set Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

section GenericIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def cubeTimeDerivative (F : ℝ → Vec → E) (t : ℝ) (x : Vec) : E :=
  derivWithin (fun s : ℝ => F s x) (Ici (0 : ℝ)) t

theorem cubeSlice_contDiff (F : ℝ → Vec → E)
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => F z.1 z.2) forwardSpacetime)
    {t : ℝ} (ht : 0 ≤ t) : ContDiff ℝ ∞ (F t) := by
  have hslice : ContDiff ℝ ∞ (fun x : Vec => (t, x)) :=
    contDiff_const.prodMk contDiff_id
  simpa only [Function.comp_def] using hF.comp_contDiff hslice (fun _ => ht)

theorem cubeTimeDerivative_smooth (F : ℝ → Vec → E)
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => F z.1 z.2) forwardSpacetime) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => cubeTimeDerivative F z.1 z.2)
      forwardSpacetime := by
  apply (directional_smooth hF (1, 0)).congr
  intro z hz
  exact time_restriction_derivWithin hF hz z.2

theorem cubeTime_hasDerivWithinAt (F : ℝ → Vec → E)
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => F z.1 z.2) forwardSpacetime)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    HasDerivWithinAt (fun s : ℝ => F s x) (cubeTimeDerivative F t x) (Ici 0) t := by
  have h := time_restriction_hasDerivWithinAt hF ht x
  rw [← time_restriction_derivWithin hF ht x] at h
  exact h

theorem cubeIntegral_local_uniform_time_bound (F : ℝ → Vec → E)
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => F z.1 z.2) forwardSpacetime)
    {t : ℝ} (ht : 0 ≤ t) :
    ∃ C : ℝ, IntegrableOn (fun _ : Vec => C) unitCube ∧
      ∀ᶠ s in 𝓝[Ici (0 : ℝ)] t, ∀ x ∈ unitCube,
        ‖F s x - F t x‖ ≤ C * ‖s - t‖ := by
  have hcompact : IsCompact (Icc (0 : ℝ) (t + 1) ×ˢ unitCube) :=
    isCompact_Icc.prod isCompact_unitCube
  have hsub : Icc (0 : ℝ) (t + 1) ×ˢ unitCube ⊆ forwardSpacetime := by
    intro z hz
    exact hz.1.1
  have hcont : ContinuousOn (fun z : ℝ × Vec => cubeTimeDerivative F z.1 z.2)
      (Icc (0 : ℝ) (t + 1) ×ˢ unitCube) :=
    (cubeTimeDerivative_smooth F hF).continuousOn.mono hsub
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hcont
  refine ⟨C, integrableOn_unitCube_of_continuous continuous_const, ?_⟩
  have hupper_nhds : ∀ᶠ s in 𝓝 t, s < t + 1 := Iio_mem_nhds (lt_add_one t)
  have hupper : ∀ᶠ s in 𝓝[Ici (0 : ℝ)] t, s < t + 1 :=
    hupper_nhds.filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, hupper] with s hs hsu
  intro x hx
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun r : ℝ => F r x) (f' := fun r : ℝ => cubeTimeDerivative F r x)
    (s := Icc (0 : ℝ) (t + 1)) (C := C)
    (fun r hr => (cubeTime_hasDerivWithinAt F hF hr.1 x).mono
      (fun q hq => hq.1))
    (fun r hr => hC (r, x) ⟨hr, hx⟩)
    (convex_Icc (0 : ℝ) (t + 1))
    (show t ∈ Icc (0 : ℝ) (t + 1) from ⟨ht, le_add_of_nonneg_right zero_le_one⟩)
    (show s ∈ Icc (0 : ℝ) (t + 1) from ⟨hs, hsu.le⟩)

theorem cubeIntegral_hasDerivWithinAt (F : ℝ → Vec → E)
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => F z.1 z.2) forwardSpacetime)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => ∫ x in unitCube, F s x)
      (∫ x in unitCube, cubeTimeDerivative F t x) (Ici (0 : ℝ)) t := by
  obtain ⟨C, hCint, hC⟩ := cubeIntegral_local_uniform_time_bound F hF ht
  have hFi : ∀ᶠ s in 𝓝[Ici (0 : ℝ)] t, IntegrableOn (F s) unitCube := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact integrableOn_unitCube_of_continuous (cubeSlice_contDiff F hF hs).continuous
  have hF0 : IntegrableOn (F t) unitCube :=
    integrableOn_unitCube_of_continuous (cubeSlice_contDiff F hF ht).continuous
  have hFd : IntegrableOn (cubeTimeDerivative F t) unitCube :=
    integrableOn_unitCube_of_continuous
      (cubeSlice_contDiff _ (cubeTimeDerivative_smooth F hF) ht).continuous
  have hb : ∀ᶠ s in 𝓝[Ici (0 : ℝ)] t,
      ∀ᵐ x ∂volume.restrict unitCube, ‖F s x - F t x‖ ≤ C * ‖s - t‖ := by
    filter_upwards [hC] with s hs
    exact (ae_restrict_mem isCompact_unitCube.isClosed.measurableSet).mono
      (fun x hx => hs x hx)
  exact NSEMaxwell.DominatedWithin.hasDerivWithinAt_integral_of_dominated
    hFi hF0 hFd hb hCint
    (Filter.Eventually.of_forall (fun x => cubeTime_hasDerivWithinAt F hF ht x))

theorem cubeIntegral_derivWithin (F : ℝ → Vec → E)
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => F z.1 z.2) forwardSpacetime)
    {t : ℝ} (ht : 0 ≤ t) :
    derivWithin (fun s : ℝ => ∫ x in unitCube, F s x) (Ici (0 : ℝ)) t =
      ∫ x in unitCube, cubeTimeDerivative F t x :=
  (cubeIntegral_hasDerivWithinAt F hF ht).derivWithin (uniqueDiffOn_Ici 0 t ht)

theorem cubeIntegral_contDiffOn_nat (n : ℕ) (F : ℝ → Vec → E)
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => F z.1 z.2) forwardSpacetime) :
    ContDiffOn ℝ n (fun t : ℝ => ∫ x in unitCube, F t x) (Ici (0 : ℝ)) := by
  induction n generalizing F with
  | zero =>
      apply contDiffOn_zero.mpr
      intro t ht
      exact (cubeIntegral_hasDerivWithinAt F hF ht).continuousWithinAt
  | succ n ih =>
      simp only [Nat.cast_add, Nat.cast_one]
      rw [contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)]
      refine ⟨?_, by simp, ?_⟩
      · intro t ht
        exact (cubeIntegral_hasDerivWithinAt F hF ht).differentiableWithinAt
      · apply (ih (cubeTimeDerivative F) (cubeTimeDerivative_smooth F hF)).congr
        intro t ht
        exact cubeIntegral_derivWithin F hF ht

theorem cubeIntegral_contDiffOn (F : ℝ → Vec → E)
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => F z.1 z.2) forwardSpacetime) :
    ContDiffOn ℝ ∞ (fun t : ℝ => ∫ x in unitCube, F t x) (Ici (0 : ℝ)) := by
  rw [contDiffOn_infty]
  intro n
  exact cubeIntegral_contDiffOn_nat n F hF

end GenericIntegral

theorem scalarTimeDerivative_smooth {f : Pressure} (hf : SmoothPressure f) :
    SmoothPressure (fun t => scalarTimeDerivative f t) :=
  cubeTimeDerivative_smooth f hf

theorem scalarTimeDerivative_periodic {f : Pressure} (hp : PeriodicPressure f) :
    PeriodicPressure (fun t => scalarTimeDerivative f t) := by
  intro t ht x i
  apply derivWithin_congr
  · intro s hs
    exact hp s hs x i
  · exact hp t ht x i

theorem scalarSpatialDerivative_smooth {f : Pressure} (hf : SmoothPressure f)
    (j : Fin 3) :
    SmoothPressure (fun t x => fderiv ℝ (f t) x (unitVector j)) := by
  apply (directional_smooth hf (0, unitVector j)).congr
  intro z hz
  exact spatial_restriction_fderiv hf hz z.2 (unitVector j)

theorem scalarSpatialDerivative_periodic {f : Pressure} (hp : PeriodicPressure f)
    (j : Fin 3) :
    PeriodicPressure (fun t x => fderiv ℝ (f t) x (unitVector j)) := by
  intro t ht x i
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L (unitVector j)) (fderiv_periodic (hp t ht) x i)

theorem scalarCoeff_integrand_smooth (f : Pressure) (hf : SmoothPressure f)
    (k : Frequency) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec =>
      star (SingularClosure.fourierCharacter k z.2) * (f z.1 z.2 : ℂ))
      forwardSpacetime := by
  have hc : ContDiffOn ℝ ∞ (fun z : ℝ × Vec =>
      star (SingularClosure.fourierCharacter k z.2)) forwardSpacetime := by
    simpa only [Function.comp_def, SingularClosure.fourierCharacter_neg] using
      (SingularClosure.fourierCharacter_contDiff (-k)).comp_contDiffOn
        (contDiffOn_snd : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => z.2) forwardSpacetime)
  exact hc.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hf)

theorem scalarCoeff_contDiffOn (f : Pressure) (hf : SmoothPressure f) (k : Frequency) :
    ContDiffOn ℝ ∞ (fun t : ℝ => scalarCoeff (f t) k) (Ici (0 : ℝ)) :=
  cubeIntegral_contDiffOn _ (scalarCoeff_integrand_smooth f hf k)

theorem scalarCoeff_hasDerivWithinAt (f : Pressure) (hf : SmoothPressure f)
    (k : Frequency) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => scalarCoeff (f s) k)
      (scalarCoeff (scalarTimeDerivative f t) k) (Ici (0 : ℝ)) t := by
  have h := cubeIntegral_hasDerivWithinAt
    (fun (s : ℝ) (x : Vec) => star (SingularClosure.fourierCharacter k x) * (f s x : ℂ))
    (scalarCoeff_integrand_smooth f hf k) ht
  have he : cubeTimeDerivative
      (fun s x => star (SingularClosure.fourierCharacter k x) * (f s x : ℂ)) t =
      fun x => star (SingularClosure.fourierCharacter k x) *
        (scalarTimeDerivative f t x : ℂ) := by
    funext x
    have hr : HasDerivWithinAt (fun s : ℝ => f s x)
        (scalarTimeDerivative f t x) (Ici (0 : ℝ)) t :=
      cubeTime_hasDerivWithinAt f hf ht x
    have hc := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivWithinAt t hr
    have hm := hc.const_mul (star (SingularClosure.fourierCharacter k x))
    exact hm.derivWithin (uniqueDiffOn_Ici 0 t ht)
  rw [he] at h
  exact h

theorem scalarCoeff_derivWithin (f : Pressure) (hf : SmoothPressure f)
    (k : Frequency) {t : ℝ} (ht : 0 ≤ t) :
    derivWithin (fun s : ℝ => scalarCoeff (f s) k) (Ici (0 : ℝ)) t =
      scalarCoeff (scalarTimeDerivative f t) k :=
  (scalarCoeff_hasDerivWithinAt f hf k ht).derivWithin (uniqueDiffOn_Ici 0 t ht)

theorem scalarCoeff_hasDerivAt_pos (f : Pressure) (hf : SmoothPressure f)
    (k : Frequency) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => scalarCoeff (f s) k)
      (scalarCoeff (scalarTimeDerivative f t) k) t :=
  (scalarCoeff_hasDerivWithinAt f hf k ht.le).hasDerivAt (Ici_mem_nhds ht)

theorem scalarCoeff_trajectory_smooth (f : Pressure) (hf : SmoothPressure f)
    (k : Frequency) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => scalarCoeff (f z.1) k)
      forwardSpacetime :=
  (scalarCoeff_contDiffOn f hf k).comp contDiffOn_fst (fun _ hz => hz)

theorem datumFourierCoeff_contDiffOn (u : Velocity) (hu : SmoothVelocity u)
    (k : Frequency) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun t : ℝ => SingularClosure.datumFourierCoeff (u t) k i)
      (Ici (0 : ℝ)) :=
  scalarCoeff_contDiffOn (fun t x => u t x i) ((contDiffOn_piLp 2).mp hu i) k

theorem datumFourierCoeff_hasDerivWithinAt (u : Velocity) (hu : SmoothVelocity u)
    (k : Frequency) (i : Fin 3) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => SingularClosure.datumFourierCoeff (u s) k i)
      (SingularClosure.datumFourierCoeff (timeDerivative u t) k i)
      (Ici (0 : ℝ)) t := by
  have h := scalarCoeff_hasDerivWithinAt (fun s x => u s x i)
    ((contDiffOn_piLp 2).mp hu i) k ht
  have he : scalarTimeDerivative (fun s x => u s x i) t =
      fun x => timeDerivative u t x i := by
    funext x
    exact timeDerivative_component hu ht x i
  rw [he] at h
  exact h

end

end NSEMaxwell.HodgeProof
