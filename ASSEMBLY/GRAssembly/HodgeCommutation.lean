import GRAssembly.HodgeBounds

/-! Mixed ordinary Fréchet derivatives of the actual periodic inverse. -/
set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Assembly
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators
noncomputable section

theorem poissonInverse_const_mul (c : ℝ) (f : ScalarField) :
    poissonInverse (fun x => c * f x) = fun x => c * poissonInverse f x := by
  funext x
  unfold poissonInverse
  simp_rw [show ∀ k y, cosineKernel k x y * (c * f y) =
    c * (cosineKernel k x y * f y) by intros; ring, integral_const_mul]
  simp_rw [show ∀ k, poissonSymbol k * (c * ∫ y in unitCube, cosineKernel k x y * f y) =
    c * (poissonSymbol k * ∫ y in unitCube, cosineKernel k x y * f y) by intros; ring]
  exact tsum_mul_left

theorem poissonInverse_add (f g : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hp : SpatialPeriodic f) (hq : SpatialPeriodic g) :
    poissonInverse (f + g) = poissonInverse f + poissonInverse g := by
  simp only [poissonInverse_eq_neg_scalarL,
    NSEMaxwell.HodgeProof.scalarL_add f g hf hg hp hq, neg_add]

theorem jointLinear_coordinate_expansion (L : (ℝ × Vec) →L[ℝ] ℝ) (d : ℝ × Vec) :
    L d = d.1 * L (1, 0) + ∑ j : Fin 3, d.2 j * L (0, unitVector j) := by
  have hd : d = d.1 • ((1 : ℝ), (0 : Vec)) +
      ∑ j : Fin 3, d.2 j • ((0 : ℝ), unitVector j) := by
    apply Prod.ext
    · simp
    · ext i
      simp [unitVector, Finset.sum_apply, EuclideanSpace.single_apply]
  calc
    _ = L (d.1 • ((1 : ℝ), (0 : Vec)) +
        ∑ j : Fin 3, d.2 j • ((0 : ℝ), unitVector j)) := congrArg L hd
    _ = _ := by simp

theorem joint_fderiv_time (F : ℝ × Vec → ℝ) (z : ℝ × Vec)
    (hF : DifferentiableAt ℝ F z) :
    deriv (fun t : ℝ => F (t, z.2)) z.1 = fderiv ℝ F z (1, 0) := by
  have hm : HasFDerivAt (fun t : ℝ => (t, z.2))
      ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] Vec)) z.1 :=
    (hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1)
  have h := hF.hasFDerivAt.comp z.1 hm
  simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.zero_apply] using h.hasDerivAt.deriv

theorem joint_fderiv_space (F : ℝ × Vec → ℝ) (z : ℝ × Vec)
    (hF : DifferentiableAt ℝ F z) (v : Vec) :
    fderiv ℝ (fun x : Vec => F (z.1, x)) z.2 v = fderiv ℝ F z (0, v) := by
  have hm : HasFDerivAt (fun x : Vec => (z.1, x))
      ((0 : Vec →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Vec)) z.2 :=
    (hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2)
  have h := hF.hasFDerivAt.comp z.2 hm
  simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.zero_apply] using congrArg (fun L : Vec →L[ℝ] ℝ => L v) h.fderiv

theorem joint_fderiv_smooth (F : ℝ × Vec → ℝ)
    (hF : ContDiff ℝ ∞ F) (d : ℝ × Vec) :
    ContDiff ℝ ∞ (fun z => fderiv ℝ F z d) :=
  (hF.fderiv_right (by simp)).clm_apply contDiff_const

theorem joint_fderiv_periodic (F : ℝ × Vec → ℝ)
    (hp : ∀ t, SpatialPeriodic (fun x => F (t, x))) (d : ℝ × Vec) (t : ℝ) :
    SpatialPeriodic (fun x => fderiv ℝ F (t, x) d) := by
  intro x i
  have he : (fun z : ℝ × Vec => F (z + (0, unitVector i))) = F := by
    funext z
    simpa only [Prod.fst_add, Prod.snd_add, add_zero] using hp z.1 z.2 i
  have h := congrArg (fun K : (ℝ × Vec → ℝ) => fderiv ℝ K (t, x)) he
  simp only [fderiv_comp_add_right] at h
  simpa only [Prod.mk_add_mk, add_zero] using
    congrArg (fun L : (ℝ × Vec) →L[ℝ] ℝ => L d) h

theorem poissonInverse_fderiv_commute_global (F : ℝ × Vec → ℝ)
    (hF : ContDiff ℝ ∞ F)
    (hp : ∀ t, SpatialPeriodic (fun x => F (t, x))) (z d : ℝ × Vec) :
    fderiv ℝ (fun w : ℝ × Vec => poissonInverse (fun y => F (w.1, y)) w.2) z d =
      poissonInverse (fun y => fderiv ℝ F (z.1, y) d) z.2 := by
  let H : ℝ × Vec → ℝ := fun w => poissonInverse (fun y => F (w.1, y)) w.2
  let T : ScalarField := fun y => fderiv ℝ F (z.1, y) (1, 0)
  let P : Fin 3 → ScalarField := fun j y => fderiv ℝ F (z.1, y) (0, unitVector j)
  have hH : ContDiff ℝ ∞ H := poissonInverse_joint_smooth_global (fun t x => F (t, x)) hF hp
  have hT : ContDiff ℝ ∞ T :=
    (joint_fderiv_smooth F hF (1, 0)).comp (contDiff_const.prodMk contDiff_id)
  have hP (j : Fin 3) : ContDiff ℝ ∞ (P j) :=
    (joint_fderiv_smooth F hF (0, unitVector j)).comp (contDiff_const.prodMk contDiff_id)
  have hpT : SpatialPeriodic T := joint_fderiv_periodic F hp (1, 0) z.1
  have hpP (j : Fin 3) : SpatialPeriodic (P j) :=
    joint_fderiv_periodic F hp (0, unitVector j) z.1
  have htime : fderiv ℝ H z (1, 0) = poissonInverse T z.2 := by
    rw [← joint_fderiv_time H z (hH.differentiable (by simp) z)]
    have h := (poissonInverse_hasDerivAt_global (fun t x => F (t, x)) hF hp z.1 z.2).deriv
    have he : scalarLocalTimeDerivative (fun t x => F (t, x)) z.1 = T := by
      funext y
      exact joint_fderiv_time F (z.1, y) (hF.differentiable (by simp) _)
    simpa only [he] using h
  have hspace (j : Fin 3) : fderiv ℝ H z (0, unitVector j) = poissonInverse (P j) z.2 := by
    rw [← joint_fderiv_space H z (hH.differentiable (by simp) z)]
    have hslice : ContDiff ℝ ∞ (fun y => F (z.1, y)) :=
      hF.comp (contDiff_const.prodMk contDiff_id)
    have h := congrFun (scalarPartial_poissonInverse_commute
      (fun y => F (z.1, y)) hslice (hp z.1) j) z.2
    have he : fourierScalarPartial (fun y => F (z.1, y)) j = P j := by
      funext y
      exact joint_fderiv_space F (z.1, y) (hF.differentiable (by simp) _) (unitVector j)
    simpa only [he] using h
  have he : (fun y => fderiv ℝ F (z.1, y) d) =
      (fun y => d.1 * T y) + (fun y => ∑ j : Fin 3, d.2 j * P j y) := by
    funext y
    exact jointLinear_coordinate_expansion (fderiv ℝ F (z.1, y)) d
  have hsum : ContDiff ℝ ∞ (fun y => ∑ j : Fin 3, d.2 j * P j y) :=
    ContDiff.sum (fun j _ => contDiff_const.mul (hP j))
  have hsumP : SpatialPeriodic (fun y => ∑ j : Fin 3, d.2 j * P j y) := by
    intro y i
    exact Finset.sum_congr rfl (fun j _ => congrArg (fun a => d.2 j * a) (hpP j y i))
  rw [he, poissonInverse_add _ _ (contDiff_const.mul hT) hsum
    (fun y i => congrArg (fun a => d.1 * a) (hpT y i)) hsumP,
    poissonInverse_const_mul, poissonInverse_finset_sum Finset.univ
      (fun j y => d.2 j * P j y) (fun j => contDiff_const.mul (hP j))
      (fun j y i => congrArg (fun a => d.2 j * a) (hpP j y i))]
  change fderiv ℝ H z d = _
  rw [jointLinear_coordinate_expansion, htime]
  simp only [Pi.add_apply, poissonInverse_const_mul, hspace]

theorem iteratedFDeriv_apply_smooth_global (F : ℝ × Vec → ℝ)
    (hF : ContDiff ℝ ∞ F) (n : ℕ) (v : Fin n → ℝ × Vec) :
    ContDiff ℝ ∞ (fun z => iteratedFDeriv ℝ n F z v) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => ℝ × Vec) ℝ v).contDiff.comp
    (hF.iteratedFDeriv_right (by simp))

theorem iteratedFDeriv_slice_periodic_global (F : ℝ × Vec → ℝ)
    (hp : ∀ t, SpatialPeriodic (fun x => F (t, x))) (n : ℕ)
    (v : Fin n → ℝ × Vec) (t : ℝ) :
    SpatialPeriodic (fun x => iteratedFDeriv ℝ n F (t, x) v) := by
  intro x i
  have he : (fun z : ℝ × Vec => F (z + (0, unitVector i))) = F := by
    funext z
    simpa only [Prod.fst_add, Prod.snd_add, add_zero] using hp z.1 z.2 i
  have h := congrArg (fun K : (ℝ × Vec → ℝ) => iteratedFDeriv ℝ n K (t, x)) he
  simp only [iteratedFDeriv_comp_add_right] at h
  simpa only [Prod.mk_add_mk, add_zero] using congrArg (fun L => L v) h

theorem poissonInverse_iteratedFDeriv_commute_global (F : ℝ × Vec → ℝ)
    (hF : ContDiff ℝ ∞ F)
    (hp : ∀ t, SpatialPeriodic (fun x => F (t, x))) (n : ℕ)
    (v : Fin n → ℝ × Vec) (z : ℝ × Vec) :
    iteratedFDeriv ℝ n
      (fun w : ℝ × Vec => poissonInverse (fun y => F (w.1, y)) w.2) z v =
      poissonInverse (fun y => iteratedFDeriv ℝ n F (z.1, y) v) z.2 := by
  let H : ℝ × Vec → ℝ := fun w => poissonInverse (fun y => F (w.1, y)) w.2
  have hH : ContDiff ℝ ∞ H := poissonInverse_joint_smooth_global (fun t x => F (t, x)) hF hp
  induction n generalizing v z with
  | zero => rfl
  | succ n ih =>
      have hFn : ContDiff ℝ ∞ (iteratedFDeriv ℝ n F) := hF.iteratedFDeriv_right (by simp)
      have hHn : ContDiff ℝ ∞ (iteratedFDeriv ℝ n H) := hH.iteratedFDeriv_right (by simp)
      rw [(hHn.differentiable (by simp) z).iteratedFDeriv_succ_apply_left']
      have he : (fun w => iteratedFDeriv ℝ n H w (Fin.tail v)) =
          (fun w : ℝ × Vec => poissonInverse
            (fun y => iteratedFDeriv ℝ n F (w.1, y) (Fin.tail v)) w.2) := by
        funext w
        exact ih (Fin.tail v) w
      rw [he, poissonInverse_fderiv_commute_global
        (fun w => iteratedFDeriv ℝ n F w (Fin.tail v))
        (iteratedFDeriv_apply_smooth_global F hF n (Fin.tail v))
        (iteratedFDeriv_slice_periodic_global F hp n (Fin.tail v)) z (v 0)]
      congr 1
      funext y
      exact ((hFn.differentiable (by simp) (z.1, y)).iteratedFDeriv_succ_apply_left').symm

/-- Full-slice equality near one time transports every joint derivative at
that time, uniformly in the spatial evaluation point. -/
theorem fullSlice_iteratedFDeriv_eq (f g : Pressure) {t : ℝ}
    (heq : f =ᶠ[𝓝 t] g) (n : ℕ) (v : Fin n → ℝ × Vec) (x : Vec) :
    iteratedFDeriv ℝ n (fun z : ℝ × Vec => f z.1 z.2) (t, x) v =
      iteratedFDeriv ℝ n (fun z : ℝ × Vec => g z.1 z.2) (t, x) v := by
  have he : (fun z : ℝ × Vec => f z.1 z.2) =ᶠ[𝓝 (t, x)]
      (fun z : ℝ × Vec => g z.1 z.2) := by
    filter_upwards [continuousAt_fst.tendsto.eventually heq] with z hz
    exact congrFun hz z.2
  exact congrArg (fun L => L v) (he.iteratedFDeriv ℝ n).self_of_nhds

theorem iteratedFDeriv_slice_smooth_periodic (f : Pressure) {I : Set ℝ}
    (hI : IsOpen I)
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => f z.1 z.2) {z | z.1 ∈ I})
    (hp : ∀ t ∈ I, SpatialPeriodic (f t)) {t : ℝ} (ht : t ∈ I)
    (n : ℕ) (v : Fin n → ℝ × Vec) :
    ContDiff ℝ ∞ (fun x => iteratedFDeriv ℝ n
      (fun z : ℝ × Vec => f z.1 z.2) (t, x) v) ∧
    SpatialPeriodic (fun x => iteratedFDeriv ℝ n
      (fun z : ℝ × Vec => f z.1 z.2) (t, x) v) := by
  obtain ⟨g, hg, hgp, heq⟩ := exists_smooth_periodic_extension f hI hf hp ht
  have he : (fun x => iteratedFDeriv ℝ n (fun z : ℝ × Vec => f z.1 z.2) (t, x) v) =
      (fun x => iteratedFDeriv ℝ n (fun z : ℝ × Vec => g z.1 z.2) (t, x) v) := by
    funext x
    exact fullSlice_iteratedFDeriv_eq f g heq.symm n v x
  rw [he]
  exact ⟨(iteratedFDeriv_apply_smooth_global (fun z : ℝ × Vec => g z.1 z.2) hg n v).comp
    (contDiff_const.prodMk contDiff_id),
    iteratedFDeriv_slice_periodic_global (fun z : ℝ × Vec => g z.1 z.2) hgp n v t⟩

theorem poissonInverse_iteratedFDeriv_commute (f : Pressure) {I : Set ℝ}
    (hI : IsOpen I)
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => f z.1 z.2) {z | z.1 ∈ I})
    (hp : ∀ t ∈ I, SpatialPeriodic (f t)) {t : ℝ} (ht : t ∈ I)
    (n : ℕ) (v : Fin n → ℝ × Vec) (x : Vec) :
    iteratedFDeriv ℝ n (fun z : ℝ × Vec => poissonInverse (f z.1) z.2) (t, x) v =
      poissonInverse (fun y => iteratedFDeriv ℝ n
        (fun z : ℝ × Vec => f z.1 z.2) (t, y) v) x := by
  obtain ⟨g, hg, hgp, heq⟩ := exists_smooth_periodic_extension f hI hf hp ht
  have hGeq : (fun s => poissonInverse (g s)) =ᶠ[𝓝 t] (fun s => poissonInverse (f s)) :=
    heq.mono (fun s hs => congrArg poissonInverse hs)
  rw [← fullSlice_iteratedFDeriv_eq _ _ hGeq n v x,
    poissonInverse_iteratedFDeriv_commute_global (fun z : ℝ × Vec => g z.1 z.2) hg hgp]
  congr 1
  funext y
  exact fullSlice_iteratedFDeriv_eq g f heq n v y

/-- Spatial directions are prepended without changing the original slots. -/
def prependSpatialDirections {n : ℕ} (j : Fin 3) :
    (m : ℕ) → (Fin n → ℝ × Vec) → (Fin (n + m) → ℝ × Vec)
  | 0, v => v
  | m + 1, v => Fin.cons (0, unitVector j) (prependSpatialDirections j m v)

theorem scalarSpatialIterate_iteratedFDeriv_global (F : ℝ × Vec → ℝ)
    (hF : ContDiff ℝ ∞ F) (n m : ℕ) (v : Fin n → ℝ × Vec)
    (j : Fin 3) (t : ℝ) :
    scalarSpatialIterate j m (fun x => iteratedFDeriv ℝ n F (t, x) v) =
      fun x => iteratedFDeriv ℝ (n + m) F (t, x) (prependSpatialDirections j m v) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [scalarSpatialIterate, ih]
      funext x
      have hFn : ContDiff ℝ ∞ (iteratedFDeriv ℝ (n + m) F) :=
        hF.iteratedFDeriv_right (by simp)
      have happ := iteratedFDeriv_apply_smooth_global F hF (n + m)
        (prependSpatialDirections j m v)
      change fderiv ℝ (fun y => iteratedFDeriv ℝ (n + m) F (t, y)
        (prependSpatialDirections j m v)) x (unitVector j) = _
      rw [joint_fderiv_space _ (t, x) (happ.differentiable (by simp) _) (unitVector j)]
      simpa only [Nat.add_succ, prependSpatialDirections, Fin.cons_zero, Fin.tail_cons] using
        ((hFn.differentiable (by simp) (t, x)).iteratedFDeriv_succ_apply_left'
          (m := Fin.cons (0, unitVector j) (prependSpatialDirections j m v))).symm

theorem prependSpatialDirections_norm_prod {n : ℕ} (j : Fin 3) (m : ℕ)
    (v : Fin n → ℝ × Vec) :
    (∏ i : Fin (n + m), ‖prependSpatialDirections j m v i‖) = ∏ i : Fin n, ‖v i‖ := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simpa [Nat.add_succ, prependSpatialDirections, Fin.prod_univ_succ,
        Prod.norm_def, unitVector, PiLp.norm_single] using ih

theorem scalarSpatialIterate_iteratedFDeriv (f : Pressure) {I : Set ℝ}
    (hI : IsOpen I)
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => f z.1 z.2) {z | z.1 ∈ I})
    (hp : ∀ t ∈ I, SpatialPeriodic (f t)) {t : ℝ} (ht : t ∈ I)
    (n m : ℕ) (v : Fin n → ℝ × Vec) (j : Fin 3) :
    scalarSpatialIterate j m
      (fun x => iteratedFDeriv ℝ n (fun z : ℝ × Vec => f z.1 z.2) (t, x) v) =
    fun x => iteratedFDeriv ℝ (n + m) (fun z : ℝ × Vec => f z.1 z.2) (t, x)
      (prependSpatialDirections j m v) := by
  obtain ⟨g, hg, hgp, heq⟩ := exists_smooth_periodic_extension f hI hf hp ht
  have he (k : ℕ) (w : Fin k → ℝ × Vec) :
      (fun x => iteratedFDeriv ℝ k (fun z : ℝ × Vec => f z.1 z.2) (t, x) w) =
      (fun x => iteratedFDeriv ℝ k (fun z : ℝ × Vec => g z.1 z.2) (t, x) w) := by
    funext x
    exact fullSlice_iteratedFDeriv_eq f g heq.symm k w x
  rw [he n v, he (n + m) (prependSpatialDirections j m v)]
  exact scalarSpatialIterate_iteratedFDeriv_global (fun z : ℝ × Vec => g z.1 z.2)
    hg n m v j t

end
end NSEGR.Assembly
