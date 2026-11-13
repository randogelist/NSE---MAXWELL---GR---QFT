import GRAssembly.NativeCalculus
import GRAdapter.Contracts

/-! Actual scalar correction conservation and boundary admissibility. -/
set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
namespace NSEGR.Assembly
noncomputable section

theorem jointSpace_isotropic_sum {f : ℝ × Vec → ℝ} {z : ℝ × Vec}
    (j : Fin 3) :
    (∑ i : Fin 3, jointSpace (fun y => f y * identity3 i j) i z) = jointSpace f j z := by
  rw [Finset.sum_eq_single j]
  · simp only [identity3, ite_true, mul_one]
  · intro i hi hij
    simp [identity3, hij, jointSpace]
  · simp

theorem jointSpace_hessian_divergence {f : ℝ × Vec → ℝ} {z : ℝ × Vec}
    (hf : AnalyticAt ℝ f z) (j : Fin 3) :
    (∑ i : Fin 3, jointSpace (jointSpace (jointSpace f j) i) i z) =
      jointSpace (fun y => ∑ i : Fin 3, jointSpace (jointSpace f i) i y) j z := by
  rw [jointSpace_sum _ (fun i _ => analyticAt_jointSpace (analyticAt_jointSpace hf i) i)]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = jointSpace (jointSpace (jointSpace f i) j) i z := by
      apply jointSpace_congr
      filter_upwards [hf.eventually_analyticAt] with y hy
      exact jointSpace_jointSpace hy j i
    _ = _ := jointSpace_jointSpace (analyticAt_jointSpace hf i) j i

theorem scalarCompletionUpper_conserved {ψ : Pressure} {t : ℝ} {x : Vec}
    (hψ : AnalyticAt ℝ (fun z : ℝ × Vec => ψ z.1 z.2) (t, x)) :
    ∀ b, upperDivergence (scalarCompletionUpper ψ) t x b = 0 := by
  let f : ℝ × Vec → ℝ := fun z => ψ z.1 z.2
  let L : ℝ × Vec → ℝ := fun z => ∑ i : Fin 3, jointSpace (jointSpace f i) i z
  have hT := analyticAt_jointTime hψ
  have hTT := analyticAt_jointTime hT
  have hL : AnalyticAt ℝ L (t, x) :=
    analyticAt_fin3_sum (fun i => analyticAt_jointSpace (analyticAt_jointSpace hψ i) i)
  intro b
  refine Fin.cases ?_ (fun j => ?_) b
  · rw [upperDivergence, Fin.sum_univ_succ]
    simp only [boundaryPartial, scalarCompletionUpper, boundaryBlock,
      Fin.cases_zero, Fin.cases_succ]
    change scalarLocalTimeDerivative (fun s => scalarLaplacian (ψ s)) t x +
      (∑ i : Fin 3, fderiv ℝ (fun y => -fderiv ℝ (scalarLocalTimeDerivative ψ t)
        y (unitVector i)) x (unitVector i)) = 0
    rw [scalar_time_laplacian_commute hψ]
    simp only [fderiv_fun_neg, ContinuousLinearMap.neg_apply, Finset.sum_neg_distrib,
      scalarLaplacian, add_neg_cancel]
  · rw [upperDivergence, Fin.sum_univ_succ]
    simp only [boundaryPartial, scalarCompletionUpper, boundaryBlock,
      Fin.cases_zero, Fin.cases_succ]
    change jointTime (fun y => -jointSpace (jointTime f) j y) (t, x) +
      (∑ i : Fin 3, jointSpace (fun y => jointSpace (jointSpace f j) i y +
        (jointTime (jointTime f) y - L y) * identity3 i j) i (t, x)) = 0
    rw [jointTime_neg, jointTime_jointSpace hT j]
    have hadd (i : Fin 3) :
        jointSpace (fun y => jointSpace (jointSpace f j) i y +
          (jointTime (jointTime f) y - L y) * identity3 i j) i (t,x) =
        jointSpace (jointSpace (jointSpace f j) i) i (t,x) +
          jointSpace (fun y => (jointTime (jointTime f) y - L y) * identity3 i j) i (t,x) :=
      jointSpace_add (f := jointSpace (jointSpace f j) i)
        (g := fun y => (jointTime (jointTime f) y - L y) * identity3 i j)
        (analyticAt_jointSpace (analyticAt_jointSpace hψ j) i)
        ((hTT.sub hL).mul (show AnalyticAt ℝ (fun _ : ℝ × Vec => identity3 i j) (t,x)
          from analyticAt_const)) i
    have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun i _ => hadd i)
    rw [hsum, Finset.sum_add_distrib, jointSpace_hessian_divergence hψ j,
      jointSpace_isotropic_sum j, jointSpace_sub hTT hL j]
    change -jointSpace (jointTime (jointTime f)) j (t,x) +
      (jointSpace L j (t,x) + (jointSpace (jointTime (jointTime f)) j (t,x) -
        jointSpace L j (t,x))) = 0
    ring

theorem analyticAt_conservedSourceUpper_entry {ν ρ : ℝ} {u : Velocity} {p : Pressure}
    {z : ℝ × Vec}
    (hu : AnalyticAt ℝ (fun y : ℝ × Vec => u y.1 y.2) z)
    (hp : AnalyticAt ℝ (fun y : ℝ × Vec => p y.1 y.2) z) (a b : Fin 4) :
    AnalyticAt ℝ (fun y : ℝ × Vec => conservedSourceUpper ν ρ u p y.1 y.2 a b) z := by
  refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b
  · exact analyticAt_const
  · exact ((EuclideanSpace.proj j).analyticAt _).comp hu
  · exact ((EuclideanSpace.proj i).analyticAt _).comp hu
  · exact analyticAt_nseSpatialSource3_components hu hp i j

theorem analyticAt_scalarCompletionUpper_entry {ψ : Pressure} {z : ℝ × Vec}
    (hψ : AnalyticAt ℝ (fun y : ℝ × Vec => ψ y.1 y.2) z) (a b : Fin 4) :
    AnalyticAt ℝ (fun y : ℝ × Vec => scalarCompletionUpper ψ y.1 y.2 a b) z := by
  have hT := analyticAt_jointTime hψ
  have hTT := analyticAt_jointTime hT
  have hL := analyticAt_scalarLaplacian_joint hψ
  refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b
  · exact hL
  · exact (analyticAt_jointSpace hT j).neg
  · exact (analyticAt_jointSpace hT i).neg
  · exact (analyticAt_jointSpace (analyticAt_jointSpace hψ j) i).add
      ((hTT.sub hL).mul analyticAt_const)

theorem analyticAt_completedBoundary {ν ρ : ℝ} {u : Velocity} {p ψ : Pressure}
    {z : ℝ × Vec}
    (hu : AnalyticAt ℝ (fun y : ℝ × Vec => u y.1 y.2) z)
    (hp : AnalyticAt ℝ (fun y : ℝ × Vec => p y.1 y.2) z)
    (hψ : AnalyticAt ℝ (fun y : ℝ × Vec => ψ y.1 y.2) z) :
    AnalyticAt ℝ (fun y : ℝ × Vec => completedBoundary ν ρ u p ψ y.1 y.2) z := by
  have hB (a b : Fin 4) : AnalyticAt ℝ
      (fun y : ℝ × Vec => lowerTensor4
        (conservedSourceUpper ν ρ u p y.1 y.2 + scalarCompletionUpper ψ y.1 y.2) a b) z :=
    analyticAt_const.mul ((analyticAt_conservedSourceUpper_entry hu hp a b).add
      (analyticAt_scalarCompletionUpper_entry hψ a b))
  have htr := (((hB 0 0).neg.add (hB 1 1)).add (hB 2 2)).add (hB 3 3)
  apply analyticAt_tensor4_of_entries
  intro a b
  have hc : AnalyticAt ℝ (fun _ : ℝ × Vec => (3 : ℝ)⁻¹ * eta4 a b) z := analyticAt_const
  simpa only [completedBoundary, traceReverse4, lorentzTrace4, div_eq_mul_inv,
    mul_assoc, Pi.sub_def, Pi.mul_def, Pi.add_def, Pi.neg_def] using
    (htr.mul hc).sub (hB a b)

theorem boundaryPartial_add_native {f q : Pressure} {t : ℝ} {x : Vec}
    (hf : AnalyticAt ℝ (fun z : ℝ × Vec => f z.1 z.2) (t,x))
    (hq : AnalyticAt ℝ (fun z : ℝ × Vec => q z.1 z.2) (t,x)) (a : Fin 4) :
    boundaryPartial (fun s y => f s y + q s y) a t x =
      boundaryPartial f a t x + boundaryPartial q a t x := by
  refine Fin.cases ?_ (fun i => ?_) a
  · exact jointTime_add hf hq
  · exact jointSpace_add hf hq i

theorem boundaryPartial_const_mul_native {f : Pressure} {t : ℝ} {x : Vec}
    (hf : AnalyticAt ℝ (fun z : ℝ × Vec => f z.1 z.2) (t,x)) (c : ℝ) (a : Fin 4) :
    boundaryPartial (fun s y => c * f s y) a t x = c * boundaryPartial f a t x := by
  refine Fin.cases ?_ (fun i => ?_) a
  · simpa only [boundaryPartial, Fin.cases_zero, smul_eq_mul] using
      (deriv_fun_const_smul c hf.curry_left.differentiableAt)
  · have h := fderiv_fun_const_smul hf.curry_right.differentiableAt c
    simpa only [boundaryPartial, Fin.cases_succ, smul_eq_mul, ContinuousLinearMap.smul_apply] using
      congrArg (fun L : Vec →L[ℝ] ℝ => L (unitVector i)) h

theorem traceReverse_lower_codazzi {T : BoundaryTensor} {t : ℝ} {x : Vec}
    (hT : ∀ a b, AnalyticAt ℝ (fun z : ℝ × Vec => T z.1 z.2 a b) (t,x))
    (b : Fin 4) :
    boundaryCodazzi (fun s y => traceReverse4 (lowerTensor4 (T s y))) t x b =
      -lorentzSign4 b * upperDivergence T t x b := by
  let K : BoundaryTensor := fun s y => traceReverse4 (lowerTensor4 (T s y))
  have he (a : Fin 4) :
      (fun s y => K s y a b - lorentzTrace4 (K s y) * eta4 a b) =
        fun s y => (-lorentzSign4 a * lorentzSign4 b) * T s y a b := by
    funext s y
    have h := congrArg (fun M : Tensor4 => M a b)
      (traceRecover4_traceReverse4 (lowerTensor4 (T s y)))
    change lorentzTrace4 (K s y) * eta4 a b - K s y a b =
      lorentzSign4 a * lorentzSign4 b * T s y a b at h
    linarith
  change (∑ a : Fin 4, lorentzSign4 a * boundaryPartial
    (fun s y => K s y a b - lorentzTrace4 (K s y) * eta4 a b) a t x) = _
  have hD (a : Fin 4) :
      boundaryPartial (fun s y => (-lorentzSign4 a * lorentzSign4 b) * T s y a b) a t x =
        (-lorentzSign4 a * lorentzSign4 b) * boundaryPartial (fun s y => T s y a b) a t x :=
    boundaryPartial_const_mul_native (f := fun s y => T s y a b)
      (hT a b) (-lorentzSign4 a * lorentzSign4 b) a
  simp_rw [he, hD]
  rw [upperDivergence, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    _ = -(lorentzSign4 a * lorentzSign4 a) * lorentzSign4 b *
      boundaryPartial (fun s y => T s y a b) a t x := by ring
    _ = _ := by rw [lorentzSign4_mul_self]; ring

theorem completedBoundary_codazzi {ν ρ : ℝ} {u : Velocity} {p ψ : Pressure}
    {t : ℝ} {x : Vec}
    (hu : ContDiff ℝ ∞ (u t))
    (hua : AnalyticAt ℝ (fun z : ℝ × Vec => u z.1 z.2) (t,x))
    (hpa : AnalyticAt ℝ (fun z : ℝ × Vec => p z.1 z.2) (t,x))
    (hψ : AnalyticAt ℝ (fun z : ℝ × Vec => ψ z.1 z.2) (t,x))
    (hdiv : ∀ y, divergence (u t) y = 0) (hmom : nseResidual ν u p t x = 0)
    (b : Fin 4) : boundaryCodazzi (completedBoundary ν ρ u p ψ) t x b = 0 := by
  have hS := conservedSourceUpper_conserved ν ρ u p t x hu hua
    (hpa.comp (analyticAt_const.prod analyticAt_id)).differentiableAt hdiv hmom b
  have hC := scalarCompletionUpper_conserved hψ b
  have hT (a c : Fin 4) : AnalyticAt ℝ (fun z : ℝ × Vec =>
      (conservedSourceUpper ν ρ u p z.1 z.2 + scalarCompletionUpper ψ z.1 z.2) a c) (t,x) :=
    (analyticAt_conservedSourceUpper_entry (ν := ν) (ρ := ρ) hua hpa a c).add
      (analyticAt_scalarCompletionUpper_entry hψ a c)
  change boundaryCodazzi (fun s y => traceReverse4 (lowerTensor4
    (conservedSourceUpper ν ρ u p s y + scalarCompletionUpper ψ s y))) t x b = 0
  rw [traceReverse_lower_codazzi hT]
  have hd : upperDivergence (fun s y => conservedSourceUpper ν ρ u p s y +
      scalarCompletionUpper ψ s y) t x b =
      upperDivergence (conservedSourceUpper ν ρ u p) t x b +
        upperDivergence (scalarCompletionUpper ψ) t x b := by
    simp only [upperDivergence, Matrix.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    exact boundaryPartial_add_native
      (f := fun s y => conservedSourceUpper ν ρ u p s y a b)
      (q := fun s y => scalarCompletionUpper ψ s y a b)
      (analyticAt_conservedSourceUpper_entry (ν := ν) (ρ := ρ) hua hpa a b)
      (analyticAt_scalarCompletionUpper_entry hψ a b) a
  rw [hd, hS, hC, add_zero, mul_zero]

theorem completedBoundary_symmetric {ν ρ : ℝ} {u : Velocity} {p ψ : Pressure}
    {t : ℝ} {x : Vec}
    (hψ : AnalyticAt ℝ (fun z : ℝ × Vec => ψ z.1 z.2) (t,x)) :
    (completedBoundary ν ρ u p ψ t x).IsSymm := by
  have hs (a b : Fin 4) : conservedSourceUpper ν ρ u p t x a b =
      conservedSourceUpper ν ρ u p t x b a := by
    refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b
    · rfl
    · rfl
    · rfl
    · exact nseSpatialSource3_symmetric ν u p t x i j
  have hc (a b : Fin 4) : scalarCompletionUpper ψ t x a b =
      scalarCompletionUpper ψ t x b a := by
    refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b
    · rfl
    · rfl
    · rfl
    · have hh := jointSpace_jointSpace hψ j i
      change scalarHessian (ψ t) x i j = scalarHessian (ψ t) x j i at hh
      simp only [scalarCompletionUpper_space_space, hh, identity3, eq_comm]
  apply Matrix.IsSymm.ext
  intro a b
  simp only [completedBoundary, traceReverse4, lowerTensor4, Matrix.add_apply,
    hs b a, hc b a]
  have he : eta4 b a = eta4 a b := by
    by_cases hab : a = b
    · subst b; rfl
    · simp [eta4, hab, Ne.symm hab]
  rw [he]
  ring

theorem scalarLocalTimeDerivative_periodic_on_interval {ψ : Pressure} {I : Set ℝ}
    (hI : IsOpen I) (hp : ∀ s ∈ I, SpatialPeriodic (ψ s)) {t : ℝ} (ht : t ∈ I) :
    SpatialPeriodic (scalarLocalTimeDerivative ψ t) := by
  intro x i
  have he : (fun s => ψ s (x + unitVector i)) =ᶠ[𝓝 t] (fun s => ψ s x) := by
    filter_upwards [hI.mem_nhds ht] with s hs
    exact hp s hs x i
  exact he.deriv_eq

theorem scalarHessian_periodic_native {f : ScalarField} (hp : SpatialPeriodic f) :
    SpatialPeriodic (scalarHessian f) := by
  intro x l
  ext i j
  have hq : SpatialPeriodic (fun y => fderiv ℝ f y (unitVector j)) := by
    intro y k
    exact congrArg (fun L : Vec →L[ℝ] ℝ => L (unitVector j)) (fderiv_periodic hp y k)
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L (unitVector i)) (fderiv_periodic hq x l)

theorem completedBoundary_periodic {ν ρ t0 δ : ℝ} {u : Velocity} {p ψ : Pressure}
    (hpair : AnalyticPeriodicPair t0 δ u p)
    (hp : ∀ s ∈ timeInterval t0 δ, SpatialPeriodic (ψ s))
    {t : ℝ} (ht : t ∈ timeInterval t0 δ) :
    SpatialPeriodic (completedBoundary ν ρ u p ψ t) := by
  have hpt := scalarLocalTimeDerivative_periodic_on_interval isOpen_Ioo hp ht
  have hptt := scalarLocalTimeDerivative_periodic_on_interval isOpen_Ioo
    (fun s hs => scalarLocalTimeDerivative_periodic_on_interval isOpen_Ioo hp hs) ht
  intro x l
  have hu := hpair.periodic_velocity t ht x l
  have hpress := hpair.periodic_pressure t ht x l
  have hz : strain (u t) (x + unitVector l) = strain (u t) x := by
    ext i j
    simp only [strain, spatialPartial_periodic (hpair.periodic_velocity t ht) _ x l]
  have hH := scalarHessian_periodic_native (hp t ht) x l
  have hL := scalarLaplacian_periodic (ψ t) (hp t ht) x l
  have hgrad := gradient_periodic hpt x l
  simp only [completedBoundary, conservedSourceUpper, scalarCompletionUpper,
    hu, hpress, hz, hH, hL, hgrad, hptt x l]

theorem completedBoundary_admissible {ν ρ t0 δ : ℝ} {u : Velocity} {p ψ : Pressure}
    (hn : LocalNSE ν t0 δ u p)
    (hψ : AnalyticOnNhd ℝ (fun z : ℝ × Vec => ψ z.1 z.2) (spacetimeSlab t0 δ))
    (hper : ∀ t ∈ timeInterval t0 δ, SpatialPeriodic (ψ t))
    (h0 : ∀ x, ψ t0 x = 0)
    (h1 : ∀ x, scalarLocalTimeDerivative ψ t0 x = 0)
    (hH : ∀ t ∈ timeInterval t0 δ, ∀ x,
      boundaryHamiltonian (completedBoundary ν ρ u p ψ) t x = 0) :
    BoundaryAdmissible ρ t0 δ (completedBoundary ν ρ u p ψ) := by
  have ht0 : t0 ∈ timeInterval t0 δ := by constructor <;> linarith [hn.radius_pos]
  have hbeta (t : ℝ) (ht : t ∈ timeInterval t0 δ) (x : Vec) :=
    completedBoundary_beta ν ρ u p ψ t x (hn.divergence_free t ht x)
  refine {
    radius_pos := hn.radius_pos
    analytic := fun z hz => analyticAt_completedBoundary (hn.velocity_analytic z hz)
      (hn.pressure_analytic z hz) (hψ z hz)
    periodic := fun t ht => completedBoundary_periodic hn.toAnalyticPeriodicPair hper ht
    symmetric := fun t ht x => completedBoundary_symmetric (hψ (t,x) ht)
    momentum_constraint := fun t ht x b => completedBoundary_codazzi
      (analyticOnNhd_slab_slice_smooth hn.velocity_analytic ht)
      (hn.velocity_analytic (t,x) ht) (hn.pressure_analytic (t,x) ht)
      (hψ (t,x) ht) (hn.divergence_free t ht) (hn.momentum t ht x) b
    hamiltonian := hH
    beta_initial := ?_
    beta_time_initial := ?_ }
  · intro x
    rw [hbeta t0 ht0 x]
    have hz : ψ t0 = (0 : ScalarField) := funext h0
    simp [hz, scalarLaplacian]
  · intro x
    have he : (fun t => boundaryBeta (completedBoundary ν ρ u p ψ) t x) =ᶠ[𝓝 t0]
        fun t => ρ + scalarLaplacian (ψ t) x := by
      filter_upwards [isOpen_Ioo.mem_nhds ht0] with t ht
      exact hbeta t ht x
    rw [he.deriv_eq, deriv_const_add]
    change scalarLocalTimeDerivative (fun t => scalarLaplacian (ψ t)) t0 x = 0
    rw [scalar_time_laplacian_commute (hψ (t0,x) ht0)]
    have hz : scalarLocalTimeDerivative ψ t0 = (0 : ScalarField) := funext h1
    simp [hz, scalarLaplacian]

end
end NSEGR.Assembly
