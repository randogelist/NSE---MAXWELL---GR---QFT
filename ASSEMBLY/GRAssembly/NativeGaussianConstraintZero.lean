import GRAssembly.NativeGaussianConstraintInitial
import GRAssembly.NativeGaussianEvolutionCompatibility
import GRAssembly.NativeCKFiniteDimensional

/-! The five actual Ricci constraints vanish by literal analytic CK uniqueness. -/
set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

namespace NSEGR.NativeLiterature

open Set Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
noncomputable section

abbrev GaussianConstraintState := ℝ × (Fin 4 → ℝ)

def gaussianResidualState (h : Bulk → Tensor4) (z : Bulk) : GaussianConstraintState :=
  (gaussianResidualA h z, gaussianResidualC h z)

def gaussianConstraintSolution (h : Bulk → Tensor4)
    (z : ℝ × GaussianBase) : GaussianConstraintState :=
  gaussianResidualState h (gaussianBulkCoordinates z)

def gaussianConstraintRHS (h : Bulk → Tensor4) :
    CKRHS GaussianBase GaussianConstraintState := fun J =>
  (-2 * (∑ a : Fin 4, ∑ b : Fin 4,
      (h (gaussianBulkCoordinates J.1))⁻¹ a b *
        ((J.2.2 (gaussianBaseBasis a)).2 b -
          ∑ c : Fin 4, gaussianTangentialChristoffel h (gaussianBulkCoordinates J.1) c a b *
            J.2.1.2 c)) -
      2 * gaussianKappa h (gaussianBulkCoordinates J.1) * J.2.1.1,
    fun i => (1 / 2 : ℝ) * (J.2.2 (gaussianBaseBasis i)).1 -
      gaussianKappa h (gaussianBulkCoordinates J.1) * J.2.1.2 i)

theorem analyticAt_gaussianResidualState {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (hN : IsUnit (h z).det) :
    AnalyticAt ℝ (gaussianResidualState h) z := by
  have hr := analyticAt_nativeRicci (analyticAt_gaussianBlockMetric hh)
    (gaussianBlockMetric_unit hN)
  apply AnalyticAt.prod
  · exact Assembly.analyticAt_matrix_entry hr 0 0
  · apply AnalyticAt.pi
    intro i
    exact Assembly.analyticAt_matrix_entry hr 0 i.succ

theorem analyticAt_gaussianKappa {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (hN : IsUnit (h z).det) :
    AnalyticAt ℝ (gaussianKappa h) z := by
  apply Finset.analyticAt_fun_sum
  intro a ha
  exact Assembly.analyticAt_matrix_entry (Assembly.analyticAt_gaussianShape hh hN) a a

theorem gaussianConstraintRHS_analyticAt {h : Bulk → Tensor4}
    {J : CKJet GaussianBase GaussianConstraintState}
    (hh : AnalyticAt ℝ h (gaussianBulkCoordinates J.1))
    (hN : IsUnit (h (gaussianBulkCoordinates J.1)).det) :
    AnalyticAt ℝ (gaussianConstraintRHS h) J := by
  have hz : AnalyticAt ℝ
      (fun q : CKJet GaussianBase GaussianConstraintState => gaussianBulkCoordinates q.1) J :=
    (gaussianBulkCoordinates.analyticAt _).comp analyticAt_fst
  have hi a b : AnalyticAt ℝ
      (fun q : CKJet GaussianBase GaussianConstraintState =>
        (h (gaussianBulkCoordinates q.1))⁻¹ a b) J :=
    (Assembly.analyticAt_matrix_entry (Assembly.analyticAt_matrix_inverse hh hN) a b).comp_of_eq hz rfl
  have hg c a b : AnalyticAt ℝ
      (fun q : CKJet GaussianBase GaussianConstraintState =>
        gaussianTangentialChristoffel h (gaussianBulkCoordinates q.1) c a b) J :=
    (Assembly.analyticAt_gaussianTangentialChristoffel hh hN c a b).comp_of_eq hz rfl
  have hk : AnalyticAt ℝ
      (fun q : CKJet GaussianBase GaussianConstraintState =>
        gaussianKappa h (gaussianBulkCoordinates q.1)) J :=
    (analyticAt_gaussianKappa hh hN).comp_of_eq hz rfl
  have hA : AnalyticAt ℝ
      (fun q : CKJet GaussianBase GaussianConstraintState => q.2.1.1) J :=
    analyticAt_fst.comp (analyticAt_fst.comp analyticAt_snd)
  have hC (c : Fin 4) : AnalyticAt ℝ
      (fun q : CKJet GaussianBase GaussianConstraintState => q.2.1.2 c) J :=
    ((ContinuousLinearMap.proj c : (Fin 4 → ℝ) →L[ℝ] ℝ).analyticAt
      J.2.1.2).comp_of_eq
      (show AnalyticAt ℝ
        (fun q : CKJet GaussianBase GaussianConstraintState => q.2.1.2) J from
        analyticAt_snd.comp (analyticAt_fst.comp analyticAt_snd)) rfl
  have hD (a : Fin 4) : AnalyticAt ℝ
      (fun q : CKJet GaussianBase GaussianConstraintState =>
        q.2.2 (gaussianBaseBasis a)) J :=
    ((ContinuousLinearMap.apply ℝ GaussianConstraintState (gaussianBaseBasis a)).analyticAt _).comp
      (analyticAt_snd.comp analyticAt_snd)
  apply AnalyticAt.prod
  · apply AnalyticAt.sub
    · apply analyticAt_const.mul
      apply Finset.analyticAt_fun_sum
      intro a ha
      apply Finset.analyticAt_fun_sum
      intro b hb
      apply (hi a b).mul
      apply AnalyticAt.sub
      · exact ((ContinuousLinearMap.proj b : (Fin 4 → ℝ) →L[ℝ] ℝ).analyticAt _).comp
          (analyticAt_snd.comp (hD a))
      · apply Finset.analyticAt_fun_sum
        intro c hc
        exact (hg c a b).mul (hC c)
    · exact (analyticAt_const.mul hk).mul hA
  · apply AnalyticAt.pi
    intro i
    exact (analyticAt_const.mul (analyticAt_fst.comp (hD i))).sub (hk.mul (hC i))

theorem gaussianResidualState_derivative_fst {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (hN : IsUnit (h z).det) (i : Fin 5) :
    (coordDeriv (gaussianResidualState h) i z).1 = bulkPartial (gaussianResidualA h) i z := by
  exact (gaussianDirectional_clm (ContinuousLinearMap.fst ℝ ℝ (Fin 4 → ℝ))
    (analyticAt_gaussianResidualState hh hN).differentiableAt (bulkBasis i)).symm

theorem gaussianResidualState_derivative_snd {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (hN : IsUnit (h z).det) (i : Fin 5) (a : Fin 4) :
    (coordDeriv (gaussianResidualState h) i z).2 a =
      bulkPartial (fun y => gaussianResidualC h y a) i z := by
  exact (gaussianDirectional_clm
    ((ContinuousLinearMap.proj a).comp (ContinuousLinearMap.snd ℝ ℝ (Fin 4 → ℝ)))
    (analyticAt_gaussianResidualState hh hN).differentiableAt (bulkBasis i)).symm

theorem gaussianConstraintRHS_zero (h : Bulk → Tensor4) (z : ℝ × GaussianBase) :
    gaussianConstraintRHS h (z, (0, 0)) = 0 := by
  ext i <;> simp [gaussianConstraintRHS]

theorem gaussianConstraint_zero_solution (h : Bulk → Tensor4) (y : GaussianBase) :
    CKLocalSolution (gaussianConstraintRHS h) (fun _ => 0) 0 y (fun _ => 0) := by
  constructor
  · exact analyticAt_const
  · exact Filter.Eventually.of_forall (fun _ => rfl)
  · exact Filter.Eventually.of_forall (fun z => by
      simpa only [deriv_const, fderiv_const_apply]
        using (gaussianConstraintRHS_zero h z).symm)

theorem gaussianConstraintSolution_isSolution
    {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec} {h : Bulk → Tensor4}
    (hE : GaussianEvolutionGerm K t0 x0 h)
    (hK : LiteratureFlatBoundaryGerm K t0 x0) :
    CKLocalSolution (gaussianConstraintRHS h) (fun _ => 0) 0 (t0, x0)
      (gaussianConstraintSolution h) := by
  constructor
  · exact (analyticAt_gaussianResidualState hE.analytic hE.nondegenerate.self_of_nhds).comp_of_eq
      (gaussianBulkCoordinates.analyticAt (0, (t0, x0))) rfl
  · filter_upwards [gaussian_constraints_initial_zero_germ hE hK] with y hy
    exact Prod.ext hy.1 (funext hy.2)
  · have hp : ∀ᶠ z in 𝓝 (bulkPoint 0 t0 x0),
        AnalyticAt ℝ h z ∧
          (∀ᶠ q in 𝓝 z, (h q).IsSymm) ∧
          (∀ᶠ q in 𝓝 z, IsUnit (h q).det) ∧
          (∀ᶠ q in 𝓝 z, ∀ a b : Fin 4,
            ricci (gaussianMetric h) q a.succ b.succ = 0) := by
      filter_upwards [hE.analytic.eventually_analyticAt,
        eventually_eventually_nhds.2 hE.symmetric,
        eventually_eventually_nhds.2 hE.nondegenerate,
        eventually_eventually_nhds.2 hE.tangential_vacuum] with z hz hs hn ht
      exact ⟨hz, hs, hn, ht⟩
    have hmap : Tendsto gaussianBulkCoordinates (𝓝 (0, (t0, x0)))
        (𝓝 (bulkPoint 0 t0 x0)) := gaussianBulkCoordinates.continuous.continuousAt
    have hp' := hmap.eventually hp
    filter_upwards [hp'] with z hz
    have ha := analyticAt_gaussianResidualState hz.1 hz.2.2.1.self_of_nhds
    have he := gaussian_constraint_evolution hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
    have ht : deriv (fun r => gaussianConstraintSolution h (r, z.2)) z.1 =
        coordDeriv (gaussianResidualState h) 0 (gaussianBulkCoordinates z) :=
      gaussianBulk_timeDerivative ha.differentiableAt
    have hs (a : Fin 4) :
        fderiv ℝ (fun y => gaussianConstraintSolution h (z.1, y)) z.2 (gaussianBaseBasis a) =
          coordDeriv (gaussianResidualState h) a.succ (gaussianBulkCoordinates z) :=
      gaussianBulk_spaceDerivative ha.differentiableAt a
    rw [ht]
    apply Prod.ext
    · simp only [gaussianConstraintRHS]
      simp only [hs,
        gaussianResidualState_derivative_snd hz.1 hz.2.2.1.self_of_nhds,
        gaussianResidualState_derivative_fst hz.1 hz.2.2.1.self_of_nhds]
      simpa only [gaussianConstraintSolution, gaussianResidualState,
        gaussianResidualDivergence] using he.1
    · funext i
      simp only [gaussianConstraintRHS]
      simp only [hs,
        gaussianResidualState_derivative_snd hz.1 hz.2.2.1.self_of_nhds,
        gaussianResidualState_derivative_fst hz.1 hz.2.2.1.self_of_nhds]
      simpa only [gaussianConstraintSolution, gaussianResidualState] using he.2 i

/-- Only the literal analytic CK input is used to discharge the residual system. -/
theorem gaussian_constraints_zero_germ (input : LiteratureAnalyticCKInput)
    {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec} {h : Bulk → Tensor4}
    (hE : GaussianEvolutionGerm K t0 x0 h)
    (hK : LiteratureFlatBoundaryGerm K t0 x0) :
    ∀ᶠ z in 𝓝 (bulkPoint 0 t0 x0),
      gaussianResidualA h z = 0 ∧ ∀ a : Fin 4, gaussianResidualC h z a = 0 := by
  have hF : AnalyticAt ℝ (gaussianConstraintRHS h)
      (ckInitialJet 0 (t0, x0) (fun _ : GaussianBase => (0 : GaussianConstraintState))) :=
    gaussianConstraintRHS_analyticAt hE.analytic hE.nondegenerate.self_of_nhds
  obtain ⟨u, hu, huniq⟩ := ckLocal_exists_unique_of_literatureCK input
    (gaussianConstraintRHS h) (fun _ => 0) 0 (t0, x0) analyticAt_const hF
  have he : gaussianConstraintSolution h =ᶠ[𝓝 (0, (t0, x0))]
      (fun _ => (0 : GaussianConstraintState)) :=
    (huniq _ (gaussianConstraintSolution_isSolution hE hK)).symm.trans
      (huniq _ (gaussianConstraint_zero_solution h (t0, x0)))
  have hmap : Tendsto gaussianSplitCoordinates (𝓝 (bulkPoint 0 t0 x0))
      (𝓝 (0, (t0, x0))) := by
    simpa only [gaussianSplitCoordinates_bulkPoint] using
      (gaussianSplitCoordinates.continuous.continuousAt (x := bulkPoint 0 t0 x0)).tendsto
  have hp := hmap.eventually he
  filter_upwards [hp] with z hz
  have hz' : gaussianResidualState h z = 0 := by
    simpa only [gaussianConstraintSolution, gaussianBulkCoordinates_split] using hz
  exact ⟨congrArg Prod.fst hz', fun a => congrArg (fun v : GaussianConstraintState => v.2 a) hz'⟩

/-- Full native Ricci vanishing, with no curvature or constraint certificate premise. -/
theorem gaussianEvolution_vacuum_of_constraints (input : LiteratureAnalyticCKInput)
    {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec} {h : Bulk → Tensor4}
    (hE : GaussianEvolutionGerm K t0 x0 h)
    (hK : LiteratureFlatBoundaryGerm K t0 x0) :
    ∀ᶠ z in 𝓝 (bulkPoint 0 t0 x0), ricci (gaussianMetric h) z = 0 := by
  filter_upwards [gaussian_constraints_zero_germ input hE hK,
    gaussianRicci_symmetric_eventually hE.analytic hE.symmetric hE.nondegenerate,
    hE.tangential_vacuum] with z hz hs ht
  ext i j
  refine Fin.cases ?_ (fun a => ?_) i
  · refine Fin.cases hz.1 (fun b => hz.2 b) j
  · refine Fin.cases ?_ (fun b => ht a b) j
    exact (hs.apply 0 a.succ).trans (hz.2 a)

end
end NSEGR.NativeLiterature
