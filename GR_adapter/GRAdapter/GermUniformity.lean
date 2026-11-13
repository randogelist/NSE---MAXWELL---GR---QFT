import GRAdapter.UnitTorus
import GRAdapter.Germs

/-!
# Compact spatial uniformization of actual metric germs

Local equality on neighborhoods of the compact unit cell and the actual
integer-periodicity equations imply equality on a single full-spatial collar.
No analytic uniqueness or radial existence theorem is included in this step.
-/

set_option autoImplicit false

open Set Filter
open scoped BigOperators Topology Matrix.Norms.Frobenius

namespace NSEGR
noncomputable section

/-- A compact family of joint neighborhood equalities has one uniform parameter neighborhood. -/
theorem compact_slice_eventually_eq
    {S X E : Type*} [TopologicalSpace S] [TopologicalSpace X]
    {s0 : S} {K : Set X} (hK : IsCompact K) {f g : S → X → E}
    (hlocal : ∀ x ∈ K, ∀ᶠ z : S × X in 𝓝 (s0, x), f z.1 z.2 = g z.1 z.2) :
    ∀ᶠ s in 𝓝 s0, ∀ x ∈ K, f s x = g s x :=
  hK.eventually_forall_of_forall_eventually hlocal

/-- Literal integer translation in the three marked unit directions. -/
def integerSpatialShift (n : Fin 3 → ℤ) : Vec :=
  ∑ i : Fin 3, n i • unitVector i

theorem integerSpatialShift_apply (n : Fin 3 → ℤ) (j : Fin 3) :
    integerSpatialShift n j = (n j : ℝ) := by
  change (WithLp.ofLp (∑ i : Fin 3, n i • unitVector i)) j = (n j : ℝ)
  simp [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
    unitVector, PiLp.single_apply, Pi.single_apply, zsmul_eq_mul, mul_ite]

/-- The actual fractional-coordinate representative of a spatial point. -/
def spatialCellRepresentative (x : Vec) : Vec :=
  WithLp.toLp 2 (fun i : Fin 3 => Int.fract (x i))

theorem spatialCellRepresentative_mem_unitCube (x : Vec) :
    spatialCellRepresentative x ∈ unitCube := by
  intro i
  exact ⟨Int.fract_nonneg (x i), (Int.fract_lt_one (x i)).le⟩

theorem spatialCellRepresentative_add_shift (x : Vec) :
    spatialCellRepresentative x + integerSpatialShift (fun i => ⌊x i⌋) = x := by
  ext i
  change Int.fract (x i) + integerSpatialShift (fun j => ⌊x j⌋) i = x i
  rw [integerSpatialShift_apply]
  exact Int.fract_add_floor (x i)

/-- Unit-direction periodicity entails every literal integer spatial period. -/
theorem spatialPeriodic_integerSpatialShift {E : Type*} {f : Vec → E}
    (hf : SpatialPeriodic f) (n : Fin 3 → ℤ) :
    Function.Periodic f (integerSpatialShift n) := by
  have hsum (s : Finset (Fin 3)) :
      Function.Periodic f (∑ i ∈ s, n i • unitVector i) := by
    induction s using Finset.induction_on with
    | empty =>
        intro x
        simp
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi]
        have hunit : Function.Periodic f (unitVector i) := fun x => hf x i
        exact (hunit.zsmul (n i)).add_period ih
  exact hsum Finset.univ

theorem spatialPeriodic_eq_cellRepresentative {E : Type*} {f : Vec → E}
    (hf : SpatialPeriodic f) (x : Vec) :
    f x = f (spatialCellRepresentative x) := by
  calc
    f x = f (spatialCellRepresentative x + integerSpatialShift (fun i => ⌊x i⌋)) :=
      congrArg f (spatialCellRepresentative_add_shift x).symm
    _ = f (spatialCellRepresentative x) :=
      spatialPeriodic_integerSpatialShift hf (fun i => ⌊x i⌋) _

/-- Equality of actual periodic functions on the concrete unit cube is global equality. -/
theorem spatialPeriodic_eq_of_eqOn_unitCube {E : Type*} {f g : Vec → E}
    (hf : SpatialPeriodic f) (hg : SpatialPeriodic g)
    (heq : EqOn f g unitCube) : f = g := by
  funext x
  calc
    f x = f (spatialCellRepresentative x) := spatialPeriodic_eq_cellRepresentative hf x
    _ = g (spatialCellRepresentative x) :=
      heq (spatialCellRepresentative_mem_unitCube x)
    _ = g x := (spatialPeriodic_eq_cellRepresentative hg x).symm

/-- Compactness plus integer reduction supplies one neighborhood for every spatial point. -/
theorem periodic_slice_germs_uniform
    {S E : Type*} [TopologicalSpace S] {s0 : S} {f g : S → Vec → E}
    (hperiodic : ∀ᶠ s in 𝓝 s0, SpatialPeriodic (f s) ∧ SpatialPeriodic (g s))
    (hlocal : ∀ x ∈ unitCube, ∀ᶠ z : S × Vec in 𝓝 (s0, x),
      f z.1 z.2 = g z.1 z.2) :
    ∀ᶠ s in 𝓝 s0, ∀ x : Vec, f s x = g s x := by
  filter_upwards [hperiodic, compact_slice_eventually_eq isCompact_unitCube hlocal]
    with s hp heq
  exact congrFun (spatialPeriodic_eq_of_eqOn_unitCube hp.1 hp.2 heq)

theorem continuous_bulkPoint_product :
    Continuous (fun z : (ℝ × ℝ) × Vec => bulkPoint z.1.1 z.1.2 z.2) := by
  unfold bulkPoint
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun a => ?_) i
  · exact continuous_fst.fst
  · refine Fin.cases ?_ (fun j => ?_) a
    · exact continuous_fst.snd
    · exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) j).comp continuous_snd

/-- The full-slice metric germ follows from actual bulk neighborhood equality over the unit cell. -/
theorem sameMetricAt_of_boundary_germs {t0 : ℝ} {g h : Metric}
    (hperiodic : ∀ᶠ rt : ℝ × ℝ in 𝓝 ((0 : ℝ), t0),
      SpatialPeriodic (fun x => g (bulkPoint rt.1 rt.2 x)) ∧
      SpatialPeriodic (fun x => h (bulkPoint rt.1 rt.2 x)))
    (hlocal : ∀ x ∈ unitCube, g =ᶠ[𝓝 (bulkPoint 0 t0 x)] h) :
    SameMetricAt t0 g h := by
  apply periodic_slice_germs_uniform hperiodic
  intro x hx
  have hc : ContinuousAt
      (fun z : (ℝ × ℝ) × Vec => bulkPoint z.1.1 z.1.2 z.2) (((0 : ℝ), t0), x) :=
    continuous_bulkPoint_product.continuousAt
  exact hc.tendsto.eventually (hlocal x hx)

theorem gaussianVacuum_eventually_periodic {ρ t0 δ ε : ℝ} {g : Metric}
    (hg : GaussianVacuum ρ t0 δ ε g) :
    ∀ᶠ rt : ℝ × ℝ in 𝓝 ((0 : ℝ), t0),
      SpatialPeriodic (fun x => g (bulkPoint rt.1 rt.2 x)) := by
  have hr : ∀ᶠ r in 𝓝 (0 : ℝ), r ∈ Ioo (-ε) ε := by
    apply Ioo_mem_nhds <;> linarith [hg.radial_radius_pos]
  have ht : ∀ᶠ t in 𝓝 t0, t ∈ timeInterval t0 δ := by
    apply Ioo_mem_nhds <;> linarith [hg.time_radius_pos]
  filter_upwards [hr.prodMk_nhds ht] with rt hrt
  exact hg.periodic rt.1 hrt.1 rt.2 hrt.2

/-- Collar periodicity of the actual vacua is sufficient; global periodicity is unnecessary. -/
theorem gaussianVacuum_sameMetricAt_of_boundary_germs
    {ρg ρh t0 δg εg δh εh : ℝ} {g h : Metric}
    (hg : GaussianVacuum ρg t0 δg εg g) (hh : GaussianVacuum ρh t0 δh εh h)
    (hlocal : ∀ x ∈ unitCube, g =ᶠ[𝓝 (bulkPoint 0 t0 x)] h) :
    SameMetricAt t0 g h :=
  sameMetricAt_of_boundary_germs
    ((gaussianVacuum_eventually_periodic hg).and (gaussianVacuum_eventually_periodic hh))
    hlocal

end
end NSEGR
