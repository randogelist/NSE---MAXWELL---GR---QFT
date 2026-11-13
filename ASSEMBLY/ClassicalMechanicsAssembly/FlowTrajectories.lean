import Mathlib.Analysis.ODE.ExistUnique
import ClassicalMechanics.Material
import ClassicalMechanicsAssembly.FlowBounds

/-!
# Whole-slab trajectories and their algebraic flow laws

The hypotheses below are uniform bounds on the supplied vector field. They
do not assert existence of any trajectory. Mathlib's Picard-Lindelof theorem
constructs trajectories on the entire finite interval. Uniqueness gives the
cocycle, inverse identities, and lattice equivariance. Joint smoothness in
time and the initial label is a separate endpoint.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly.Flow

open Set Metric
open scoped NNReal Topology ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {T : ℝ} {u : ℝ → E → E} {B K : ℝ≥0}

/-- The bounded globally spatially Lipschitz data needed by Picard-Lindelof. -/
structure SlabODEData (T : ℝ) (u : ℝ → E → E) (B K : ℝ≥0) : Prop where
  continuous_time : ∀ x : E, ContinuousOn (fun t => u t x) (Icc 0 T)
  norm_le : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : E, ‖u t x‖ ≤ B
  lipschitz : ∀ t ∈ Icc (0 : ℝ) T, LipschitzWith K (u t)

theorem SlabODEData.isPicardLindelof (h : SlabODEData T u B K)
    (s : Icc (0 : ℝ) T) (a : E) :
    IsPicardLindelof u s a (B * Real.toNNReal T) 0 B K := by
  have hT : 0 ≤ T := s.property.1.trans s.property.2
  refine ⟨fun t ht => (h.lipschitz t ht).lipschitzOnWith,
    fun x _ => h.continuous_time x, fun t ht x _ => h.norm_le t ht x, ?_⟩
  simp only [NNReal.coe_mul, Real.coe_toNNReal T hT, NNReal.coe_zero, sub_zero]
  exact mul_le_mul_of_nonneg_left
    (max_le (sub_le_self T s.property.1) s.property.2) B.coe_nonneg

/-- A trajectory for every starting time and every initial label, on all of `[0,T]`. -/
theorem exists_trajectory (h : SlabODEData T u B K)
    (s : Icc (0 : ℝ) T) (a : E) :
    ∃ γ : ℝ → E, γ s = a ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt γ (u t (γ t)) (Icc (0 : ℝ) T) t :=
  (h.isPicardLindelof s a).exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- Selected whole-slab trajectory; its values outside the slab are immaterial. -/
def trajectory (h : SlabODEData T u B K) (s : Icc (0 : ℝ) T) (a : E) : ℝ → E :=
  Classical.choose (exists_trajectory h s a)

theorem trajectory_initial (h : SlabODEData T u B K)
    (s : Icc (0 : ℝ) T) (a : E) : trajectory h s a s = a :=
  (Classical.choose_spec (exists_trajectory h s a)).1

theorem trajectory_hasDerivWithinAt (h : SlabODEData T u B K)
    (s : Icc (0 : ℝ) T) (a : E) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (trajectory h s a) (u t (trajectory h s a t)) (Icc 0 T) t :=
  (Classical.choose_spec (exists_trajectory h s a)).2 t ht

theorem trajectory_continuousOn (h : SlabODEData T u B K)
    (s : Icc (0 : ℝ) T) (a : E) :
    ContinuousOn (trajectory h s a) (Icc (0 : ℝ) T) :=
  HasDerivWithinAt.continuousOn (trajectory_hasDerivWithinAt h s a)

/-- Boundary-inclusive uniqueness, with the initial time anywhere in the slab. -/
theorem solution_unique (h : SlabODEData T u B K)
    (s : Icc (0 : ℝ) T) {f g : ℝ → E}
    (hf : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt f (u t (f t)) (Icc 0 T) t)
    (hg : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt g (u t (g t)) (Icc 0 T) t)
    (heq : f s = g s) : EqOn f g (Icc (0 : ℝ) T) := by
  have hfc := HasDerivWithinAt.continuousOn hf
  have hgc := HasDerivWithinAt.continuousOn hg
  have hleft : EqOn f g (Icc (0 : ℝ) (s : ℝ)) := by
    apply ODE_solution_unique_of_mem_Icc_left
      (s := fun _ => (univ : Set E)) (K := K)
      (fun t ht => (h.lipschitz t ⟨ht.1.le, ht.2.trans s.property.2⟩).lipschitzOnWith)
      (hfc.mono (Icc_subset_Icc_right s.property.2))
      (fun t ht => (hf t ⟨ht.1.le, ht.2.trans s.property.2⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem ⟨ht.1, ht.2.trans s.property.2⟩))
      (fun _ _ => mem_univ _)
      (hgc.mono (Icc_subset_Icc_right s.property.2))
      (fun t ht => (hg t ⟨ht.1.le, ht.2.trans s.property.2⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem ⟨ht.1, ht.2.trans s.property.2⟩))
      (fun _ _ => mem_univ _) heq
  have hright : EqOn f g (Icc (s : ℝ) T) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (s := fun _ => (univ : Set E)) (K := K)
      (fun t ht => (h.lipschitz t ⟨s.property.1.trans ht.1, ht.2.le⟩).lipschitzOnWith)
      (hfc.mono (Icc_subset_Icc_left s.property.1))
      (fun t ht => (hf t ⟨s.property.1.trans ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨s.property.1.trans ht.1, ht.2⟩))
      (fun _ _ => mem_univ _)
      (hgc.mono (Icc_subset_Icc_left s.property.1))
      (fun t ht => (hg t ⟨s.property.1.trans ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨s.property.1.trans ht.1, ht.2⟩))
      (fun _ _ => mem_univ _) heq
  intro t ht
  rcases le_total t (s : ℝ) with hts | hst
  · exact hleft ⟨ht.1, hts⟩
  · exact hright ⟨hst, ht.2⟩

theorem trajectory_cocycle (h : SlabODEData T u B K)
    (s q : Icc (0 : ℝ) T) (a : E) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    trajectory h q (trajectory h s a q) t = trajectory h s a t := by
  apply solution_unique h q
    (trajectory_hasDerivWithinAt h q (trajectory h s a q))
    (trajectory_hasDerivWithinAt h s a) (trajectory_initial h q _) ht

/-- Translation invariance of the vector field implies equivariance of its flow. -/
theorem trajectory_translate (h : SlabODEData T u B K) (v : E)
    (hperiod : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : E, u t (x + v) = u t x)
    (s : Icc (0 : ℝ) T) (a : E) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    trajectory h s (a + v) t = trajectory h s a t + v := by
  have hshift : ∀ r ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun r => trajectory h s a r + v)
        (u r (trajectory h s a r + v)) (Icc 0 T) r := by
    intro r hr
    rw [hperiod r hr]
    exact (trajectory_hasDerivWithinAt h s a r hr).add_const v
  apply solution_unique h s (trajectory_hasDerivWithinAt h s (a + v)) hshift ?_ ht
  rw [trajectory_initial, trajectory_initial]

def flow (h : SlabODEData T u B K) (hT : 0 ≤ T) : ℝ → E → E :=
  fun t a => trajectory h ⟨0, ⟨le_rfl, hT⟩⟩ a t

def inverseFlow (h : SlabODEData T u B K) : ℝ → E → E :=
  fun t x => if ht : t ∈ Icc (0 : ℝ) T then trajectory h ⟨t, ht⟩ x 0 else x

theorem flow_initial (h : SlabODEData T u B K) (hT : 0 ≤ T) (a : E) :
    flow h hT 0 a = a := trajectory_initial h _ a

theorem flow_hasDerivWithinAt (h : SlabODEData T u B K) (hT : 0 ≤ T)
    (a : E) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun r => flow h hT r a) (u t (flow h hT t a)) (Icc 0 T) t :=
  trajectory_hasDerivWithinAt h _ a t ht

theorem inverseFlow_flow (h : SlabODEData T u B K) (hT : 0 ≤ T)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : E) :
    inverseFlow h t (flow h hT t a) = a := by
  simp only [inverseFlow, dif_pos ht, flow]
  rw [trajectory_cocycle h _ ⟨t, ht⟩ a 0 ⟨le_rfl, hT⟩, trajectory_initial]

theorem flow_inverseFlow (h : SlabODEData T u B K) (hT : 0 ≤ T)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : E) :
    flow h hT t (inverseFlow h t x) = x := by
  simp only [inverseFlow, dif_pos ht, flow]
  rw [trajectory_cocycle h ⟨t, ht⟩ ⟨0, ⟨le_rfl, hT⟩⟩ x t ht, trajectory_initial]

theorem flow_translate (h : SlabODEData T u B K) (hT : 0 ≤ T) (v : E)
    (hperiod : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : E, u t (x + v) = u t x)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : E) :
    flow h hT t (a + v) = flow h hT t a + v :=
  trajectory_translate h v hperiod _ a t ht

/-- Time regularity only; no initial-label regularity is claimed by this endpoint. -/
theorem trajectory_contDiffOn {n : ℕ∞} (h : SlabODEData T u B K)
    (hu : ContDiffOn ℝ n (Function.uncurry u) (Icc (0 : ℝ) T ×ˢ (univ : Set E)))
    (s : Icc (0 : ℝ) T) (a : E) :
    ContDiffOn ℝ n (trajectory h s a) (Icc (0 : ℝ) T) :=
  ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt hu
    (trajectory_hasDerivWithinAt h s a) (fun _ _ => mem_univ _)

/-- Uniform label stability, including evaluation before the starting time. -/
theorem trajectory_dist_le (h : SlabODEData T u B K)
    (s : Icc (0 : ℝ) T) (a b : E) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    dist (trajectory h s a t) (trajectory h s b t) ≤
      dist a b * Real.exp ((K : ℝ) * T) := by
  rcases le_total (s : ℝ) t with hst | hts
  · have hg := dist_le_of_trajectories_ODE_of_mem
      (s := fun _ => (univ : Set E)) (K := K) (δ := dist a b)
      (fun r hr => (h.lipschitz r ⟨s.property.1.trans hr.1, hr.2.le⟩).lipschitzOnWith)
      ((trajectory_continuousOn h s a).mono (Icc_subset_Icc_left s.property.1))
      (fun r hr => (trajectory_hasDerivWithinAt h s a r
        ⟨s.property.1.trans hr.1, hr.2.le⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨s.property.1.trans hr.1, hr.2⟩))
      (fun _ _ => mem_univ _)
      ((trajectory_continuousOn h s b).mono (Icc_subset_Icc_left s.property.1))
      (fun r hr => (trajectory_hasDerivWithinAt h s b r
        ⟨s.property.1.trans hr.1, hr.2.le⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨s.property.1.trans hr.1, hr.2⟩))
      (fun _ _ => mem_univ _) (by simp only [trajectory_initial, le_refl]) t ⟨hst, ht.2⟩
    apply hg.trans
    apply mul_le_mul_of_nonneg_left _ (dist_nonneg : 0 ≤ dist a b)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left
      ((sub_le_self t s.property.1).trans ht.2) K.coe_nonneg
  · have hmaps : MapsTo Neg.neg (Icc (-(s : ℝ)) 0) (Icc (0 : ℝ) T) := by
      intro r hr
      exact ⟨neg_nonneg.mpr hr.2, (neg_le.mp hr.1).trans s.property.2⟩
    have hmem : ∀ r ∈ Ico (-(s : ℝ)) 0, -r ∈ Ioc (0 : ℝ) T := by
      intro r hr
      exact ⟨neg_pos.mpr hr.2, (neg_le.mp hr.1).trans s.property.2⟩
    have hder (x : E) : ∀ r ∈ Ico (-(s : ℝ)) 0,
        HasDerivWithinAt (fun q => trajectory h s x (-q))
          (-u (-r) (trajectory h s x (-r))) (Ici r) r := by
      intro r hr
      have hd := (trajectory_hasDerivWithinAt h s x (-r)
        ⟨(hmem r hr).1.le, (hmem r hr).2⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem (hmem r hr))
      convert HasFDerivWithinAt.comp_hasDerivWithinAt r hd
        (hasDerivAt_neg r).hasDerivWithinAt
        (fun q (hq : q ∈ Ici r) => mem_Iic.mpr (neg_le_neg (mem_Ici.mp hq))) using 1 <;> simp
    have hg := dist_le_of_trajectories_ODE_of_mem
      (s := fun _ => (univ : Set E)) (K := K) (δ := dist a b)
      (v := fun r x => -u (-r) x)
      (fun r hr => ((h.lipschitz (-r)
        ⟨(hmem r hr).1.le, (hmem r hr).2⟩).neg).lipschitzOnWith)
      ((trajectory_continuousOn h s a).comp continuous_neg.continuousOn hmaps)
      (hder a) (fun _ _ => mem_univ _)
      ((trajectory_continuousOn h s b).comp continuous_neg.continuousOn hmaps)
      (hder b) (fun _ _ => mem_univ _)
      (by simp only [Function.comp_def, neg_neg, trajectory_initial, le_refl]) (-t)
      ⟨neg_le_neg hts, neg_nonpos.mpr ht.1⟩
    simp only [Function.comp_def, neg_neg] at hg
    apply hg.trans
    apply mul_le_mul_of_nonneg_left _ (dist_nonneg : 0 ≤ dist a b)
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
    linarith [s.property.2, ht.1]

theorem trajectory_lipschitz (h : SlabODEData T u B K)
    (s : Icc (0 : ℝ) T) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    LipschitzWith (Real.toNNReal (Real.exp ((K : ℝ) * T)))
      (fun a => trajectory h s a t) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simpa only [Real.coe_toNNReal _ (Real.exp_nonneg _), mul_comm] using
    trajectory_dist_le h s a b t ht

/-- Bounded velocity makes every trajectory Lipschitz in time. -/
theorem trajectory_time_lipschitz (h : SlabODEData T u B K)
    (s : Icc (0 : ℝ) T) (a : E) :
    LipschitzOnWith B (trajectory h s a) (Icc (0 : ℝ) T) := by
  apply (convex_Icc (0 : ℝ) T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (trajectory_hasDerivWithinAt h s a)
  intro t ht
  exact_mod_cast h.norm_le t ht (trajectory h s a t)

/-- Joint continuity in time and label for any fixed starting time. -/
theorem trajectory_joint_continuousOn (h : SlabODEData T u B K)
    (s : Icc (0 : ℝ) T) :
    ContinuousOn (fun z : ℝ × E => trajectory h s z.2 z.1)
      (Icc (0 : ℝ) T ×ˢ (univ : Set E)) := by
  apply continuousOn_prod_of_continuousOn_lipschitzOnWith' _
    (Real.toNNReal (Real.exp ((K : ℝ) * T)))
  · exact fun t ht => (trajectory_lipschitz h s t ht).lipschitzOnWith
  · exact fun a _ => trajectory_continuousOn h s a

theorem inverseFlow_lipschitz (h : SlabODEData T u B K) (hT : 0 ≤ T)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    LipschitzWith (Real.toNNReal (Real.exp ((K : ℝ) * T))) (inverseFlow h t) := by
  have heq : inverseFlow h t = (fun a => trajectory h ⟨t, ht⟩ a 0) := by
    funext a
    simp only [inverseFlow, dif_pos ht]
  rw [heq]
  exact trajectory_lipschitz h ⟨t, ht⟩ 0 ⟨le_rfl, hT⟩

section ClassicalAdapter

open NSEMaxwell.Classical ClassicalMechanics

theorem smooth_periodic_slabODEData {T : ℝ} (hT : 0 < T) {u : Velocity}
    (hu : SmoothVelocityOn T u)
    (hperiodic : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (u t)) :
    ∃ B K : ℝ≥0, SlabODEData T u B K := by
  obtain ⟨B, K, hB, hK⟩ := periodic_velocity_uniform_bounds hT hu hperiodic
  exact ⟨B, K, ⟨flow_velocity_time_continuousOn hu, hB, hK⟩⟩

theorem flow_materialVelocity {T : ℝ} {u : Velocity} {B K : ℝ≥0}
    (h : SlabODEData T u B K) (hT : 0 < T)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : Vec) :
    materialVelocity T (flow h hT.le) t a = u t (flow h hT.le t a) :=
  (flow_hasDerivWithinAt h hT.le a t ht).derivWithin (uniqueDiffOn_Icc hT t ht)

theorem flow_lattice_equivariant {T : ℝ} {u : Velocity} {B K : ℝ≥0}
    (h : SlabODEData T u B K) (hT : 0 ≤ T)
    (hperiodic : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (u t))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : Vec) (i : Fin 3) :
    flow h hT t (a + unitVector i) = flow h hT t a + unitVector i :=
  flow_translate h hT (unitVector i) (fun r hr x => hperiodic r hr x i) t ht a

/-- Exact trajectory/inverse/lattice subpackage of L1, with no divergence assumption.
The two joint smoothness fields and determinant-one field are not asserted here. -/
theorem exists_flow_inverse_lattice {T : ℝ} (hT : 0 < T) {u : Velocity}
    (hu : SmoothVelocityOn T u)
    (hperiodic : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (u t)) :
    ∃ η ρ : Velocity,
      (η 0 = fun a => a) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec, ρ t (η t a) = a) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec, η t (ρ t x) = x) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec, ∀ i : Fin 3,
        η t (a + unitVector i) = η t a + unitVector i) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
        materialVelocity T η t a = u t (η t a)) := by
  obtain ⟨B, K, h⟩ := smooth_periodic_slabODEData hT hu hperiodic
  refine ⟨flow h hT.le, inverseFlow h, ?_, ?_, ?_, ?_, ?_⟩
  · funext a
    exact flow_initial h hT.le a
  · exact inverseFlow_flow h hT.le
  · exact flow_inverseFlow h hT.le
  · exact flow_lattice_equivariant h hT.le hperiodic
  · exact flow_materialVelocity h hT

end ClassicalAdapter

end

end ClassicalMechanicsAssembly.Flow
