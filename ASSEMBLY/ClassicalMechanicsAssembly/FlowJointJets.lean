import ClassicalMechanicsAssembly.FlowPathJets
import ClassicalMechanicsAssembly.FlowJetTime
import ClassicalMechanicsAssembly.FlowSpatialJets

/-!
# Concrete forcing jets and closed-slab joint smoothness

The label and forcing towers below are literal iterated derivatives. The
finite-order forcing implication is discharged by Mathlib's ordered-partition
Faà di Bruno formula. No smoothness of variable-time evaluation on continuous
paths is asserted or used.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly

open Set ClassicalMechanics NSEMaxwell.Classical
open scoped Topology ContDiff Interval

noncomputable section

/-- Evaluation of a varying finite multilinear map preserves finite-order smoothness. -/
theorem flow_contDiffOn_multilinear_apply
    {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω} {s : Set D} :
    ∀ r : ℕ, ∀ M : Fin r → Type*,
      ∀ [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace ℝ (M i)],
      ∀ (f : D → ContinuousMultilinearMap ℝ M F) (g : D → ∀ i, M i),
      ContDiffOn ℝ n f s → (∀ i, ContDiffOn ℝ n (fun z => g z i) s) →
      ContDiffOn ℝ n (fun z => f z (g z)) s := by
  intro r
  induction r with
  | zero =>
      intro M _ _ f g hf _
      have hg : g = fun _ i => Fin.elim0 i := by
        funext z i
        exact Fin.elim0 i
      rw [hg]
      exact (ContinuousMultilinearMap.apply ℝ M F (fun i => Fin.elim0 i)).contDiff.comp_contDiffOn hf
  | succ r ih =>
      intro M _ _ f g hf hg
      let e : ContinuousMultilinearMap ℝ M F ≃ₗᵢ[ℝ]
          M 0 →L[ℝ] ContinuousMultilinearMap ℝ (fun i : Fin r => M i.succ) F :=
        continuousMultilinearCurryLeftEquiv ℝ M F
      have he : ContDiffOn ℝ n (fun z => e (f z)) s :=
        e.contDiff.comp_contDiffOn hf
      have hc : ContDiffOn ℝ n (fun z => (f z).curryLeft (g z 0)) s :=
        he.clm_apply (hg 0)
      have ht := ih (fun i => M i.succ)
        (fun z => (f z).curryLeft (g z 0)) (fun z i => g z i.succ)
        hc (fun i => hg i.succ)
      apply ht.congr
      intro z _
      change (f z) (g z) = (f z) (Fin.cons (g z 0) (Fin.tail (g z)))
      exact congrArg (f z) (Fin.cons_self_tail (g z)).symm

/-- Literal ordinary label derivatives of the total trajectory representative. -/
def flowLabelJet (η : Velocity) (r : ℕ) (z : ℝ × Vec) : FlowJet r :=
  iteratedFDeriv ℝ r (η z.1) z.2

/-- Literal ordinary label derivatives of the composed ODE right-hand side. -/
def flowForcingJet (u η : Velocity) (r : ℕ) (z : ℝ × Vec) : FlowJet r :=
  iteratedFDeriv ℝ r (fun b => u z.1 (η z.1 b)) z.2

/-- Fixed-time slices of a smooth Banach path family retain full label smoothness. -/
theorem flow_representative_slice_contDiff {T : ℝ}
    {Γ : Vec → C(Icc (0 : ℝ) T, Vec)} (hΓ : ContDiff ℝ ∞ Γ)
    {η : Velocity}
    (hrep : ∀ t (ht : t ∈ Icc (0 : ℝ) T) a, η t a = Γ a ⟨t, ht⟩)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : ContDiff ℝ ∞ (η t) := by
  have heq : η t = fun a => Γ a ⟨t, ht⟩ := funext (hrep t ht)
  rw [heq]
  exact flowPath_contDiff_evaluation hΓ ⟨t, ht⟩

/-- The literal label jet equals evaluation of the actual Banach derivative. -/
theorem flowLabelJet_eq_evaluatedFlowJet {T : ℝ}
    {Γ : Vec → C(Icc (0 : ℝ) T, Vec)} (hΓ : ContDiff ℝ ∞ Γ)
    {η : Velocity}
    (hrep : ∀ t (ht : t ∈ Icc (0 : ℝ) T) a, η t a = Γ a ⟨t, ht⟩)
    (r : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (a : Vec) :
    flowLabelJet η r (t, a) = evaluatedFlowJet Γ r ⟨t, ht⟩ a := by
  change iteratedFDeriv ℝ r (η t) a = _
  rw [show η t = fun b => Γ b ⟨t, ht⟩ from funext (hrep t ht)]
  exact (ContinuousMap.evalCLM ℝ ⟨t, ht⟩).iteratedFDeriv_comp_left
    hΓ.contDiffAt (i := r) (ENat.natCast_le_of_coe_top_le_withTop le_rfl r)

/-- Actual label jets are jointly continuous on the closed time slab. -/
theorem flowLabelJet_continuousOn {T : ℝ}
    {Γ : Vec → C(Icc (0 : ℝ) T, Vec)} (hΓ : ContDiff ℝ ∞ Γ)
    {η : Velocity}
    (hrep : ∀ t (ht : t ∈ Icc (0 : ℝ) T) a, η t a = Γ a ⟨t, ht⟩)
    (r : ℕ) : ContinuousOn (flowLabelJet η r) (finiteSpacetime T) := by
  rw [continuousOn_iff_continuous_restrict]
  have hmap : Continuous (fun z : finiteSpacetime T =>
      ((⟨z.1.1, z.2⟩ : Icc (0 : ℝ) T), z.1.2)) :=
    (continuous_subtype_val.fst.subtype_mk (fun z => z.2)).prodMk
      continuous_subtype_val.snd
  have he := (evaluatedFlowJet_continuous hΓ r).comp hmap
  convert he using 1
  funext z
  exact flowLabelJet_eq_evaluatedFlowJet hΓ hrep r z.2 z.1.2

/-- Actual label differentiation shifts the literal jet tower by one order. -/
theorem flowLabelJet_hasFDerivAt {T : ℝ}
    {Γ : Vec → C(Icc (0 : ℝ) T, Vec)} (hΓ : ContDiff ℝ ∞ Γ)
    {η : Velocity}
    (hrep : ∀ t (ht : t ∈ Icc (0 : ℝ) T) a, η t a = Γ a ⟨t, ht⟩)
    (r : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (a : Vec) :
    HasFDerivAt (fun b => flowLabelJet η r (t, b))
      (flowLabelJet η (r + 1) (t, a)).curryLeft a := by
  have hs := flow_representative_slice_contDiff hΓ hrep ht
  have hd := ((ContDiff.differentiable_iteratedFDeriv (n := ∞) (m := r)
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl r) hs) a).hasFDerivAt
  apply hd.congr_fderiv
  ext h v
  rfl

/-- Every literal forcing jet is the actual finite ordered-partition polynomial. -/
theorem flowForcingJet_eq_partition_sum {T : ℝ}
    {u η : Velocity} (hu : SmoothVelocityOn T u)
    (hη : ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ ∞ (η t))
    (r : ℕ) (z : ℝ × Vec) (hz : z ∈ finiteSpacetime T) :
    flowForcingJet u η r z = ∑ c : OrderedFinpartition r,
      c.compAlongOrderedFinpartition
        (flowSpatialJet u c.length z.1 (η z.1 z.2))
        (fun i => flowLabelJet η (c.partSize i) z) := by
  simpa only [flowForcingJet, flowSpatialJet, flowLabelJet,
    FormalMultilinearSeries.taylorComp,
    FormalMultilinearSeries.compAlongOrderedFinpartition, ftaylorSeries,
    Function.comp_def] using
    iteratedFDeriv_comp (finite_velocity_slice_smooth hu hz).contDiffAt
      (hη z.1 hz).contDiffAt (i := r)
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl r)

/-- Concrete Faà di Bruno forcing closes every finite-order simultaneous induction. -/
theorem flowForcingJet_contDiffOn {T : ℝ} (hT : 0 < T)
    {u η : Velocity} (hu : SmoothVelocityOn T u)
    (hη : ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ ∞ (η t))
    (n : ℕ) (hJ : ∀ r, ContDiffOn ℝ n (flowLabelJet η r) (finiteSpacetime T))
    (r : ℕ) : ContDiffOn ℝ n (flowForcingJet u η r) (finiteSpacetime T) := by
  have hηn : ContDiffOn ℝ n (fun z : ℝ × Vec => η z.1 z.2)
      (finiteSpacetime T) :=
    (continuousMultilinearCurryFin0 ℝ Vec Vec).contDiff.comp_contDiffOn (hJ 0)
  have hinner : ContDiffOn ℝ n (fun z : ℝ × Vec => (z.1, η z.1 z.2))
      (finiteSpacetime T) := contDiffOn_fst.prodMk hηn
  have hterm : ∀ c : OrderedFinpartition r,
      ContDiffOn ℝ n (fun z : ℝ × Vec =>
        c.compAlongOrderedFinpartition
          (flowSpatialJet u c.length z.1 (η z.1 z.2))
          (fun i => flowLabelJet η (c.partSize i) z)) (finiteSpacetime T) := by
    intro c
    have houter := ((flowSpatialJet_contDiffOn hT hu c.length).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).comp hinner (fun _ hz => hz)
    exact flow_contDiffOn_multilinear_apply c.length
      (fun i => FlowJet (c.partSize i))
      (fun z => c.compAlongOrderedFinpartitionL ℝ Vec Vec Vec
        (flowSpatialJet u c.length z.1 (η z.1 z.2)))
      (fun z i => flowLabelJet η (c.partSize i) z)
      ((c.compAlongOrderedFinpartitionL ℝ Vec Vec Vec).contDiff.comp_contDiffOn houter)
      (fun i => hJ (c.partSize i))
  have hsum := ContDiffOn.sum (s := Finset.univ) (fun c _ => hterm c)
  exact hsum.congr (fun z hz => flowForcingJet_eq_partition_sum hu hη r z hz)

/-- Joint closed-slab smoothness from a smooth path family and its actual jet integral identities.
The forcing closure and all derivative/continuity premises are discharged here. -/
theorem smoothVelocityOn_of_path_jet_integrals {T : ℝ} (hT : 0 < T)
    {u η : Velocity} (hu : SmoothVelocityOn T u)
    {Γ : Vec → C(Icc (0 : ℝ) T, Vec)} (hΓ : ContDiff ℝ ∞ Γ)
    (hrep : ∀ t (ht : t ∈ Icc (0 : ℝ) T) a, η t a = Γ a ⟨t, ht⟩)
    (hbase : ∀ r s, s ∈ Icc (0 : ℝ) T → ∀ b : Vec,
      flowLabelJet η r (s, b) = flowLabelJet η r (0, b) +
        ∫ q in (0 : ℝ)..s, flowForcingJet u η r (q, b)) :
    SmoothVelocityOn T η := by
  apply smoothVelocityOn_of_flowJet_integrals hT (flowLabelJet η) (flowForcingJet u η)
  · exact flowLabelJet_continuousOn hΓ hrep
  · intro r t ht a
    exact flowLabelJet_hasFDerivAt hΓ hrep r ht a
  · exact hbase
  · exact fun n hJ r => flowForcingJet_contDiffOn hT hu
      (fun _ ht => flow_representative_slice_contDiff hΓ hrep ht) n hJ r
  · intro z _
    rfl

end

end ClassicalMechanicsAssembly
