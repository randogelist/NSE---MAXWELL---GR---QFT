import GRAdapter.GermUniformity
import ML002.Endpoint
import ML003.Endpoint
import ML004.Endpoint
import ML006.Endpoint
import ML007.Endpoint
import ML010.Endpoint
import ML012.Endpoint
import ML013.Endpoint

/-!
Actual construction gluing for a finite spatial atlas and all integer translates.
The finite-index and compact-overlap hypotheses are geometric source data;
the result constructs a total function and proves its local equality and
periodicity. No already-glued solution, final project law, or new axiom is input.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology BigOperators

namespace NSEGR.Assembly
noncomputable section

/-- Precompact refinement of a compact set, retaining the larger source domains. -/
theorem finite_precompact_refinement
    {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    {K : Set X} (hK : IsCompact K) (U : K → Set X)
    (hU : ∀ i, IsOpen (U i)) (hmem : ∀ i : K, (i : X) ∈ U i) :
    ∃ (V : K → Set X) (t : Finset K),
      (∀ i, IsOpen (V i) ∧ IsCompact (closure (V i)) ∧ closure (V i) ⊆ U i) ∧
      K ⊆ ⋃ i ∈ t, V i := by
  classical
  choose C hC hiC hCU using fun i : K => GRTemp.ML002.endpoint (hU i) (hmem i)
  let V : K → Set X := fun i => interior (C i)
  have hv : ∀ i, IsOpen (V i) ∧ IsCompact (closure (V i)) ∧ closure (V i) ⊆ U i := by
    intro i
    have hs : closure (V i) ⊆ C i := closure_minimal interior_subset (hC i).isClosed
    exact ⟨isOpen_interior, (hC i).of_isClosed_subset isClosed_closure hs, hs.trans (hCU i)⟩
  have hcover : K ⊆ ⋃ i, V i := by
    intro x hx
    exact mem_iUnion_of_mem (⟨x, hx⟩ : K) (hiC ⟨x, hx⟩)
  obtain ⟨t, ht⟩ := GRTemp.ML003.endpoint hK V (fun i => (hv i).1) hcover
  exact ⟨V, t, hv, ht⟩

/-- Finite many compact families of joint equality germs have one parameter germ. -/
theorem finite_compact_overlap_uniform
    {S X Y ι : Type*} [TopologicalSpace S] [TopologicalSpace X] [Finite ι]
    {s0 : S} (C : ι → Set X) (hC : ∀ i, IsCompact (C i))
    (f g : ι → S → X → Y)
    (hlocal : ∀ i, ∀ x ∈ C i,
      ∀ᶠ z : S × X in 𝓝 (s0, x), f i z.1 z.2 = g i z.1 z.2) :
    ∀ᶠ s in 𝓝 s0, ∀ i, ∀ x ∈ C i, f i s x = g i s x := by
  exact Filter.eventually_all.2 (fun i => GRTemp.ML004.endpoint (hC i) (hlocal i))

/-- The actual union-lift, totalized only outside its supplied domain. -/
def overlapGlue {X Y ι : Type*} (U : ι → Set X) (f : ι → X → Y)
    (D : Set X) (hcover : D ⊆ ⋃ i, U i)
    (hcompat : ∀ i j x, x ∈ U i → x ∈ U j → f i x = f j x)
    (outside : Y) (x : X) : Y := by
  classical
  exact if hx : x ∈ D then
    GRTemp.ML006.endpoint U (fun i z => f i z)
      (fun i j y hi hj => hcompat i j y hi hj) D hcover ⟨x, hx⟩
  else outside

theorem overlapGlue_eq {X Y ι : Type*} (U : ι → Set X) (f : ι → X → Y)
    (D : Set X) (hcover : D ⊆ ⋃ i, U i)
    (hcompat : ∀ i j x, x ∈ U i → x ∈ U j → f i x = f j x)
    (outside : Y) {x : X} (hxD : x ∈ D) {i : ι} (hxU : x ∈ U i) :
    overlapGlue U f D hcover hcompat outside x = f i x := by
  classical
  rw [overlapGlue, dif_pos hxD]
  exact GRTemp.ML007.endpoint
    (S := U) (f := fun i z => f i z)
    (hf := fun i j y hi hj => hcompat i j y hi hj) (hT := hcover) ⟨x, hxD⟩ hxU

theorem overlapGlue_eventuallyEq
    {X Y ι : Type*} [TopologicalSpace X]
    (U : ι → Set X) (f : ι → X → Y) (D : Set X)
    (hcover : D ⊆ ⋃ i, U i)
    (hcompat : ∀ i j x, x ∈ U i → x ∈ U j → f i x = f j x)
    (outside : Y) (hD : IsOpen D) (hU : ∀ i, IsOpen (U i))
    {x : X} (hxD : x ∈ D) {i : ι} (hxU : x ∈ U i) :
    overlapGlue U f D hcover hcompat outside =ᶠ[𝓝 x] f i := by
  filter_upwards [hD.mem_nhds hxD, (hU i).mem_nhds hxU] with y hyD hyU
  exact overlapGlue_eq U f D hcover hcompat outside hyD hyU

theorem overlapGlue_analyticAt
    {X Y ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : ι → Set X) (f : ι → X → Y) (D : Set X)
    (hcover : D ⊆ ⋃ i, U i)
    (hcompat : ∀ i j x, x ∈ U i → x ∈ U j → f i x = f j x)
    (outside : Y) (hD : IsOpen D) (hU : ∀ i, IsOpen (U i))
    {x : X} (hxD : x ∈ D) {i : ι} (hxU : x ∈ U i)
    (hf : AnalyticAt ℝ (f i) x) :
    AnalyticAt ℝ (overlapGlue U f D hcover hcompat outside) x := by
  exact GRTemp.ML010.endpoint hf
    (overlapGlue_eventuallyEq U f D hcover hcompat outside hD hU hxD hxU).symm

theorem overlapGlue_fderiv
    {X Y ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : ι → Set X) (f : ι → X → Y) (D : Set X)
    (hcover : D ⊆ ⋃ i, U i)
    (hcompat : ∀ i j x, x ∈ U i → x ∈ U j → f i x = f j x)
    (outside : Y) (hD : IsOpen D) (hU : ∀ i, IsOpen (U i))
    {x : X} (hxD : x ∈ D) {i : ι} (hxU : x ∈ U i) :
    fderiv ℝ (overlapGlue U f D hcover hcompat outside) x = fderiv ℝ (f i) x := by
  exact GRTemp.ML012.endpoint
    (overlapGlue_eventuallyEq U f D hcover hcompat outside hD hU hxD hxU)

theorem overlapGlue_fderiv_eventuallyEq
    {X Y ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : ι → Set X) (f : ι → X → Y) (D : Set X)
    (hcover : D ⊆ ⋃ i, U i)
    (hcompat : ∀ i j x, x ∈ U i → x ∈ U j → f i x = f j x)
    (outside : Y) (hD : IsOpen D) (hU : ∀ i, IsOpen (U i))
    {x : X} (hxD : x ∈ D) {i : ι} (hxU : x ∈ U i) :
    fderiv ℝ (overlapGlue U f D hcover hcompat outside) =ᶠ[𝓝 x] fderiv ℝ (f i) := by
  exact GRTemp.ML013.endpoint
    (overlapGlue_eventuallyEq U f D hcover hcompat outside hD hU hxD hxU)

theorem integerSpatialShift_add (n m : Frequency) :
    integerSpatialShift (n + m) = integerSpatialShift n + integerSpatialShift m := by
  ext i
  change integerSpatialShift (n + m) i = integerSpatialShift n i + integerSpatialShift m i
  simp only [integerSpatialShift_apply, Pi.add_apply, Int.cast_add]

theorem integerSpatialShift_sub (n m : Frequency) :
    integerSpatialShift (n - m) = integerSpatialShift n - integerSpatialShift m := by
  ext i
  change integerSpatialShift (n - m) i = integerSpatialShift n i - integerSpatialShift m i
  simp only [integerSpatialShift_apply, Pi.sub_apply, Int.cast_sub]

theorem integerSpatialShift_single (i : Fin 3) :
    integerSpatialShift (Pi.single i (1 : ℤ)) = unitVector i := by
  ext j
  simp [integerSpatialShift_apply, unitVector, PiLp.single_apply, Pi.single_apply]

def latticePatch {ι : Type*} (U : ι → Set Vec) (a : ι × Frequency) : Set Vec :=
  {x | x - integerSpatialShift a.2 ∈ U a.1}

def latticeLocal {S Y ι : Type*} (f : ι → S → Vec → Y) (a : ι × Frequency)
    (s : S) (x : Vec) : Y := f a.1 s (x - integerSpatialShift a.2)

theorem latticePatch_isOpen {ι : Type*} (U : ι → Set Vec)
    (hU : ∀ i, IsOpen (U i)) (a : ι × Frequency) : IsOpen (latticePatch U a) :=
  (hU a.1).preimage (continuous_id.sub continuous_const)

theorem latticePatch_cover {ι : Type*} (U : ι → Set Vec)
    (hcover : unitCube ⊆ ⋃ i, U i) (x : Vec) : ∃ a, x ∈ latticePatch U a := by
  have hr := hcover (spatialCellRepresentative_mem_unitCube x)
  rcases mem_iUnion.1 hr with ⟨i, hi⟩
  refine ⟨(i, fun j => ⌊x j⌋), ?_⟩
  have hx : x - integerSpatialShift (fun j => ⌊x j⌋) = spatialCellRepresentative x := by
    apply sub_eq_iff_eq_add.mpr
    exact (spatialCellRepresentative_add_shift x).symm
  change x - integerSpatialShift (fun j => ⌊x j⌋) ∈ U i
  rwa [hx]

/-- Finite relative translations; this type has 7^3 elements. -/
abbrev BoundedLatticeShift := Fin 3 → Set.Icc (-3 : ℤ) 3

def boundedShiftVector (a : BoundedLatticeShift) : Frequency := fun i => (a i).val

theorem lattice_relative_shift_bound {ι : Type*} (U : ι → Set Vec)
    (hbox : ∀ i, ∀ y ∈ U i, ∀ j, (-1 : ℝ) < y j ∧ y j < 2)
    {a b : ι × Frequency} {x : Vec}
    (ha : x ∈ latticePatch U a) (hb : x ∈ latticePatch U b) (j : Fin 3) :
    (-3 : ℤ) ≤ b.2 j - a.2 j ∧ b.2 j - a.2 j ≤ 3 := by
  have hya := hbox a.1 _ ha j
  have hyb := hbox b.1 _ hb j
  change (-1 : ℝ) < x j - integerSpatialShift a.2 j ∧
    x j - integerSpatialShift a.2 j < 2 at hya
  change (-1 : ℝ) < x j - integerSpatialShift b.2 j ∧
    x j - integerSpatialShift b.2 j < 2 at hyb
  rw [integerSpatialShift_apply] at hya hyb
  constructor
  · have h : (-3 : ℝ) ≤ (b.2 j : ℝ) - (a.2 j : ℝ) := by linarith
    exact_mod_cast h
  · have h : (b.2 j : ℝ) - (a.2 j : ℝ) ≤ 3 := by linarith
    exact_mod_cast h

def compactLatticeOverlap {ι : Type*} (U : ι → Set Vec)
    (i j : ι) (a : BoundedLatticeShift) : Set Vec :=
  closure (U i) ∩ {x | x - integerSpatialShift (boundedShiftVector a) ∈ closure (U j)}

theorem compactLatticeOverlap_isCompact {ι : Type*} (U : ι → Set Vec)
    (hU : ∀ i, IsCompact (closure (U i))) (i j : ι) (a : BoundedLatticeShift) :
    IsCompact (compactLatticeOverlap U i j a) := by
  exact (hU i).inter_right
    (isClosed_closure.preimage (continuous_id.sub continuous_const))

/-- Local germs on finitely many compact relative overlaps imply compatibility
on all infinitely many translated open patches at one common parameter germ. -/
theorem lattice_overlap_germs_uniform
    {S Y ι : Type*} [TopologicalSpace S] [Finite ι] {s0 : S}
    (U : ι → Set Vec) (f : ι → S → Vec → Y)
    (hcompact : ∀ i, IsCompact (closure (U i)))
    (hbox : ∀ i, ∀ y ∈ U i, ∀ j, (-1 : ℝ) < y j ∧ y j < 2)
    (hlocal : ∀ i j (a : BoundedLatticeShift), ∀ x ∈ compactLatticeOverlap U i j a,
      ∀ᶠ z : S × Vec in 𝓝 (s0, x),
        f i z.1 z.2 = f j z.1 (z.2 - integerSpatialShift (boundedShiftVector a))) :
    ∀ᶠ s in 𝓝 s0, ∀ a b : ι × Frequency, ∀ x,
      x ∈ latticePatch U a → x ∈ latticePatch U b →
        latticeLocal f a s x = latticeLocal f b s x := by
  have hfinite := finite_compact_overlap_uniform
    (fun a : ι × ι × BoundedLatticeShift => compactLatticeOverlap U a.1 a.2.1 a.2.2)
    (fun a => compactLatticeOverlap_isCompact U hcompact a.1 a.2.1 a.2.2)
    (fun a s x => f a.1 s x)
    (fun a s x => f a.2.1 s (x - integerSpatialShift (boundedShiftVector a.2.2)))
    (fun a => hlocal a.1 a.2.1 a.2.2)
  filter_upwards [hfinite] with s hs
  intro a b x ha hb
  let ell : BoundedLatticeShift := fun j =>
    ⟨b.2 j - a.2 j, lattice_relative_shift_bound U hbox ha hb j⟩
  have hshift : integerSpatialShift (boundedShiftVector ell) =
      integerSpatialShift b.2 - integerSpatialShift a.2 :=
    integerSpatialShift_sub b.2 a.2
  have hsub : x - integerSpatialShift a.2 - integerSpatialShift (boundedShiftVector ell) =
      x - integerSpatialShift b.2 := by rw [hshift]; abel
  have hmem : x - integerSpatialShift a.2 ∈ compactLatticeOverlap U a.1 b.1 ell := by
    constructor
    · exact subset_closure ha
    · change x - integerSpatialShift a.2 - integerSpatialShift (boundedShiftVector ell) ∈ closure (U b.1)
      rw [hsub]
      exact subset_closure hb
  have heq := hs (a.1, b.1, ell) _ hmem
  simpa only [latticeLocal, hsub] using heq

end
end NSEGR.Assembly
