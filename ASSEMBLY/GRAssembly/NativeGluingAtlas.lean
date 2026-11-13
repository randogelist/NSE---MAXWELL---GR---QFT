import GRAssembly.PeriodicWitness
import ML001.Endpoint

/-! Actual periodic construction from point-local, unique differential-law germs.
The closure margins and translated compatibility are constructed in the body. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology

namespace NSEGR.Assembly
noncomputable section

def spatialTranslate {S Y : Type*} (f : S × Vec → Y) (n : Frequency) : S × Vec → Y :=
  fun z => f (z.1, z.2 - integerSpatialShift n)

/-- The open box retaining finitely many possible relative integer shifts. -/
def gluingSpatialBox : Set Vec := {x | ∀ j : Fin 3, (-1 : ℝ) < x j ∧ x j < 2}

theorem gluingSpatialBox_isOpen : IsOpen gluingSpatialBox := by
  have hset : gluingSpatialBox =
      ⋂ j : Fin 3, {x : Vec | (-1 : ℝ) < x j ∧ x j < 2} := by
    ext x
    simp only [gluingSpatialBox, mem_setOf_eq, mem_iInter]
  rw [hset]
  apply isOpen_iInter_of_finite
  intro j
  exact isOpen_Ioo.preimage (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) j)

theorem unitCube_subset_gluingSpatialBox : unitCube ⊆ gluingSpatialBox := by
  intro x hx j
  have hj := hx j
  constructor <;> linarith [hj.1, hj.2]

/-- Local existence, germ uniqueness and literal translation covariance create
one periodic field satisfying every supplied germ-local law on an open slab.
No compatible atlas or already-glued field occurs among the hypotheses. -/
theorem periodic_law_of_unique_local_germs
    {S Y : Type*} [TopologicalSpace S] {s0 : S}
    (Law : ((S × Vec) → Y) → S × Vec → Prop)
    (hex : ∀ x ∈ unitCube, ∃ f : S × Vec → Y,
      ∀ᶠ z in 𝓝 (s0, x), Law f z)
    (hlocality : ∀ f g z, f =ᶠ[𝓝 z] g → (Law f z ↔ Law g z))
    (htranslate : ∀ f z n,
      Law f (z.1, z.2 - integerSpatialShift n) → Law (spatialTranslate f n) z)
    (hunique : ∀ f g x,
      (∀ᶠ z in 𝓝 (s0, x), Law f z) →
      (∀ᶠ z in 𝓝 (s0, x), Law g z) → f =ᶠ[𝓝 (s0, x)] g)
    (outside : Y) :
    ∃ W : Set S, IsOpen W ∧ s0 ∈ W ∧ ∃ g : S × Vec → Y,
      (∀ s ∈ W, SpatialPeriodic (fun x => g (s, x))) ∧
      ∀ s ∈ W, ∀ x, Law g (s, x) := by
  classical
  choose f hf using fun x : unitCube => hex x x.property
  have hp (x : unitCube) :
      ∃ V O, IsOpen V ∧ s0 ∈ V ∧ IsOpen O ∧ (x : Vec) ∈ O ∧
        V ×ˢ O ⊆ {z | Law (f x) z} :=
    GRTemp.ML001.endpoint.mp (hf x)
  choose V O hV hsV hO hxO hsource using hp
  let O' : unitCube → Set Vec := fun i => O i ∩ gluingSpatialBox
  have hO' : ∀ i, IsOpen (O' i) := fun i => (hO i).inter gluingSpatialBox_isOpen
  have hxO' : ∀ i : unitCube, (i : Vec) ∈ O' i :=
    fun i => ⟨hxO i, unitCube_subset_gluingSpatialBox i.property⟩
  obtain ⟨U, t, hU, hcover⟩ :=
    finite_precompact_refinement isCompact_unitCube O' hO' hxO'
  let I := {i : unitCube // i ∈ t}
  let P : I → Set Vec := fun i => U i.val
  let F : I → S → Vec → Y := fun i s x => f i.val (s, x)
  have hP : ∀ i, IsOpen (P i) := fun i => (hU i.val).1
  have hcompact : ∀ i, IsCompact (closure (P i)) := fun i => (hU i.val).2.1
  have hmargin : ∀ i : I, closure (P i) ⊆ O i.val :=
    fun i => (hU i.val).2.2.trans inter_subset_left
  have hbox : ∀ i : I, ∀ y ∈ P i, ∀ j, (-1 : ℝ) < y j ∧ y j < 2 := by
    intro i y hy
    exact ((hU i.val).2.2 (subset_closure hy)).2
  have hcoverP : unitCube ⊆ ⋃ i : I, P i := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    obtain ⟨hit, hxi⟩ := mem_iUnion.mp hi
    exact mem_iUnion_of_mem (⟨i, hit⟩ : I) hxi
  have hrecenter (i : I) {x : Vec} (hx : x ∈ closure (P i)) :
      ∀ᶠ z in 𝓝 (s0, x), Law (f i.val) z := by
    have hs : ∀ᶠ s in 𝓝 s0, s ∈ V i.val := (hV i.val).mem_nhds (hsV i.val)
    have hx' : ∀ᶠ y in 𝓝 x, y ∈ O i.val := (hO i.val).mem_nhds (hmargin i hx)
    filter_upwards [hs.prodMk_nhds hx'] with z hz
    exact hsource i.val hz
  have hoverlap : ∀ i j (a : BoundedLatticeShift),
      ∀ x ∈ compactLatticeOverlap P i j a,
      ∀ᶠ z : S × Vec in 𝓝 (s0, x),
        F i z.1 z.2 = F j z.1 (z.2 - integerSpatialShift (boundedShiftVector a)) := by
    intro i j a x hx
    have hm : Tendsto
        (fun z : S × Vec => (z.1, z.2 - integerSpatialShift (boundedShiftVector a)))
        (𝓝 (s0, x)) (𝓝 (s0, x - integerSpatialShift (boundedShiftVector a))) :=
      (continuous_fst.prodMk (continuous_snd.sub continuous_const)).continuousAt.tendsto
    have ht : ∀ᶠ z in 𝓝 (s0, x),
        Law (spatialTranslate (f j.val) (boundedShiftVector a)) z := by
      filter_upwards [hm.eventually (hrecenter j hx.2)] with z hz
      exact htranslate _ z _ hz
    exact hunique (f i.val) (spatialTranslate (f j.val) (boundedShiftVector a)) x
      (hrecenter i hx.1) ht
  obtain ⟨W, hW, hsW, hdomains, g, hperiodic, hglued⟩ :=
    periodic_witness_of_compact_overlap_germs P (fun i => V i.val) F hP
      (fun i => (hV i.val).mem_nhds (hsV i.val)) hcoverP hcompact hbox hoverlap outside
  refine ⟨W, hW, hsW, (fun z => g z.1 z.2), hperiodic, ?_⟩
  intro s hs x
  obtain ⟨a, ha⟩ := latticePatch_cover P hcoverP x
  have hsrc : Law (f a.1.val) (s, x - integerSpatialShift a.2) :=
    hsource a.1.val ⟨hdomains a.1 hs, hmargin a.1 (subset_closure ha)⟩
  have htranslated := htranslate (f a.1.val) (s, x) a.2 hsrc
  exact (hlocality _ _ (s, x) (hglued a s hs x ha)).mpr htranslated

/-- A positive symmetric interval can be retained inside any real neighborhood. -/
theorem positive_timeInterval_subset {t0 δ : ℝ} {W : Set ℝ}
    (hδ : 0 < δ) (hW : W ∈ 𝓝 t0) :
    ∃ d : ℝ, 0 < d ∧ d ≤ δ ∧ timeInterval t0 d ⊆ W := by
  obtain ⟨a, b, ht, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp hW
  have hta : 0 < t0 - a := sub_pos.mpr ht.1
  have hbt : 0 < b - t0 := sub_pos.mpr ht.2
  let d := min δ (min (t0 - a) (b - t0)) / 2
  have hd : 0 < d := by
    exact half_pos (lt_min hδ (lt_min hta hbt))
  refine ⟨d, hd, ?_, ?_⟩
  · have hm : min δ (min (t0 - a) (b - t0)) ≤ δ := min_le_left _ _
    dsimp [d]
    linarith
  · intro t htt
    apply hab
    have hma : min δ (min (t0 - a) (b - t0)) ≤ t0 - a :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hmb : min δ (min (t0 - a) (b - t0)) ≤ b - t0 :=
      (min_le_right _ _).trans (min_le_right _ _)
    change t0 - d < t ∧ t < t0 + d at htt
    rcases htt with ⟨httl, httr⟩
    constructor <;> dsimp [d] at * <;> linarith

end
end NSEGR.Assembly
