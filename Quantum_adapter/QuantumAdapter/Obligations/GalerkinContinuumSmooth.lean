import QuantumAdapter.Obligations.ContinuumSeries
import QuantumAdapter.Obligations.FourierTimeTower
import QuantumAdapter.Obligations.ForwardSpatial
import QuantumAdapter.Obligations.GalerkinLimits

/-!
# Closed-halfspace smooth Fourier reconstruction from an actual time-derivative tower

The tower equations and finite Sobolev sums are explicit inputs. Their
construction from the native Galerkin orbits is a separate compactness edge.
-/

set_option autoImplicit false
set_option Elab.async true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff

namespace QuantumAdapter.Obligations
open SingularClosure QuantumAdapter.Assembly
noncomputable section

theorem FourierTimeTowerBounds.weighted_coefficient_decay
    {d : ℕ → ℝ → FourierCoeff} (hb : FourierTimeTowerBounds d)
    (n m : ℕ) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → t ≤ T → ∀ k i,
      torusSobolevWeight k ^ m * ‖d n t k i‖ ≤ C * (torusSobolevWeight k)⁻¹ ^ 4 := by
  obtain ⟨C, hC, hbound⟩ := hb n (m + 4) T hT
  refine ⟨Real.sqrt C, Real.sqrt_nonneg C, ?_⟩
  intro t ht htT k i
  have hs : ‖sobolevWeightedCoeff (m + 4) (d n t) (k, i)‖ ^ 2 ≤ C := by
    simpa only [Finset.sum_singleton] using hbound t ht htT {(k, i)}
  have hr := Real.sqrt_le_sqrt hs
  rw [Real.sqrt_sq (norm_nonneg _), sobolevWeightedCoeff_norm_eq] at hr
  have hw : 0 < torusSobolevWeight k ^ 4 := pow_pos (torusSobolevWeight_pos k) 4
  have hdiv : torusSobolevWeight k ^ m * ‖d n t k i‖ ≤
      Real.sqrt C / torusSobolevWeight k ^ 4 := by
    apply (le_div_iff₀ hw).2
    calc
      _ = torusSobolevWeight k ^ (m + 4) * ‖d n t k i‖ := by rw [pow_add]; ring
      _ ≤ Real.sqrt C := hr
  simpa only [div_eq_mul_inv, inv_pow] using hdiv

theorem FourierTimeTowerBounds.mem_sobolev
    {d : ℕ → ℝ → FourierCoeff} (hb : FourierTimeTowerBounds d)
    (n m : ℕ) (t : ℝ) (ht : 0 ≤ t) : Memℓp (sobolevWeightedCoeff m (d n t)) 2 := by
  obtain ⟨C, hC, hbound⟩ := hb n m (t + 1) (by linarith)
  apply memℓp_gen' (C := C)
  intro I
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hbound t ht (by linarith) I

structure FourierJetIndex where
  time : ℕ
  spatial : List (Fin 3)
  component : Fin 3

def fourierJetStep : Option (Fin 3) → FourierJetIndex → FourierJetIndex
  | none, a => ⟨a.time + 1, a.spatial, a.component⟩
  | some j, a => ⟨a.time, j :: a.spatial, a.component⟩

def fourierWordSymbol (w : List (Fin 3)) (k : Frequency) : ℂ :=
  (w.map (fun j => derivativeSymbol j k)).prod

@[simp] theorem fourierWordSymbol_nil (k : Frequency) : fourierWordSymbol [] k = 1 := rfl
@[simp] theorem fourierWordSymbol_cons (j : Fin 3) (w : List (Fin 3)) (k : Frequency) :
    fourierWordSymbol (j :: w) k = derivativeSymbol j k * fourierWordSymbol w k := rfl

theorem derivativeSymbol_norm_le_weight (j : Fin 3) (k : Frequency) :
    ‖derivativeSymbol j k‖ ≤ (2 * Real.pi) * torusSobolevWeight k := by
  rw [derivativeSymbol_norm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h := (norm_le_pi_norm (fun l : Fin 3 => (k l : ℝ)) j).trans
    (frequencyLatticePoint_norm_le_weight k)
  simpa only [Real.norm_eq_abs] using h

theorem fourierWordSymbol_norm_le (w : List (Fin 3)) (k : Frequency) :
    ‖fourierWordSymbol w k‖ ≤ (2 * Real.pi) ^ w.length * torusSobolevWeight k ^ w.length := by
  induction w with
  | nil => simp
  | cons j w ih =>
    rw [fourierWordSymbol_cons, norm_mul]
    calc
      _ ≤ ((2 * Real.pi) * torusSobolevWeight k) *
          ((2 * Real.pi) ^ w.length * torusSobolevWeight k ^ w.length) :=
        mul_le_mul (derivativeSymbol_norm_le_weight j k) ih (norm_nonneg _)
          (mul_nonneg (by positivity) (torusSobolevWeight_pos k).le)
      _ = _ := by simp only [List.length_cons, pow_succ]; ring

def spacetimeCoordinate : Option (Fin 3) → (ℝ × Vec) →L[ℝ] ℂ
  | none => Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ Vec)
  | some j => Complex.ofRealCLM.comp
      ((EuclideanSpace.proj j : Vec →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Vec))

def fourierJetTerm (d : ℕ → ℝ → FourierCoeff) (a : FourierJetIndex)
    (k : Frequency) (z : ℝ × Vec) : ℂ :=
  fourierCharacter k z.2 * (fourierWordSymbol a.spatial k * d a.time z.1 k a.component)

def fourierJetSynthesis (d : ℕ → ℝ → FourierCoeff) (a : FourierJetIndex)
    (z : ℝ × Vec) : ℂ := ∑' k, fourierJetTerm d a k z

theorem FourierTimeTowerBounds.uniform_jet_summable_bound
    {d : ℕ → ℝ → FourierCoeff} (hb : FourierTimeTowerBounds d)
    (a : FourierJetIndex) (T : ℝ) (hT : 0 < T) :
    ∃ b : Frequency → ℝ, Summable b ∧ (∀ k, 0 ≤ b k) ∧
      ∀ z : ℝ × Vec, 0 ≤ z.1 → z.1 ≤ T → ∀ k, ‖fourierJetTerm d a k z‖ ≤ b k := by
  obtain ⟨C, hC, hbound⟩ := hb.weighted_coefficient_decay a.time a.spatial.length T hT
  refine ⟨fun k => ((2 * Real.pi) ^ a.spatial.length * C) *
    (torusSobolevWeight k)⁻¹ ^ 4,
    summable_torusSobolevWeight_inv_four.mul_left _, ?_, ?_⟩
  · intro k
    positivity
  · intro z hz hzT k
    simp only [fourierJetTerm, norm_mul, fourierCharacter_norm, one_mul]
    calc
      _ ≤ ((2 * Real.pi) ^ a.spatial.length * torusSobolevWeight k ^ a.spatial.length) *
          ‖d a.time z.1 k a.component‖ :=
        mul_le_mul_of_nonneg_right (fourierWordSymbol_norm_le _ _) (norm_nonneg _)
      _ = (2 * Real.pi) ^ a.spatial.length *
          (torusSobolevWeight k ^ a.spatial.length * ‖d a.time z.1 k a.component‖) := by ring
      _ ≤ (2 * Real.pi) ^ a.spatial.length * (C * (torusSobolevWeight k)⁻¹ ^ 4) :=
        mul_le_mul_of_nonneg_left (hbound z.1 hz hzT k a.component) (by positivity)
      _ = _ := by ring

theorem FourierTimeTowerBounds.jet_summable_norm
    {d : ℕ → ℝ → FourierCoeff} (hb : FourierTimeTowerBounds d)
    (a : FourierJetIndex) (z : ℝ × Vec) (hz : 0 ≤ z.1) :
    Summable (fun k => ‖fourierJetTerm d a k z‖) := by
  obtain ⟨b, hb', hb₀, hbound⟩ := hb.uniform_jet_summable_bound a (z.1 + 1) (by linarith)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (hbound z hz (by linarith)) hb'

/-- Every literal Fourier term has the derivative prescribed by the time/spatial jet shift. -/
theorem fourierJetTerm_hasFDerivWithinAt
    {d : ℕ → ℝ → FourierCoeff} (hd : FourierTimeTowerDerivative d)
    (a : FourierJetIndex) (k : Frequency) (z : ℝ × Vec) (hz : z ∈ forwardSpacetime) :
    HasFDerivWithinAt (fourierJetTerm d a k)
      (∑ j : Option (Fin 3), fourierJetTerm d (fourierJetStep j a) k z • spacetimeCoordinate j)
      forwardSpacetime z := by
  have ht := (hd a.time z.1 hz k a.component).hasFDerivWithinAt.comp z
    (ContinuousLinearMap.fst ℝ ℝ Vec).hasFDerivAt.hasFDerivWithinAt
    (fun y hy => hy)
  have hx := (fourierCharacter_hasFDerivAt k z.2).comp_hasFDerivWithinAt z
    ((ContinuousLinearMap.snd ℝ ℝ Vec).hasFDerivAt.hasFDerivWithinAt
      (s := forwardSpacetime))
  have h := hx.mul (ht.const_mul (fourierWordSymbol a.spatial k))
  convert! h using 1
  ext v
  simp only [Fintype.sum_option, fourierJetTerm, fourierJetStep, spacetimeCoordinate,
    fourierWordSymbol_cons, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.fst_apply, ContinuousLinearMap.snd_apply,
    Complex.ofRealCLM_apply, EuclideanSpace.coe_proj, smul_eq_mul,
    Complex.real_smul, fourierPhaseCLM, Finset.sum_mul, Finset.mul_sum]
  simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring

def forwardTimeSlab (T : ℝ) : Set (ℝ × Vec) :=
  forwardSpacetime ∩ {z | z.1 < T}

theorem forwardTimeSlab_convex (T : ℝ) : Convex ℝ (forwardTimeSlab T) := by
  exact (convex_Ico (0 : ℝ) T).linear_preimage (LinearMap.fst ℝ ℝ Vec)

theorem forwardTimeSlab_uniqueDiffOn (T : ℝ) : UniqueDiffOn ℝ (forwardTimeSlab T) :=
  uniqueDiffOn_forwardSpacetime.inter (isOpen_lt continuous_fst continuous_const)

theorem FourierTimeTowerBounds.uniform_jet_derivative_bound
    {d : ℕ → ℝ → FourierCoeff} (hb : FourierTimeTowerBounds d)
    (a : FourierJetIndex) (T : ℝ) (hT : 0 < T) :
    ∃ b : Frequency → ℝ, Summable b ∧ (∀ k, 0 ≤ b k) ∧
      ∀ z ∈ forwardTimeSlab T, ∀ k,
        ‖∑ j : Option (Fin 3), fourierJetTerm d (fourierJetStep j a) k z •
          spacetimeCoordinate j‖ ≤ b k := by
  choose b hbs hb₀ hbound using (fun j : Option (Fin 3) =>
    hb.uniform_jet_summable_bound (fourierJetStep j a) T hT)
  refine ⟨fun k => ∑ j : Option (Fin 3), b j k * ‖spacetimeCoordinate j‖,
    summable_sum (fun j _ => (hbs j).mul_right _), ?_, ?_⟩
  · intro k
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hb₀ j k) (norm_nonneg _))
  · intro z hz k
    calc
      _ ≤ ∑ j : Option (Fin 3), ‖fourierJetTerm d (fourierJetStep j a) k z •
          spacetimeCoordinate j‖ := norm_sum_le _ _
      _ ≤ ∑ j : Option (Fin 3), b j k * ‖spacetimeCoordinate j‖ := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (hbound j z hz.1 hz.2.le k) (norm_nonneg _)

/-- Joint differentiation of the actual series is valid up to and including time zero. -/
theorem fourierJetSynthesis_hasFDerivWithinAt_slab
    {d : ℕ → ℝ → FourierCoeff} (hd : FourierTimeTowerDerivative d)
    (hb : FourierTimeTowerBounds d) (a : FourierJetIndex) (T : ℝ) (hT : 0 < T)
    (z : ℝ × Vec) (hz : z ∈ forwardTimeSlab T) :
    HasFDerivWithinAt (fourierJetSynthesis d a)
      (∑ j : Option (Fin 3), fourierJetSynthesis d (fourierJetStep j a) z • spacetimeCoordinate j)
      (forwardTimeSlab T) z := by
  obtain ⟨b, hbs, hb₀, hbound⟩ := hb.uniform_jet_derivative_bound a T hT
  have h := hasFDerivWithinAt_tsum_of_convex_bound (forwardTimeSlab_convex T)
    (fun y hy => hb.jet_summable_norm a y hy.1) b hbs hb₀
    (fun k y hy => hbound y hy k)
    (fun k y hy => (fourierJetTerm_hasFDerivWithinAt hd a k y hy.1).mono
      (fun w hw => hw.1)) z hz
  have hs (j : Option (Fin 3)) : Summable (fun k =>
      fourierJetTerm d (fourierJetStep j a) k z • spacetimeCoordinate j) :=
    (hb.jet_summable_norm (fourierJetStep j a) z hz.1).of_norm.smul_const _
  have heq : (∑' k : Frequency, ∑ j : Option (Fin 3),
      fourierJetTerm d (fourierJetStep j a) k z • spacetimeCoordinate j) =
      ∑ j : Option (Fin 3), fourierJetSynthesis d (fourierJetStep j a) z •
        spacetimeCoordinate j := by
    rw [Summable.tsum_finsetSum (fun j _ => hs j)]
    apply Finset.sum_congr rfl
    intro j hj
    exact (hb.jet_summable_norm (fourierJetStep j a) z hz.1).of_norm.tsum_smul_const _
  rw [heq] at h
  exact h

theorem fourierJetSynthesis_contDiffOn_slab
    {d : ℕ → ℝ → FourierCoeff} (hd : FourierTimeTowerDerivative d)
    (hb : FourierTimeTowerBounds d) (a : FourierJetIndex) (T : ℝ) (hT : 0 < T) :
    ContDiffOn ℝ ∞ (fourierJetSynthesis d a) (forwardTimeSlab T) :=
  contDiffOn_of_finite_derivative_family (forwardTimeSlab T)
    (forwardTimeSlab_uniqueDiffOn T) (fourierJetSynthesis d) fourierJetStep spacetimeCoordinate
    (fun a z hz => fourierJetSynthesis_hasFDerivWithinAt_slab hd hb a T hT z hz) a

/-- The reconstructed mixed-derivative family is jointly smooth on the entire closed halfspace. -/
theorem fourierJetSynthesis_contDiffOn
    {d : ℕ → ℝ → FourierCoeff} (hd : FourierTimeTowerDerivative d)
    (hb : FourierTimeTowerBounds d) (a : FourierJetIndex) :
    ContDiffOn ℝ ∞ (fourierJetSynthesis d a) forwardSpacetime := by
  apply contDiffOn_of_locally_contDiffOn
  intro z hz
  refine ⟨{y : ℝ × Vec | y.1 < z.1 + 1}, isOpen_lt continuous_fst continuous_const,
    by dsimp; linarith, ?_⟩
  exact fourierJetSynthesis_contDiffOn_slab hd hb a (z.1 + 1) (by change 0 ≤ z.1 at hz; linarith)

/-- Full native velocity smoothness, including the initial-time boundary. -/
theorem smoothFourierSynthesis_timeTower_contDiffOn
    {d : ℕ → ℝ → FourierCoeff} (hd : FourierTimeTowerDerivative d)
    (hb : FourierTimeTowerBounds d) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => smoothFourierSynthesis (d n z.1) z.2)
      forwardSpacetime := by
  apply (contDiffOn_piLp 2).2
  intro i
  have hs := Complex.reCLM.contDiff.comp_contDiffOn
    (fourierJetSynthesis_contDiffOn hd hb ⟨n, [], i⟩)
  simpa only [smoothFourierSynthesis, fourierJetSynthesis, fourierJetTerm,
    fourierWordSymbol_nil, one_mul, scalarFourierSeries, Function.comp_def,
    Complex.reCLM_apply] using! hs

/-- The same summed derivative on the whole forward halfspace, localized only in time. -/
theorem fourierJetSynthesis_hasFDerivWithinAt
    {d : ℕ → ℝ → FourierCoeff} (hd : FourierTimeTowerDerivative d)
    (hb : FourierTimeTowerBounds d) (a : FourierJetIndex)
    (z : ℝ × Vec) (hz : z ∈ forwardSpacetime) :
    HasFDerivWithinAt (fourierJetSynthesis d a)
      (∑ j : Option (Fin 3), fourierJetSynthesis d (fourierJetStep j a) z • spacetimeCoordinate j)
      forwardSpacetime z := by
  have hT : 0 < z.1 + 1 := by change 0 ≤ z.1 at hz; linarith
  have hzT : z.1 < z.1 + 1 := by linarith
  apply (fourierJetSynthesis_hasFDerivWithinAt_slab hd hb a (z.1 + 1) hT z
    ⟨hz, hzT⟩).mono_of_mem_nhdsWithin
  exact inter_mem self_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds ((isOpen_lt continuous_fst continuous_const).mem_nhds hzT))

theorem fourierJetSynthesis_hasDerivWithinAt_time
    {d : ℕ → ℝ → FourierCoeff} (hd : FourierTimeTowerDerivative d)
    (hb : FourierTimeTowerBounds d) (a : FourierJetIndex)
    (t : ℝ) (ht : 0 ≤ t) (x : Vec) :
    HasDerivWithinAt (fun s => fourierJetSynthesis d a (s, x))
      (fourierJetSynthesis d (fourierJetStep none a) (t, x)) (Ici (0 : ℝ)) t := by
  have hj := fourierJetSynthesis_hasFDerivWithinAt hd hb a (t, x) ht
  have hi : HasDerivAt (fun s : ℝ => (s, x)) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have hc := hj.comp_hasDerivWithinAt t (hi.hasDerivWithinAt (s := Ici (0 : ℝ)))
    (fun s hs => hs)
  simpa [Function.comp_def, Fintype.sum_option, spacetimeCoordinate] using! hc

/-- The literal right-time derivative of the synthesized field is the next tower level. -/
theorem smoothFourierSynthesis_timeTower_hasDerivWithinAt
    {d : ℕ → ℝ → FourierCoeff} (hd : FourierTimeTowerDerivative d)
    (hb : FourierTimeTowerBounds d) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (x : Vec) :
    HasDerivWithinAt (fun s => smoothFourierSynthesis (d n s) x)
      (smoothFourierSynthesis (d (n + 1) t) x) (Ici (0 : ℝ)) t := by
  change HasFDerivWithinAt _
    ((1 : ℝ →L[ℝ] ℝ).smulRight (smoothFourierSynthesis (d (n + 1) t) x)) _ _
  apply (hasFDerivWithinAt_piLp 2).2
  intro i
  have hs := fourierJetSynthesis_hasDerivWithinAt_time hd hb ⟨n, [], i⟩ t ht x
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t hs
  have hr' : HasDerivWithinAt (fun s => smoothFourierSynthesis (d n s) x i)
      (smoothFourierSynthesis (d (n + 1) t) x i) (Ici (0 : ℝ)) t := by
    simpa only [smoothFourierSynthesis, fourierJetSynthesis, fourierJetTerm,
      fourierJetStep, fourierWordSymbol_nil, one_mul, scalarFourierSeries,
      Complex.reCLM_apply, Function.comp_def] using! hr
  convert! hr'.hasFDerivWithinAt using 1 <;> ext r <;> simp

theorem timeDerivative_smoothFourierSynthesis_timeTower
    {d : ℕ → ℝ → FourierCoeff} (hd : FourierTimeTowerDerivative d)
    (hb : FourierTimeTowerBounds d) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (x : Vec) :
    timeDerivative (fun s => smoothFourierSynthesis (d n s)) t x =
      smoothFourierSynthesis (d (n + 1) t) x :=
  (smoothFourierSynthesis_timeTower_hasDerivWithinAt hd hb n t ht x).derivWithin
    (uniqueDiffOn_Ici (0 : ℝ) t ht)

theorem smoothFourierSynthesis_timeTower_data_coefficients
    {d : ℕ → ℝ → FourierCoeff} (hb : FourierTimeTowerBounds d)
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hr : SpectralReality (d n t)) (hs : SpectralSolenoidal (d n t)) :
    NSEMaxwell.Classical.Data (smoothFourierSynthesis (d n t)) ∧
      datumFourierCoeff (smoothFourierSynthesis (d n t)) = d n t :=
  allSobolev_nativeData_and_coefficients (d n t) (fun m => hb.mem_sobolev n m t ht) hr hs

theorem smoothFourierSynthesis_timeTower_initial
    {d : ℕ → ℝ → FourierCoeff} (a : NSEMaxwell.Classical.Field)
    (ha : NSEMaxwell.Classical.Data a) (hzero : d 0 0 = datumFourierCoeff a) :
    smoothFourierSynthesis (d 0 0) = a := by
  rw [hzero]
  exact smoothFourierSynthesis_eq_original a ha.smooth ha.periodic

end
end QuantumAdapter.Obligations
