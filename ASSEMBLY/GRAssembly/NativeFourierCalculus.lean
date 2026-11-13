import GRAdapter.LiteratureInputs

/-! Dimension-general calculus for the literal periodic Fourier input. -/
set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

namespace NSEGR.NativeLiterature
noncomputable section

variable {n : ℕ}

def coordinateDerivative (f : LiteratureSpace n → ℂ) (j : Fin n) :
    LiteratureSpace n → ℂ := fun x => fderiv ℝ f x (LiteratureUnitVector j)

def derivativeSymbol (j : Fin n) (k : LiteratureFrequency n) : ℂ :=
  2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)

def characterPhaseCLM (k : LiteratureFrequency n) : LiteratureSpace n →L[ℝ] ℂ :=
  ∑ j : Fin n, derivativeSymbol j k •
    (Complex.ofRealCLM.comp (EuclideanSpace.proj j))

theorem characterPhaseCLM_apply (k : LiteratureFrequency n) (x : LiteratureSpace n) :
    characterPhaseCLM k x =
      (2 * (Real.pi : ℂ) * Complex.I) *
        ((∑ j : Fin n, (k j : ℝ) * x j : ℝ) : ℂ) := by
  simp only [characterPhaseCLM, derivativeSymbol, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, EuclideanSpace.coe_proj, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

theorem characterPhaseCLM_unitVector (k : LiteratureFrequency n) (j : Fin n) :
    characterPhaseCLM k (LiteratureUnitVector j) = derivativeSymbol j k := by
  simp [characterPhaseCLM, LiteratureUnitVector, apply_ite, mul_ite]

theorem character_eq_exp_phase (k : LiteratureFrequency n) (x : LiteratureSpace n) :
    LiteratureCharacter k x = Complex.exp (characterPhaseCLM k x) := by
  rw [characterPhaseCLM_apply]
  rfl

theorem character_contDiff (k : LiteratureFrequency n) :
    ContDiff ℝ ∞ (LiteratureCharacter k) := by
  have heq : LiteratureCharacter k = fun x => Complex.exp (characterPhaseCLM k x) :=
    funext (character_eq_exp_phase k)
  rw [heq]
  exact (characterPhaseCLM k).contDiff.cexp

theorem character_hasFDerivAt (k : LiteratureFrequency n) (x : LiteratureSpace n) :
    HasFDerivAt (LiteratureCharacter k)
      (LiteratureCharacter k x • characterPhaseCLM k) x := by
  have hp : HasFDerivAt (fun y : LiteratureSpace n => characterPhaseCLM k y)
      (characterPhaseCLM k) x := (characterPhaseCLM k).hasFDerivAt
  have heq : LiteratureCharacter k = fun y => Complex.exp (characterPhaseCLM k y) :=
    funext (character_eq_exp_phase k)
  rw [heq]
  exact hp.cexp

theorem character_periodic (k : LiteratureFrequency n) :
    LiteraturePeriodic (LiteratureCharacter k) := by
  intro x j
  simp only [character_eq_exp_phase]
  rw [map_add, characterPhaseCLM_unitVector, Complex.exp_add]
  have hz : derivativeSymbol j k = (k j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    unfold derivativeSymbol
    ring
  rw [hz, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem character_norm (k : LiteratureFrequency n) (x : LiteratureSpace n) :
    ‖LiteratureCharacter k x‖ = 1 := by
  have heq : LiteratureCharacter k x =
      Complex.exp (((2 * Real.pi * ∑ j : Fin n, (k j : ℝ) * x j : ℝ) : ℂ) *
        Complex.I) := by
    unfold LiteratureCharacter
    congr 1
    push_cast
    ring
  rw [heq, Complex.norm_exp_ofReal_mul_I]

theorem coordinateDerivative_contDiff {f : LiteratureSpace n → ℂ}
    (hf : ContDiff ℝ ∞ f) (j : Fin n) :
    ContDiff ℝ ∞ (coordinateDerivative f j) :=
  (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const

theorem coordinateDerivative_periodic {f : LiteratureSpace n → ℂ}
    (hp : LiteraturePeriodic f) (j : Fin n) :
    LiteraturePeriodic (coordinateDerivative f j) := by
  intro x i
  have heq : (fun y : LiteratureSpace n => f (y + LiteratureUnitVector i)) = f :=
    funext (fun y => hp y i)
  have h := congrArg (fun g : LiteratureSpace n → ℂ => fderiv ℝ g x) heq
  have hd : fderiv ℝ f (x + LiteratureUnitVector i) = fderiv ℝ f x := by
    simpa only [fderiv_comp_add_right] using h
  exact congrArg (fun L : LiteratureSpace n →L[ℝ] ℂ => L (LiteratureUnitVector j)) hd

theorem partialWord_contDiff {f : LiteratureSpace n → ℂ}
    (hf : ContDiff ℝ ∞ f) (w : List (Fin n)) :
    ContDiff ℝ ∞ (LiteraturePartialWord w f) := by
  induction w with
  | nil => exact hf
  | cons j w ih => exact coordinateDerivative_contDiff ih j

theorem partialWord_periodic {f : LiteratureSpace n → ℂ}
    (hp : LiteraturePeriodic f) (w : List (Fin n)) :
    LiteraturePeriodic (LiteraturePartialWord w f) := by
  induction w with
  | nil => exact hp
  | cons j w ih => exact coordinateDerivative_periodic ih j

theorem cube_isCompact (n : ℕ) : IsCompact (LiteratureUnitCube n) := by
  have hc : IsCompact (Set.univ.pi (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hi := hc.image (PiLp.continuous_toLp (p := (2 : ENNReal))
    (β := fun _ : Fin n => ℝ))
  convert hi using 1
  ext x
  constructor
  · intro hx
    refine ⟨WithLp.ofLp x, ?_, ?_⟩
    · change ∀ i : Fin n, i ∈ Set.univ →
        0 ≤ WithLp.ofLp x i ∧ WithLp.ofLp x i ≤ 1
      intro i _
      exact hx i
    · simp
  · rintro ⟨y, hy, rfl⟩
    intro i
    exact hy i (Set.mem_univ i)

private theorem integral_cube_eq_integral_piCube (f : LiteratureSpace n → ℂ) :
    (∫ x in LiteratureUnitCube n, f x) =
      ∫ x in Icc (0 : Fin n → ℝ) (fun _ => 1), f (WithLp.toLp 2 x) := by
  have hchange := (PiLp.volume_preserving_toLp (Fin n)).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding f (LiteratureUnitCube n)
  have hpre : (@WithLp.toLp 2 (Fin n → ℝ)) ⁻¹' LiteratureUnitCube n =
      Icc (0 : Fin n → ℝ) (fun _ => 1) := by
    ext x
    constructor
    · intro hx
      exact ⟨fun i => (hx i).1, fun i => (hx i).2⟩
    · intro hx i
      exact ⟨hx.1 i, hx.2 i⟩
  rw [hpre] at hchange
  exact hchange.symm

private theorem insertNth_one_eq_insertNth_zero_add {m : ℕ}
    (i : Fin (m + 1)) (x : Fin m → ℝ) :
    i.insertNth (α := fun _ : Fin (m + 1) => ℝ) 1 x =
      i.insertNth (α := fun _ : Fin (m + 1) => ℝ) 0 x + Pi.single i 1 := by
  funext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩
  · simp
  · simp [Fin.succAbove_ne]

private theorem integral_piCube_divergence_eq_zero {m : ℕ}
    (f : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℂ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hp : ∀ i x, f i (x + Pi.single i 1) = f i x) :
    (∫ x in Icc (0 : Fin (m + 1) → ℝ) (fun _ => 1),
      ∑ i : Fin (m + 1), fderiv ℝ (f i) x (Pi.single i 1)) = 0 := by
  have hcont : Continuous (fun x : Fin (m + 1) → ℝ =>
      ∑ i : Fin (m + 1), fderiv ℝ (f i) x (Pi.single i 1)) :=
    continuous_finsetSum _ (fun i _ =>
      ((hf i).continuous_fderiv (by simp)).clm_apply continuous_const)
  have hdiv := integral_divergence_of_hasFDerivAt_off_countable'
    (0 : Fin (m + 1) → ℝ) (fun _ => 1) (by intro i; norm_num)
    f (fun i => fderiv ℝ (f i)) ∅ Set.countable_empty
    (fun i => (hf i).continuous.continuousOn)
    (fun x _ i => ((hf i).differentiable (by simp) x).hasFDerivAt)
    (hcont.continuousOn.integrableOn_compact isCompact_Icc)
  calc
    _ = ∑ i : Fin (m + 1),
        ((∫ x in Icc (fun _ : Fin m => (0 : ℝ)) (fun _ => 1),
          f i (i.insertNth 1 x)) -
         ∫ x in Icc (fun _ : Fin m => (0 : ℝ)) (fun _ => 1),
          f i (i.insertNth 0 x)) := hdiv
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have he : (fun x : Fin m → ℝ => f i (i.insertNth 1 x)) =
          (fun x => f i (i.insertNth 0 x)) := by
        funext x
        rw [insertNth_one_eq_insertNth_zero_add, hp]
      rw [he, sub_self]

private theorem integral_cube_divergence_eq_zero {m : ℕ}
    (f : Fin (m + 1) → LiteratureSpace (m + 1) → ℂ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hp : ∀ i x, f i (x + LiteratureUnitVector i) = f i x) :
    (∫ x in LiteratureUnitCube (m + 1),
      ∑ i : Fin (m + 1), fderiv ℝ (f i) x (LiteratureUnitVector i)) = 0 := by
  let L : (Fin (m + 1) → ℝ) ≃L[ℝ] LiteratureSpace (m + 1) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m + 1) => ℝ)).symm
  have hL (i : Fin (m + 1)) : L (Pi.single i 1) = LiteratureUnitVector i := by
    ext j
    rfl
  have hderiv (i : Fin (m + 1)) (x : Fin (m + 1) → ℝ) :
      fderiv ℝ (fun y => f i (L y)) x (Pi.single i 1) =
        fderiv ℝ (f i) (L x) (LiteratureUnitVector i) := by
    have h := ((hf i).differentiable (by simp) (L x)).hasFDerivAt.comp x L.hasFDerivAt
    have he := congrArg
      (fun D : (Fin (m + 1) → ℝ) →L[ℝ] ℂ => D (Pi.single i 1)) h.fderiv
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, hL] using he
  rw [integral_cube_eq_integral_piCube]
  change (∫ x in Icc (0 : Fin (m + 1) → ℝ) (fun _ => 1),
    ∑ i : Fin (m + 1), fderiv ℝ (f i) (L x) (LiteratureUnitVector i)) = 0
  have h := integral_piCube_divergence_eq_zero (fun i x => f i (L x))
    (fun i => (hf i).comp L.contDiff) (by
      intro i x
      rw [map_add, hL, hp])
  simpa only [hderiv] using h

theorem integral_cube_coordinateDerivative_eq_zero {f : LiteratureSpace n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : LiteraturePeriodic f) (j : Fin n) :
    (∫ x in LiteratureUnitCube n, coordinateDerivative f j x) = 0 := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ m =>
    classical
    let F : Fin (m + 1) → LiteratureSpace (m + 1) → ℂ :=
      fun l => if l = j then f else fun _ => 0
    have hF : ∀ l, ContDiff ℝ ∞ (F l) := by
      intro l
      by_cases hl : l = j
      · simpa [F, hl] using hf
      · simpa [F, hl] using
          (contDiff_const : ContDiff ℝ ∞ (fun _ : LiteratureSpace (m + 1) => (0 : ℂ)))
    have hperiod : ∀ l x, F l (x + LiteratureUnitVector l) = F l x := by
      intro l x
      by_cases hl : l = j
      · subst l
        simpa [F] using hp x j
      · simp [F, hl]
    have hsum (x : LiteratureSpace (m + 1)) :
        (∑ l : Fin (m + 1), fderiv ℝ (F l) x (LiteratureUnitVector l)) =
          coordinateDerivative f j x := by
      have hterm (l : Fin (m + 1)) : fderiv ℝ (F l) x (LiteratureUnitVector l) =
          if l = j then coordinateDerivative f j x else 0 := by
        by_cases hl : l = j
        · subst l
          simp [F, coordinateDerivative]
        · simp [F, hl]
      simp_rw [hterm]
      simp
    have h := integral_cube_divergence_eq_zero F hF hperiod
    simpa only [hsum] using h

theorem fourierIntegrand_contDiff {f : LiteratureSpace n → ℂ}
    (hf : ContDiff ℝ ∞ f) (k : LiteratureFrequency n) :
    ContDiff ℝ ∞ (fun x => f x * LiteratureCharacter (-k) x) :=
  hf.mul (character_contDiff (-k))

theorem fourierIntegrand_periodic {f : LiteratureSpace n → ℂ}
    (hp : LiteraturePeriodic f) (k : LiteratureFrequency n) :
    LiteraturePeriodic (fun x => f x * LiteratureCharacter (-k) x) := by
  intro x j
  change f (x + LiteratureUnitVector j) * LiteratureCharacter (-k) (x + LiteratureUnitVector j) =
    f x * LiteratureCharacter (-k) x
  rw [hp x j, character_periodic (-k) x j]

theorem fourierIntegrand_integrableOn {f : LiteratureSpace n → ℂ}
    (hf : Continuous f) (k : LiteratureFrequency n) :
    IntegrableOn (fun x => f x * LiteratureCharacter (-k) x)
      (LiteratureUnitCube n) volume :=
  (hf.mul (character_contDiff (-k)).continuous).continuousOn.integrableOn_compact
    (cube_isCompact n)

set_option backward.isDefEq.respectTransparency false in
theorem fourierIntegrand_coordinateDerivative {f : LiteratureSpace n → ℂ}
    (hf : Differentiable ℝ f) (k : LiteratureFrequency n) (j : Fin n)
    (x : LiteratureSpace n) :
    coordinateDerivative (fun y => f y * LiteratureCharacter (-k) y) j x =
      coordinateDerivative f j x * LiteratureCharacter (-k) x -
        derivativeSymbol j k * (f x * LiteratureCharacter (-k) x) := by
  have hd := (hf x).hasFDerivAt.mul (character_hasFDerivAt (-k) x)
  have hd' : HasFDerivAt (fun y => f y * LiteratureCharacter (-k) y)
      (f x • (LiteratureCharacter (-k) x • characterPhaseCLM (-k)) +
        LiteratureCharacter (-k) x • fderiv ℝ f x) x := by
    simpa only [Pi.mul_def] using hd
  rw [coordinateDerivative, hd'.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    characterPhaseCLM_unitVector, smul_eq_mul, coordinateDerivative]
  unfold derivativeSymbol
  simp only [Pi.neg_apply, Int.cast_neg]
  ring

theorem fourierCoefficient_coordinateDerivative {f : LiteratureSpace n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : LiteraturePeriodic f)
    (j : Fin n) (k : LiteratureFrequency n) :
    LiteratureFourierCoefficient (coordinateDerivative f j) k =
      derivativeSymbol j k * LiteratureFourierCoefficient f k := by
  have hzero := integral_cube_coordinateDerivative_eq_zero
    (fourierIntegrand_contDiff hf k) (fourierIntegrand_periodic hp k) j
  simp_rw [fourierIntegrand_coordinateDerivative (hf.differentiable (by simp))] at hzero
  have hd := fourierIntegrand_integrableOn (coordinateDerivative_contDiff hf j).continuous k
  have hv := (fourierIntegrand_integrableOn hf.continuous k).const_mul
    (derivativeSymbol j k)
  rw [integral_sub hd hv, integral_const_mul] at hzero
  exact sub_eq_zero.mp hzero

theorem fourierCoefficient_partialWord {f : LiteratureSpace n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : LiteraturePeriodic f)
    (w : List (Fin n)) (k : LiteratureFrequency n) :
    LiteratureFourierCoefficient (LiteraturePartialWord w f) k =
      LiteratureFourierWordMultiplier w k * LiteratureFourierCoefficient f k := by
  induction w with
  | nil => simp [LiteraturePartialWord, LiteratureFourierWordMultiplier]
  | cons j w ih =>
      change LiteratureFourierCoefficient (coordinateDerivative (LiteraturePartialWord w f) j) k = _
      rw [fourierCoefficient_coordinateDerivative (partialWord_contDiff hf w)
        (partialWord_periodic hp w), ih]
      simp only [LiteratureFourierWordMultiplier, List.map_cons, List.prod_cons, derivativeSymbol]
      ring

theorem fourierCoefficient_norm_le_integral_norm
    (f : LiteratureSpace n → ℂ) (k : LiteratureFrequency n) :
    ‖LiteratureFourierCoefficient f k‖ ≤ ∫ x in LiteratureUnitCube n, ‖f x‖ := by
  calc
    _ ≤ ∫ x in LiteratureUnitCube n, ‖f x * LiteratureCharacter (-k) x‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by simp only [norm_mul, character_norm, mul_one]

end
end NSEGR.NativeLiterature
