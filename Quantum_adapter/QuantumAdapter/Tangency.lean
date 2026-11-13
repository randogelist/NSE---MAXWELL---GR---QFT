import QuantumAdapter.FiniteModel

/-!
# Tangency of the actual full Fourier vector field

All mean and nonzero Fourier modes are retained. The proof establishes that
the explicit real-submodule projection in `drift` is the identity on the raw
viscous Leray-convolution field. No tangency assumption remains in the final
equality `drift_eq_rawRhs`.
-/

set_option autoImplicit false
set_option Elab.async true

open scoped BigOperators

namespace QuantumAdapter

noncomputable section

open SingularClosure

theorem fullTransport_zero_frequency (N : ℕ) (c : FourierCoeff)
    (hc : SpectralSolenoidal c) (i : Fin 3) :
    fullTransport N c 0 i = 0 := by
  classical
  unfold fullTransport
  apply Finset.sum_eq_zero
  intro p hp
  have hinner :
      (∑ j : Fin 3, c p j *
        (((2 * Real.pi * (((0 : Frequency) j - p j : ℤ) : ℝ) : ℝ) : ℂ) *
          Complex.I)) = 0 := by
    calc
      _ = -(2 * (Real.pi : ℂ) * Complex.I) *
          ∑ j : Fin 3, (p j : ℂ) * c p j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp only [Pi.zero_apply, zero_sub]
        push_cast
        ring
      _ = 0 := by rw [hc p, mul_zero]
  rw [hinner, zero_mul]

theorem fullTransport_reality (N : ℕ) (c : FourierCoeff)
    (hc : SpectralReality c) : SpectralReality (fullTransport N c) := by
  classical
  intro k i
  let term : Frequency → Frequency → ℂ := fun q p =>
    (∑ j : Fin 3, c p j *
      (((2 * Real.pi * ((q j - p j : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I)) * c (q - p) i
  have hterm (p : Frequency) : term (-k) (-p) = star (term k p) := by
    have hsub : -k - -p = -(k - p) := by abel
    dsimp [term]
    rw [hsub, hc]
    simp only [Complex.star_def, map_mul, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [hc]
    simp only [Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_I,
      Pi.neg_apply]
    push_cast
    ring
  change (∑ p ∈ fullModes N, term (-k) p) =
    star (∑ p ∈ fullModes N, term k p)
  rw [star_sum]
  apply Finset.sum_nbij' (fun p => -p) (fun p => -p)
    (fun p hp => fullModes_neg_mem hp) (fun p hp => fullModes_neg_mem hp)
  · intro p hp
    simp
  · intro p hp
    simp
  · intro p hp
    simpa only [neg_neg] using hterm (-p)

theorem frequencySquare_ne_zero (k : Frequency) (hk : k ≠ 0) :
    (∑ i : Fin 3, (k i : ℂ) ^ 2) ≠ 0 := by
  have hr : (∑ i : Fin 3, (k i : ℝ) ^ 2) ≠ 0 := by
    intro hz
    apply hk
    funext i
    have hi : (k i : ℝ) ^ 2 ≤ ∑ j : Fin 3, (k j : ℝ) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (k j : ℝ)) (Finset.mem_univ i)
    rw [hz] at hi
    have hki : (k i : ℝ) = 0 := by nlinarith [sq_nonneg (k i : ℝ)]
    exact_mod_cast hki
  have heq : (∑ i : Fin 3, (k i : ℂ) ^ 2) =
      ((∑ i : Fin 3, (k i : ℝ) ^ 2 : ℝ) : ℂ) := by
    push_cast <;> rfl
  rw [heq]
  exact_mod_cast hr

theorem coefficientLeray_solenoidal (k : Frequency) (v : Fin 3 → ℂ) :
    (∑ i : Fin 3, (k i : ℂ) * coefficientLeray k v i) = 0 := by
  by_cases hk : k = 0
  · subst k
    simp
  · simp only [coefficientLeray, if_neg hk, mul_sub, Finset.sum_sub_distrib]
    have hsum :
        (∑ i : Fin 3, (k i : ℂ) *
          ((k i : ℂ) * (∑ j : Fin 3, (k j : ℂ) * v j) /
            (∑ j : Fin 3, (k j : ℂ) ^ 2))) =
        (∑ i : Fin 3, (k i : ℂ) ^ 2) *
          ((∑ j : Fin 3, (k j : ℂ) * v j) /
            (∑ j : Fin 3, (k j : ℂ) ^ 2)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum]
    have hden := frequencySquare_ne_zero k hk
    field_simp [hden] <;> ring

theorem rawRhs_coeff (ν : ℝ) (N : ℕ) (q : Phase N)
    (k : Frequency) (i : Fin 3) :
    extendCoeff (rawRhs ν N q) k i =
      if k ∈ fullModes N then
        if k = 0 then 0 else
          -((ν * laplaceSymbol k : ℝ) : ℂ) * phaseCoeff q k i -
            coefficientLeray k (fullTransport N (phaseCoeff q) k) i
      else 0 := by
  by_cases hk : k ∈ fullModes N <;> simp [extendCoeff, rawRhs, hk]

/-- The zero-mode branch is the actual Galerkin equation, by solenoidality. -/
theorem rawRhs_all_modes (ν : ℝ) (N : ℕ) (q : Phase N)
    (k : Frequency) (i : Fin 3) :
    extendCoeff (rawRhs ν N q) k i =
      if k ∈ fullModes N then
        -((ν * laplaceSymbol k : ℝ) : ℂ) * phaseCoeff q k i -
          coefficientLeray k (fullTransport N (phaseCoeff q) k) i
      else 0 := by
  rw [rawRhs_coeff]
  by_cases hm : k ∈ fullModes N
  · rw [if_pos hm, if_pos hm]
    by_cases hk : k = 0
    · subst k
      simp [laplaceSymbol, galerkinFreqSq, coefficientLeray,
        fullTransport_zero_frequency N (phaseCoeff q) (phaseCoeff_solenoidal q)]
    · rw [if_neg hk]
  · rw [if_neg hm, if_neg hm]

theorem rawRhs_reality (ν : ℝ) (N : ℕ) (q : Phase N) :
    SpectralReality (extendCoeff (rawRhs ν N q)) := by
  intro k i
  rw [rawRhs_coeff, rawRhs_coeff]
  by_cases hm : k ∈ fullModes N
  · rw [if_pos hm, if_pos (fullModes_neg_mem hm)]
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, if_neg (neg_ne_zero.mpr hk)]
      have htrans : fullTransport N (phaseCoeff q) (-k) =
          fun j => star (fullTransport N (phaseCoeff q) k j) := by
        funext j
        exact fullTransport_reality N (phaseCoeff q) (phaseCoeff_reality q) k j
      rw [htrans, coefficientLeray_neg_star, phaseCoeff_reality q k i]
      simp [laplaceSymbol, galerkinFreqSq, Complex.star_def]
  · rw [if_neg hm, if_neg ((fullModes_neg_mem_iff N k).not.mpr hm)]
    simp

theorem rawRhs_solenoidal (ν : ℝ) (N : ℕ) (q : Phase N) :
    SpectralSolenoidal (extendCoeff (rawRhs ν N q)) := by
  intro k
  simp_rw [rawRhs_coeff]
  by_cases hm : k ∈ fullModes N
  · simp only [if_pos hm]
    by_cases hk : k = 0
    · subst k
      simp
    · simp only [if_neg hk, mul_sub, Finset.sum_sub_distrib]
      have hlinear :
          (∑ i : Fin 3, (k i : ℂ) *
            (-((ν * laplaceSymbol k : ℝ) : ℂ) * phaseCoeff q k i)) =
          -((ν * laplaceSymbol k : ℝ) : ℂ) *
            ∑ i : Fin 3, (k i : ℂ) * phaseCoeff q k i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hlinear, phaseCoeff_solenoidal q k, coefficientLeray_solenoidal]
      simp
  · simp [hm]

theorem rawRhs_tangent : RawRhsTangent := by
  intro ν N q
  exact ⟨rawRhs_reality ν N q, rawRhs_solenoidal ν N q⟩

theorem drift_eq_rawRhs (ν : ℝ) (N : ℕ) (q : Phase N) :
    (drift ν N q).val = rawRhs ν N q :=
  drift_eq_rawRhs_of_tangent rawRhs_tangent ν N q

theorem drift_mean (ν : ℝ) (N : ℕ) (q : Phase N) (i : Fin 3) :
    phaseCoeff (drift ν N q) 0 i = 0 := by
  change extendCoeff (drift ν N q).val 0 i = 0
  rw [drift_eq_rawRhs]
  exact rawRhs_mean ν N q i

end

end QuantumAdapter
