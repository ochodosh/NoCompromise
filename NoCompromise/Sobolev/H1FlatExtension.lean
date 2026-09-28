import NoCompromise.Sobolev.H1Reflection
import NoCompromise.Sobolev.H1Approximation
import NoCompromise.Sobolev.WeakCompactness

/-!
# H¹ reflection across a flat face

Uniformly bounded interior mollifications converge strongly in L² after shifted
folding. Weak Hilbert-space compactness then supplies the weak gradient of even
reflection on every strictly smaller cube, with the sharp two-sheet L² bounds.
-/

noncomputable section

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient Convolution

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- A weak limit in a real Hilbert space preserves a uniform norm bound. -/
lemma norm_le_of_weakly_tendsto_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ι : Type*} {l : Filter ι} [NeBot l]
    {u : ι → E} {v : E} {C : ℝ} (hC : 0 ≤ C) (hu : ∀ j, ‖u j‖ ≤ C)
    (ht : ∀ ℓ : E →L[ℝ] ℝ, Tendsto (fun j => ℓ (u j)) l (𝓝 (ℓ v))) :
    ‖v‖ ≤ C := by
  have h := le_of_tendsto (ht (innerSL ℝ v))
    (Eventually.of_forall fun j => (real_inner_le_norm v (u j)).trans
      (mul_le_mul_of_nonneg_left (hu j) (norm_nonneg v)))
  simp only [innerSL_apply_apply, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg v]

/-- Strong L² limits of uniformly H¹-bounded representatives remain H¹. Each of
the two separate L² bounds is retained through weak Hilbert-space convergence. -/
theorem exists_hasH1GradientOn_of_l2_limit_of_uniform_bounds {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    {G : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : ∀ j, HasH1GradientOn (f j) (G j) U)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : MemLp g 2 (volume.restrict U))
    (ht : Tendsto (fun j => eLpNorm (f j - g) 2 (volume.restrict U)) atTop (𝓝 0))
    {A B : ℝ≥0∞} (hA : A < ∞) (hB : B < ∞)
    (hfA : ∀ j, eLpNorm (f j) 2 (volume.restrict U) ≤ A)
    (hGB : ∀ j, eLpNorm (G j) 2 (volume.restrict U) ≤ B) :
    ∃ H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      HasH1GradientOn g H U ∧ eLpNorm g 2 (volume.restrict U) ≤ A ∧
        eLpNorm H 2 (volume.restrict U) ≤ B := by
  let u (j : ℕ) : H1Space U := H1Space.ofFunction (f j) (G j) (hf j)
  have hfa (j) : ‖(u j).toLp‖ ≤ A.toReal := by
    change ‖(hf j).memLp_function.toLp (f j)‖ ≤ A.toReal
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_mono hA.ne (hfA j)
  have hgb (j) : ‖(u j).gradientLp‖ ≤ B.toReal := by
    change ‖(hf j).memLp_gradient.toLp (G j)‖ ≤ B.toReal
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_mono hB.ne (hGB j)
  obtain ⟨v, σ, hσ, _, _, hweakf, hweakG⟩ := exists_subseq_weakly_tendsto_h1_components
    u (fun j => (u j).norm_le_sum.trans (add_le_add (hfa j) (hgb j)))
  have hstrong : Tendsto (fun j => (u j).toLp) atTop (𝓝 (hg.toLp g)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f (fun j => (hf j).memLp_function) g hg).mpr ht
  have heq : hg.toLp g = v.toLp := by
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
    intro ℓ
    exact tendsto_nhds_unique
      ((ℓ.continuous.continuousAt.tendsto.comp hstrong).comp hσ.tendsto_atTop)
      (hweakf ℓ)
  have hvf := norm_le_of_weakly_tendsto_bound ENNReal.toReal_nonneg
    (fun j => hfa (σ j)) hweakf
  have hvG := norm_le_of_weakly_tendsto_bound ENNReal.toReal_nonneg
    (fun j => hgb (σ j)) hweakG
  have hvg : (v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume.restrict U] g := by
    exact (Lp.ext_iff.mp heq).symm.trans hg.coeFn_toLp
  refine ⟨v.gradientLp, v.hasH1GradientOn.congr_ae hvg EventuallyEq.rfl, ?_, ?_⟩
  · rw [← ofReal_lpNorm hg, ← toReal_eLpNorm, ← Lp.norm_toLp g hg, heq]
    exact (ENNReal.ofReal_le_ofReal hvf).trans_eq (ENNReal.ofReal_toReal hA.ne)
  · rw [← ofReal_lpNorm (Lp.memLp v.gradientLp), ← v.norm_gradientLp_eq_lpNorm]
    exact (ENNReal.ofReal_le_ofReal hvG).trans_eq (ENNReal.ofReal_toReal hB.ne)

/-- Translation before even folding is continuous in every finite Lᵖ space. -/
theorem tendsto_eLpNorm_shiftedCoordinateFold_sub {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] (i : Fin n) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {f : EuclideanSpace ℝ (Fin n) → F} (hf : MemLp f p volume)
    {ι : Type*} {l : Filter ι} {δ : ι → ℝ} (hδ : Tendsto δ l (𝓝 0)) :
    Tendsto (fun j => eLpNorm
      (fun x => f (shiftedCoordinateFold i (δ j) x) - f (coordinateFold i x)) p volume)
      l (𝓝 0) := by
  let a (j : ι) := -(δ j • EuclideanSpace.single i (1 : ℝ))
  have ha : Tendsto a l (𝓝 0) := by
    simpa only [zero_smul, neg_zero] using
      (hδ.smul_const (EuclideanSpace.single i (1 : ℝ))).neg
  have ht := (tendsto_eLpNorm_translate_sub_zero hp hf).comp ha
  have hmul := ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞) ^ (1 / p).toReal)
    ht (Or.inr (by finiteness))
  simp only [mul_zero] at hmul
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul
    (fun _ => bot_le) (fun j => ?_)
  have hm := (hf.comp_measurePreserving (measurePreserving_sub_right volume (a j))).sub hf
  have hb := (memLp_comp_shiftedCoordinateFold i 0 MeasurableSet.univ (mapsTo_univ _ _)
    (by simpa only [Measure.restrict_univ] using hm)).2
  simpa only [Measure.restrict_univ, shiftedCoordinateFold_zero, Function.comp_def,
    Pi.sub_def, a, sub_neg_eq_add, shiftedCoordinateFold] using hb

/-- Shrinking mollification and vanishing inward shifts converge to even reflection
in L², before any weak-gradient argument is used. -/
theorem tendsto_eLpNorm_bump_convolution_shiftedCoordinateFold_sub {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (i : Fin n) {f : EuclideanSpace ℝ (Fin n) → F} (hf : MemLp f 2 volume)
    {ι : Type*} {l : Filter ι} {δ : ι → ℝ}
    {φ : ι → ContDiffBump (0 : EuclideanSpace ℝ (Fin n))}
    (hδ : Tendsto δ l (𝓝 0)) (hφ : Tendsto (fun j => (φ j).rOut) l (𝓝 0)) :
    Tendsto (fun j => eLpNorm (fun x =>
      ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f)
        (shiftedCoordinateFold i (δ j) x) - f (coordinateFold i x)) 2 volume) l (𝓝 0) := by
  let g (j : ι) := (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f
  have hg (j) : MemLp (g j) 2 volume :=
    (memLp_two_convolution_probability_kernel (φ j).continuous_normed
      (φ j).hasCompactSupport_normed (φ j).nonneg_normed (φ j).integral_normed hf).1
  have ht := tendsto_eLpNorm_bump_convolution_sub hf hφ
  have hmul := ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞) ^ (1 / 2 : ℝ))
    ht (Or.inr (by finiteness))
  simp only [mul_zero] at hmul
  have hfold := tendsto_eLpNorm_shiftedCoordinateFold_sub i (by norm_num) hf hδ
  have hsum := hmul.add hfold
  simp only [zero_add] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) (fun j => ?_)
  have hm1 := memLp_comp_shiftedCoordinateFold i (δ j) MeasurableSet.univ
    (mapsTo_univ _ _) (by simpa only [Measure.restrict_univ] using (hg j).sub hf)
  have hm2 := memLp_comp_shiftedCoordinateFold i (δ j) MeasurableSet.univ
    (mapsTo_univ _ _) (by simpa only [Measure.restrict_univ] using hf)
  have hm0 := memLp_comp_shiftedCoordinateFold i 0 MeasurableSet.univ
    (mapsTo_univ _ _) (by simpa only [Measure.restrict_univ] using hf)
  simp only [Measure.restrict_univ, shiftedCoordinateFold_zero] at hm1 hm2 hm0
  calc
    _ = eLpNorm (((g j - f) ∘ shiftedCoordinateFold i (δ j)) +
        (f ∘ shiftedCoordinateFold i (δ j) - f ∘ coordinateFold i)) 2 volume := by
      congr 1
      ext x
      simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply, sub_add_sub_cancel, g]
    _ ≤ _ := (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans (add_le_add
      (by simpa only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat,
        Pi.sub_def, g] using hm1.2)
      le_rfl)

/-- Even reflection of an H¹ function across a flat face is H¹ on every strictly
smaller cube. Function and gradient each obey the sharp square-root-of-two L² bound. -/
theorem HasH1GradientOn.coordinateFold_halfCube {n : ℕ} (i : Fin n)
    {r R : ℝ} (hrR : r < R)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G (coordinateHalfCube i R)) :
    ∃ H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      HasH1GradientOn (f ∘ coordinateFold i) H (coordinateCube n r) ∧
        eLpNorm (f ∘ coordinateFold i) 2 (volume.restrict (coordinateCube n r)) ≤
          (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
            eLpNorm f 2 (volume.restrict (coordinateHalfCube i R)) ∧
        eLpNorm H 2 (volume.restrict (coordinateCube n r)) ≤
          (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
            eLpNorm G 2 (volume.restrict (coordinateHalfCube i R)) := by
  let a (j : ℕ) : ℝ := ((R - r) / 4) / ((j : ℝ) + 1)
  have ha (j) : 0 < a j := div_pos (div_pos (sub_pos.mpr hrR) (by norm_num)) (by positivity)
  let φ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨a j / 2, a j, half_pos (ha j), half_lt_self (ha j)⟩
  let δ (j : ℕ) := 2 * a j
  have hδ (j) : (φ j).rOut < δ j := by
    change a j < 2 * a j
    linarith [ha j]
  have hR (j) : r + δ j + (φ j).rOut ≤ R := by
    have hsmall : a j ≤ (R - r) / 4 := div_le_self
      (by linarith : 0 ≤ (R - r) / 4) (by linarith [Nat.cast_nonneg (α := ℝ) j])
    change r + 2 * a j + a j ≤ R
    linarith
  have ha0 : Tendsto a atTop (𝓝 0) := by
    simpa only [a, mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((R - r) / 4)
  have hδ0 : Tendsto δ atTop (𝓝 0) := by
    simpa only [δ, mul_zero] using ha0.const_mul 2
  let f0 := (coordinateHalfCube i R).indicator f
  have hmf0 : MemLp f0 2 volume :=
    (memLp_indicator_iff_restrict (isOpen_coordinateHalfCube i R).measurableSet).mpr
      hf.memLp_function
  let F (j : ℕ) := (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f0
  let u (j : ℕ) := F j ∘ shiftedCoordinateFold i (δ j)
  have hub (j) := hf.bump_convolution_shiftedCoordinateFold i (φ j) (hδ j) (hR j)
  have huh1 (j) : HasH1GradientOn (u j) (gradient (u j)) (coordinateCube n r) := (hub j).1
  have hconv : Tendsto (fun j => eLpNorm
      (u j - f0 ∘ coordinateFold i) 2 volume) atTop (𝓝 0) :=
    tendsto_eLpNorm_bump_convolution_shiftedCoordinateFold_sub i hmf0 hδ0 ha0
  have hconvU : Tendsto (fun j => eLpNorm
      (u j - f0 ∘ coordinateFold i) 2 (volume.restrict (coordinateCube n r)))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
      (fun _ => bot_le) (fun _ => eLpNorm_mono_measure _ Measure.restrict_le_self)
  have hae := indicator_halfCube_comp_coordinateFold_ae i hrR.le f
  have hconvF : Tendsto (fun j => eLpNorm
      (u j - f ∘ coordinateFold i) 2 (volume.restrict (coordinateCube n r)))
      atTop (𝓝 0) := by
    apply hconvU.congr
    intro j
    exact eLpNorm_congr_ae (EventuallyEq.rfl.sub hae)
  have hfold0 := (memLp_comp_shiftedCoordinateFold i 0 MeasurableSet.univ (mapsTo_univ _ _)
    (by simpa only [Measure.restrict_univ] using hmf0)).1
  simp only [Measure.restrict_univ, shiftedCoordinateFold_zero] at hfold0
  have hfold : MemLp (f ∘ coordinateFold i) 2 (volume.restrict (coordinateCube n r)) :=
    (hfold0.mono_measure Measure.restrict_le_self).ae_eq hae
  apply exists_hasH1GradientOn_of_l2_limit_of_uniform_bounds huh1 hfold hconvF
  · exact ENNReal.mul_lt_top (by finiteness) hf.memLp_function.eLpNorm_lt_top
  · exact ENNReal.mul_lt_top (by finiteness) hf.memLp_gradient.eLpNorm_lt_top
  · intro j
    exact (hub j).2.1
  · intro j
    exact (hub j).2.2

end LiquidDrop
