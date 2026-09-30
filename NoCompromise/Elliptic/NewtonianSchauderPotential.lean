module

public import NoCompromise.Elliptic.NewtonianSchauderHessian
public import NoCompromise.Elliptic.NewtonianSchauderNorm

@[expose] public section

/-!
# Quantitative Hölder bounds for the actual Newtonian potential

The coordinate estimates control the full bilinear operator norm. The source's
L¹ norm controls the far integral; for sources supported in the unit ball this
is bounded by its uniform norm times the fixed ball volume.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "D₃" => E₃ →L[ℝ] ℝ
local notation "H₃" => E₃ →L[ℝ] D₃

lemma norm_schauderCoordinateBilinear (i j : Fin 3) : ‖schauderCoordinateBilinear i j‖ = 1 := by
  simp only [schauderCoordinateBilinear, ContinuousLinearMap.norm_smulRight_apply,
    innerSL_apply_norm, PiLp.norm_single, norm_one, mul_one]

lemma schauder_bilinear_norm_le_of_entries (L : H₃) {M : ℝ}
    (hM : ∀ i j, ‖L (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)‖ ≤ M) :
    ‖L‖ ≤ 9 * M := by
  rw [schauder_bilinear_eq_sum L]
  calc
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, M := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul, norm_schauderCoordinateBilinear, mul_one]
      exact hM i j
    _ = _ := by simp only [Fin.sum_univ_three]; ring

lemma norm_schauderFarConvolution_le_mass {d : ℝ} (hd : 0 < d)
    (i j : Fin 3) {f : E₃ → ℝ} (hf : Integrable f) (x : E₃) :
    ‖schauderFarConvolution d i j f x‖ ≤ (Real.pi⁻¹ * (d ^ 3)⁻¹) * ∫ y, ‖f y‖ := by
  unfold schauderFarConvolution
  calc
    _ ≤ ∫ y, ‖f y * schauderFarKernel d i j (x - y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, (Real.pi⁻¹ * (d ^ 3)⁻¹) * ‖f y‖ :=
      integral_mono (integrable_schauderFarConvolution hd i j hf x).norm
        (hf.norm.const_mul _) (fun y => by
          rw [norm_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (norm_schauderFarKernel_le hd i j _) (norm_nonneg _))
    _ = _ := integral_const_mul _ _

lemma norm_schauderHessianCandidate_le {α A B : ℝ} (hα : 0 < α) (hA : 0 ≤ A)
    {f : E₃ → ℝ} (hf : Measurable f) (hi : Integrable f) (hfb : ∀ x, ‖f x‖ ≤ B)
    (hinc : ∀ x y, ‖f x - f y‖ ≤ A * ‖x - y‖ ^ α) (i j : Fin 3) (x : E₃) :
    ‖schauderHessianCandidate i j f x‖ ≤
      4 * A * (2 : ℝ) ^ α / α + Real.pi⁻¹ * (∫ y, ‖f y‖) + B := by
  have hn := (schauder_near_cutoff_bound hα (by norm_num : (0 : ℝ) < 1) hA hf hinc i j x).2
  have hfar := norm_schauderFarConvolution_le_mass (by norm_num : (0 : ℝ) < 1) i j hi x
  simp only [mul_one, one_pow, inv_one] at hn hfar
  have hc : ‖(if i = j then (1 / 3 : ℝ) else 0) * f x‖ ≤ B := by
    have hb : ‖if i = j then (1 / 3 : ℝ) else 0‖ ≤ 1 := by split_ifs <;> norm_num
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans (by simpa using hfb x)
  rw [schauderHessianCandidate_split hα hA (by norm_num : (0 : ℝ) < 1) hf hi hinc i j x]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add hn hfar)) hc)

/-- The full Hessian operator has a finite Hölder norm bounded by the source's
Hölder constant, uniform bound and L¹ norm. The constant precedes the source. -/
theorem exists_schauderHessianCandidateMap_norm_bound {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C > 0, ∀ A ≥ 0, ∀ B ≥ 0, ∀ (f : E₃ → ℝ),
      Measurable f → Integrable f → (∀ x, ‖f x‖ ≤ B) →
      (∀ x y, ‖f x - f y‖ ≤ A * ‖x - y‖ ^ α) → ∀ U : Set E₃,
      HasFiniteHolderNormOn α (schauderHessianCandidateMap f) U ∧
        holderNorm α (schauderHessianCandidateMap f) U ≤ C * (A + B + ∫ y, ‖f y‖) := by
  obtain ⟨C, hC, hb⟩ := exists_schauderHessianCandidate_holder_bound hα hα1
  let K := 9 * (4 * (2 : ℝ) ^ α / α + Real.pi⁻¹ + 1 + C)
  refine ⟨K, by dsimp [K]; positivity, fun A hA B hB f hf hi hfb hinc U => ?_⟩
  let I : ℝ := ∫ y, ‖f y‖
  have hI : 0 ≤ I := integral_nonneg (fun y => norm_nonneg _)
  let M := 9 * (4 * A * (2 : ℝ) ^ α / α + Real.pi⁻¹ * I + B)
  let Q := 9 * C * A
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hval : ∀ x ∈ U, ‖schauderHessianCandidateMap f x‖ ≤ M := by
    intro x _
    apply schauder_bilinear_norm_le_of_entries
    intro i j
    rw [schauderHessianCandidateMap_apply_basis]
    exact norm_schauderHessianCandidate_le hα hA hf hi hfb hinc i j x
  have hincH (x y : E₃) :
      ‖schauderHessianCandidateMap f x - schauderHessianCandidateMap f y‖ ≤ Q * ‖x - y‖ ^ α := by
    have hh := schauder_bilinear_norm_le_of_entries
      (schauderHessianCandidateMap f x - schauderHessianCandidateMap f y)
      (M := C * A * ‖x - y‖ ^ α) (fun i j => by
        simp only [sub_apply, schauderHessianCandidateMap_apply_basis]
        exact hb A hA f hf hi hinc i j x y)
    dsimp [Q]
    nlinarith
  have hquot : ∀ x ∈ U, ∀ y ∈ U,
      ‖schauderHessianCandidateMap f x - schauderHessianCandidateMap f y‖ / ‖x - y‖ ^ α ≤ Q := by
    intro x _ y _
    by_cases hxy : x = y
    · subst y
      simpa only [sub_self, norm_zero, zero_div] using hQ
    exact (div_le_iff₀ (Real.rpow_pos_of_pos
      (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α)).mpr (hincH x y)
  refine ⟨HasFiniteHolderNormOn.of_bounds hM hQ hval hquot,
    (holderNorm_le hM hQ hval hquot).trans ?_⟩
  have hAT : A ≤ A + B + I := by linarith
  have hBT : B ≤ A + B + I := by linarith
  have hIT : I ≤ A + B + I := by linarith
  calc
    M + Q = 9 * (4 * (2 : ℝ) ^ α / α * A + Real.pi⁻¹ * I + B + C * A) := by
      dsimp [M, Q]
      ring
    _ ≤ 9 * (4 * (2 : ℝ) ^ α / α * (A + B + I) + Real.pi⁻¹ * (A + B + I) +
        (A + B + I) + C * (A + B + I)) := by gcongr
    _ = _ := by dsimp [K, I]; ring

lemma schauder_integral_norm_le_unitBall {f : E₃ → ℝ} {B : ℝ}
    (hi : Integrable f) (hB : ∀ x, ‖f x‖ ≤ B) (hs : tsupport f ⊆ ball 0 1) :
    (∫ y, ‖f y‖) ≤ volume.real (ball (0 : E₃) 1) * B := by
  let : IsFiniteMeasure (volume.restrict (ball (0 : E₃) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isBounded_ball.measure_lt_top⟩
  have hz (y : E₃) (hy : y ∉ ball (0 : E₃) 1) : ‖f y‖ = 0 := by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hs h)), norm_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  calc
    _ ≤ ∫ y in ball (0 : E₃) 1, B := integral_mono hi.norm.integrableOn (integrable_const B) hB
    _ = _ := by simp only [integral_const, Measure.restrict_apply_univ, smul_eq_mul, Measure.real]

lemma norm_schauderPotential_le_unitBall {f : E₃ → ℝ} {B : ℝ}
    (hf : Measurable f) (hcf : HasCompactSupport f) (hB : ∀ x, ‖f x‖ ≤ B)
    (hs : tsupport f ⊆ ball 0 1) (x : E₃) :
    ‖schauderPotential f x‖ ≤
      ((4 * Real.pi)⁻¹ * (coulombBoundConstant *
        volume.real (ball (0 : E₃) 1) ^ ((2 : ℝ) / 3))) * B := by
  rw [schauderPotential, norm_mul, norm_neg, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (4 * Real.pi)⁻¹)]
  calc
    _ ≤ (4 * Real.pi)⁻¹ * ((coulombBoundConstant *
        volume.real (ball (0 : E₃) 1) ^ ((2 : ℝ) / 3)) * B) :=
      mul_le_mul_of_nonneg_left
        (norm_scalarNewtonianPotential_le_of_support_subset_unitBall
          hf.aestronglyMeasurable hcf hB hs x) (by positivity)
    _ = _ := by ring

/-- The actual signed Newtonian potential satisfies a C²,α norm estimate on every
fixed positive-radius ball, for Hölder sources supported in the unit ball. -/
theorem exists_schauderPotential_norm_bound {α R : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hR : 0 < R) :
    ∃ C > 0, ∀ A ≥ 0, ∀ B ≥ 0, ∀ (f : E₃ → ℝ),
      Measurable f → HasCompactSupport f → (∀ x, ‖f x‖ ≤ B) →
      (∀ x y, ‖f x - f y‖ ≤ A * ‖x - y‖ ^ α) → tsupport f ⊆ ball 0 1 →
      HasC2HolderOn α (schauderPotential f) (ball 0 R) ∧
        schauderC2HolderNorm α (schauderPotential f) (ball 0 R) ≤ C * (A + B) := by
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_schauderHessianCandidateMap_norm_bound hα hα1
  obtain ⟨C₂, hC₂, hb₂⟩ := exists_schauderC2HolderNorm_le hα hα1 hR (0 : E₃)
  let V : ℝ := volume.real (ball (0 : E₃) 1)
  let K : ℝ := (4 * Real.pi)⁻¹ * (coulombBoundConstant * V ^ ((2 : ℝ) / 3))
  have hV : 0 ≤ V := measureReal_nonneg
  have hK : 0 ≤ K := by dsimp [K, coulombBoundConstant]; positivity
  refine ⟨C₂ * (K + C₁ * (1 + V)), by positivity, fun A hA B hB f hf hcf hfb hinc hs => ?_⟩
  have hi := integrable_scalarDensity_of_bounded_compact hf.aestronglyMeasurable hcf hfb
  have hc := contDiff_two_schauderPotential hα hα1 hA hB hf hcf hfb hinc
  have hval (x : E₃) : ‖schauderPotential f x‖ ≤ K * B :=
    norm_schauderPotential_le_unitBall hf hcf hfb hs x
  have hm : AEStronglyMeasurable (schauderPotential f) (volume.restrict (ball 0 R)) :=
    hc.continuous.aestronglyMeasurable
  have hae : ∀ᵐ x ∂volume.restrict (ball (0 : E₃) R), ‖schauderPotential f x‖ ≤ K * B :=
    Eventually.of_forall hval
  have hmu := memLp_top_of_bound hm (K * B) hae
  have hlp : lpNorm (schauderPotential f) ∞ (volume.restrict (ball 0 R)) ≤ K * B := by
    rw [← toReal_eLpNorm, eLpNorm_exponent_top hm]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (eLpNormEssSup_le_of_ae_bound hae)).trans_eq
      (ENNReal.toReal_ofReal (mul_nonneg hK hB))
  have he : fderiv ℝ (fderiv ℝ (schauderPotential f)) = schauderHessianCandidateMap f :=
    funext (fderiv_two_schauderPotential hα hA hB hf hcf hfb hinc)
  obtain ⟨hh, hhbound⟩ := hb₁ A hA B hB f hf hi hfb hinc (ball 0 R)
  rw [← he] at hh hhbound
  obtain ⟨hu, huB⟩ := hb₂ (schauderPotential f) hc.contDiffOn hmu hh
  have hmass := schauder_integral_norm_le_unitBall hi hfb hs
  have hsum : A + B + (∫ y, ‖f y‖) ≤ (1 + V) * (A + B) := by
    change _ ≤ V * B at hmass
    nlinarith [mul_nonneg hV hA]
  refine ⟨hu, huB.trans ?_⟩
  calc
    _ ≤ C₂ * (K * (A + B) + C₁ * ((1 + V) * (A + B))) := by
      apply mul_le_mul_of_nonneg_left _ hC₂.le
      apply add_le_add
      · exact hlp.trans (mul_le_mul_of_nonneg_left (by linarith : B ≤ A + B) hK)
      · exact hhbound.trans (mul_le_mul_of_nonneg_left hsum hC₁.le)
    _ = _ := by ring

end LiquidDrop
