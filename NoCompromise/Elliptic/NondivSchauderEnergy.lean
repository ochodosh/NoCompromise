module

public import NoCompromise.Elliptic.NondivSchauderTests

@[expose] public section

/-!
# A uniform interior energy estimate for difference-quotient solutions

The first result keeps an arbitrary actual compact cutoff. The second chooses a
fixed cutoff between B₃/₄ and B₇/₈, and chooses its constant before the coefficient
field, solution, weak gradient, and vector source.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The previously proved Caccioppoli inequality gives an actual unweighted
interior energy bound on every set where the compact cutoff equals one. -/
theorem nondiv_caccioppoli_cutoff_bound {n : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hV : MeasurableSet V)
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {u η : EuclideanSpace ℝ (Fin n) → ℝ}
    {D G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {lam cap B : ℝ} (hlam : 0 < lam) (hlamcap : lam ≤ cap)
    (hA : AEStronglyMeasurable A (volume.restrict U))
    (hell : ∀ᵐ x ∂volume.restrict U, ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v))
    (hbA : ∀ᵐ x ∂volume.restrict U, ‖A x‖ ≤ cap)
    (hu : HasH1GradientOn u D U) (hG : MemLp G 2 (volume.restrict U))
    (he : IsWeakDivergenceEquationOn A D G U)
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ U)
    (hvη : ∀ x, 0 ≤ η x ∧ η x ≤ 1) (hbη : ∀ x, ‖gradient η x‖ ≤ B)
    (hηone : EqOn η (fun _ => 1) V) :
    (∫ x in V, ‖D x‖ ^ 2) ≤ ((8 * cap ^ 2 + 2 * lam + 2) / lam ^ 2) *
      (B ^ 2 * (∫ x in U, u x ^ 2) + ∫ x in U, ‖G x‖ ^ 2) := by
  have hGloc : IsLocallyL2On G U :=
    fun _ _ hKU => hG.mono_measure (Measure.restrict_mono hKU le_rfl)
  have hcgrad : HasCompactSupport (gradient η) :=
    hcη.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset η)
  have hmD := hu.locallyH1.locallyL2_gradient.smul_compact_scalar hη.continuous hcη hsη
  have hmW := hu.locallyH1.locallyL2_function.smul_compact_vector
    (continuous_gradient_of_contDiff hη) hcgrad ((tsupport_gradient_subset η).trans hsη)
  have hmG := hGloc.smul_compact_scalar hη.continuous hcη hsη
  have hiD : Integrable (fun x => η x ^ 2 * ‖D x‖ ^ 2) := by
    simpa only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] using
      hmD.integrable_norm_pow (by norm_num)
  have hiW : Integrable (fun x => u x ^ 2 * ‖gradient η x‖ ^ 2) := by
    simpa only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] using
      hmW.integrable_norm_pow (by norm_num)
  have hiG : Integrable (fun x => η x ^ 2 * ‖G x‖ ^ 2) := by
    simpa only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] using
      hmG.integrable_norm_pow (by norm_num)
  have hiu : Integrable (fun x => u x ^ 2) (volume.restrict U) := by
    simpa only [Real.norm_eq_abs, sq_abs] using hu.memLp_function.integrable_norm_pow (by norm_num)
  have hiGG : Integrable (fun x => ‖G x‖ ^ 2) (volume.restrict U) :=
    hG.integrable_norm_pow (by norm_num)
  have hzeroη (x : EuclideanSpace ℝ (Fin n)) (hx : x ∉ U) : η x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (hsη h))
  have hzeroDη (x : EuclideanSpace ℝ (Fin n)) (hx : x ∉ U) : gradient η x = 0 :=
    gradient_eq_zero_of_notMem_tsupport (fun h => hx (hsη h))
  have hDb : (∫ x in V, ‖D x‖ ^ 2) ≤ ∫ x, η x ^ 2 * ‖D x‖ ^ 2 := by
    calc
      _ = ∫ x in V, η x ^ 2 * ‖D x‖ ^ 2 := by
        apply setIntegral_congr_fun hV
        intro x hx
        change ‖D x‖ ^ 2 = η x ^ 2 * ‖D x‖ ^ 2
        rw [hηone hx, one_pow, one_mul]
      _ ≤ _ := setIntegral_le_integral hiD
        (Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hWb : (∫ x, u x ^ 2 * ‖gradient η x‖ ^ 2) ≤ B ^ 2 * ∫ x in U, u x ^ 2 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U)
      (fun x hx => by rw [hzeroDη x hx, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]),
      ← integral_const_mul]
    apply integral_mono_ae hiW.integrableOn (hiu.const_mul _)
    exact Eventually.of_forall fun x => by
      have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hbη x) 2)
        (sq_nonneg (u x))
      simpa only [mul_comm] using h
  have hGb : (∫ x, η x ^ 2 * ‖G x‖ ^ 2) ≤ ∫ x in U, ‖G x‖ ^ 2 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U)
      (fun x hx => by rw [hzeroη x hx, zero_pow (by decide : 2 ≠ 0), zero_mul])]
    apply integral_mono_ae hiG.integrableOn hiGG
    exact Eventually.of_forall fun x => by
      have hηsq : η x ^ 2 ≤ 1 := by nlinarith [(hvη x).1, (hvη x).2]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hηsq (sq_nonneg _)
  have h := caccioppoli hU hlam hlamcap hA hell hbA hu.locallyH1 hGloc he hη hcη hsη
  exact hDb.trans (h.trans (mul_le_mul_of_nonneg_left (add_le_add hWb hGb) (by positivity)))

/-- A fixed nested-ball Caccioppoli bound, uniform before all equation data. -/
theorem nondiv_caccioppoli_nested_balls {n : ℕ} {lam cap : ℝ}
    (hlam : 0 < lam) (hlamcap : lam ≤ cap) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (u : EuclideanSpace ℝ (Fin n) → ℝ)
      (D G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      AEStronglyMeasurable A (volume.restrict (ball 0 (7 / 8))) →
      (∀ᵐ x ∂volume.restrict (ball 0 (7 / 8)), ∀ v,
        lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      (∀ᵐ x ∂volume.restrict (ball 0 (7 / 8)), ‖A x‖ ≤ cap) →
      HasH1GradientOn u D (ball 0 (7 / 8)) →
      MemLp G 2 (volume.restrict (ball 0 (7 / 8))) →
      IsWeakDivergenceEquationOn A D G (ball 0 (7 / 8)) →
      (∫ x in ball 0 (3 / 4), ‖D x‖ ^ 2) ≤
        C * ((∫ x in ball 0 (7 / 8), u x ^ 2) + ∫ x in ball 0 (7 / 8), ‖G x‖ ^ 2) := by
  let η : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨3 / 4, 13 / 16, by norm_num, by norm_num⟩
  have hcη := η.hasCompactSupport
  have hcgrad : HasCompactSupport (gradient η) :=
    hcη.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset η)
  obtain ⟨B₀, hB₀⟩ := hcgrad.exists_bound_of_continuous
    (continuous_gradient_of_contDiff (η.contDiff : ContDiff ℝ 1 η))
  let B := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hbη (x : EuclideanSpace ℝ (Fin n)) : ‖gradient η x‖ ≤ B :=
    (hB₀ x).trans (le_max_left _ _)
  have hsη : tsupport η ⊆ ball 0 (7 / 8 : ℝ) := by
    rw [η.tsupport_eq]
    exact closedBall_subset_ball (by norm_num : (13 / 16 : ℝ) < 7 / 8)
  let K := (8 * cap ^ 2 + 2 * lam + 2) / lam ^ 2
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K * (B ^ 2 + 1), by positivity, ?_⟩
  intro A u D G hA hell hbA hu hG he
  have ht := nondiv_caccioppoli_cutoff_bound isOpen_ball measurableSet_ball hlam hlamcap
    hA hell hbA hu hG he (η.contDiff : ContDiff ℝ 1 η) hcη hsη
    (fun _ => ⟨η.nonneg, η.le_one⟩) hbη
    (show EqOn η (fun _ => 1) (ball 0 (3 / 4)) from
      fun _ hx => η.one_of_mem_closedBall (ball_subset_closedBall hx))
  apply ht.trans
  have hI : 0 ≤ ∫ x in ball 0 (7 / 8), u x ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have hJ : 0 ≤ ∫ x in ball 0 (7 / 8), ‖G x‖ ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  change K * _ ≤ (K * (B ^ 2 + 1)) * _
  have h := mul_le_mul_of_nonneg_left
    (show B ^ 2 * (∫ x in ball 0 (7 / 8), u x ^ 2) + (∫ x in ball 0 (7 / 8), ‖G x‖ ^ 2) ≤
      (B ^ 2 + 1) * ((∫ x in ball 0 (7 / 8), u x ^ 2) +
        ∫ x in ball 0 (7 / 8), ‖G x‖ ^ 2) by nlinarith [sq_nonneg B]) hK.le
  simpa only [mul_assoc] using h

end LiquidDrop
