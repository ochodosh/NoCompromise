module

public import NoCompromise.Elliptic.FrozenDecay

@[expose] public section

/-!
# Energy comparisons for actual weak gradients

Restriction and almost-everywhere replacement preserve the original compact-test
weak equation. The frozen replacement is constructed in the genuine H¹ space.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma IsWeakDivergenceEquationOn.mono {n : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {F G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (h : IsWeakDivergenceEquationOn A F G U) (hVU : V ⊆ U) :
    IsWeakDivergenceEquationOn A F G V :=
  fun φ hφ hcφ hsφ => h φ hφ hcφ (hsφ.trans hVU)

lemma IsWeakDivergenceEquationOn.congr_gradient_ae {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {F H G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (h : IsWeakDivergenceEquationOn A F G U) (he : F =ᵐ[volume.restrict U] H) :
    IsWeakDivergenceEquationOn A H G U := by
  intro φ hφ hcφ hsφ
  rw [← h φ hφ hcφ hsφ]
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' hU).mp he] with x hx
  by_cases hxU : x ∈ U
  · rw [hx hxU]
  · rw [gradient_eq_zero_of_notMem_tsupport (fun ht => hxU (hsφ ht)), inner_zero_right,
      inner_zero_right]

lemma campanato_integral_norm_sq_le_twice {X F : Type*}
    [MeasurableSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure X} {f g : X → F} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) ≤
      2 * (∫ x, ‖f x - g x‖ ^ 2 ∂μ) + 2 * (∫ x, ‖g x‖ ^ 2 ∂μ) := by
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hd : Integrable (fun x => ‖f x - g x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hf.sub hg).aestronglyMeasurable).mp (hf.sub hg)
  have hj := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  calc
    _ ≤ ∫ x, 2 * ‖f x - g x‖ ^ 2 + 2 * ‖g x‖ ^ 2 ∂μ := by
      apply integral_mono hi ((hd.const_mul 2).add (hj.const_mul 2))
      intro x
      change ‖f x‖ ^ 2 ≤ 2 * ‖f x - g x‖ ^ 2 + 2 * ‖g x‖ ^ 2
      have ht : ‖f x‖ ≤ ‖f x - g x‖ + ‖g x‖ := by
        simpa only [add_comm] using norm_le_insert' (f x) (g x)
      have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr ht
      nlinarith [sq_nonneg (‖f x - g x‖ - ‖g x‖)]
    _ = _ := by rw [integral_add (hd.const_mul 2) (hj.const_mul 2), integral_const_mul,
      integral_const_mul]

lemma campanato_integral_bounded_coefficient_sq {X F H : Type*}
    [MeasurableSpace X] [NormedAddCommGroup F] [NormedAddCommGroup H]
    {μ : Measure X} {f : X → F} {q : X → H} {B : ℝ}
    (hf : MemLp f 2 μ) (hq : AEStronglyMeasurable q μ) (hB : 0 ≤ B)
    (hb : ∀ᵐ x ∂μ, ‖q x‖ ≤ B) :
    (∫ x, ‖q x‖ ^ 2 * ‖f x‖ ^ 2 ∂μ) ≤ B ^ 2 * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have hm : MemLp (fun x => ‖q x‖ * ‖f x‖) 2 μ := by
    apply hf.norm.of_le_mul (c := B) (hq.norm.mul hf.aestronglyMeasurable.norm)
    filter_upwards [hb] with x hx
    simpa only [Pi.mul_apply, norm_mul, norm_norm] using
      mul_le_mul_of_nonneg_right hx (norm_nonneg (f x))
  have hi : Integrable (fun x => ‖q x‖ ^ 2 * ‖f x‖ ^ 2) μ := by
    simpa only [mul_pow] using hm.integrable_sq
  have hj := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  rw [← integral_const_mul]
  apply integral_mono_ae hi (hj.const_mul (B ^ 2))
  filter_upwards [hb] with x hx
  exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) hB).mpr hx) (sq_nonneg _)

lemma campanato_integral_sq_le_measure {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → F} {B : ℝ} (hf : MemLp f 2 μ) (hB : 0 ≤ B)
    (hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ B) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) ≤ B ^ 2 * μ.real univ := by
  calc
    _ ≤ ∫ _x, B ^ 2 ∂μ := by
      apply integral_mono_ae ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf)
        (integrable_const _)
      filter_upwards [hb] with x hx
      exact (sq_le_sq₀ (norm_nonneg _) hB).mpr hx
    _ = _ := by rw [integral_const]; simp only [smul_eq_mul]; ring

/-- Construct the frozen solution for raw representatives and bound its gradient
error by the actual coefficient and datum oscillations on the ball. -/
theorem exists_campanato_comparison_bounded_oscillation {n : ℕ} (hn : 0 < n)
    (c : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {F G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hu : HasH1GradientOn u F (ball c r))
    (hw : IsWeakDivergenceEquationOn A F G (ball c r))
    (hA : AEStronglyMeasurable A (volume.restrict (ball c r)))
    {cap lam B Q : ℝ} (hbA : ∀ᵐ x ∂volume.restrict (ball c r), ‖A x‖ ≤ cap)
    (hG : MemLp G 2 (volume.restrict (ball c r))) (hlam : 0 < lam)
    (hell : ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A c ξ) ξ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q)
    (hBA : ∀ᵐ x ∂volume.restrict (ball c r), ‖A x - A c‖ ≤ B)
    (hQG : ∀ᵐ x ∂volume.restrict (ball c r), ‖G x - G c‖ ≤ Q) :
    ∃ h : H1Space (ball c r),
      IsWeakDivergenceEquationOn (fun _ => A c) h.gradientLp (fun _ => 0) (ball c r) ∧
      (∫ x in ball c r, ‖F x - h.gradientLp x‖ ^ 2) ≤
        (2 / lam ^ 2) * (B ^ 2 * (∫ x in ball c r, ‖F x‖ ^ 2) +
          Q ^ 2 * volume.real (ball c r)) := by
  let w := H1Space.ofFunction u F hu
  have he : w.gradientLp =ᵐ[volume.restrict (ball c r)] F :=
    H1Space.gradientLp_ofFunction u F hu
  obtain ⟨h, _, hh, herr⟩ := exists_campanato_comparison_ball hn c r A G w hA hbA hG
    hlam hell (hw.congr_gradient_ae measurableSet_ball he.symm)
  have herr' : (∫ x in ball c r, ‖F x - h.gradientLp x‖ ^ 2) ≤
      (2 / lam ^ 2) * (∫ x in ball c r, ‖A x - A c‖ ^ 2 * ‖F x‖ ^ 2) +
      (2 / lam ^ 2) * (∫ x in ball c r, ‖G x - G c‖ ^ 2) := by
    have hi₁ : (∫ x in ball c r, ‖F x - h.gradientLp x‖ ^ 2) =
        ∫ x in ball c r, ‖w.gradientLp x - h.gradientLp x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [he] with x hx
      rw [hx]
    have hi₂ : (∫ x in ball c r, ‖A x - A c‖ ^ 2 * ‖F x‖ ^ 2) =
        ∫ x in ball c r, ‖A x - A c‖ ^ 2 * ‖w.gradientLp x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [he] with x hx
      rw [hx]
    rwa [hi₁, hi₂]
  let : IsFiniteMeasure (volume.restrict (ball c r)) :=
    ⟨by simpa using (isBounded_ball (x := c) (r := r)).measure_lt_top⟩
  have ha := campanato_integral_bounded_coefficient_sq hu.memLp_gradient
    (hA.sub aestronglyMeasurable_const) hB hBA
  have hg := campanato_integral_sq_le_measure (hG.sub (memLp_const (G c))) hQ hQG
  simp only [Measure.real, Measure.restrict_apply_univ] at hg
  refine ⟨h, hh, herr'.trans ?_⟩
  have hc : 0 ≤ 2 / lam ^ 2 := by positivity
  calc
    _ ≤ (2 / lam ^ 2) * (B ^ 2 * (∫ x in ball c r, ‖F x‖ ^ 2)) +
        (2 / lam ^ 2) * (Q ^ 2 * volume.real (ball c r)) :=
      add_le_add (mul_le_mul_of_nonneg_left ha hc) (mul_le_mul_of_nonneg_left hg hc)
    _ = _ := by ring

end LiquidDrop
