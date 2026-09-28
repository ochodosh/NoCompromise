import NoCompromise.Elliptic.FrozenDecayEstimates

/-! Affine subtraction preserves the genuine frozen equation. This lets the
second derivative estimate depend on centered gradient energy. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma frozen_gradient_inner (c x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => inner ℝ c y) x = c := by
  apply (toDual ℝ (EuclideanSpace ℝ (Fin n))).injective
  rw [toDual_gradient]
  exact (innerSL ℝ c).fderiv

lemma frozen_hasH1GradientOn_inner_ball (c : EuclideanSpace ℝ (Fin n)) :
    HasH1GradientOn (fun y => inner ℝ c y) (fun _ => c) (ball 0 1) := by
  let : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isBounded_ball.measure_lt_top⟩
  have hc : ContDiff ℝ 1 (fun y => inner ℝ c y) := (innerSL ℝ c).contDiff
  refine ⟨?_, ?_, memLp_const c⟩
  · have he : gradient (fun y => inner ℝ c y) = fun _ => c :=
      funext (frozen_gradient_inner c)
    rw [← he]
    exact hasWeakGradientOn_of_contDiffOn isOpen_ball hc.contDiffOn
  · apply MemLp.of_bound hc.continuous.aestronglyMeasurable ‖c‖
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact (norm_inner_le_norm _ _).trans (by
      have hx' : ‖x‖ ≤ 1 := (mem_ball_zero_iff.mp hx).le
      nlinarith [norm_nonneg c])

lemma frozen_equation_sub_constant_unit_ball {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hG : MemLp G 2 (volume.restrict (ball 0 1)))
    (hw : IsWeakDivergenceEquationOn (fun _ => A) G (fun _ => 0) (ball 0 1))
    (c : EuclideanSpace ℝ (Fin n)) :
    IsWeakDivergenceEquationOn (fun _ => A) (fun x => G x - c) (fun _ => 0) (ball 0 1) := by
  let : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isBounded_ball.measure_lt_top⟩
  intro φ hφ hcφ hsφ
  simp only [sub_zero, map_sub, inner_sub_left]
  have hφG : MemLp (gradient φ) 2 (volume.restrict (ball 0 1)) :=
    ((continuous_gradient_of_contDiff hφ).memLp_of_hasCompactSupport
      (hcφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset φ))).mono_measure
      Measure.restrict_le_self
  have hi : IntegrableOn (fun x => inner ℝ (A (G x)) (gradient φ x)) (ball 0 1) :=
    integrable_inner_of_memLp_two (A.comp_memLp' hG) hφG
  have hj : IntegrableOn (fun x => inner ℝ (A c) (gradient φ x)) (ball 0 1) :=
    integrable_inner_of_memLp_two (memLp_const (A c)) hφG
  have hset (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :
      (∫ x in ball 0 1, inner ℝ (F x) (gradient φ x)) =
        ∫ x, inner ℝ (F x) (gradient φ x) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [gradient_eq_zero_of_notMem_tsupport (fun ht => hx (hsφ ht)), inner_zero_right])
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ball 0 1)
    (fun x hx => by rw [gradient_eq_zero_of_notMem_tsupport (fun ht => hx (hsφ ht)),
      inner_zero_right, inner_zero_right, sub_self]), integral_sub hi hj,
    hset (fun x => A (G x)), hset (fun _ => A c)]
  have htest := hw φ hφ hcφ hsφ
  simp only [sub_zero] at htest
  rw [htest, campanato_integral_inner_const_gradient hφ hcφ, sub_self]

/-- The derivative of order two of an affine function vanishes, including
inside arbitrary smooth representatives. -/
lemma frozen_norm_second_sub_inner {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (c x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U) :
    iteratedFDeriv ℝ 2 (fun y => u y - inner ℝ c y) x = iteratedFDeriv ℝ 2 u x := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y => inner ℝ c y) := (innerSL ℝ c).contDiff
  have he : iteratedFDeriv ℝ 2 (fun y => inner ℝ c y) x = 0 := by
    ext v
    rw [iteratedFDeriv_two_apply]
    have hd : fderiv ℝ (fun y => inner ℝ c y) = fun _ => innerSL ℝ c :=
      funext (fun _ => (innerSL ℝ c).fderiv)
    rw [hd, fderiv_const_apply]
    rfl
  change iteratedFDeriv ℝ 2 (u - fun y => inner ℝ c y) x = _
  rw [iteratedFDeriv_sub_apply
    ((hu.contDiffAt (hU.mem_nhds hx)).of_le (by simp)) (hc.contDiffAt.of_le (by simp)),
    he, sub_zero]

/-- Subtracting any affine slope gives a Hessian bound by the corresponding
gradient oscillation, with an ellipticity-only constant. -/
theorem frozen_hessian_unit_ball_centered_bound {n : ℕ} (hn : n < 4)
    {lam cap : ℝ} (hlam : 0 < lam) (hcap : 0 ≤ cap) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        HasH1GradientOn u G (ball 0 1) →
        IsWeakDivergenceEquationOn (fun _ => A) G (fun _ => 0) (ball 0 1) →
        (∀ x, lam * ‖x‖ ^ 2 ≤ inner ℝ (A x) x) → ‖A‖ ≤ cap →
        ContDiffOn ℝ (⊤ : ℕ∞) u (ball 0 1) →
        ∀ c x, x ∈ ball 0 (1 / 2 : ℝ) → ‖fderiv ℝ (gradient u) x‖ ≤
          C * lpNorm (fun y => G y - c) 2 (volume.restrict (ball 0 1)) := by
  obtain ⟨C, hC, hb⟩ := frozen_derivative_unit_ball_bound (k := 1) hn hlam hcap
  refine ⟨C, hC, ?_⟩
  intro A u G hu hw hell hbound hc c x hx
  have hf := hu.sub (frozen_hasH1GradientOn_inner_ball c)
  have heq := frozen_equation_sub_constant_unit_ball A hu.memLp_gradient hw c
  have hsc : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => u y - inner ℝ c y) (ball 0 1) :=
    hc.sub (innerSL ℝ c).contDiff.contDiffOn
  have h := hb A (fun y => u y - inner ℝ c y) (fun y => G y - c)
    hf heq hell hbound hsc x hx
  rw [frozen_norm_second_sub_inner isOpen_ball hc c x
    ((ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1)) hx)] at h
  have he : ‖fderiv ℝ (gradient u) x‖ = ‖iteratedFDeriv ℝ 2 u x‖ := by
    rw [← norm_iteratedFDeriv_one, sobolevChain_norm_iteratedFDeriv_gradient]
  rwa [he]

end LiquidDrop
