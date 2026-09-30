module

public import NoCompromise.Elliptic.HarmonicDerivativeTranslation
public import NoCompromise.Elliptic.HarmonicMeanValue

@[expose] public section

/-!
# Harmonic derivative estimates

For dimensions below four, including the two blueprint dimensions, all derivative
orders satisfy the interior L²-to-L∞ and L∞-to-L∞ estimates. Positive orders are
also controlled by the L² norm of the actual gradient. The derivatives use the
continuous-multilinear operator norm, and every constant is independent of the
center and of the harmonic function. Distributional harmonicity and continuity
are the only regularity hypotheses; smoothness is obtained from the proved
harmonic regularity theorem.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma harmonicDerivative_contDiffOn_gradient {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (gradient u) U :=
  (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.contDiff.comp_contDiffOn
    (hu.fderiv_of_isOpen hU (by simp))

lemma harmonicDerivative_norm_iteratedFDeriv_vector_le {n j : ℕ}
    {W : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin n)} (hW : ContDiffAt ℝ (⊤ : ℕ∞) W x) :
    ‖iteratedFDeriv ℝ j W x‖ ≤ ∑ i, ‖iteratedFDeriv ℝ j (fun y => W y i) x‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro v
  calc
    ‖iteratedFDeriv ℝ j W x v‖ ≤ ∑ i, ‖(iteratedFDeriv ℝ j W x v) i‖ :=
      sobolevChain_euclidean_norm_le_sum _
    _ = ∑ i, ‖iteratedFDeriv ℝ j (fun y => W y i) x v‖ := by
      apply Finset.sum_congr rfl
      intro i _
      have h := (EuclideanSpace.proj (𝕜 := ℝ) i).iteratedFDeriv_comp_left (i := j) (x := x) hW
        (by simp)
      exact congrArg (fun A => ‖A v‖) h.symm
    _ ≤ ∑ i, ‖iteratedFDeriv ℝ j (fun y => W y i) x‖ * ∏ l, ‖v l‖ :=
      Finset.sum_le_sum fun i _ => ContinuousMultilinearMap.le_opNorm _ _
    _ = (∑ i, ‖iteratedFDeriv ℝ j (fun y => W y i) x‖) * ∏ l, ‖v l‖ :=
      (Finset.sum_mul ..).symm

/-- Positive-order harmonic derivatives are controlled by the L² norm of the
actual classical gradient, without an L² hypothesis on the function itself. -/
theorem harmonic_derivative_gradient_l2_bound {n k : ℕ} (hn : n < 4)
    {r R : ℝ} (hrR : r < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : EuclideanSpace ℝ (Fin n))
      (u : EuclideanSpace ℝ (Fin n) → ℝ),
      HasDistributionalLaplacianOn u (fun _ => 0) (ball z R) →
      MemLp (gradient u) 2 (volume.restrict (ball z R)) →
      ContDiffOn ℝ (⊤ : ℕ∞) u (ball z R) → ∀ x ∈ ball z r,
        ‖iteratedFDeriv ℝ (k + 1) u x‖ ≤
          C * lpNorm (gradient u) 2 (volume.restrict (ball z R)) := by
  obtain ⟨C, hC, hb⟩ := harmonic_derivative_l2_bound (k := k) hn hrR
  refine ⟨((n : ℝ) + 1) * C, mul_pos (by positivity) hC, ?_⟩
  intro z u h hG hc x hx
  have hGc := harmonicDerivative_contDiffOn_gradient isOpen_ball hc
  have hbcomp (i : Fin n) :
      ‖iteratedFDeriv ℝ k (fun y => gradient u y i) x‖ ≤
        C * lpNorm (gradient u) 2 (volume.restrict (ball z R)) := by
    have hgi : HasDistributionalLaplacianOn (fun y => gradient u y i) (fun _ => 0)
        (ball z R) := by
      simpa using h.gradient_component
        (hasWeakGradientOn_of_contDiffOn isOpen_ball (hc.of_le (by simp)))
        (HasH1GradientOn.zero (ball z R)).toHasWeakGradientOn i
    have hgiC : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => gradient u y i) (ball z R) :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn hGc
    exact (hb z _ hgi ((EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hG) hgiC
      k le_rfl x hx).trans (mul_le_mul_of_nonneg_left
        (harmonicDerivative_lpNorm_component_le hG i) hC.le)
  rw [← sobolevChain_norm_iteratedFDeriv_gradient]
  calc
    ‖iteratedFDeriv ℝ k (gradient u) x‖ ≤
        ∑ i, ‖iteratedFDeriv ℝ k (fun y => gradient u y i) x‖ :=
      harmonicDerivative_norm_iteratedFDeriv_vector_le
        (hGc.contDiffAt (isOpen_ball.mem_nhds ((ball_subset_ball hrR.le) hx)))
    _ ≤ ∑ _i : Fin n, C * lpNorm (gradient u) 2 (volume.restrict (ball z R)) :=
      Finset.sum_le_sum fun i _ => hbcomp i
    _ = (n : ℝ) * C * lpNorm (gradient u) 2 (volume.restrict (ball z R)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ ((n : ℝ) + 1) * C * lpNorm (gradient u) 2 (volume.restrict (ball z R)) := by
      nlinarith [lpNorm_nonneg (f := gradient u) (p := 2)
        (μ := volume.restrict (ball z R))]

lemma harmonicDerivative_lpNorm_two_le_top {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] {μ : Measure α} [IsFiniteMeasure μ] {f : α → F}
    (hf : MemLp f ∞ μ) :
    lpNorm f 2 μ ≤ (μ.real univ) ^ (1 / 2 : ℝ) * lpNorm f ∞ μ := by
  have hb := eLpNorm_le_of_ae_bound (p := (2 : ENNReal)) hf.aestronglyMeasurable
    (ae_le_lpNorm_exponent_top hf)
  have ht : (μ univ) ^ (2 : ENNReal).toReal⁻¹ * ENNReal.ofReal (lpNorm f ∞ μ) ≠ ∞ :=
    by finiteness
  have hh := ENNReal.toReal_mono ht hb
  simpa only [toReal_eLpNorm, ENNReal.toReal_mul, ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (lpNorm_nonneg), ENNReal.toReal_ofNat, one_div, Measure.real] using hh

lemma harmonicDerivative_memLp_top_of_bound {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : EuclideanSpace ℝ (Fin n) → F} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (k : ℕ)
    {B : ℝ} (hB : ∀ x ∈ U, ‖iteratedFDeriv ℝ k u x‖ ≤ B) :
    MemLp (iteratedFDeriv ℝ k u) ∞ (volume.restrict U) ∧
      lpNorm (iteratedFDeriv ℝ k u) ∞ (volume.restrict U) ≤ max B 0 := by
  have hm : AEStronglyMeasurable (iteratedFDeriv ℝ k u) (volume.restrict U) :=
    (ContinuousOn.continuousOn_iteratedFDeriv hu hU (by simp)).aestronglyMeasurable
      hU.measurableSet
  have hb : ∀ᵐ x ∂volume.restrict U, ‖iteratedFDeriv ℝ k u x‖ ≤ max B 0 := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact (hB x hx).trans (le_max_left _ _)
  refine ⟨memLp_top_of_bound hm (max B 0) hb, ?_⟩
  rw [← toReal_eLpNorm, eLpNorm_exponent_top hm]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (eLpNormEssSup_le_of_ae_bound hb)).trans_eq (ENNReal.toReal_ofReal (le_max_right _ _))

lemma harmonicDerivative_ball_measureReal_eq {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) (R : ℝ) :
    (volume.restrict (ball z R)).real univ =
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) R)).real univ := by
  have he := (measurePreserving_add_left_ball z R).measure_preimage MeasurableSet.univ
  change (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) R)) univ =
    (volume.restrict (ball z R)) univ at he
  exact congrArg ENNReal.toReal he.symm

/-- The full L²-to-L∞ harmonic derivative estimate, with the derivative interpreted
as a continuous multilinear map with its operator norm. -/
theorem harmonic_derivative_estimate_l2 {n k : ℕ} (hn : n < 4)
    {r R : ℝ} (hrR : r < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : EuclideanSpace ℝ (Fin n))
      (u : EuclideanSpace ℝ (Fin n) → ℝ),
      HasDistributionalLaplacianOn u (fun _ => 0) (ball z R) →
      ContinuousOn u (ball z R) → MemLp u 2 (volume.restrict (ball z R)) →
      MemLp (iteratedFDeriv ℝ k u) ∞ (volume.restrict (ball z r)) ∧
        lpNorm (iteratedFDeriv ℝ k u) ∞ (volume.restrict (ball z r)) ≤
          C * lpNorm u 2 (volume.restrict (ball z R)) := by
  obtain ⟨C, hC, hb⟩ := harmonic_derivative_l2_bound (k := k) hn hrR
  refine ⟨C, hC, fun z u h hc hu => ?_⟩
  have hs := h.contDiffOn_of_continuous hn isOpen_ball hc
  obtain ⟨hm, hbound⟩ := harmonicDerivative_memLp_top_of_bound isOpen_ball
    (hs.mono (ball_subset_ball hrR.le)) k (hb z u h hu hs k le_rfl)
  refine ⟨hm, ?_⟩
  simpa only [max_eq_left (mul_nonneg hC.le lpNorm_nonneg)] using hbound

/-- The L∞ input version of the same estimate.  Its constant remains independent
of the center of the ball and of the harmonic function. -/
theorem harmonic_derivative_estimate_top {n k : ℕ} (hn : n < 4)
    {r R : ℝ} (hrR : r < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : EuclideanSpace ℝ (Fin n))
      (u : EuclideanSpace ℝ (Fin n) → ℝ),
      HasDistributionalLaplacianOn u (fun _ => 0) (ball z R) →
      ContinuousOn u (ball z R) → MemLp u ∞ (volume.restrict (ball z R)) →
      MemLp (iteratedFDeriv ℝ k u) ∞ (volume.restrict (ball z r)) ∧
        lpNorm (iteratedFDeriv ℝ k u) ∞ (volume.restrict (ball z r)) ≤
          C * lpNorm u ∞ (volume.restrict (ball z R)) := by
  obtain ⟨C, hC, hb⟩ := harmonic_derivative_estimate_l2 (k := k) hn hrR
  let v : ℝ := ((volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) R)).real univ) ^
    (1 / 2 : ℝ)
  have hv : 0 ≤ v := Real.rpow_nonneg (measureReal_nonneg) _
  refine ⟨C * (v + 1), mul_pos hC (by linarith), fun z u h hc hu => ?_⟩
  let : IsFiniteMeasure (volume.restrict (ball z R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isBounded_ball.measure_lt_top⟩
  obtain ⟨hm, hbound⟩ := hb z u h hc (hu.mono_exponent le_top)
  refine ⟨hm, hbound.trans ?_⟩
  have hh := harmonicDerivative_lpNorm_two_le_top hu
  rw [harmonicDerivative_ball_measureReal_eq z R] at hh
  change lpNorm u 2 (volume.restrict (ball z R)) ≤
    v * lpNorm u ∞ (volume.restrict (ball z R)) at hh
  calc
    C * lpNorm u 2 (volume.restrict (ball z R)) ≤
        C * (v * lpNorm u ∞ (volume.restrict (ball z R))) :=
      mul_le_mul_of_nonneg_left hh hC.le
    _ ≤ C * (v + 1) * lpNorm u ∞ (volume.restrict (ball z R)) := by
      nlinarith [lpNorm_nonneg (f := u) (p := ∞) (μ := volume.restrict (ball z R))]

/-- Every positive derivative order can instead be controlled solely by the
L² norm of the actual gradient on the outer ball. -/
theorem harmonic_derivative_estimate_gradient {n k : ℕ} (hn : n < 4)
    {r R : ℝ} (hrR : r < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : EuclideanSpace ℝ (Fin n))
      (u : EuclideanSpace ℝ (Fin n) → ℝ),
      HasDistributionalLaplacianOn u (fun _ => 0) (ball z R) →
      ContinuousOn u (ball z R) → MemLp (gradient u) 2 (volume.restrict (ball z R)) →
      MemLp (iteratedFDeriv ℝ (k + 1) u) ∞ (volume.restrict (ball z r)) ∧
        lpNorm (iteratedFDeriv ℝ (k + 1) u) ∞ (volume.restrict (ball z r)) ≤
          C * lpNorm (gradient u) 2 (volume.restrict (ball z R)) := by
  obtain ⟨C, hC, hb⟩ := harmonic_derivative_gradient_l2_bound (k := k) hn hrR
  refine ⟨C, hC, fun z u h hc hu => ?_⟩
  have hs := h.contDiffOn_of_continuous hn isOpen_ball hc
  obtain ⟨hm, hbound⟩ := harmonicDerivative_memLp_top_of_bound isOpen_ball
    (hs.mono (ball_subset_ball hrR.le)) (k + 1) (hb z u h hu hs)
  refine ⟨hm, ?_⟩
  simpa only [max_eq_left (mul_nonneg hC.le lpNorm_nonneg)] using hbound

end LiquidDrop
