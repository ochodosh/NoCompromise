import NoCompromise.Elliptic.QuasilinearHessian
import NoCompromise.Elliptic.QuasilinearLinearization
import NoCompromise.Elliptic.NondivSchauderDatumLimit
import NoCompromise.Elliptic.NondivSchauderEquationLimit

/-! Passage from the genuine quasilinear quotient equations to the equation for
an actual first derivative. Weak compactness, uniform coefficient convergence,
and the constructed Gh source supply every hypothesis of the limit theorem. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma quasilinear_segmentField_tendsto_L2 {n : ℕ} {a : ℝ} (ha : 0 < a)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} {U V : Set (EuclideanSpace ℝ (Fin n))}
    (hV : MeasurableSet V) (hVfin : volume V ≠ ∞) (hg : HasFiniteHolderNormOn a g U)
    (e : EuclideanSpace ℝ (Fin n)) (he : ‖e‖ = 1)
    {h : ℕ → ℝ} (ht : Tendsto h atTop (𝓝 0))
    (hseg : ∀ j, V ⊆ campanatoSegmentDomain U (h j • e)) :
    Tendsto (fun j => eLpNorm (fun x => campanatoSegmentField g (h j) e x - g x • e)
      2 (volume.restrict V)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun j => ‖h j‖ ^ a) atTop (𝓝 0) := by
    simpa only [norm_zero, Real.zero_rpow ha.ne', Function.comp_def] using!
      (Real.continuous_rpow_const ha.le).continuousAt.tendsto.comp ht.norm
  have hof : Tendsto (fun j => ENNReal.ofReal (holderSeminorm a g U * ‖h j‖ ^ a))
      atTop (𝓝 0) := by
    simpa only [mul_zero, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (hpow.const_mul (holderSeminorm a g U))
  have hlim := ENNReal.Tendsto.const_mul hof
    (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hVfin))
  simp only [mul_zero] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
  intro j
  have hb : ∀ᵐ x ∂volume.restrict V,
      ‖campanatoSegmentField g (h j) e x - g x • e‖ ≤ holderSeminorm a g U * ‖h j‖ ^ a := by
    filter_upwards [ae_restrict_mem hV] with x hx
    exact nondiv_segmentField_sub_le ha hg (h j) e he (hseg j hx)
  have hgc : ContinuousOn g U := hg.nondiv_continuousOn ha
  have hVU : V ⊆ U := (hseg j).trans (campanatoSegmentDomain_subset U _)
  have hm : AEStronglyMeasurable (fun x => campanatoSegmentField g (h j) e x - g x • e)
      (volume.restrict V) :=
    ((((campanatoSegmentField_continuousOn ha hgc hg (h j) e he).mono (hseg j)).sub
      ((hgc.mono hVU).smul continuousOn_const))).aestronglyMeasurable hV
  simpa only [Measure.restrict_apply_univ, ENNReal.toReal_ofNat, one_div] using
    (eLpNorm_le_of_ae_bound (p := 2) hm hb)

/-- The original quasilinear equation gives the actual linearized equation for
each coordinate derivative, with no assumed second derivative or tested energy
identity. The constant is chosen before all solution data. -/
theorem quasilinear_exists_coordinate_linearized {n : ℕ} {a lam cap M B N : ℝ}
    (ha : 0 < a) (hlam : 0 < lam) (hlamcap : lam ≤ cap)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (f g : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiff ℝ 2 A → HasC1HolderOn a f (ball 0 1) →
      HasFiniteHolderNormOn a g (ball 0 1) → holderNorm a g (ball 0 1) ≤ N →
      (∀ x ∈ ball 0 (1 : ℝ), ‖gradient f x‖ ≤ M) →
      (∀ p ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) M, ‖fderiv ℝ A p‖ ≤ cap) →
      (∀ p ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) M,
        ‖fderiv ℝ (fderiv ℝ A) p‖ ≤ B) →
      (∀ p ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) M, ∀ ξ,
        lam * ‖ξ‖ ^ 2 ≤ inner ℝ (fderiv ℝ A p ξ) ξ) →
      IsWeakQuasilinearEquationOn A f g (ball 0 1) →
      ∀ i : Fin n, ∃ G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        HasH1GradientOn (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) G
          (ball 0 (3 / 4)) ∧
        lpNorm G 2 (volume.restrict (ball 0 (3 / 4))) ≤ C ∧
        IsWeakDivergenceEquationOn (fun x => fderiv ℝ A (gradient f x)) G
          (fun x => g x • EuclideanSpace.single i 1) (ball 0 (3 / 4)) := by
  obtain ⟨C, hC, hder⟩ := quasilinear_exists_coordinate_h1_gradient
    (n := n) ha hlam hlamcap hM hB hN
  obtain ⟨Cq, _, hquot⟩ := quasilinear_quotient_h1_bound (n := n) ha hlam hlamcap hM hB hN
  refine ⟨C, hC, ?_⟩
  intro A f g hA hf hg hgN hfM hcap hb hell he i
  obtain ⟨G, hG, hGb, σ, hσ, hweak⟩ := hder A f g hA hf hg hgN hfM hcap hb hell he i
  refine ⟨G, hG, hGb, ?_⟩
  let V : Set (EuclideanSpace ℝ (Fin n)) := ball 0 (3 / 4)
  let s (j : ℕ) := nondivQuotientStep (σ j)
  let Q (j : ℕ) := quasilinearCoefficientField A (gradient f) i (s j)
  let H (j : ℕ) := campanatoSegmentField g (s j) (EuclideanSpace.single i 1)
  have hVU : V ⊆ ball 0 (1 : ℝ) := ball_subset_ball (by norm_num : (3 / 4 : ℝ) ≤ 1)
  have hVW : V ⊆ ball 0 (7 / 8 : ℝ) := ball_subset_ball (by norm_num : (3 / 4 : ℝ) ≤ 7 / 8)
  have hseg (j : ℕ) : V ⊆ campanatoSegmentDomain (ball 0 1)
      (s j • EuclideanSpace.single i 1) :=
    fun _ hx _ ht => nondiv_segment_mem_unitBall i (nondivQuotientStep_small (σ j)) (hVW hx) ht
  have hmap (j : ℕ) : ∀ x ∈ V, x + s j • EuclideanSpace.single i 1 ∈ ball 0 (1 : ℝ) := by
    intro x hx
    simpa only [one_smul] using hseg j hx 1 (by simp)
  have hFM : ∀ x ∈ ball 0 (1 : ℝ), gradient f x ∈ closedBall 0 M := by
    intro x hx
    simpa only [mem_closedBall, dist_zero_right] using hfM x hx
  have hhold := hf.gradient_holder.1
  let L := holderSeminorm a (gradient f) (ball 0 1)
  have hL : 0 ≤ L := hhold.seminorm_nonneg
  have hFhold : ∀ x ∈ ball 0 (1 : ℝ), ∀ y ∈ ball 0 (1 : ℝ),
      ‖gradient f x - gradient f y‖ ≤ L * dist x y ^ a := by
    intro x hx y hy
    simpa only [L, dist_eq_norm] using hhold.nondiv_norm_sub_le hx hy
  have hQc (j : ℕ) : ContinuousOn (Q j) V :=
    quasilinearCoefficientField_continuousOn hA hB hL ha hb hFM hFhold hVU i (s j) (hmap j)
  have hDAc : Continuous (fderiv ℝ A) :=
    (hA.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).continuous_fderiv one_ne_zero
  have hA₀c : ContinuousOn (fun x => fderiv ℝ A (gradient f x)) V :=
    hDAc.comp_continuousOn
      ((continuousOn_gradient_of_contDiffOn isOpen_ball hf.contDiff).mono hVU)
  have hq (j : ℕ) := hquot A f g hA hf hg hgN hfM hcap hb hell he i (s j)
    (nondivQuotientStep_pos (σ j)).ne' (nondivQuotientStep_small (σ j))
  have hHeq (j : ℕ) := (quasilinear_quotient_equation ha hB isOpen_ball isOpen_ball
    isBounded_ball isBounded_ball hA hf hg hfM hcap hb he i
      (nondivQuotientStep_pos (σ j)).ne' (hseg j)).2
  let : IsFiniteMeasure (volume.restrict V) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isBounded_ball.measure_lt_top⟩
  have hHholder (j : ℕ) : HasFiniteHolderNormOn a (H j) V :=
    (schauder_holder_mono
      (campanatoSegmentField_holder (hg.nondiv_continuousOn ha) hg (s j)
        (EuclideanSpace.single i 1) (by simp)).1 (hseg j)).1
  have hHm (j : ℕ) : MemLp (H j) 2 (volume.restrict V) := by
    apply MemLp.of_bound ((hHholder j).nondiv_continuousOn ha |>.aestronglyMeasurable
      measurableSet_ball) (holderNorm a (H j) V)
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact (hHholder j).nondiv_norm_le hx
  have hG₀m : MemLp (fun x => g x • EuclideanSpace.single i (1 : ℝ))
      2 (volume.restrict V) := by
    apply MemLp.of_bound
      (((hg.nondiv_continuousOn ha).mono hVU).smul continuousOn_const |>.aestronglyMeasurable
        measurableSet_ball) N
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    change ‖g x • EuclideanSpace.single i (1 : ℝ)‖ ≤ N
    simpa only [norm_smul, PiLp.norm_single, norm_one, mul_one] using
      (hg.nondiv_norm_le (hVU hx)).trans hgN
  have hs : Tendsto s atTop (𝓝 0) := tendsto_nondivQuotientStep.comp hσ.tendsto_atTop
  have hpow : Tendsto (fun j => ‖s j‖ ^ a) atTop (𝓝 0) := by
    simpa only [norm_zero, Real.zero_rpow ha.ne', Function.comp_def] using!
      (Real.continuous_rpow_const ha.le).continuousAt.tendsto.comp hs.norm
  apply nondiv_weakDivergenceEquation_limit
    (fun j => (hQc j).aestronglyMeasurable measurableSet_ball)
    (hA₀c.aestronglyMeasurable measurableSet_ball)
    (fun j => (hq j).1.memLp_gradient) hG.memLp_gradient hHm hG₀m
    (cap := cap) (M := Cq)
    (by
      intro j
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact quasilinearSecantCoefficient_norm_le hcap (hFM x (hVU hx)) (hFM _ (hmap j x hx)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact hcap _ (hFM x (hVU hx)))
    (fun j => (le_add_of_nonneg_left (lpNorm_nonneg (f := coordinateDifferenceQuotient i (s j) f)
      (p := 2) (μ := volume.restrict V))).trans (hq j).2)
    (ε := fun j => (B * L) * ‖s j‖ ^ a) (fun j => by positivity)
    (by simpa only [mul_zero] using hpow.const_mul (B * L))
    (by
      intro j
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact quasilinearCoefficientField_error_le hA hB hb hFM hFhold i (s j)
        (hVU hx) (hmap j x hx)) hweak
    (quasilinear_segmentField_tendsto_L2 ha measurableSet_ball
      (ne_of_lt isBounded_ball.measure_lt_top) hg (EuclideanSpace.single i 1) (by simp) hs hseg)
    hHeq

end LiquidDrop
