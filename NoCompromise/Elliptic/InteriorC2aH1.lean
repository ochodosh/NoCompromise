import NoCompromise.Elliptic.InteriorC2aDiv
import NoCompromise.Elliptic.CampanatoHolder

/-!
# Interior C²,α from H¹ for `div(A∇u) = div G`

An H¹ weak solution on the unit ball has a C¹,α representative on `ball 0 (1/2)`
(`campanato_c1_holder`); the divergence-form Schauder estimate for C¹,α solutions
(`interior_c2a_holder_div_ball`) then gives C²,α on `ball 0 (1/4)`.
This is the interior (covering) piece of `thm:boundary-C2a`.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

theorem interior_c2a_holder_of_h1 {α lam cap M E : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hlamcap : lam ≤ cap) (hM : 0 ≤ M) (hE : 0 ≤ E) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3))
      (G F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (u : EuclideanSpace ℝ (Fin 3) → ℝ),
      HasC1HolderOn α A (ball 0 1) → HasC1HolderOn α G (ball 0 1) →
      nondivC1HolderNorm α A (ball 0 1) ≤ M → nondivC1HolderNorm α G (ball 0 1) ≤ M →
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, ‖A x‖ ≤ cap) →
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ) →
      HasH1GradientOn u F (ball 0 1) → IsWeakDivergenceEquationOn A F G (ball 0 1) →
      (∫ x in ball 0 1, ‖F x‖ ^ 2) ≤ E →
      ∃ v : EuclideanSpace ℝ (Fin 3) → ℝ,
        u =ᵐ[volume.restrict (ball 0 (1 / 2 : ℝ))] v ∧
        HasC2HolderOn α v (ball 0 (1 / 4)) ∧
        schauderC2HolderNorm α v (ball 0 (1 / 4)) ≤
          C * (lpNorm v ∞ (volume.restrict (ball 0 (1 / 2 : ℝ))) + 1) := by
  obtain ⟨C₁, hC₁, hc1⟩ := campanato_c1_holder (n := 3) (by norm_num) (by norm_num) hα hα1
    hlam (hlam.le.trans hlamcap) hM hM hE
  obtain ⟨C₂, hC₂, hc2⟩ := interior_c2a_holder_div_ball hα hα1 hlam hlamcap hM
  refine ⟨8 * C₂ * (3 * M + 1), by positivity, ?_⟩
  intro A G F u hA hG hAn hGn hcap hell hu hw hE'
  have hsemi : ∀ {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}, HasC1HolderOn α f (ball 0 1) →
      nondivC1HolderNorm α f (ball 0 1) ≤ M →
      ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1,
        ‖f x - f y‖ ≤ M * dist x y ^ α := by
    intro f hf hfn x hx y hy
    rw [dist_eq_norm]
    refine (hf.function_holder.nondiv_norm_sub_le hx hy).trans
      (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact ((le_add_of_nonneg_left (holderUniformNorm_nonneg
      hf.function_holder.uniform_bounded)).trans hf.function_norm_le).trans hfn
  have hHA := hsemi hA hAn
  have hHG : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, ‖G x - G y‖ ≤ M * dist x y ^ α := by
    intro x hx y hy
    rw [dist_eq_norm]
    refine (hG.function_holder.nondiv_norm_sub_le hx hy).trans
      (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact ((le_add_of_nonneg_left (holderUniformNorm_nonneg
      hG.function_holder.uniform_bounded)).trans hG.function_norm_le).trans hGn
  obtain ⟨v, hv1, huv, hFv, hgb, hgh, -⟩ := hc1 A G F u hA.contDiff.continuousOn
    hG.contDiff.continuousOn hcap hell hHA hHG hu hw hE'
  have hsub : ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2) ⊆ ball 0 1 :=
    ball_subset_ball (by norm_num)
  obtain ⟨hA', hAn'⟩ := hA.mono hsub
  obtain ⟨hG', hGn'⟩ := hG.mono hsub
  -- `v` is C¹,α on the half ball
  have hdiff : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2), DifferentiableAt ℝ v x :=
    fun x hx => (hv1.differentiableOn (by norm_num) x hx).differentiableAt
      (isOpen_ball.mem_nhds hx)
  have hfd : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2), ‖fderiv ℝ v x‖ ≤ C₁ := by
    intro x hx
    have h := hgb x hx
    rwa [gradient, LinearIsometryEquiv.norm_map] at h
  have hlip : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2),
      ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2), ‖v x - v y‖ ≤ C₁ * ‖x - y‖ :=
    fun x hx y hy =>
      (convex_ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2)).norm_image_sub_le_of_norm_fderiv_le
        hdiff hfd hy hx
  have hxy : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2),
      ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2), ‖x - y‖ ≤ 1 := by
    intro x hx y hy
    rw [mem_ball_zero_iff] at hx hy
    linarith [norm_sub_le x y]
  have h0 : (0 : EuclideanSpace ℝ (Fin 3)) ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2) :=
    mem_ball_self (by norm_num)
  have hfun : HasFiniteHolderNormOn α v (ball 0 (1 / 2)) := by
    refine HasFiniteHolderNormOn.of_bounds (A := ‖v 0‖ + C₁) (B := C₁) (by positivity)
      hC₁.le ?_ ?_
    · intro x hx
      have h1 := hlip x hx 0 h0
      have h2 := mul_le_of_le_one_right hC₁.le (hxy x hx 0 h0)
      have h3 := norm_sub_norm_le (v x) (v 0)
      linarith
    · intro x hx y hy
      apply div_le_of_le_mul₀ (by positivity) hC₁.le
      exact (hlip x hx y hy).trans (mul_le_mul_of_nonneg_left
        (Real.self_le_rpow_of_le_one (norm_nonneg _) (hxy x hx y hy) hα1.le) hC₁.le)
  have hder : HasFiniteHolderNormOn α (fderiv ℝ v) (ball 0 (1 / 2)) := by
    refine HasFiniteHolderNormOn.of_bounds hC₁.le hC₁.le hfd ?_
    intro x hx y hy
    apply div_le_of_le_mul₀ (by positivity) hC₁.le
    have h := hgh x hx y hy
    rwa [gradient, gradient, ← map_sub, LinearIsometryEquiv.norm_map, dist_eq_norm] at h
  have hvC : HasC1HolderOn α v (ball 0 (1 / 2)) := ⟨hv1, hfun, hder⟩
  have hell' : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2), ∀ ξ,
      lam * ‖ξ‖ ^ 2 ≤ inner ℝ ξ (A x ξ) := by
    intro x hx ξ
    rw [real_inner_comm]
    exact hell x (hsub hx) ξ
  -- the weak equation for `v` with smooth tests
  have hweak : ∀ ψ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ ball 0 (1 / 2) →
      (∫ x, inner ℝ (A x (gradient v x)) (gradient ψ x)) =
        ∫ x, inner ℝ (G x) (gradient ψ x) := by
    intro ψ hψ hcψ hsψ
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
    have hw' : IsWeakDivergenceEquationOn A (gradient v) G (ball 0 (1 / 2)) :=
      (hw.mono hsub).congr_gradient_ae measurableSet_ball hFv
    have he := hw' ψ hψ1 hcψ hsψ
    have hgψ : Continuous (gradient ψ) :=
      (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.continuous.comp
        (hψ1.continuous_fderiv one_ne_zero)
    have hz : ∀ x, x ∉ tsupport ψ → gradient ψ x = 0 := by
      intro x hx
      rw [gradient, fderiv_of_notMem_tsupport ℝ hx, map_zero]
    have hgv : ContinuousOn (gradient v) (ball 0 (1 / 2)) :=
      (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.continuous.comp_continuousOn
        (hv1.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl)
    have hi1 : Integrable (fun x => inner ℝ (A x (gradient v x)) (gradient ψ x)) := by
      rw [← integrableOn_iff_integrable_of_support_subset (s := tsupport ψ)]
      · exact ContinuousOn.integrableOn_compact hcψ
          (((hA'.contDiff.continuousOn.clm_apply hgv).inner hgψ.continuousOn).mono hsψ)
      · intro x hx
        rw [Function.mem_support] at hx
        by_contra h
        exact hx (by simp [hz x h])
    have hi2 : Integrable (fun x => inner ℝ (G x) (gradient ψ x)) := by
      rw [← integrableOn_iff_integrable_of_support_subset (s := tsupport ψ)]
      · exact ContinuousOn.integrableOn_compact hcψ
          ((hG'.contDiff.continuousOn.inner hgψ.continuousOn).mono hsψ)
      · intro x hx
        rw [Function.mem_support] at hx
        by_contra h
        exact hx (by simp [hz x h])
    simp only [inner_sub_left] at he
    rwa [integral_sub hi1 hi2, sub_eq_zero] at he
  obtain ⟨hC2, hbound⟩ := hc2 0 (1 / 2) (by norm_num) (by norm_num) A G v hA' hG' hvC
    (hAn'.trans hAn) (fun x hx => hcap x (hsub hx)) hell' hweak
  have h4 : (1 / 2 : ℝ) / 2 = 1 / 4 := by norm_num
  have h8 : ((1 / 2 : ℝ)⁻¹) ^ 3 = 8 := by norm_num
  rw [h4] at hC2 hbound
  rw [h8] at hbound
  refine ⟨v, huv, hC2, ?_⟩
  set L := lpNorm v ∞ (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ)))
  have hL : 0 ≤ L := lpNorm_nonneg
  have hGM : nondivC1HolderNorm α G (ball 0 (1 / 2)) ≤ M := hGn'.trans hGn
  have key : L + 3 * M ≤ (3 * M + 1) * (L + 1) := by nlinarith [mul_nonneg hM hL]
  calc schauderC2HolderNorm α v (ball 0 (1 / 4))
      ≤ C₂ * 8 * (L + 3 * nondivC1HolderNorm α G (ball 0 (1 / 2))) := hbound
    _ ≤ C₂ * 8 * (L + 3 * M) := by gcongr
    _ ≤ C₂ * 8 * ((3 * M + 1) * (L + 1)) := by gcongr
    _ = 8 * C₂ * (3 * M + 1) * (L + 1) := by ring

end LiquidDrop
