import NoCompromise.Elliptic.BoundaryNondivC2
import NoCompromise.Elliptic.NondivSchauder

/-!
# Interior C²,α for the divergence-form equation (C¹,α solution)

`div(A∇w) = div G` weakly is the nondivergence equation with drift `div A` and
right side `div G`. For a solution already known to be C¹,α on the unit ball,
the interior Schauder estimate `nondiv_schauder` for the nondivergence problem
applies. This is the interior (covering) piece of `thm:boundary-C2a`.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- Interior C²,α estimate for a C¹,α weak solution of `div(A∇w) = div G` on the
unit ball of `ℝ³`, with a constant chosen from `α, lam, cap, M` before the data. -/
theorem interior_c2a_holder_div {α lam cap M : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hlamcap : lam ≤ cap) (hM : 0 ≤ M) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3))
      (G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (w : EuclideanSpace ℝ (Fin 3) → ℝ),
      HasC1HolderOn α A (ball 0 1) → HasC1HolderOn α G (ball 0 1) →
      HasC1HolderOn α w (ball 0 1) →
      nondivC1HolderNorm α A (ball 0 1) ≤ M →
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, ‖A x‖ ≤ cap) →
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      (∀ ψ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ ball 0 1 →
        (∫ x, inner ℝ (A x (gradient w x)) (gradient ψ x)) =
          ∫ x, inner ℝ (G x) (gradient ψ x)) →
      HasC2HolderOn α w (ball 0 (1 / 2)) ∧
        schauderC2HolderNorm α w (ball 0 (1 / 2)) ≤
          C * (lpNorm w ∞ (volume.restrict (ball 0 1)) +
            3 * nondivC1HolderNorm α G (ball 0 1)) := by
  obtain ⟨C, hC, hreg⟩ := nondiv_schauder (n := 3) (by norm_num) (by norm_num) hα hα1 hlam
    hlamcap (by positivity : (0 : ℝ) ≤ 3 * M)
  refine ⟨C, hC, ?_⟩
  intro A G w hA hG hw hAn hcap hell he
  have hU : IsOpen (ball (0 : EuclideanSpace ℝ (Fin 3)) 1) := isOpen_ball
  obtain ⟨hdA, hdAb⟩ := nondivCoefficientDivergence_holder hA
  obtain ⟨hdiv, hdivb⟩ := nondiv_holder_comp_clm hG.derivative_holder boundaryNeumannC2Trace
  have heqd : (fun x => boundaryNeumannC2Trace (fderiv ℝ G x)) = divergenceN G := by
    funext x
    exact boundaryNeumannC2Trace_apply _
  rw [heqd] at hdiv hdivb
  have hdivN : holderNorm α (divergenceN G) (ball 0 1) ≤
      3 * nondivC1HolderNorm α G (ball 0 1) :=
    hdivb.trans (mul_le_mul boundaryNeumannC2Trace_norm hG.derivative_norm_le
      hG.derivative_holder.norm_nonneg (by norm_num))
  have hAU : ContDiffOn ℝ 1 A (ball 0 1) := hA.contDiff
  have hGU : ContDiffOn ℝ 1 G (ball 0 1) := hG.contDiff
  have hwU : ContDiffOn ℝ 1 w (ball 0 1) := hw.contDiff
  have hbU : ContinuousOn (nondivCoefficientDivergence A) (ball 0 1) :=
    hdA.nondiv_continuousOn hα
  have hfU : ContinuousOn (divergenceN G) (ball 0 1) :=
    hdiv.nondiv_continuousOn hα
  have hweak : IsWeakNondivergenceEquationOn A (nondivCoefficientDivergence A) w
      (divergenceN G) (ball 0 1) := by
    apply (isWeakNondivergenceEquationOn_iff_divergence hU hAU hbU hwU hfU).mpr
    intro φ hφ hcφ hsφ
    have hsrc : nondivDivergenceSource A (nondivCoefficientDivergence A) w (divergenceN G) =
        divergenceN G := by
      funext x
      simp only [nondivDivergenceSource, sub_self, inner_zero_left, add_zero]
    rw [hsrc, he φ hφ hcφ hsφ]
    exact boundary_neumann_c2_integral_divergence hU hGU (hφ.of_le (by simp)) hcφ hsφ
  have hbb : holderNorm α (nondivCoefficientDivergence A) (ball 0 1) ≤ 3 * M :=
    hdAb.trans (by
      have : ((3 : ℕ) : ℝ) = 3 := by norm_num
      rw [this]
      exact mul_le_mul_of_nonneg_left hAn (by norm_num))
  obtain ⟨h2, hbound⟩ := hreg A _ w _ hA hdA hw hdiv (hAn.trans (by linarith)) hbb hcap hell
    hweak
  refine ⟨h2, hbound.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hdivN) hC.le

/-- A continuous essentially bounded function on `ball c r` has pullback to the unit
ball with no larger essential uniform bound. -/
lemma interiorC2aDiv_lpNorm_top_comp_ballScaling {n : ℕ} (c : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) {z : EuclideanSpace ℝ (Fin n) → ℝ}
    (hzc : ContinuousOn z (ball c r)) (hzm : MemLp z ∞ (volume.restrict (ball c r))) :
    lpNorm (z ∘ frozenBallScaling c hr) ∞ (volume.restrict (ball 0 1)) ≤
      lpNorm z ∞ (volume.restrict (ball c r)) := by
  have hpt := holderInterpolation_norm_le_lpNorm_top isOpen_ball hzc hzm
  have hm := quasilinear_ballScaling_maps_unit c hr
  have hmeas : AEStronglyMeasurable (z ∘ frozenBallScaling c hr)
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
    (hzc.comp (frozenBallScaling c hr).continuous.continuousOn hm).aestronglyMeasurable
      measurableSet_ball
  have hb : ∀ᵐ x ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) 1)),
      ‖(z ∘ frozenBallScaling c hr) x‖ ≤ lpNorm z ∞ (volume.restrict (ball c r)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hpt _ (hm hx)
  rw [← toReal_eLpNorm, eLpNorm_exponent_top hmeas]
  exact ENNReal.toReal_le_of_le_ofReal lpNorm_nonneg (eLpNormEssSup_le_of_ae_bound hb)

/-- Interior C²,α estimate for a C¹,α weak solution of `div(A∇w) = div G` on every
ball `ball c ρ` with `0 < ρ ≤ 1`, with the explicit radius factor `ρ⁻³` and a
constant chosen from `α, lam, cap, M` before the center, radius and data. -/
theorem interior_c2a_holder_div_ball {α lam cap M : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hlamcap : lam ≤ cap) (hM : 0 ≤ M) :
    ∃ C > 0, ∀ (c : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
      ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3))
      (G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (w : EuclideanSpace ℝ (Fin 3) → ℝ),
      HasC1HolderOn α A (ball c ρ) → HasC1HolderOn α G (ball c ρ) →
      HasC1HolderOn α w (ball c ρ) →
      nondivC1HolderNorm α A (ball c ρ) ≤ M →
      (∀ x ∈ ball c ρ, ‖A x‖ ≤ cap) →
      (∀ x ∈ ball c ρ, ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      (∀ ψ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ ball c ρ →
        (∫ x, inner ℝ (A x (gradient w x)) (gradient ψ x)) =
          ∫ x, inner ℝ (G x) (gradient ψ x)) →
      HasC2HolderOn α w (ball c (ρ / 2)) ∧
        schauderC2HolderNorm α w (ball c (ρ / 2)) ≤
          C * (ρ⁻¹) ^ 3 * (lpNorm w ∞ (volume.restrict (ball c ρ)) +
            3 * nondivC1HolderNorm α G (ball c ρ)) := by
  obtain ⟨C, hC, hreg⟩ := nondiv_schauder (n := 3) (by norm_num) (by norm_num) hα hα1 hlam
    hlamcap (by positivity : (0 : ℝ) ≤ 3 * M)
  refine ⟨C, hC, ?_⟩
  intro c r hr hr1 A G w hA hG hw hAn hcap hell he
  have hU : IsOpen (ball c r) := isOpen_ball
  obtain ⟨hdA, hdAb⟩ := nondivCoefficientDivergence_holder hA
  obtain ⟨hdiv, hdivb⟩ := nondiv_holder_comp_clm hG.derivative_holder boundaryNeumannC2Trace
  have heqd : (fun x => boundaryNeumannC2Trace (fderiv ℝ G x)) = divergenceN G := by
    funext x
    exact boundaryNeumannC2Trace_apply _
  rw [heqd] at hdiv hdivb
  have hdivN : holderNorm α (divergenceN G) (ball c r) ≤
      3 * nondivC1HolderNorm α G (ball c r) :=
    hdivb.trans (mul_le_mul boundaryNeumannC2Trace_norm hG.derivative_norm_le
      hG.derivative_holder.norm_nonneg (by norm_num))
  have hAU : ContDiffOn ℝ 1 A (ball c r) := hA.contDiff
  have hGU : ContDiffOn ℝ 1 G (ball c r) := hG.contDiff
  have hwU : ContDiffOn ℝ 1 w (ball c r) := hw.contDiff
  have hbU : ContinuousOn (nondivCoefficientDivergence A) (ball c r) :=
    hdA.nondiv_continuousOn hα
  have hfU : ContinuousOn (divergenceN G) (ball c r) :=
    hdiv.nondiv_continuousOn hα
  have hweak : IsWeakNondivergenceEquationOn A (nondivCoefficientDivergence A) w
      (divergenceN G) (ball c r) := by
    apply (isWeakNondivergenceEquationOn_iff_divergence hU hAU hbU hwU hfU).mpr
    intro φ hφ hcφ hsφ
    have hsrc : nondivDivergenceSource A (nondivCoefficientDivergence A) w (divergenceN G) =
        divergenceN G := by
      funext x
      simp only [nondivDivergenceSource, sub_self, inner_zero_left, add_zero]
    rw [hsrc, he φ hφ hcφ hsφ]
    exact boundary_neumann_c2_integral_divergence hU hGU (hφ.of_le (by simp)) hcφ hsφ
  have hbb : holderNorm α (nondivCoefficientDivergence A) (ball c r) ≤ 3 * M :=
    hdAb.trans (by
      have : ((3 : ℕ) : ℝ) = 3 := by norm_num
      rw [this]
      exact mul_le_mul_of_nonneg_left hAn (by norm_num))
  -- scale `ball c r` to the unit ball
  let e := frozenBallScaling c hr
  have hm := quasilinear_ballScaling_maps_unit c hr
  obtain ⟨hAc, hAcb⟩ := nondiv_c1Holder_comp_ballScaling hα.le c hr hr1 hA
  obtain ⟨hwc, _⟩ := nondiv_c1Holder_comp_ballScaling hα.le c hr hr1 hw
  obtain ⟨hbc, hbcb⟩ := nondiv_holder_comp_ballScaling hα.le c hr hr1 hdA
  obtain ⟨hfc, hfcb⟩ := nondiv_holder_comp_ballScaling hα.le c hr hr1 hdiv
  obtain ⟨hbs, hbsb⟩ := nondiv_holder_const_smul hbc r
  obtain ⟨hfs, hfsb⟩ := nondiv_holder_const_smul hfc (r ^ 2)
  have hbBound : holderNorm α (fun x => r • nondivCoefficientDivergence A (e x)) (ball 0 1) ≤
      holderNorm α (nondivCoefficientDivergence A) (ball c r) := by
    apply hbsb.trans
    rw [Real.norm_of_nonneg hr.le]
    exact (mul_le_mul_of_nonneg_left hbcb hr.le).trans
      ((mul_le_mul_of_nonneg_right hr1 hdA.norm_nonneg).trans_eq (one_mul _))
  have hfBound : holderNorm α (fun x => r ^ 2 * divergenceN G (e x)) (ball 0 1) ≤
      holderNorm α (divergenceN G) (ball c r) := by
    apply hfsb.trans
    rw [Real.norm_of_nonneg (sq_nonneg r)]
    apply (mul_le_mul_of_nonneg_left hfcb (sq_nonneg r)).trans
    have hr2 : r ^ 2 ≤ 1 := by nlinarith
    exact (mul_le_mul_of_nonneg_right hr2 hdiv.norm_nonneg).trans_eq (one_mul _)
  have hEq := hweak.comp_nondivBallScaling c hr hAU hbU hwU hfU
  obtain ⟨hscaled, hbscaled⟩ := hreg (A ∘ e) (fun x => r • nondivCoefficientDivergence A (e x))
    (w ∘ e) (fun x => r ^ 2 * divergenceN G (e x)) hAc hbs hwc hfs
    ((hAcb.trans hAn).trans (by linarith)) (hbBound.trans hbb)
    (fun x hx => hcap _ (hm hx)) (fun x hx v => hell _ (hm hx) v) hEq
  obtain ⟨hback, hbback⟩ := nondiv_c2Holder_comp_ballScaling_symm hα.le hα1.le c hr hr1 hscaled
  have heq : (w ∘ e) ∘ e.symm = w := by
    funext x
    simp only [Function.comp_apply, e.apply_symm_apply]
  rw [heq] at hback hbback
  refine ⟨hback, hbback.trans ?_⟩
  have hlp := interiorC2aDiv_lpNorm_top_comp_ballScaling c hr hw.contDiff.continuousOn
    (hw.memLp_top hU)
  have hbtotal := hbscaled.trans
    (mul_le_mul_of_nonneg_left (add_le_add hlp (hfBound.trans hdivN)) hC.le)
  convert mul_le_mul_of_nonneg_left hbtotal (by positivity : 0 ≤ (r⁻¹) ^ 3) using 1
  ring

end LiquidDrop
