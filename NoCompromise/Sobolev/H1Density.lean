import NoCompromise.Sobolev.H1Extension
import NoCompromise.Sobolev.H1Approximation

/-!
# Smooth density in H¹ on bounded Lipschitz domains

Actual extension and mollification produce smooth representatives converging in
the genuine H¹ Hilbert norm. Continuous weak-gradient pairs therefore map densely
into H¹, providing the domain for extension of the boundary restriction operator.
-/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal Topology Gradient Convolution
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma lpNorm_restrict_le_of_memLp {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    {f : EuclideanSpace ℝ (Fin n) → F} (hf : MemLp f 2 volume)
    (U : Set (EuclideanSpace ℝ (Fin n))) :
    lpNorm f 2 (volume.restrict U) ≤ lpNorm f 2 volume := by
  rw [← toReal_eLpNorm,
    ← toReal_eLpNorm]
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mono_measure f Measure.restrict_le_self)

namespace H1Space

lemma coeFn_sub {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} (u v : H1Space U) :
    ⇑(u - v) =ᵐ[volume.restrict U] fun x => u x - v x := Lp.coeFn_sub u.toLp v.toLp

lemma norm_ofFunction_sub_le {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {G H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G U) (hg : HasH1GradientOn g H U) :
    ‖ofFunction f G hf - ofFunction g H hg‖ ≤
      lpNorm (f - g) 2 (volume.restrict U) + lpNorm (G - H) 2 (volume.restrict U) := by
  have heq : ofFunction f G hf - ofFunction g H hg =
      ofFunction (f - g) (G - H) (hf.sub hg) := by
    apply ext_ae hU
    filter_upwards [coeFn_sub (ofFunction f G hf) (ofFunction g H hg),
      coeFn_ofFunction f G hf, coeFn_ofFunction g H hg,
      coeFn_ofFunction (f - g) (G - H) (hf.sub hg)] with x h1 h2 h3 h4
    rw [h2, h3] at h1
    exact h1.trans h4.symm
  rw [heq]
  exact norm_ofFunction_le _ _ _

/-- Global strong convergence of both components gives H¹ convergence on every open set. -/
theorem tendsto_ofFunction_restrict {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G univ)
    {f' : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    {G' : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf' : ∀ j, HasH1GradientOn (f' j) (G' j) univ)
    (hcf : Tendsto (fun j => lpNorm (f' j - f) 2 volume) atTop (𝓝 0))
    (hcG : Tendsto (fun j => lpNorm (G' j - G) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun j => ofFunction (f' j) (G' j) ((hf' j).mono (subset_univ U))) atTop
      (𝓝 (ofFunction f G (hf.mono (subset_univ U)))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hmf : MemLp f 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_function
  have hmG : MemLp G 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_gradient
  have hbound (j : ℕ) :
      ‖ofFunction (f' j) (G' j) ((hf' j).mono (subset_univ U)) -
        ofFunction f G (hf.mono (subset_univ U))‖ ≤
      lpNorm (f' j - f) 2 volume + lpNorm (G' j - G) 2 volume := by
    apply (norm_ofFunction_sub_le hU ((hf' j).mono (subset_univ U))
      (hf.mono (subset_univ U))).trans
    exact add_le_add
      (lpNorm_restrict_le_of_memLp ((by
        simpa only [Measure.restrict_univ] using (hf' j).memLp_function :
          MemLp (f' j) 2 volume).sub hmf) U)
      (lpNorm_restrict_le_of_memLp ((by
        simpa only [Measure.restrict_univ] using (hf' j).memLp_gradient :
          MemLp (G' j) 2 volume).sub hmG) U)
  exact squeeze_zero (fun _ => norm_nonneg _) hbound (by
    simpa only [zero_add] using hcf.add hcG)

/-- Genuine smooth H¹ approximation on every bounded open Lipschitz domain. -/
theorem exists_smooth_approx_on_domain {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) (u : H1Space D) :
    ∃ v : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
    ∃ hv : ∀ j, HasH1GradientOn (v j) (gradient (v j)) D,
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (v j)) ∧
      Tendsto (fun j => ofFunction (v j) (gradient (v j)) (hv j)) atTop (𝓝 u) := by
  obtain ⟨T, _, _, _, _, hT⟩ := exists_h1_extension_linearMap hD hbD hL
  obtain ⟨H, hH, heq, _, _⟩ := hT u u.gradientLp u.hasH1GradientOn
  let φ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨(1 / ((j : ℝ) + 1)) / 2, 1 / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφ : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let v (j : ℕ) := (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] (T u)
  have hv (j) : HasH1GradientOn (v j) (gradient (v j)) univ := by
    have hj := hH.bump_convolution (φ j)
    change HasH1GradientOn
      ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] (T u))
      (gradient ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] (T u))) univ
    rw [funext hj.2.1]
    exact hj.2.2.1
  have hmf : MemLp (T u) 2 volume := by
    simpa only [Measure.restrict_univ] using hH.memLp_function
  have hmG : MemLp H 2 volume := by
    simpa only [Measure.restrict_univ] using hH.memLp_gradient
  have hconv := tendsto_ofFunction_restrict hD hH hv
    (tendsto_lpNorm_bump_convolution_sub hmf hφ) (by
      have hgrad (j) := funext (hH.bump_convolution (φ j)).2.1
      simp only [v, hgrad]
      exact tendsto_lpNorm_bump_convolution_sub hmG hφ)
  have hclass : ofFunction (T u) H (hH.mono (subset_univ D)) = u :=
    ext_ae hD ((coeFn_ofFunction _ _ _).trans (ae_restrict_of_forall_mem hD.measurableSet heq))
  refine ⟨v, fun j => (hv j).mono (subset_univ D),
    fun j => (hH.bump_convolution (φ j)).1, ?_⟩
  simpa only [hclass] using hconv

end H1Space

/-- Actual continuous scalar functions paired with their actual H¹ weak gradients. -/
def continuousH1Data {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n))) :
    Submodule ℝ ((EuclideanSpace ℝ (Fin n) → ℝ) ×
      (EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))) where
  carrier := {p | Continuous p.1 ∧ HasH1GradientOn p.1 p.2 D}
  zero_mem' := ⟨continuous_const, HasH1GradientOn.zero D⟩
  add_mem' hp hq := ⟨hp.1.add hq.1, hp.2.add hq.2⟩
  smul_mem' c _ hp := ⟨continuous_const.mul hp.1, hp.2.const_mul c⟩

/-- Continuous weak-gradient pairs map linearly to their H¹ classes. -/
def continuousH1Data_toH1Space {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (hD : IsOpen D) : continuousH1Data D →ₗ[ℝ] H1Space D where
  toFun p := H1Space.ofFunction p.val.1 p.val.2 p.property.2
  map_add' p q := by
    apply H1Space.ext_ae hD
    filter_upwards [H1Space.coeFn_ofFunction (p + q).val.1 (p + q).val.2 (p + q).property.2,
      H1Space.coeFn_add (H1Space.ofFunction p.val.1 p.val.2 p.property.2)
        (H1Space.ofFunction q.val.1 q.val.2 q.property.2),
      H1Space.coeFn_ofFunction p.val.1 p.val.2 p.property.2,
      H1Space.coeFn_ofFunction q.val.1 q.val.2 q.property.2] with x h1 h2 h3 h4
    rw [h3, h4] at h2
    exact h1.trans ((show (p + q).val.1 x = p.val.1 x + q.val.1 x from rfl).trans h2.symm)
  map_smul' c p := by
    apply H1Space.ext_ae hD
    filter_upwards [H1Space.coeFn_ofFunction (c • p).val.1 (c • p).val.2 (c • p).property.2,
      H1Space.coeFn_smul c (H1Space.ofFunction p.val.1 p.val.2 p.property.2),
      H1Space.coeFn_ofFunction p.val.1 p.val.2 p.property.2] with x h1 h2 h3
    rw [h3] at h2
    exact h1.trans ((show (c • p).val.1 x = c * p.val.1 x from rfl).trans h2.symm)

/-- Smooth approximation proves density of the continuous representatives. -/
theorem denseRange_continuousH1Data_toH1Space {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    DenseRange (continuousH1Data_toH1Space hD) := by
  intro u
  obtain ⟨v, hv, hc, hconv⟩ := H1Space.exists_smooth_approx_on_domain hD hbD hL u
  apply mem_closure_of_tendsto hconv
  exact Eventually.of_forall fun j =>
    ⟨⟨(v j, gradient (v j)), (hc j).continuous, hv j⟩, rfl⟩

lemma continuousH1Data_sum_lpNorm_le {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (p : continuousH1Data D) :
    lpNorm p.val.1 2 (volume.restrict D) + lpNorm p.val.2 2 (volume.restrict D) ≤
      2 * ‖continuousH1Data_toH1Space hD p‖ := by
  have hsq := H1Space.norm_ofFunction_sq p.val.1 p.val.2 p.property.2
  have hf : lpNorm p.val.1 2 (volume.restrict D) ≤
      ‖H1Space.ofFunction p.val.1 p.val.2 p.property.2‖ := by
    apply le_of_sq_le_sq _ (norm_nonneg _)
    nlinarith [sq_nonneg (lpNorm p.val.2 2 (volume.restrict D))]
  have hG : lpNorm p.val.2 2 (volume.restrict D) ≤
      ‖H1Space.ofFunction p.val.1 p.val.2 p.property.2‖ := by
    apply le_of_sq_le_sq _ (norm_nonneg _)
    nlinarith [sq_nonneg (lpNorm p.val.1 2 (volume.restrict D))]
  change _ ≤ 2 * ‖H1Space.ofFunction p.val.1 p.val.2 p.property.2‖
  linarith

end LiquidDrop
