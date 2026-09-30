module

public import NoCompromise.Elliptic.NewtonianSchauderCandidate

@[expose] public section

/-!
# Convergence of regularized Hessian kernels

The inverse-cubic size estimate becomes integrable after multiplication by the
Hölder weight. This gives a weighted L¹ error tending to zero on every bounded
ball, uniformly useful for translates of a compactly supported Hölder source.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

lemma tendsto_schauderRegularizedHessianEntry {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (i j : Fin 3) {x : E₃} (hx : x ≠ 0) :
    Tendsto (fun k => schauderRegularizedHessianEntry (ε k) i j x) atTop
      (𝓝 (schauderNewtonHessianEntry i j x)) := by
  have hc : Continuous (fun L : E₃ →L[ℝ] E₃ →L[ℝ] ℝ =>
      L (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) :=
    (continuous_id.clm_apply continuous_const).clm_apply continuous_const
  exact (hc.tendsto (schauderNewtonHessian x)).comp
    (tendsto_schauderRegularizedHessian hε hx)

lemma schauderRegularizedHessianEntry_weighted_error_le {α ε : ℝ} (hε : 0 < ε)
    (i j : Fin 3) {x : E₃} (hx : x ≠ 0) :
    ‖schauderRegularizedHessianEntry ε i j x - schauderNewtonHessianEntry i j x‖ * ‖x‖ ^ α ≤
      (2 * Real.pi⁻¹) * ‖x‖ ^ (α - 3) := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  calc
    _ ≤ (Real.pi⁻¹ * (‖x‖ ^ 3)⁻¹ + Real.pi⁻¹ * (‖x‖ ^ 3)⁻¹) * ‖x‖ ^ α := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (norm_sub_le _ _).trans (add_le_add
        (norm_schauderRegularizedHessianEntry_le hε i j hx)
        (norm_schauderNewtonHessianEntry_le i j x))
    _ = _ := by
      rw [Real.rpow_sub hn α 3, Real.rpow_ofNat]
      ring

lemma integrableOn_schauderRegularizedHessianEntry_weighted_error {α ε : ℝ}
    (hα : 0 < α) (hε : 0 < ε) (R : ℝ) (i j : Fin 3) :
    IntegrableOn (fun x : E₃ =>
      ‖schauderRegularizedHessianEntry ε i j x - schauderNewtonHessianEntry i j x‖ * ‖x‖ ^ α)
      (ball 0 R) := by
  have hm : Measurable (fun x : E₃ =>
      ‖schauderRegularizedHessianEntry ε i j x - schauderNewtonHessianEntry i j x‖ * ‖x‖ ^ α) :=
    (((continuous_schauderRegularizedHessianEntry hε i j).measurable.sub
      (measurable_schauderNewtonHessianEntry i j)).norm).mul
      (((Real.continuous_rpow_const hα.le).comp continuous_norm).measurable)
  apply ((integrableOn_schauder_near_power (R := R) hα).const_mul (2 * Real.pi⁻¹)).mono'
    hm.aestronglyMeasurable.restrict
  have hne : ∀ᵐ x : E₃ ∂volume.restrict (ball 0 R), x ≠ 0 :=
    ae_restrict_of_ae (by simp [ae_iff])
  filter_upwards [hne] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact schauderRegularizedHessianEntry_weighted_error_le hε i j hx

lemma tendsto_integral_schauderRegularizedHessianEntry_weighted_error {α : ℝ}
    (hα : 0 < α) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hεpos : ∀ k, 0 < ε k) (R : ℝ) (i j : Fin 3) :
    Tendsto (fun k => ∫ x : E₃ in ball 0 R,
      ‖schauderRegularizedHessianEntry (ε k) i j x - schauderNewtonHessianEntry i j x‖ * ‖x‖ ^ α)
      atTop (𝓝 0) := by
  have hne : ∀ᵐ x : E₃ ∂volume.restrict (ball 0 R), x ≠ 0 :=
    ae_restrict_of_ae (by simp [ae_iff])
  have h := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (ball (0 : E₃) R))
    (fun x : E₃ => (2 * Real.pi⁻¹) * ‖x‖ ^ (α - 3))
    (F := fun k x =>
      ‖schauderRegularizedHessianEntry (ε k) i j x - schauderNewtonHessianEntry i j x‖ * ‖x‖ ^ α)
    (f := fun _ => (0 : ℝ))
  apply (by simpa only [integral_zero] using h)
  · exact fun k => (integrableOn_schauderRegularizedHessianEntry_weighted_error
      hα (hεpos k) R i j).aestronglyMeasurable
  · exact (integrableOn_schauder_near_power (R := R) hα).const_mul (2 * Real.pi⁻¹)
  · intro k
    filter_upwards [hne] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact schauderRegularizedHessianEntry_weighted_error_le (hεpos k) i j hx
  · filter_upwards [hne] with x hx
    simpa only [sub_self, norm_zero, zero_mul] using
      (((tendsto_schauderRegularizedHessianEntry hε i j hx).sub
        (tendsto_const_nhds (x := schauderNewtonHessianEntry i j x))).norm).mul_const (‖x‖ ^ α)

/-- Subtraction against the fixed bump has a uniform Hölder-weight bound. -/
lemma schauder_compensated_source_bound {α A B : ℝ} (hα : 0 ≤ α) (hB : 0 ≤ B)
    {f : E₃ → ℝ} (hf : ∀ x, ‖f x‖ ≤ B)
    (hinc : ∀ x y, ‖f x - f y‖ ≤ A * ‖x - y‖ ^ α) (x z : E₃) :
    ‖f (x - z) - f x * schauderRadialBump z‖ ≤ (A + B) * ‖z‖ ^ α := by
  have hin := hinc (x - z) x
  rw [show x - z - x = -z by abel, norm_neg] at hin
  have hb : ‖f x * (1 - schauderRadialBump z)‖ ≤ B * ‖z‖ ^ α := by
    by_cases hz : ‖z‖ ≤ 1
    · rw [schauderRadialBump_one hz, sub_self, mul_zero, norm_zero]
      positivity
    · have hm := schauderRadialBump_mem_Icc z
      have hχ : ‖1 - schauderRadialBump z‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hm.2)]
        linarith [hm.1]
      calc
        _ ≤ B * 1 := by rw [norm_mul]; exact mul_le_mul (hf x) hχ (norm_nonneg _) hB
        _ ≤ B * ‖z‖ ^ α := mul_le_mul_of_nonneg_left
          (Real.one_le_rpow (le_of_lt (lt_of_not_ge hz)) hα) hB
  calc
    _ = ‖(f (x - z) - f x) + f x * (1 - schauderRadialBump z)‖ := by congr 1; ring
    _ ≤ ‖f (x - z) - f x‖ + ‖f x * (1 - schauderRadialBump z)‖ := norm_add_le _ _
    _ ≤ A * ‖z‖ ^ α + B * ‖z‖ ^ α := add_le_add hin hb
    _ = _ := by ring

/-- On a bounded set of centers, all compensated sources have support in one ball. -/
lemma schauder_compensated_source_uniform_support {f : E₃ → ℝ}
    (hf : HasCompactSupport f) (S : ℝ) :
    ∃ R > 0, ∀ x ∈ ball (0 : E₃) S,
      Function.support (fun z => f (x - z) - f x * schauderRadialBump z) ⊆ ball 0 R := by
  obtain ⟨M, hM⟩ := hf.isBounded.exists_norm_le
  let R := max S 0 + max M 0 + 3
  refine ⟨R, by dsimp [R]; positivity, fun x hx z hz => ?_⟩
  by_contra hzR
  have hzR' : R ≤ ‖z‖ := not_lt.mp (by simpa using hzR)
  have hx' : ‖x‖ < S := by simpa using hx
  have hbump : schauderRadialBump z = 0 := by
    apply Function.notMem_support.mp
    rw [schauderRadialBump_support, mem_ball, dist_zero_right, not_lt]
    dsimp [R] at hzR'
    linarith [le_max_right S 0, le_max_right M 0]
  have hzero : f (x - z) = 0 := by
    by_contra hn
    have hm := hM (x - z) (subset_tsupport f (Function.mem_support.mpr hn))
    have ht : ‖z‖ ≤ ‖x‖ + ‖x - z‖ := by
      calc
        ‖z‖ = ‖x - (x - z)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖x‖ + ‖x - z‖ := norm_sub_le _ _
    dsimp [R] at hzR'
    linarith [le_max_left S 0, le_max_left M 0]
  exact hz (by simp only [hzero, hbump, mul_zero, sub_zero])

lemma norm_schauderRegularizedHessianEntry_le_uniform {ε : ℝ} (hε : 0 < ε)
    (i j : Fin 3) (x : E₃) :
    ‖schauderRegularizedHessianEntry ε i j x‖ ≤ Real.pi⁻¹ * (ε ^ 3)⁻¹ := by
  have h := (((schauderRegularizedHessian ε x) (EuclideanSpace.single i 1)).le_opNorm
    (EuclideanSpace.single j 1)).trans
    (mul_le_mul_of_nonneg_right ((schauderRegularizedHessian ε x).le_opNorm
      (EuclideanSpace.single i 1)) (norm_nonneg _))
  simp only [PiLp.norm_single, norm_one, mul_one] at h
  apply (h.trans (norm_schauderRegularizedHessian_le hε x)).trans
  exact mul_le_mul_of_nonneg_left
    (inv_anti₀ (by positivity) (pow_le_pow_left₀ hε.le
      (regularizedNewton_sqrt_bounds hε x).2.2 3)) (by positivity)

lemma integrable_schauderRegularizedHessianEntry_mul {ε : ℝ} (hε : 0 < ε)
    (i j : Fin 3) {g : E₃ → ℝ} (hg : Integrable g) :
    Integrable (fun z => schauderRegularizedHessianEntry ε i j z * g z) := by
  apply (hg.norm.const_mul (Real.pi⁻¹ * (ε ^ 3)⁻¹)).mono'
    ((continuous_schauderRegularizedHessianEntry hε i j).aestronglyMeasurable.mul
      hg.aestronglyMeasurable)
  exact Eventually.of_forall fun z => by
    change ‖schauderRegularizedHessianEntry ε i j z * g z‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_schauderRegularizedHessianEntry_le_uniform hε i j z) (norm_nonneg _)

/-- Actual convolution of a regularized Hessian entry with the source. -/
def schauderRegularizedHessianConvolution (ε : ℝ) (i j : Fin 3) (f : E₃ → ℝ) (x : E₃) : ℝ :=
  ∫ z, schauderRegularizedHessianEntry ε i j z * f (x - z)

lemma schauder_regularized_compensated_error_bound {α ε A B R : ℝ}
    (hα : 0 < α) (hε : 0 < ε) (_hA : 0 ≤ A) (hB : 0 ≤ B)
    {f : E₃ → ℝ} (hf : Measurable f) (hfb : ∀ x, ‖f x‖ ≤ B)
    (hinc : ∀ x y, ‖f x - f y‖ ≤ A * ‖x - y‖ ^ α) (i j : Fin 3) (x : E₃)
    (hs : Function.support (fun z => f (x - z) - f x * schauderRadialBump z) ⊆ ball 0 R) :
    Integrable (fun z =>
      (schauderRegularizedHessianEntry ε i j z - schauderNewtonHessianEntry i j z) *
        (f (x - z) - f x * schauderRadialBump z)) ∧
    ‖∫ z, (schauderRegularizedHessianEntry ε i j z - schauderNewtonHessianEntry i j z) *
      (f (x - z) - f x * schauderRadialBump z)‖ ≤
        (A + B) * ∫ z : E₃ in ball 0 R,
          ‖schauderRegularizedHessianEntry ε i j z - schauderNewtonHessianEntry i j z‖ *
            ‖z‖ ^ α := by
  let g (z : E₃) := f (x - z) - f x * schauderRadialBump z
  let e (z : E₃) := schauderRegularizedHessianEntry ε i j z - schauderNewtonHessianEntry i j z
  have hg : Measurable g :=
    (hf.comp (continuous_const.sub continuous_id).measurable).sub
      (measurable_const.mul contDiff_schauderRadialBump.continuous.measurable)
  have he : Measurable e := (continuous_schauderRegularizedHessianEntry hε i j).measurable.sub
    (measurable_schauderNewtonHessianEntry i j)
  have hb := (integrableOn_schauderRegularizedHessianEntry_weighted_error hα hε R i j).const_mul
    (A + B)
  have hbound (z : E₃) : ‖e z * g z‖ ≤ (A + B) * (‖e z‖ * ‖z‖ ^ α) := by
    rw [norm_mul]
    calc
      _ ≤ ‖e z‖ * ((A + B) * ‖z‖ ^ α) := mul_le_mul_of_nonneg_left
        (schauder_compensated_source_bound hα.le hB hfb hinc x z) (norm_nonneg _)
      _ = _ := by ring
  have hi : IntegrableOn (fun z => e z * g z) (ball 0 R) :=
    hb.mono' (he.mul hg).aestronglyMeasurable.restrict (Eventually.of_forall hbound)
  have hzero (z : E₃) (hz : z ∉ ball (0 : E₃) R) : e z * g z = 0 := by
    have hg0 : g z = 0 := Function.notMem_support.mp (fun hz' => hz (hs hz'))
    rw [hg0, mul_zero]
  refine ⟨hi.integrable_of_forall_notMem_eq_zero hzero, ?_⟩
  change ‖∫ z, e z * g z‖ ≤ _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  calc
    _ ≤ ∫ z in ball (0 : E₃) R, ‖e z * g z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z in ball (0 : E₃) R, (A + B) * (‖e z‖ * ‖z‖ ^ α) :=
      integral_mono hi.norm hb hbound
    _ = _ := integral_const_mul _ _

lemma schauderRegularizedHessianConvolution_sub_candidate {α ε A : ℝ}
    (hα : 0 < α) (hε : 0 < ε) (hA : 0 ≤ A) {f : E₃ → ℝ}
    (hf : Measurable f) (hi : Integrable f)
    (hinc : ∀ x y, ‖f x - f y‖ ≤ A * ‖x - y‖ ^ α) (i j : Fin 3) (x : E₃) :
    schauderRegularizedHessianConvolution ε i j f x - schauderHessianCandidate i j f x =
      (∫ z, (schauderRegularizedHessianEntry ε i j z - schauderNewtonHessianEntry i j z) *
        (f (x - z) - f x * schauderRadialBump z)) +
      f x * ((∫ z, schauderRegularizedHessianEntry ε i j z * schauderRadialBump z) -
        (if i = j then (1 / 3 : ℝ) else 0)) := by
  let g (z : E₃) := f (x - z) - f x * schauderRadialBump z
  have hshift : Integrable (fun z => f (x - z)) := (integrable_comp_sub_left f x).mpr hi
  have hbump : Integrable schauderRadialBump :=
    contDiff_schauderRadialBump.continuous.integrable_of_hasCompactSupport
      schauderRadialBump_hasCompactSupport
  have hg : Integrable g := hshift.sub (hbump.const_mul (f x))
  have hr := integrable_schauderRegularizedHessianEntry_mul hε i j hg
  have hk := integrable_schauderHessian_compensated hα hA hf hi hinc i j x
  have hm := integrable_schauderRegularizedHessianEntry_mul hε i j hbump
  have hfun : (fun z => schauderRegularizedHessianEntry ε i j z * f (x - z)) =
      (fun z => schauderRegularizedHessianEntry ε i j z * g z +
        f x * (schauderRegularizedHessianEntry ε i j z * schauderRadialBump z)) := by
    funext z
    dsimp [g]
    ring
  have herror : (fun z =>
      (schauderRegularizedHessianEntry ε i j z - schauderNewtonHessianEntry i j z) * g z) =
      (fun z => schauderRegularizedHessianEntry ε i j z * g z -
        schauderNewtonHessianEntry i j z * g z) := by
    funext z
    ring
  change _ = (∫ z, (schauderRegularizedHessianEntry ε i j z -
    schauderNewtonHessianEntry i j z) * g z) + _
  rw [schauderRegularizedHessianConvolution, hfun, integral_add hr (hm.const_mul (f x)),
    integral_const_mul, herror, integral_sub hr hk, schauderHessianCandidate]
  dsimp [g]
  ring

/-- On every bounded ball of centers, the genuine smooth Hessian convolutions
converge uniformly to the compensated integral. -/
theorem tendstoUniformlyOn_schauderRegularizedHessianConvolution {α A B : ℝ}
    (hα : 0 < α) (hA : 0 ≤ A) (hB : 0 ≤ B) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hεpos : ∀ k, 0 < ε k)
    {f : E₃ → ℝ} (hf : Measurable f) (hcf : HasCompactSupport f)
    (hfb : ∀ x, ‖f x‖ ≤ B) (hinc : ∀ x y, ‖f x - f y‖ ≤ A * ‖x - y‖ ^ α)
    (S : ℝ) (i j : Fin 3) :
    TendstoUniformlyOn (fun k => schauderRegularizedHessianConvolution (ε k) i j f)
      (schauderHessianCandidate i j f) atTop (ball 0 S) := by
  have hi := integrable_scalarDensity_of_bounded_compact hf.aestronglyMeasurable hcf hfb
  obtain ⟨R, _, hR⟩ := schauder_compensated_source_uniform_support hcf S
  let E (k : ℕ) : ℝ :=
    (A + B) * (∫ z : E₃ in ball 0 R,
      ‖schauderRegularizedHessianEntry (ε k) i j z - schauderNewtonHessianEntry i j z‖ * ‖z‖ ^ α) +
    B * ‖(∫ z, schauderRegularizedHessianEntry (ε k) i j z * schauderRadialBump z) -
      (if i = j then (1 / 3 : ℝ) else 0)‖
  have hE : Tendsto E atTop (𝓝 0) := by
    have hnear := (tendsto_integral_schauderRegularizedHessianEntry_weighted_error
      hα hε hεpos R i j).const_mul (A + B)
    have hmoment := (((tendsto_integral_schauderRegularized_radialBump hε hεpos i j).sub
      (tendsto_const_nhds (x := if i = j then (1 / 3 : ℝ) else 0))).norm).const_mul B
    simpa only [mul_zero, sub_self, norm_zero, add_zero] using hnear.add hmoment
  have hbound (k : ℕ) (x : E₃) (hx : x ∈ ball (0 : E₃) S) :
      ‖schauderRegularizedHessianConvolution (ε k) i j f x -
        schauderHessianCandidate i j f x‖ ≤ E k := by
    rw [schauderRegularizedHessianConvolution_sub_candidate hα (hεpos k) hA hf hi hinc i j x]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact (schauder_regularized_compensated_error_bound hα (hεpos k) hA hB hf hfb hinc
        i j x (hR x hx)).2
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hfb x) (norm_nonneg _)
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  filter_upwards [hE.eventually (gt_mem_nhds hδ)] with k hk x hx
  rw [dist_eq_norm, norm_sub_rev]
  exact (hbound k x hx).trans_lt hk

end LiquidDrop
