module

public import NoCompromise.Elliptic.NewtonianSchauderEstimates
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

@[expose] public section

/-!
# An explicit radial cutoff for the Newtonian kernel

The cutoff is constructed directly from the norm using the inner-product-space
bump base. Thus full orthogonal invariance is proved, rather than inferred from
the abstract `ContDiffBump` interface, which only promises symmetry under negation.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- A fixed genuinely radial smooth cutoff, one on `B̄₁` and supported in `B̄₂`. -/
def schauderRadialBump : E₃ → ℝ := (ContDiffBumpBase.ofInnerProductSpace E₃).toFun 2

lemma contDiff_schauderRadialBump : ContDiff ℝ (⊤ : ℕ∞) schauderRadialBump := by
  apply contDiffOn_univ.mp
  exact (ContDiffBumpBase.ofInnerProductSpace E₃).smooth.comp
    (contDiff_const.prodMk contDiff_id).contDiffOn (fun x _ => ⟨by norm_num, mem_univ x⟩)

lemma schauderRadialBump_mem_Icc (x : E₃) : schauderRadialBump x ∈ Icc (0 : ℝ) 1 :=
  (ContDiffBumpBase.ofInnerProductSpace E₃).mem_Icc 2 x

lemma schauderRadialBump_one {x : E₃} (hx : ‖x‖ ≤ 1) : schauderRadialBump x = 1 :=
  (ContDiffBumpBase.ofInnerProductSpace E₃).eq_one 2 one_lt_two x hx

lemma schauderRadialBump_support : Function.support schauderRadialBump = ball (0 : E₃) 2 :=
  (ContDiffBumpBase.ofInnerProductSpace E₃).support 2 one_lt_two

lemma schauderRadialBump_tsupport : tsupport schauderRadialBump = closedBall (0 : E₃) 2 := by
  rw [tsupport, schauderRadialBump_support, closure_ball _ (by norm_num : (2 : ℝ) ≠ 0)]

lemma schauderRadialBump_hasCompactSupport : HasCompactSupport schauderRadialBump := by
  rw [HasCompactSupport, schauderRadialBump_tsupport]
  exact isCompact_closedBall _ _

lemma schauderRadialBump_isometry (e : E₃ ≃ₗᵢ[ℝ] E₃) (x : E₃) :
    schauderRadialBump (e x) = schauderRadialBump x := by
  simp only [schauderRadialBump, ContDiffBumpBase.ofInnerProductSpace, e.norm_map]

lemma schauderRadialBump_neg (x : E₃) : schauderRadialBump (-x) = schauderRadialBump x := by
  simp only [schauderRadialBump, ContDiffBumpBase.ofInnerProductSpace, norm_neg]

/-- The same explicit radial cutoff at a variable positive length scale. -/
def schauderRadialCutoff (d : ℝ) (x : E₃) : ℝ := schauderRadialBump (d⁻¹ • x)

lemma contDiff_schauderRadialCutoff (d : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (schauderRadialCutoff d) :=
  contDiff_schauderRadialBump.comp (contDiff_id.const_smul _)

lemma schauderRadialCutoff_mem_Icc (d : ℝ) (x : E₃) :
    schauderRadialCutoff d x ∈ Icc (0 : ℝ) 1 := schauderRadialBump_mem_Icc _

lemma schauderRadialCutoff_one {d : ℝ} (hd : 0 < d) {x : E₃} (hx : ‖x‖ ≤ d) :
    schauderRadialCutoff d x = 1 := by
  apply schauderRadialBump_one
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hd]
  exact (inv_mul_le_iff₀ hd).mpr (by simpa using hx)

lemma schauderRadialCutoff_zero {d : ℝ} (hd : 0 < d) {x : E₃} (hx : 2 * d ≤ ‖x‖) :
    schauderRadialCutoff d x = 0 := by
  change schauderRadialBump (d⁻¹ • x) = 0
  apply Function.notMem_support.mp
  rw [schauderRadialBump_support, mem_ball, dist_zero_right, norm_smul,
    Real.norm_eq_abs, abs_inv, abs_of_pos hd, not_lt]
  exact (le_inv_mul_iff₀ hd).mpr (by linarith)

lemma schauderRadialCutoff_isometry (d : ℝ) (e : E₃ ≃ₗᵢ[ℝ] E₃) (x : E₃) :
    schauderRadialCutoff d (e x) = schauderRadialCutoff d x := by
  rw [schauderRadialCutoff, ← e.map_smul, schauderRadialBump_isometry]
  rfl

lemma schauderRadialCutoff_neg (d : ℝ) (x : E₃) :
    schauderRadialCutoff d (-x) = schauderRadialCutoff d x := by
  simp only [schauderRadialCutoff, smul_neg, schauderRadialBump_neg]

lemma schauderRadialCutoff_hasCompactSupport {d : ℝ} (hd : 0 < d) :
    HasCompactSupport (schauderRadialCutoff d) :=
  schauderRadialBump_hasCompactSupport.comp_homeomorph
    (Homeomorph.smulOfNeZero _ (inv_ne_zero hd.ne'))

lemma schauderRadialCutoff_eventually_one {d : ℝ} (hd : 0 < d) {x : E₃}
    (hx : ‖x‖ < d) : schauderRadialCutoff d =ᶠ[𝓝 x] 1 := by
  filter_upwards [isOpen_ball.mem_nhds (show x ∈ ball (0 : E₃) d by
    simpa only [mem_ball, dist_zero_right] using hx)] with y hy
  exact schauderRadialCutoff_one hd (le_of_lt (by
    simpa only [mem_ball, dist_zero_right] using hy))

lemma fderiv_schauderRadialCutoff (d : ℝ) (x : E₃) :
    fderiv ℝ (schauderRadialCutoff d) x =
      d⁻¹ • fderiv ℝ schauderRadialBump (d⁻¹ • x) := by
  have h := (contDiff_schauderRadialBump.differentiable (by simp) _).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul d⁻¹)
  change HasFDerivAt (schauderRadialCutoff d) _ x at h
  simpa only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id,
    Pi.smul_apply, id_eq] using h.fderiv

/-- A fixed derivative constant works at every positive scale. -/
lemma exists_schauderRadialCutoff_derivative_bound :
    ∃ C > 0, ∀ d > 0, ∀ x : E₃, ‖fderiv ℝ (schauderRadialCutoff d) x‖ ≤ C / d := by
  have hc := (contDiff_schauderRadialBump.fderiv_right (m := 0) (by simp)).continuous
  obtain ⟨C, hC⟩ := (schauderRadialBump_hasCompactSupport.fderiv ℝ).exists_bound_of_continuous hc
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun d hd x => ?_⟩
  rw [fderiv_schauderRadialCutoff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hd]
  calc
    _ ≤ d⁻¹ * max C 1 := mul_le_mul_of_nonneg_left ((hC _).trans (le_max_left _ _))
      (inv_nonneg.mpr hd.le)
    _ = _ := by ring

lemma schauderRadialCutoff_eventually_zero {d : ℝ} (hd : 0 < d) {x : E₃}
    (hx : 2 * d < ‖x‖) : schauderRadialCutoff d =ᶠ[𝓝 x] 0 := by
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
  exact schauderRadialCutoff_zero hd hy.le

lemma fderiv_schauderRadialCutoff_zero_outside {d : ℝ} (hd : 0 < d) {x : E₃}
    (hx : 2 * d < ‖x‖) : fderiv ℝ (schauderRadialCutoff d) x = 0 := by
  rw [(schauderRadialCutoff_eventually_zero hd hx).fderiv_eq]
  exact fderiv_const_apply (0 : ℝ)

end LiquidDrop
