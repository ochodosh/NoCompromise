module

public import NoCompromise.Elliptic.CampanatoComparisonTests

@[expose] public section

/-!
# Comparison with the frozen solution

The actual weak divergence equations and the genuine H¹₀ boundary difference
give the squared-gradient comparison with explicit constant `2 / lam²`.
Coefficients may be merely measurable and bounded, and need not be symmetric.
The frozen coefficient must have the stated strictly positive coercivity.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The full frozen-coefficient energy comparison. The original weak equations
are required only on smooth compact tests, and the boundary relation is actual
membership in the H¹ closure of interior tests. No symmetry is assumed. -/
theorem campanato_comparison {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (hvol : volume D < ∞)
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (A₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (G₀ : EuclideanSpace ℝ (Fin n)) (w h : H1Space D)
    (hA : AEStronglyMeasurable A (volume.restrict D))
    {cap lam : ℝ} (hbA : ∀ᵐ x ∂volume.restrict D, ‖A x‖ ≤ cap)
    (hG : MemLp G 2 (volume.restrict D)) (hlam : 0 < lam)
    (hell : ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A₀ ξ) ξ)
    (hw : IsWeakDivergenceEquationOn A w.gradientLp G D)
    (hh : IsWeakDivergenceEquationOn (fun _ => A₀) h.gradientLp (fun _ => 0) D)
    (hbd : h - w ∈ h1ZeroSubmodule hD) :
    (∫ x in D, ‖w.gradientLp x - h.gradientLp x‖ ^ 2) ≤
      (2 / lam ^ 2) * (∫ x in D, ‖A x - A₀‖ ^ 2 * ‖w.gradientLp x‖ ^ 2) +
      (2 / lam ^ 2) * (∫ x in D, ‖G x - G₀‖ ^ 2) := by
  let μ := volume.restrict D
  let : IsFiniteMeasure μ := ⟨by simpa [μ] using hvol⟩
  have hW := w.hasH1GradientOn.memLp_gradient
  have hAW := campanato_memLp_apply_bounded hA hW hbA
  have hC : MemLp (fun _ : EuclideanSpace ℝ (Fin n) => G₀) 2 μ := memLp_const G₀
  let AW := hAW.toLp (fun x => A x (w.gradientLp x))
  let GG := hG.toLp G
  let Z := hC.toLp (fun _ => G₀)
  let V := w.gradientLp - h.gradientLp
  let P := A₀.compLp w.gradientLp - AW
  let Q := GG - Z
  let v : H1ZeroSpace hD := ⟨w - h, by
    simpa only [neg_sub] using ((h1ZeroSubmodule hD).neg_mem hbd)⟩
  have hv : v.val.gradientLp = V := by
    change H1Space.gradientCLM (w - h) = _
    rw [map_sub]
    rfl
  have htest (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hsφ : tsupport φ ⊆ D) :
      (∫ x in D, inner ℝ (F x) (gradient φ x)) =
        ∫ x, inner ℝ (F x) (gradient φ x) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [gradient_eq_zero_of_notMem_tsupport (fun ht => hx (hsφ ht)), inner_zero_right]
  have hw0 : inner ℝ (AW - GG) V = 0 := by
    rw [← hv]
    apply campanato_inner_gradient_eq_zero_of_smooth_tests hD (AW - GG) ?_ v
    intro φ hφ hcφ hsφ
    calc
      _ = ∫ x in D, inner ℝ (A x (w.gradientLp x) - G x) (gradient φ x) := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub AW GG, MemLp.coeFn_toLp hAW,
          MemLp.coeFn_toLp hG] with x hx hy hz
        rw [hx, Pi.sub_apply, hy, hz]
      _ = 0 := (htest _ φ hsφ).trans (hw φ (hφ.of_le (by simp)) hcφ hsφ)
  have hh0 : inner ℝ (A₀.compLp h.gradientLp) V = 0 := by
    rw [← hv]
    apply campanato_inner_gradient_eq_zero_of_smooth_tests hD (A₀.compLp h.gradientLp) ?_ v
    intro φ hφ hcφ hsφ
    calc
      _ = ∫ x in D, inner ℝ (A₀ (h.gradientLp x)) (gradient φ x) := by
        apply integral_congr_ae
        filter_upwards [A₀.coeFn_compLp h.gradientLp] with x hx
        rw [hx]
      _ = 0 := (htest _ φ hsφ).trans (by
        simpa only [sub_zero] using hh φ (hφ.of_le (by simp)) hcφ hsφ)
  have hz0 : inner ℝ Z V = 0 := by
    rw [← hv, L2.inner_def]
    calc
      _ = ∫ x in D, inner ℝ G₀ (v.val.gradientLp x) := by
        apply integral_congr_ae
        filter_upwards [MemLp.coeFn_toLp hC] with x hx
        rw [hx]
      _ = 0 := campanato_integral_inner_const_gradient_h1Zero hD hvol G₀ v
  have hid : inner ℝ (P + Q) V = inner ℝ (A₀.compLp V) V := by
    have ha : A₀.compLp V = A₀.compLp w.gradientLp - A₀.compLp h.gradientLp :=
      (A₀.compLpL 2 (volume.restrict D)).map_sub _ _
    change inner ℝ ((A₀.compLp w.gradientLp - AW) + (GG - Z)) V = _
    rw [inner_add_left, inner_sub_left, inner_sub_left, ha, inner_sub_left]
    rw [inner_sub_left] at hw0
    linarith
  have hen : ‖V‖ ^ 2 ≤ (2 / lam ^ 2) * (‖P‖ ^ 2 + ‖Q‖ ^ 2) :=
    campanato_hilbert_energy_le hlam ((campanato_coercive_compLp A₀ hell V).trans_eq hid.symm)
  have hV : ‖V‖ ^ 2 = ∫ x in D, ‖w.gradientLp x - h.gradientLp x‖ ^ 2 := by
    rw [campanato_norm_Lp_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub w.gradientLp h.gradientLp] with x hx
    rw [hx, Pi.sub_apply]
  have hQ : ‖Q‖ ^ 2 = ∫ x in D, ‖G x - G₀‖ ^ 2 := by
    rw [campanato_norm_Lp_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub GG Z, MemLp.coeFn_toLp hG,
      MemLp.coeFn_toLp hC] with x hx hy hz
    rw [hx, Pi.sub_apply, hy, hz]
  have hO : MemLp (fun x => ‖A x - A₀‖ * ‖w.gradientLp x‖) 2 (volume.restrict D) := by
    apply hW.norm.of_le_mul (c := cap + ‖A₀‖)
    · exact (hA.sub aestronglyMeasurable_const).norm.mul hW.aestronglyMeasurable.norm
    · filter_upwards [hbA] with x hx
      simp only [norm_mul, norm_norm]
      exact mul_le_mul_of_nonneg_right
        ((norm_sub_le _ _).trans (add_le_add hx le_rfl)) (norm_nonneg _)
  have hP : ‖P‖ ^ 2 ≤ ∫ x in D, ‖A x - A₀‖ ^ 2 * ‖w.gradientLp x‖ ^ 2 := by
    rw [campanato_norm_Lp_sq_eq_integral]
    have hiO : IntegrableOn (fun x => ‖A x - A₀‖ ^ 2 * ‖w.gradientLp x‖ ^ 2) D := by
      simpa only [IntegrableOn, mul_pow] using hO.integrable_sq
    apply integral_mono_ae (Lp.memLp P).norm.integrable_sq hiO
    filter_upwards [Lp.coeFn_sub (A₀.compLp w.gradientLp) AW,
      A₀.coeFn_compLp w.gradientLp, MemLp.coeFn_toLp hAW] with x hx hy hz
    rw [hx, Pi.sub_apply, hy, hz]
    have ht : ‖A₀ (w.gradientLp x) - A x (w.gradientLp x)‖ ≤
        ‖A x - A₀‖ * ‖w.gradientLp x‖ := by
      have ht0 := (A₀ - A x).le_opNorm (w.gradientLp x)
      change ‖A₀ (w.gradientLp x) - A x (w.gradientLp x)‖ ≤
        ‖A₀ - A x‖ * ‖w.gradientLp x‖ at ht0
      rwa [norm_sub_rev A₀ (A x)] at ht0
    have ht2 := mul_self_le_mul_self (norm_nonneg _) ht
    nlinarith only [ht2]
  rw [hV, hQ] at hen
  have hconst : 0 ≤ 2 / lam ^ 2 := by positivity
  have hb := mul_le_mul_of_nonneg_left hP hconst
  nlinarith only [hen, hb]

end LiquidDrop
