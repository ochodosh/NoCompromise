import NoCompromise.Elliptic.Caccioppoli
import NoCompromise.Sobolev.H1PositivePartPoincare

/-! Smooth distributional tests extend to genuine H¹₀ tests by the defining
closed subspace. Constant divergence data cancel, and the Hilbert energy
estimate records the explicit comparison constant. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The defining H¹ closure extends a genuine smooth distributional test
identity to all zero-boundary H¹ functions. -/
theorem campanato_integral_inner_gradient_eq_zero_of_smooth_tests {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hF : MemLp F 2 (volume.restrict D))
    (h : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ D →
      (∫ x in D, inner ℝ (F x) (gradient φ x)) = 0)
    (v : H1ZeroSpace hD) : (∫ x in D, inner ℝ (F x) (v.val.gradientLp x)) = 0 := by
  let ℓ : H1Space D →L[ℝ] ℝ :=
    (innerSL ℝ (hF.toLp F)).comp H1Space.gradientCLM
  have hclosed : IsClosed {u : H1Space D | ℓ u = 0} := isClosed_eq ℓ.continuous continuous_const
  have hz : ℓ v.val = 0 := closure_minimal
    (s := ((h1ZeroTestFunctions.toH1Space hD).range : Set (H1Space D)))
    (t := {u | ℓ u = 0}) (by
      rintro u ⟨φ, rfl⟩
      change inner ℝ (hF.toLp F) (h1ZeroTestFunctions.toH1Space hD φ).gradientLp = 0
      rw [L2.inner_def]
      calc
        _ = ∫ x in D, inner ℝ (F x) (gradient φ.val x) := by
          apply integral_congr_ae
          filter_upwards [MemLp.coeFn_toLp hF,
            H1Space.gradientLp_ofFunction φ.val (gradient φ.val)
              (h1ZeroTestFunctions.hasH1GradientOn φ hD)] with x hx hy
          rw [hx]
          exact congrArg (fun z => inner ℝ (F x) z) hy
        _ = 0 := h φ.val φ.property.1 φ.property.2.1 φ.property.2.2) hclosed v.property
  change inner ℝ (hF.toLp F) v.val.gradientLp = 0 at hz
  rw [L2.inner_def] at hz
  convert hz using 1
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hF] with x hx
  rw [hx]

lemma campanato_integral_inner_const_gradient {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hcφ : HasCompactSupport φ) (c : EuclideanSpace ℝ (Fin n)) :
    (∫ x, inner ℝ c (gradient φ x)) = 0 := by
  have h := integral_divergenceN_eq_zero (hφ.smul contDiff_const)
    (hcφ.smul_right (f' := fun _ => c))
  have he : divergenceN (fun x => φ x • c) = fun x => inner ℝ c (gradient φ x) := by
    funext x
    rw [divergenceN_smul hφ contDiff_const]
    simp [divergenceN]
  change (∫ x, divergenceN (fun y => φ y • c) x) = 0 at h
  rwa [he] at h

/-- Constant divergence data cancel against the genuine zero-boundary space. -/
theorem campanato_integral_inner_const_gradient_h1Zero {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (hvol : volume D < ∞) (c : EuclideanSpace ℝ (Fin n)) (v : H1ZeroSpace hD) :
    (∫ x in D, inner ℝ c (v.val.gradientLp x)) = 0 := by
  let : IsFiniteMeasure (volume.restrict D) := ⟨by simpa using hvol⟩
  apply campanato_integral_inner_gradient_eq_zero_of_smooth_tests hD (memLp_const c) ?_ v
  intro φ hφ hcφ hsφ
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [gradient_eq_zero_of_notMem_tsupport (fun ht => hx (hsφ ht)), inner_zero_right])]
  exact campanato_integral_inner_const_gradient (hφ.of_le (by simp)) hcφ c

lemma campanato_memLp_apply_bounded {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hA : AEStronglyMeasurable A μ) (hF : MemLp F 2 μ)
    {Λ : ℝ} (hb : ∀ᵐ x ∂μ, ‖A x‖ ≤ Λ) :
    MemLp (fun x => A x (F x)) 2 μ := by
  apply hF.of_le_mul (c := Λ)
  · exact isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable (hA.prodMk hF.aestronglyMeasurable)
  · filter_upwards [hb] with x hx
    exact (A x).le_opNorm (F x) |>.trans
      (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

/-- The elementary Hilbert-space comparison estimate used after testing the
actual weak equations with their zero-boundary difference. -/
lemma campanato_hilbert_energy_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v P Q : E} {lam : ℝ} (hlam : 0 < lam)
    (h : lam * ‖v‖ ^ 2 ≤ inner ℝ (P + Q) v) :
    ‖v‖ ^ 2 ≤ (2 / lam ^ 2) * (‖P‖ ^ 2 + ‖Q‖ ^ 2) := by
  have hb : inner ℝ (P + Q) v ≤ (‖P‖ + ‖Q‖) * ‖v‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (norm_add_le _ _) (norm_nonneg _))
  have hl : lam * ‖v‖ ≤ ‖P‖ + ‖Q‖ := by
    by_cases hv : ‖v‖ = 0
    · rw [hv, mul_zero]
      positivity
    · have hvp : 0 < ‖v‖ := (norm_nonneg _).lt_of_ne (Ne.symm hv)
      apply (mul_le_mul_iff_left₀ hvp).mp
      nlinarith only [h, hb]
  have hs := mul_self_le_mul_self (mul_nonneg hlam.le (norm_nonneg v)) hl
  rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hlam)]
  nlinarith [sq_nonneg (‖P‖ - ‖Q‖)]

lemma campanato_norm_Lp_sq_eq_integral {n : ℕ} {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (v : Lp (EuclideanSpace ℝ (Fin n)) 2 μ) : ‖v‖ ^ 2 = ∫ x, ‖v x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

lemma campanato_coercive_compLp {n : ℕ} {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) {lam : ℝ}
    (hell : ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A ξ) ξ)
    (v : Lp (EuclideanSpace ℝ (Fin n)) 2 μ) :
    lam * ‖v‖ ^ 2 ≤ inner ℝ (A.compLp v) v := by
  rw [campanato_norm_Lp_sq_eq_integral, L2.inner_def, ← integral_const_mul]
  apply integral_mono_ae ((Lp.memLp v).norm.integrable_sq.const_mul lam)
    (integrable_inner_of_memLp_two (Lp.memLp (A.compLp v)) (Lp.memLp v))
  filter_upwards [A.coeFn_compLp v] with x hx
  rw [hx]
  exact hell _

lemma campanato_inner_gradient_eq_zero_of_smooth_tests {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (F : Lp (EuclideanSpace ℝ (Fin n)) 2 (volume.restrict D))
    (h : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ D →
      (∫ x in D, inner ℝ (F x) (gradient φ x)) = 0)
    (v : H1ZeroSpace hD) : inner ℝ F v.val.gradientLp = 0 := by
  rw [L2.inner_def]
  exact campanato_integral_inner_gradient_eq_zero_of_smooth_tests hD (Lp.memLp F) h v

end LiquidDrop
