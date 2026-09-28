import NoCompromise.Area.GoodPiecesExhaustion

/-!
# Uniform continuity of the derivative

Global Lipschitz control and uniform full-space remainders force the derivative
to vary uniformly continuously. Together with compact remainder extraction,
this gives compact sets on which both uniform differentiability and continuity
of the derivative hold, without any rank hypothesis.
-/

noncomputable section
open MeasureTheory Set Module Filter
open scoped ENNReal NNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8
/-- Comparing two difference quotients controls the difference of their derivatives. -/
lemma norm_fderiv_sub_le_of_uniform_remainder {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)} {C : ℝ≥0}
    (hf : LipschitzWith C f) {S : Set (EuclideanSpace ℝ (Fin 2))}
    {η r t : ℝ} (hη : 0 ≤ η) (ht : 0 < t) (htr : t < r)
    (hrem : ∀ x ∈ S, ∀ y, ‖y - x‖ < r →
      ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ η * ‖y - x‖)
    {x z : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ S) (hz : z ∈ S) :
    ‖fderiv ℝ f x - fderiv ℝ f z‖ ≤ 2 * (C : ℝ) / t * ‖x - z‖ + 2 * η := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  have htv : ‖t • v‖ = t := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, hv, mul_one]
  have hex := hrem x hx (x + t • v) (by simpa only [add_sub_cancel_left, htv] using htr)
  have hez := hrem z hz (z + t • v) (by simpa only [add_sub_cancel_left, htv] using htr)
  simp only [add_sub_cancel_left, htv] at hex hez
  have hxy : ‖f (x + t • v) - f (z + t • v)‖ ≤ (C : ℝ) * ‖x - z‖ := by
    simpa only [add_sub_add_right_eq_sub] using hf.norm_sub_le (x + t • v) (z + t • v)
  have hxz := hf.norm_sub_le x z
  have hid : t • ((fderiv ℝ f x - fderiv ℝ f z) v) =
      (f (x + t • v) - f (z + t • v)) - (f x - f z) -
        (f (x + t • v) - f x - fderiv ℝ f x (t • v)) +
        (f (z + t • v) - f z - fderiv ℝ f z (t • v)) := by
    simp only [sub_apply, map_smul]
    module
  have hn : t * ‖(fderiv ℝ f x - fderiv ℝ f z) v‖ ≤
      2 * (C : ℝ) * ‖x - z‖ + 2 * η * t := by
    calc
      _ = ‖t • ((fderiv ℝ f x - fderiv ℝ f z) v)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      _ = _ := congrArg norm hid
      _ ≤ ‖f (x + t • v) - f (z + t • v)‖ + ‖f x - f z‖ +
          ‖f (x + t • v) - f x - fderiv ℝ f x (t • v)‖ +
          ‖f (z + t • v) - f z - fderiv ℝ f z (t • v)‖ := by
        have h₁ := norm_sub_le (f (x + t • v) - f (z + t • v)) (f x - f z)
        have h₂ := norm_sub_le ((f (x + t • v) - f (z + t • v)) - (f x - f z))
          (f (x + t • v) - f x - fderiv ℝ f x (t • v))
        have h₃ := norm_add_le
          ((f (x + t • v) - f (z + t • v)) - (f x - f z) -
            (f (x + t • v) - f x - fderiv ℝ f x (t • v)))
          (f (z + t • v) - f z - fderiv ℝ f z (t • v))
        linarith
      _ ≤ _ := by linarith
  calc
    _ ≤ (2 * (C : ℝ) * ‖x - z‖ + 2 * η * t) / t :=
      (le_div_iff₀ ht).2 (by linarith)
    _ = _ := by field_simp
/-- Uniform full-space differentiability of a Lipschitz function gives uniform
continuity of its derivative on the source set. -/
lemma UniformRemainderOn.uniformContinuousOn_fderiv {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)} {C : ℝ≥0}
    (hf : LipschitzWith C f) {S : Set (EuclideanSpace ℝ (Fin 2))}
    (hrem : UniformRemainderOn f S) : UniformContinuousOn (fderiv ℝ f) S := by
  rw [Metric.uniformContinuousOn_iff]
  intro ε hε
  obtain ⟨r, hr, hcontrol⟩ := hrem (ε / 8) (by positivity)
  let t : ℝ := r / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htr : t < r := by dsimp [t]; linarith
  let δ : ℝ := ε / (8 * ((C : ℝ) + 1)) * t
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro x hx z hz hxz
  rw [dist_eq_norm] at hxz ⊢
  have hbound := norm_fderiv_sub_le_of_uniform_remainder hf
    (by positivity : 0 ≤ ε / 8) ht htr hcontrol hx hz
  have hC : (C : ℝ) / ((C : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith)
  have hsmall : 2 * (C : ℝ) / t * ‖x - z‖ ≤ ε / 4 := by
    calc
      _ ≤ 2 * (C : ℝ) / t * δ := mul_le_mul_of_nonneg_left hxz.le (by positivity)
      _ = ε / 4 * ((C : ℝ) / ((C : ℝ) + 1)) := by dsimp [δ]; field_simp; ring
      _ ≤ ε / 4 := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hC (by positivity)
  linarith

/-- Compact extraction with both uniform full-space remainders and a uniformly
continuous derivative. No rank assumption is imposed. -/
lemma exists_compact_uniform_derivative {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)} {C : ℝ≥0}
    (hf : LipschitzWith C f)
    {S : Set (EuclideanSpace ℝ (Fin 2))} (hS : MeasurableSet S) (hSf : volume S ≠ ∞)
    (hdiff : ∀ x ∈ S, DifferentiableAt ℝ f x) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ K ⊆ S, IsCompact K ∧ volume (S \ K) < η ∧ UniformRemainderOn f K ∧
      UniformContinuousOn (fderiv ℝ f) K := by
  obtain ⟨K, hKS, hK, hsmall, hrem⟩ :=
    exists_compact_uniformRemainderOn hf.continuous hS hSf hdiff hη
  exact ⟨K, hKS, hK, hsmall, hrem, hrem.uniformContinuousOn_fderiv hf⟩

end LiquidDrop
