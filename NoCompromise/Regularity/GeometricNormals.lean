module

public import NoCompromise.Regularity.GeometricRecurrence
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Group.Continuity

@[expose] public section

/-!
# Complete-space geometric tail estimates

These are sequence estimates with explicit increment hypotheses. They do not
assert that a geometric excess-decay iteration exists.
-/

open Filter
open scoped Topology
namespace LiquidDrop

/-- Natural powers of the square root match the scale exponent in the blueprint. -/
lemma geometricNormals_sqrt_pow {θ : ℝ} (hθ : 0 ≤ θ) (j : ℕ) :
    (Real.sqrt θ) ^ j = θ ^ ((j : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hθ]
  congr 1
  ring

/-- A squared geometric increment bound yields an actual limit and its full tail bound. -/
theorem geometric_limit_of_sq_increment {X : Type*} [PseudoMetricSpace X] [CompleteSpace X]
    {v : ℕ → X} {θ K T : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hK : 0 ≤ K) (hT : 0 ≤ T)
    (hinc : ∀ j, dist (v j) (v (j + 1)) ^ 2 ≤ K * θ ^ j * T) :
    ∃ vLim : X, Tendsto v atTop (𝓝 vLim) ∧ ∀ j,
      dist (v j) vLim ≤ (Real.sqrt (K * T) / (1 - Real.sqrt θ)) * θ ^ ((j : ℝ) / 2) := by
  have hq : Real.sqrt θ < 1 := (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr
    (by simpa using hθ1)
  have hi (j : ℕ) : dist (v j) (v (j + 1)) ≤ Real.sqrt (K * T) * (Real.sqrt θ) ^ j := by
    apply (sq_le_sq₀ dist_nonneg (by positivity)).mp
    calc
      _ ≤ K * θ ^ j * T := hinc j
      _ = (Real.sqrt (K * T) * (Real.sqrt θ) ^ j) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (mul_nonneg hK hT), ← pow_mul, mul_comm j 2, pow_mul,
          Real.sq_sqrt hθ]
        ring
  obtain ⟨vLim, hvLim⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric (Real.sqrt θ) (Real.sqrt (K * T)) hq hi)
  refine ⟨vLim, hvLim, fun j => ?_⟩
  have ht := dist_le_of_le_geometric_of_tendsto (Real.sqrt θ) (Real.sqrt (K * T))
    hq hi hvLim j
  rw [geometricNormals_sqrt_pow hθ j] at ht
  exact ht.trans_eq (by ring)

/-- Algebraic excess recurrence plus explicit increments imply convergence of a sequence.
The recurrence and increment estimates remain hypotheses, not a claimed geometric theorem. -/
theorem geometric_limit_of_recurrence {X : Type*} [PseudoMetricSpace X] [CompleteSpace X]
    (C K : ℝ) (hK : 0 ≤ K) :
    ∃ A > 0, ∀ (θ ω r : ℝ) (E : ℕ → ℝ) (v : ℕ → X), 0 < θ → θ < 1 →
      0 ≤ ω → 0 ≤ r → (∀ j, 0 ≤ E j) →
      (∀ j, E (j + 1) ≤ θ / 2 * E j + C * θ * ω * (θ ^ j * r)) →
      (∀ j, dist (v j) (v (j + 1)) ^ 2 ≤ K * (E j + ω * (θ ^ j * r))) →
      ∃ vLim : X, Tendsto v atTop (𝓝 vLim) ∧ ∀ j,
        dist (v j) vLim ≤ (A / (1 - Real.sqrt θ)) * θ ^ ((j : ℝ) / 2) *
          Real.sqrt (E 0 + ω * r) := by
  obtain ⟨B, hB, hb⟩ := geometric_recurrence_with_error C
  refine ⟨Real.sqrt (K * B) + 1, by positivity,
    fun θ ω r E v hθ hθ1 hω hr hE hrec hinc => ?_⟩
  have hT : 0 ≤ E 0 + ω * r := add_nonneg (hE 0) (mul_nonneg hω hr)
  have hi (j : ℕ) : dist (v j) (v (j + 1)) ^ 2 ≤ K * B * θ ^ j * (E 0 + ω * r) := by
    exact (hinc j).trans ((mul_le_mul_of_nonneg_left
      (hb θ ω r E hθ hθ1 hω hr hE hrec j) hK).trans_eq (by ring))
  obtain ⟨vLim, hvLim, ht⟩ := geometric_limit_of_sq_increment hθ.le hθ1
    (mul_nonneg hK hB.le) hT hi
  refine ⟨vLim, hvLim, fun j => (ht j).trans ?_⟩
  have hq : 0 < 1 - Real.sqrt θ := sub_pos.mpr
    ((Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by simpa using hθ1))
  rw [Real.sqrt_mul (mul_nonneg hK hB.le)]
  have hle : Real.sqrt (K * B) ≤ Real.sqrt (K * B) + 1 := by linarith
  calc
    _ = (Real.sqrt (K * B) / (1 - Real.sqrt θ)) * θ ^ ((j : ℝ) / 2) *
        Real.sqrt (E 0 + ω * r) := by ring
    _ ≤ _ := by gcongr

/-- A limit of unit vectors obtained by the tail estimate is still a unit vector. -/
lemma geometricNormals_norm_limit {X : Type*} [NormedAddCommGroup X]
    {v : ℕ → X} {vLim : X} (hv : Tendsto v atTop (𝓝 vLim)) (hunit : ∀ j, ‖v j‖ = 1) :
    ‖vLim‖ = 1 := by
  have ht := continuous_norm.continuousAt.tendsto.comp hv
  have he : (fun j => ‖v j‖) = fun _ => (1 : ℝ) := funext hunit
  rw [Function.comp_def, he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

end LiquidDrop
