import NoCompromise.Area.UniformDerivative

/-!
# Packaging compact uniform differentiability carriers

A supremum envelope combines uniform remainder control and uniform continuity
of the derivative into one nondecreasing modulus tending to zero. Quantitative
rank and location bounds then give the blueprint's compact carriers.
-/

noncomputable section

open MeasureTheory Set Module Filter
open scoped ENNReal NNReal Topology

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- Bounded errors that vanish uniformly at small scales admit a monotone vanishing envelope. -/
lemma exists_monotone_vanishing_envelope {ι : Type*} (a ρ : ι → ℝ≥0)
    {M : ℝ≥0} (hbound : ∀ i, a i ≤ M)
    (hsmall : ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0, 0 < δ ∧ ∀ i, ρ i < δ → a i ≤ ε) :
    ∃ ω : ℝ≥0 → ℝ≥0, Monotone ω ∧ Tendsto ω (𝓝 0) (𝓝 0) ∧ ∀ i, a i ≤ ω (ρ i) := by
  let ω : ℝ≥0 → ℝ≥0 := fun r => sSup (a '' {i | ρ i ≤ r})
  have hbounded (r : ℝ≥0) : BddAbove (a '' {i | ρ i ≤ r}) := by
    refine ⟨M, ?_⟩
    rintro b ⟨i, hi, rfl⟩
    exact hbound i
  refine ⟨ω, ?_, ?_, ?_⟩
  · intro r s hrs
    apply csSup_le'
    rintro b ⟨i, hi, rfl⟩
    exact le_csSup (hbounded s) ⟨i, hi.trans hrs, rfl⟩
  · apply tendsto_order.mpr
    constructor
    · intro b hb
      exact False.elim (not_lt_of_ge (show 0 ≤ b from bot_le) hb)
    · intro ε hε
      obtain ⟨δ, hδ, hδa⟩ := hsmall (ε / 2) (by positivity)
      filter_upwards [gt_mem_nhds hδ] with r hr
      have hω : ω r ≤ ε / 2 := by
        apply csSup_le'
        rintro b ⟨i, hi, rfl⟩
        exact hδa i (hi.trans_lt hr)
      exact hω.trans_lt (by simpa using half_lt_self hε)
  · intro i
    exact le_csSup (hbounded (ρ i)) ⟨i, by simp, rfl⟩
/-- Uniform remainder control and a bounded derivative admit one common monotone modulus. -/
lemma exists_common_derivative_modulus {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)} {C N : ℝ≥0}
    (hf : LipschitzWith C f) {S : Set (EuclideanSpace ℝ (Fin 2))}
    (hN : ∀ x ∈ S, ‖fderiv ℝ f x‖₊ ≤ N) (hrem : UniformRemainderOn f S) :
    ∃ ω : ℝ≥0 → ℝ≥0, Monotone ω ∧ Tendsto ω (𝓝 0) (𝓝 0) ∧
      (∀ x ∈ S, ∀ y ∈ S,
        ‖f x - f y - fderiv ℝ f y (x - y)‖ ≤ ω ‖x - y‖₊ * ‖x - y‖) ∧
      (∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ ω ‖x - y‖₊) := by
  let ρ : (S × S) → ℝ≥0 := fun p => ‖(p.1 : EuclideanSpace ℝ (Fin 2)) - p.2‖₊
  let a : (S × S) → ℝ≥0 := fun p =>
    max (‖f p.1 - f p.2 - fderiv ℝ f p.2 ((p.1 : EuclideanSpace ℝ (Fin 2)) - p.2)‖₊ / ρ p)
      ‖fderiv ℝ f p.1 - fderiv ℝ f p.2‖₊
  have hbound : ∀ p, a p ≤ max (C + N) (2 * N) := by
    intro p
    apply max_le
    · apply le_trans _ (le_max_left _ _)
      by_cases hp : ρ p = 0
      · simp [hp]
      · apply (div_le_iff₀ (pos_iff_ne_zero.mpr hp)).2
        have hNp : ‖fderiv ℝ f p.2‖ ≤ (N : ℝ) := by exact_mod_cast hN p.2 p.2.property
        have herr : ‖f p.1 - f p.2 - fderiv ℝ f p.2
            ((p.1 : EuclideanSpace ℝ (Fin 2)) - p.2)‖ ≤
            ((C : ℝ) + N) * ‖(p.1 : EuclideanSpace ℝ (Fin 2)) - p.2‖ := by
          have h₁ := norm_sub_le (f p.1 - f p.2)
            (fderiv ℝ f p.2 ((p.1 : EuclideanSpace ℝ (Fin 2)) - p.2))
          have h₂ := hf.norm_sub_le p.1 p.2
          have h₃ := (fderiv ℝ f p.2).le_opNorm
            ((p.1 : EuclideanSpace ℝ (Fin 2)) - p.2)
          nlinarith [mul_le_mul_of_nonneg_right hNp
            (norm_nonneg ((p.1 : EuclideanSpace ℝ (Fin 2)) - p.2))]
        exact_mod_cast herr
    · apply le_trans _ (le_max_right _ _)
      have hx : ‖fderiv ℝ f p.1‖ ≤ (N : ℝ) := by exact_mod_cast hN p.1 p.1.property
      have hy : ‖fderiv ℝ f p.2‖ ≤ (N : ℝ) := by exact_mod_cast hN p.2 p.2.property
      have hh : ‖fderiv ℝ f p.1 - fderiv ℝ f p.2‖ ≤ 2 * (N : ℝ) := by
        linarith [norm_sub_le (fderiv ℝ f p.1) (fderiv ℝ f p.2)]
      exact_mod_cast hh
  have hsmall : ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0, 0 < δ ∧ ∀ p, ρ p < δ → a p ≤ ε := by
    intro ε hε
    have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
    obtain ⟨r, hr, hcontrol⟩ := hrem ε hεR
    obtain ⟨δ, hδ, hcont⟩ := Metric.uniformContinuousOn_iff.mp
      (hrem.uniformContinuousOn_fderiv hf) (ε : ℝ) hεR
    let δ₀ : ℝ≥0 := ⟨min r δ, le_of_lt (lt_min hr hδ)⟩
    refine ⟨δ₀, by change 0 < min r δ; exact lt_min hr hδ, ?_⟩
    intro p hp
    have hpR : ‖(p.1 : EuclideanSpace ℝ (Fin 2)) - p.2‖ < min r δ := by exact_mod_cast hp
    apply max_le
    · by_cases hz : ρ p = 0
      · simp [hz]
      · apply (div_le_iff₀ (pos_iff_ne_zero.mpr hz)).2
        exact_mod_cast hcontrol p.2 p.2.property p.1 (hpR.trans_le (min_le_left _ _))
    · have hnorm := hcont p.1 p.1.property p.2 p.2.property
        (by simpa only [dist_eq_norm] using hpR.trans_le (min_le_right _ _))
      exact_mod_cast (show ‖fderiv ℝ f p.1 - fderiv ℝ f p.2‖ ≤ (ε : ℝ) by
        simpa only [dist_eq_norm] using hnorm.le)
  obtain ⟨ω, hωmono, hωzero, hω⟩ := exists_monotone_vanishing_envelope a ρ hbound hsmall
  refine ⟨ω, hωmono, hωzero, ?_, ?_⟩
  · intro x hx y hy
    by_cases hxy : x = y
    · simp [hxy]
    · have hp : 0 < ρ (⟨x, hx⟩, ⟨y, hy⟩) := by
        exact nnnorm_pos.mpr (sub_ne_zero.mpr hxy)
      have hh := (div_le_iff₀ hp).mp
        ((le_max_left _ _).trans (hω (⟨x, hx⟩, ⟨y, hy⟩)))
      exact_mod_cast hh
  · intro x hx y hy
    have hh := (le_max_right _ _).trans (hω (⟨x, hx⟩, ⟨y, hy⟩))
    exact_mod_cast hh

/-- A coordinate-bounded subset of the plane has finite Lebesgue measure. -/
lemma volume_ne_top_of_coordinate_bound {S : Set (EuclideanSpace ℝ (Fin 2))}
    {N : ℝ} (hN : 0 ≤ N) (hcoord : ∀ x ∈ S, ∀ i : Fin 2, |x i| ≤ N) :
    volume S ≠ ∞ := by
  have hsub : S ⊆ Metric.closedBall 0 (2 * N) := by
    intro x hx
    have hsq (i : Fin 2) : (x i) ^ 2 ≤ N ^ 2 := by
      simpa only [← pow_two, sq_abs] using mul_self_le_mul_self (abs_nonneg (x i)) (hcoord x hx i)
    have hn : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    have hnorm : ‖x‖ ≤ 2 * N := le_of_sq_le_sq
      (by nlinarith [hsq 0, hsq 1, sq_nonneg N]) (by positivity)
    simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm
  exact ne_top_of_le_ne_top (isCompact_closedBall 0 (2 * N)).measure_lt_top.ne
    (measure_mono hsub)

/-- Uniform differentiability on a compact quantitative rank-two set gives a carrier. -/
lemma exists_carrier_of_uniformRemainderOn {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)} {C : ℝ≥0}
    (hf : LipschitzWith C f) {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K)
    (N : ℕ) (hN : 1 ≤ N)
    (hcoord : ∀ x ∈ K, ∀ i : Fin 2, |x i| ≤ N)
    (hdiff : ∀ x ∈ K, DifferentiableAt ℝ f x)
    (hnorm : ∀ x ∈ K, ‖fderiv ℝ f x‖ ≤ N)
    (hsv : ∀ x ∈ K, 1 / (N : ℝ) ≤ (fderiv ℝ f x).singularValues 1)
    (hrem : UniformRemainderOn f K) :
    ∃ d : UniformDifferentiabilityCarrier f, d.carrier = K ∧ d.bound = N := by
  have hnorm' : ∀ x ∈ K, ‖fderiv ℝ f x‖₊ ≤ (N : ℝ≥0) := by
    intro x hx
    exact_mod_cast hnorm x hx
  obtain ⟨ω, hωmono, hωzero, hωrem, hωder⟩ := exists_common_derivative_modulus hf hnorm' hrem
  let d : UniformDifferentiabilityCarrier f :=
    { carrier := K
      isCompact := hK
      bound := N
      one_le_bound := hN
      coordinate_le := hcoord
      differentiableAt := hdiff
      fderiv_norm_le := hnorm
      singularValue_ge := hsv
      modulus := ω
      monotone_modulus := hωmono
      tendsto_modulus_zero := hωzero
      remainder_le := hωrem
      fderiv_sub_le := hωder }
  exact ⟨d, rfl, rfl⟩

/-- Exact local extraction of a compact uniform differentiability carrier from a
Borel set with uniform location, derivative, and rank-two bounds. The omitted
Lebesgue measure can be made arbitrarily small. -/
theorem exists_uniformDifferentiabilityCarrier_subset {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)} {C : ℝ≥0}
    (hf : LipschitzWith C f) {S : Set (EuclideanSpace ℝ (Fin 2))} (hS : MeasurableSet S)
    (N : ℕ) (hN : 1 ≤ N)
    (hcoord : ∀ x ∈ S, ∀ i : Fin 2, |x i| ≤ N)
    (hdiff : ∀ x ∈ S, DifferentiableAt ℝ f x)
    (hnorm : ∀ x ∈ S, ‖fderiv ℝ f x‖ ≤ N)
    (hsv : ∀ x ∈ S, 1 / (N : ℝ) ≤ (fderiv ℝ f x).singularValues 1)
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ d : UniformDifferentiabilityCarrier f,
      d.carrier ⊆ S ∧ volume (S \ d.carrier) < η ∧ d.bound = N := by
  have hSf := volume_ne_top_of_coordinate_bound (by positivity : (0 : ℝ) ≤ N) hcoord
  obtain ⟨K, hKS, hK, hsmall, hrem⟩ :=
    exists_compact_uniformRemainderOn hf.continuous hS hSf hdiff hη
  obtain ⟨d, hdK, hdN⟩ := exists_carrier_of_uniformRemainderOn hf hK N hN
    (fun x hx => hcoord x (hKS hx)) (fun x hx => hdiff x (hKS hx))
    (fun x hx => hnorm x (hKS hx)) (fun x hx => hsv x (hKS hx)) hrem
  exact ⟨d, hdK ▸ hKS, hdK ▸ hsmall, hdN⟩

end LiquidDrop
