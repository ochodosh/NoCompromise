module

public import NoCompromise.Regularity.CompressionJoin
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! # The exact sine-squared compression profile in the radius -/

noncomputable section
open Set Filter
open scoped Topology
namespace LiquidDrop

def compressionSine (σ τ r : ℝ) : ℝ :=
  Real.sin (Real.pi * (r - σ) / (2 * (τ - σ))) ^ 2

def compressionSineDerivative (σ τ r : ℝ) : ℝ :=
  Real.pi / (τ - σ) * Real.sin (Real.pi * (r - σ) / (2 * (τ - σ))) *
    Real.cos (Real.pi * (r - σ) / (2 * (τ - σ)))

def compressionRadialProfile (σ τ r : ℝ) : ℝ :=
  if r ≤ τ then (if r ≤ σ then 0 else compressionSine σ τ r) else 1

def compressionRadialDerivative (σ τ r : ℝ) : ℝ :=
  if r ≤ τ then (if r ≤ σ then 0 else compressionSineDerivative σ τ r) else 0

lemma hasDerivAt_compressionSine (σ τ r : ℝ) :
    HasDerivAt (compressionSine σ τ) (compressionSineDerivative σ τ r) r := by
  have h := ((((hasDerivAt_id r).sub_const σ).const_mul Real.pi).div_const
    (2 * (τ - σ))).sin.pow 2
  convert! h using 1
  simp only [compressionSineDerivative, id_eq, Nat.cast_ofNat, Nat.reduceSub,
    pow_one, mul_one, div_mul_eq_div_div]
  ring

lemma compressionSine_endpoints {σ τ : ℝ} (h : σ < τ) :
    compressionSine σ τ σ = 0 ∧ compressionSine σ τ τ = 1 ∧
      compressionSineDerivative σ τ σ = 0 ∧ compressionSineDerivative σ τ τ = 0 := by
  have hd : τ - σ ≠ 0 := sub_ne_zero.mpr h.ne'
  have he : Real.pi * (τ - σ) / (2 * (τ - σ)) = Real.pi / 2 := by field_simp
  simp [compressionSine, compressionSineDerivative, he]

lemma hasDerivAt_compressionRadialProfile {σ τ : ℝ} (h : σ < τ) (r : ℝ) :
    HasDerivAt (compressionRadialProfile σ τ) (compressionRadialDerivative σ τ r) r := by
  have he := compressionSine_endpoints h
  have hin := hasDerivAt_join_le_everywhere (fun r => hasDerivAt_const r (0 : ℝ))
    (hasDerivAt_compressionSine σ τ) he.1.symm he.2.2.1.symm
  have hv : (if τ ≤ σ then 0 else compressionSine σ τ τ) = 1 := by
    rw [ite_eq_right h.not_ge, he.2.1]
  have hd : (if τ ≤ σ then 0 else compressionSineDerivative σ τ τ) = 0 := by
    rw [ite_eq_right h.not_ge, he.2.2.2]
  exact hasDerivAt_join_le_everywhere hin (fun r => hasDerivAt_const r (1 : ℝ)) hv hd r

lemma contDiff_compressionRadialProfile {σ τ : ℝ} (h : σ < τ) :
    ContDiff ℝ 1 (compressionRadialProfile σ τ) := by
  have he := compressionSine_endpoints h
  have hs : ContDiff ℝ 1 (compressionSine σ τ) := by
    unfold compressionSine
    fun_prop
  have hin := contDiff_join_le (contDiff_const (c := (0 : ℝ))) hs he.1.symm
    (by rw [deriv_const, (hasDerivAt_compressionSine σ τ σ).deriv, he.2.2.1])
  apply contDiff_join_le hin (contDiff_const (c := (1 : ℝ)))
  · rw [ite_eq_right h.not_ge, he.2.1]
  · have hd := (hasDerivAt_join_le_everywhere
      (fun r => hasDerivAt_const r (0 : ℝ)) (hasDerivAt_compressionSine σ τ)
      he.1.symm he.2.2.1.symm τ).deriv
    rw [hd, ite_eq_right h.not_ge, he.2.2.2, deriv_const]

lemma compressionRadialProfile_zero {σ τ r : ℝ} (h : σ < τ) (hr : r ≤ σ) :
    compressionRadialProfile σ τ r = 0 := by
  simp only [compressionRadialProfile, ite_eq_left (hr.trans h.le), ite_eq_left hr]

lemma compressionRadialProfile_one {σ τ r : ℝ} (h : σ < τ) (hr : τ ≤ r) :
    compressionRadialProfile σ τ r = 1 := by
  rcases hr.eq_or_lt with rfl | hr
  · simp only [compressionRadialProfile, le_refl, ite_true, ite_eq_right h.not_ge,
      (compressionSine_endpoints h).2.1]
  · exact ite_eq_right hr.not_ge

lemma compressionRadialProfile_mem_Icc (σ τ r : ℝ) :
    compressionRadialProfile σ τ r ∈ Icc (0 : ℝ) 1 := by
  unfold compressionRadialProfile
  split_ifs <;> try norm_num
  exact ⟨sq_nonneg _, Real.sin_sq_le_one _⟩

lemma compressionRadialDerivative_sq {σ τ : ℝ} (_h : σ < τ) (r : ℝ) :
    compressionRadialDerivative σ τ r ^ 2 = Real.pi ^ 2 / (τ - σ) ^ 2 *
      compressionRadialProfile σ τ r * (1 - compressionRadialProfile σ τ r) := by
  unfold compressionRadialDerivative compressionRadialProfile
  split_ifs <;> try norm_num
  unfold compressionSineDerivative compressionSine
  have he := Real.sin_sq_add_cos_sq (Real.pi * (r - σ) / (2 * (τ - σ)))
  have hc : Real.cos (Real.pi * (r - σ) / (2 * (τ - σ))) ^ 2 =
      1 - Real.sin (Real.pi * (r - σ) / (2 * (τ - σ))) ^ 2 := by linarith
  rw [mul_pow, mul_pow, div_pow, hc]

lemma compressionRadialDerivative_bound {σ τ : ℝ} (h : σ < τ) (r : ℝ) :
    ‖compressionRadialDerivative σ τ r‖ ≤ Real.pi / (τ - σ) := by
  have ha := compressionRadialProfile_mem_Icc σ τ r
  have hk : 0 ≤ Real.pi / (τ - σ) := (div_pos Real.pi_pos (sub_pos.mpr h)).le
  have hh := compressionRadialDerivative_sq h r
  rw [Real.norm_eq_abs]
  apply (sq_le_sq₀ (abs_nonneg _) hk).mp
  rw [sq_abs, div_pow]
  have hp : compressionRadialProfile σ τ r * (1 - compressionRadialProfile σ τ r) ≤ 1 := by
    nlinarith [sq_nonneg (compressionRadialProfile σ τ r)]
  nlinarith [mul_le_mul_of_nonneg_left hp (div_nonneg (sq_nonneg Real.pi)
    (sq_nonneg (τ - σ)))]

lemma lipschitzWith_compressionRadialProfile {σ τ : ℝ} (h : σ < τ) :
    LipschitzWith ⟨Real.pi / (τ - σ), (div_pos Real.pi_pos (sub_pos.mpr h)).le⟩
      (compressionRadialProfile σ τ) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun r => (hasDerivAt_compressionRadialProfile h r).differentiableAt)
  intro r
  rw [(hasDerivAt_compressionRadialProfile h r).deriv]
  exact compressionRadialDerivative_bound h r

end LiquidDrop
