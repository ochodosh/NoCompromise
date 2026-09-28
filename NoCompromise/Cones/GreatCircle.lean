import NoCompromise.Conventions
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Elementary steps toward `lem:cone-link-great-circle`

Two finite-dimensional facts used in the last paragraph of the blueprint proof of
`lem:cone-link-great-circle` (chapter 25):

* `eq_cos_sin_of_hasDerivAt_neg`: a curve with `γ'' = -γ` in a real inner product space is
  `γ t = cos t • γ 0 + sin t • γ' 0` ("hence `γ(t) = a cos t + b sin t`").
* `greatCircles_meet`: any two great circles `{x ∈ S² | ⟪ν, x⟫ = 0}` of the unit sphere in `ℝ³`
  meet ("two distinct great circles intersect");
* `subsingleton_of_pairwise_disjoint_greatCircles`: pairwise disjoint great circles form a family
  with at most one member.

Neither the Euler equation of the link nor its smoothness is asserted here.
-/

noncomputable section

open Real

namespace LiquidDrop

section ODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Energy argument: a solution of `e' = f, f' = -e` vanishing at `0` together with its
velocity vanishes identically. -/
theorem eq_zero_of_hasDerivAt_neg_of_eq_zero {e e' : ℝ → E}
    (he : ∀ s, HasDerivAt e (e' s) s) (he' : ∀ s, HasDerivAt e' (-e s) s)
    (h0 : e 0 = 0) (h0' : e' 0 = 0) (t : ℝ) : e t = 0 := by
  have hf : ∀ s, HasDerivAt (fun s => inner ℝ (e s) (e s) + inner ℝ (e' s) (e' s)) 0 s := by
    intro s
    refine (((he s).inner ℝ (he s)).add ((he' s).inner ℝ (he' s))).congr_deriv ?_
    rw [inner_neg_right, inner_neg_left, real_inner_comm (e' s) (e s)]
    ring
  have hconst : inner ℝ (e t) (e t) + inner ℝ (e' t) (e' t) =
      inner ℝ (e 0) (e 0) + inner ℝ (e' 0) (e' 0) :=
    is_const_of_deriv_eq_zero (fun s => (hf s).differentiableAt) (fun s => (hf s).deriv) t 0
  rw [h0, h0', inner_zero_left, add_zero] at hconst
  have ha : 0 ≤ inner ℝ (e t) (e t) := real_inner_self_nonneg
  have hb : 0 ≤ inner ℝ (e' t) (e' t) := real_inner_self_nonneg
  have hsq : inner ℝ (e t) (e t) = 0 := by linarith
  exact inner_self_eq_zero.mp hsq

/-- Uniqueness for the harmonic oscillator `γ'' = -γ`: the solution is determined by its
initial position and velocity, and is the corresponding trigonometric combination. -/
theorem eq_cos_sin_of_hasDerivAt_neg {γ γ' : ℝ → E}
    (hγ : ∀ t, HasDerivAt γ (γ' t) t) (hγ' : ∀ t, HasDerivAt γ' (-γ t) t) (t : ℝ) :
    γ t = Real.cos t • γ 0 + Real.sin t • γ' 0 := by
  have he : ∀ s, HasDerivAt (fun s => γ s - (Real.cos s • γ 0 + Real.sin s • γ' 0))
      (γ' s - (Real.cos s • γ' 0 - Real.sin s • γ 0)) s := by
    intro s
    refine ((hγ s).sub (((Real.hasDerivAt_cos s).smul_const (γ 0)).add
      ((Real.hasDerivAt_sin s).smul_const (γ' 0)))).congr_deriv ?_
    module
  have he' : ∀ s, HasDerivAt (fun s => γ' s - (Real.cos s • γ' 0 - Real.sin s • γ 0))
      (-(γ s - (Real.cos s • γ 0 + Real.sin s • γ' 0))) s := by
    intro s
    refine ((hγ' s).sub (((Real.hasDerivAt_cos s).smul_const (γ' 0)).sub
      ((Real.hasDerivAt_sin s).smul_const (γ 0)))).congr_deriv ?_
    module
  have key := eq_zero_of_hasDerivAt_neg_of_eq_zero he he' (by simp) (by simp) t
  exact sub_eq_zero.mp key

end ODE

/-- Any two great circles of the unit sphere in `ℝ³` meet. -/
theorem greatCircles_meet (ν₁ ν₂ : AmbientSpace) :
    ∃ x : AmbientSpace, ‖x‖ = 1 ∧ inner ℝ ν₁ x = 0 ∧ inner ℝ ν₂ x = 0 := by
  let f : AmbientSpace →ₗ[ℝ] ℝ × ℝ := (innerₛₗ ℝ ν₁).prod (innerₛₗ ℝ ν₂)
  have hlt : Module.finrank ℝ (ℝ × ℝ) < Module.finrank ℝ AmbientSpace := by
    rw [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace, Fintype.card_fin]
    norm_num
  obtain ⟨y, hyK, hy0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hlt)
  have hf : f y = 0 := LinearMap.mem_ker.mp hyK
  have h1 : inner ℝ ν₁ y = 0 := by
    simpa [f, LinearMap.prod_apply, innerₛₗ_apply_apply] using congrArg Prod.fst hf
  have h2 : inner ℝ ν₂ y = 0 := by
    simpa [f, LinearMap.prod_apply, innerₛₗ_apply_apply] using congrArg Prod.snd hf
  have hyn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy0
  refine ⟨‖y‖⁻¹ • y, ?_, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hyn]
  · rw [inner_smul_right, h1, mul_zero]
  · rw [inner_smul_right, h2, mul_zero]

/-- Pairwise disjoint great circles of `S²` form a family with at most one member: two distinct
components of an embedded link cannot both be great circles. -/
theorem subsingleton_of_pairwise_disjoint_greatCircles {ι : Type*} (ν : ι → AmbientSpace)
    (h : Pairwise fun i j =>
      Disjoint ({x : AmbientSpace | inner ℝ (ν i) x = 0} ∩ Metric.sphere 0 1)
        ({x : AmbientSpace | inner ℝ (ν j) x = 0} ∩ Metric.sphere 0 1)) :
    Subsingleton ι := by
  refine ⟨fun i j => ?_⟩
  by_contra hij
  obtain ⟨x, hx1, hxi, hxj⟩ := greatCircles_meet (ν i) (ν j)
  have hs : x ∈ Metric.sphere (0 : AmbientSpace) 1 := mem_sphere_zero_iff_norm.mpr hx1
  exact Set.disjoint_left.mp (h hij) ⟨hxi, hs⟩ ⟨hxj, hs⟩

end LiquidDrop

namespace LiquidDrop

/-- The trigonometric parametrization determined by two orthonormal vectors has image
exactly a great circle of the unit sphere. -/
theorem range_cos_sin_eq_greatCircle {a b : AmbientSpace} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : inner ℝ a b = 0) : ∃ ν : AmbientSpace, ν ≠ 0 ∧
    Set.range (fun t : ℝ => Real.cos t • a + Real.sin t • b) =
      {x | inner ℝ ν x = 0} ∩ Metric.sphere 0 1 := by
  classical
  obtain ⟨ν, hν, haν, hbν⟩ := greatCircles_meet a b
  have hνa : inner ℝ ν a = 0 := by rw [real_inner_comm]; exact haν
  have hνb : inner ℝ ν b = 0 := by rw [real_inner_comm]; exact hbν
  have hba : inner ℝ b a = 0 := by rw [real_inner_comm]; exact hab
  have haa : inner ℝ a a = 1 := by rw [real_inner_self_eq_norm_sq, ha]; norm_num
  have hbb : inner ℝ b b = 1 := by rw [real_inner_self_eq_norm_sq, hb]; norm_num
  let v : Fin 3 → AmbientSpace := ![a, b, ν]
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [v, ha, hb, hν, hab, hba, haν, hbν, hνa, hνb]
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ AmbientSpace := by
    simp [AmbientSpace]
  let B := basisOfOrthonormalOfCardEqFinrank hv hcard
  have hB : Orthonormal ℝ B := by simpa [B] using hv
  let e := B.toOrthonormalBasis hB
  have he : (e : Fin 3 → AmbientSpace) = v := by simp [e, B]
  have hexpand (x : AmbientSpace) (hx : inner ℝ ν x = 0) :
      inner ℝ a x • a + inner ℝ b x • b = x := by
    have h := e.sum_repr' x
    simpa [he, v, Fin.sum_univ_succ, hx] using h
  have hnorm (c d : ℝ) : ‖c • a + d • b‖ ^ 2 = c ^ 2 + d ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real, haa, hbb, hab, hba]
    ring
  refine ⟨ν, ?_, ?_⟩
  · intro hz
    simp [hz] at hν
  · ext x
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨?_, mem_sphere_zero_iff_norm.mpr ?_⟩
      · simp [inner_add_right, inner_smul_right, hνa, hνb]
      · have hsq := hnorm (Real.cos t) (Real.sin t)
        have htrig := Real.sin_sq_add_cos_sq t
        have hn := norm_nonneg (Real.cos t • a + Real.sin t • b)
        nlinarith
    · rintro ⟨hx, hs⟩
      have hxn : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hs
      have hrepr := hexpand x hx
      have hsq : (inner ℝ a x) ^ 2 + (inner ℝ b x) ^ 2 = 1 := by
        have h := hnorm (inner ℝ a x) (inner ℝ b x)
        rw [hrepr, hxn] at h
        nlinarith
      have hc : inner ℝ a x ∈ Set.Icc (-1 : ℝ) 1 := by
        constructor <;> nlinarith [sq_nonneg (inner ℝ b x)]
      obtain ⟨t, ht, hcos⟩ := Real.surjOn_cos hc
      have hsin := Real.sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2
      have htrig := Real.sin_sq_add_cos_sq t
      rw [hcos] at htrig
      by_cases hbpos : 0 ≤ inner ℝ b x
      · have hsine : Real.sin t = inner ℝ b x := by nlinarith
        exact ⟨t, by simpa only [hcos, hsine] using hrepr⟩
      · have hsine : Real.sin t = -(inner ℝ b x) := by nlinarith
        refine ⟨-t, ?_⟩
        simpa only [Real.cos_neg, Real.sin_neg, hcos, hsine, neg_neg] using hrepr

/-- A harmonic-oscillator curve with orthonormal initial position and velocity has
image exactly a great circle. -/
theorem range_eq_greatCircle_of_hasDerivAt_neg {γ γ' : ℝ → AmbientSpace}
    (hγ : ∀ t, HasDerivAt γ (γ' t) t) (hγ' : ∀ t, HasDerivAt γ' (-γ t) t)
    (h0 : ‖γ 0‖ = 1) (h1 : ‖γ' 0‖ = 1) (h01 : inner ℝ (γ 0) (γ' 0) = 0) :
    ∃ ν : AmbientSpace, ν ≠ 0 ∧
      Set.range γ = {x | inner ℝ ν x = 0} ∩ Metric.sphere 0 1 := by
  have hfun : γ = fun t => Real.cos t • γ 0 + Real.sin t • γ' 0 :=
    funext (eq_cos_sin_of_hasDerivAt_neg hγ hγ')
  obtain ⟨ν, hν, hrange⟩ := range_cos_sin_eq_greatCircle h0 h1 h01
  exact ⟨ν, hν, (congrArg Set.range hfun).trans hrange⟩

end LiquidDrop
