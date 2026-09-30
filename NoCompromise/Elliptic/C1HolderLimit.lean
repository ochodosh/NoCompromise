module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.MetricSpace.Sequences

@[expose] public section

/-!
# Uniform `C^{1,α}` bounds pass to pointwise limits

The limit step of the tangential difference-quotient argument in blueprint
`thm:boundary-neumann` (second assertion), `thm:boundary-nondiv` and
`thm:boundary-C2a`: if differentiable functions on an open convex set have uniformly
bounded, uniformly `α`-Hölder derivatives and converge pointwise, then the limit is
differentiable with the same bounds. No uniform convergence and no Arzelà–Ascoli theorem
is needed: every subsequential limit of the derivatives at a point is the derivative of
the limit there, by the uniform first-order Taylor estimate.
-/

noncomputable section
open Filter Metric Set
open scoped Topology Gradient

namespace LiquidDrop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- First-order Taylor estimate for a function with `α`-Hölder derivative on a convex open set. -/
lemma taylor_of_fderiv_holder {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {a C : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C) {g : E → ℝ} (hg : DifferentiableOn ℝ g U)
    (hhold : ∀ x ∈ U, ∀ y ∈ U, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ C * dist x y ^ a)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    ‖g y - g x - fderiv ℝ g x (y - x)‖ ≤ C * dist y x ^ a * ‖y - x‖ := by
  set L := fderiv ℝ g x
  set s := U ∩ closedBall x (dist y x)
  have hs : Convex ℝ s := hconv.inter (convex_closedBall x _)
  have hxs : x ∈ s := ⟨hx, mem_closedBall_self dist_nonneg⟩
  have hys : y ∈ s := ⟨hy, by simp [mem_closedBall]⟩
  have hdiff : ∀ z ∈ s, DifferentiableAt ℝ (fun w => g w - L w) z := fun z hz =>
    ((hg z hz.1).differentiableAt (hU.mem_nhds hz.1)).sub L.differentiableAt
  have hder : ∀ z ∈ s, ‖fderiv ℝ (fun w => g w - L w) z‖ ≤ C * dist y x ^ a := by
    intro z hz
    rw [fderiv_fun_sub ((hg z hz.1).differentiableAt (hU.mem_nhds hz.1)) L.differentiableAt,
      L.fderiv]
    refine (hhold z hz.1 x hx).trans ?_
    have hzx : dist z x ≤ dist y x := hz.2
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hzx ha) hC
  have hmv := hs.norm_image_sub_le_of_norm_fderiv_le hdiff hder hxs hys
  have heq : (g y - L y) - (g x - L x) = g y - g x - L (y - x) := by
    rw [map_sub]; ring
  rw [heq] at hmv
  exact hmv

/-- A uniform first-order Taylor bound with Hölder gain gives a Fréchet derivative. -/
lemma hasFDerivAt_of_taylor_bound {U : Set E} (hU : IsOpen U) {G : E → ℝ} {L : E →L[ℝ] ℝ}
    {x : E} (hx : x ∈ U) {a C : ℝ} (ha : 0 < a)
    (htaylor : ∀ y ∈ U, ‖G y - G x - L (y - x)‖ ≤ C * dist y x ^ a * ‖y - x‖) :
    HasFDerivAt G L x := by
  refine HasFDerivAt.of_isLittleO ?_
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hcont : Tendsto (fun y => C * dist y x ^ a) (𝓝 x) (𝓝 (C * dist x x ^ a)) :=
    tendsto_const_nhds.mul
      (((continuous_id.dist continuous_const).rpow_const
        (fun _ => Or.inr ha.le)).tendsto x)
  rw [dist_self, Real.zero_rpow ha.ne', mul_zero] at hcont
  filter_upwards [hU.mem_nhds hx, hcont.eventually (gt_mem_nhds hc)] with y hy hyc
  exact (htaylor y hy).trans (mul_le_mul_of_nonneg_right hyc.le (norm_nonneg _))

/-- Every subsequential limit of the derivatives at a point is the derivative of the
pointwise limit there. -/
lemma hasFDerivAt_of_subseq_fderiv_tendsto {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (g : ℕ → E → ℝ) (G : E → ℝ)
    (hg : ∀ n, DifferentiableOn ℝ (g n) U)
    (hhold : ∀ n, ∀ x ∈ U, ∀ y ∈ U, ‖fderiv ℝ (g n) x - fderiv ℝ (g n) y‖ ≤ C * dist x y ^ a)
    (hlim : ∀ x ∈ U, Tendsto (fun n => g n x) atTop (𝓝 (G x)))
    {x : E} (hx : x ∈ U) {φ : ℕ → ℕ} (hφ : StrictMono φ) {L : E →L[ℝ] ℝ}
    (hL : Tendsto (fun n => fderiv ℝ (g (φ n)) x) atTop (𝓝 L)) :
    HasFDerivAt G L x := by
  refine hasFDerivAt_of_taylor_bound hU hx ha (C := C) fun y hy => ?_
  have hT : Tendsto (fun n => ‖g (φ n) y - g (φ n) x - fderiv ℝ (g (φ n)) x (y - x)‖) atTop
      (𝓝 ‖G y - G x - L (y - x)‖) :=
    ((((hlim y hy).comp hφ.tendsto_atTop).sub ((hlim x hx).comp hφ.tendsto_atTop)).sub
      (((ContinuousLinearMap.apply ℝ ℝ (y - x)).continuous.tendsto L).comp hL)).norm
  exact le_of_tendsto' hT fun n =>
    taylor_of_fderiv_holder hU hconv ha.le hC (hg (φ n)) (hhold (φ n)) hx hy

/-- Uniform `C^{1,α}` bounds on an open convex set pass to pointwise limits. -/
theorem c1_holder_of_tendsto [FiniteDimensional ℝ E] {U : Set E} (hU : IsOpen U)
    (hconv : Convex ℝ U)
    {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (g : ℕ → E → ℝ) (G : E → ℝ)
    (hg : ∀ n, DifferentiableOn ℝ (g n) U)
    (hbound : ∀ n, ∀ x ∈ U, ‖fderiv ℝ (g n) x‖ ≤ C)
    (hhold : ∀ n, ∀ x ∈ U, ∀ y ∈ U, ‖fderiv ℝ (g n) x - fderiv ℝ (g n) y‖ ≤ C * dist x y ^ a)
    (hlim : ∀ x ∈ U, Tendsto (fun n => g n x) atTop (𝓝 (G x))) :
    DifferentiableOn ℝ G U ∧ (∀ x ∈ U, ‖fderiv ℝ G x‖ ≤ C) ∧
      ∀ x ∈ U, ∀ y ∈ U, ‖fderiv ℝ G x - fderiv ℝ G y‖ ≤ C * dist x y ^ a := by
  have hsub : ∀ x ∈ U, ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ L : E →L[ℝ] ℝ, ∃ χ : ℕ → ℕ,
      StrictMono χ ∧ Tendsto (fun n => fderiv ℝ (g (ψ (χ n))) x) atTop (𝓝 L) := by
    intro x hx ψ _
    obtain ⟨L, -, χ, hχ, hL⟩ := tendsto_subseq_of_bounded (isBounded_closedBall (x := 0) (r := C))
      (x := fun n => fderiv ℝ (g (ψ n)) x)
      (fun n => mem_closedBall_zero_iff.mpr (hbound (ψ n) x hx))
    exact ⟨L, χ, hχ, hL⟩
  have hder : ∀ x ∈ U, ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ L : E →L[ℝ] ℝ,
      Tendsto (fun n => fderiv ℝ (g (ψ n)) x) atTop (𝓝 L) → fderiv ℝ G x = L ∧ ‖L‖ ≤ C :=
    fun x hx ψ hψ L hL =>
      ⟨(hasFDerivAt_of_subseq_fderiv_tendsto hU hconv ha hC g G hg hhold hlim hx hψ hL).fderiv,
        le_of_tendsto' hL.norm fun n => hbound (ψ n) x hx⟩
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx y hy => ?_⟩
  · obtain ⟨L, χ, hχ, hL⟩ := hsub x hx id strictMono_id
    exact (hasFDerivAt_of_subseq_fderiv_tendsto hU hconv ha hC g G hg hhold hlim hx hχ
      hL).differentiableAt.differentiableWithinAt
  · obtain ⟨L, χ, hχ, hL⟩ := hsub x hx id strictMono_id
    obtain ⟨hGL, hLC⟩ := hder x hx χ hχ L hL
    rw [hGL]; exact hLC
  · obtain ⟨L, χ, hχ, hL⟩ := hsub x hx id strictMono_id
    obtain ⟨L', ω, hω, hL'⟩ := hsub y hy χ hχ
    have hLx : Tendsto (fun n => fderiv ℝ (g (χ (ω n))) x) atTop (𝓝 L) :=
      hL.comp hω.tendsto_atTop
    rw [(hder x hx (χ ∘ ω) (hχ.comp hω) L hLx).1, (hder y hy (χ ∘ ω) (hχ.comp hω) L' hL').1]
    exact le_of_tendsto' (hLx.sub hL').norm fun n => hhold (χ (ω n)) x hx y hy

/-- The gradient form of `c1_holder_of_tendsto` on a real inner product space. -/
theorem c1_holder_of_tendsto_gradient {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] [FiniteDimensional ℝ F] {U : Set F} (hU : IsOpen U) (hconv : Convex ℝ U)
    {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (g : ℕ → F → ℝ) (G : F → ℝ)
    (hg : ∀ n, DifferentiableOn ℝ (g n) U)
    (hbound : ∀ n, ∀ x ∈ U, ‖∇ (g n) x‖ ≤ C)
    (hhold : ∀ n, ∀ x ∈ U, ∀ y ∈ U, ‖∇ (g n) x - ∇ (g n) y‖ ≤ C * dist x y ^ a)
    (hlim : ∀ x ∈ U, Tendsto (fun n => g n x) atTop (𝓝 (G x))) :
    DifferentiableOn ℝ G U ∧ (∀ x ∈ U, ‖∇ G x‖ ≤ C) ∧
      ∀ x ∈ U, ∀ y ∈ U, ‖∇ G x - ∇ G y‖ ≤ C * dist x y ^ a := by
  have hn : ∀ (f : F → ℝ) (x : F), ‖∇ f x‖ = ‖fderiv ℝ f x‖ := fun f x => by
    simp only [gradient, LinearIsometryEquiv.norm_map]
  have hd : ∀ (f : F → ℝ) (x y : F), ‖∇ f x - ∇ f y‖ = ‖fderiv ℝ f x - fderiv ℝ f y‖ :=
    fun f x y => by
      simp only [gradient, ← map_sub, LinearIsometryEquiv.norm_map]
  obtain ⟨h1, h2, h3⟩ := c1_holder_of_tendsto hU hconv ha hC g G hg
    (fun n x hx => by simpa only [hn] using hbound n x hx)
    (fun n x hx y hy => by simpa only [hd] using hhold n x hx y hy) hlim
  exact ⟨h1, fun x hx => by simpa only [hn] using h2 x hx,
    fun x hx y hy => by simpa only [hd] using h3 x hx y hy⟩

end LiquidDrop
