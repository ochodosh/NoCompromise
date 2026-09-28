import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Global flows of bounded Lipschitz vector fields
-/

open Set MeasureTheory
open scoped NNReal

namespace LiquidDrop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Even without a measurability hypothesis on the curve, the integral identity for a
bounded continuous vector field forces the curve to be differentiable. -/
private theorem hasDerivAt_of_flow_integral {X : E → E} {M : ℝ}
    (hX : Continuous X) (hM : ∀ x, ‖X x‖ ≤ M) {f : ℝ → E} {x : E}
    (hf : ∀ t, f t = x + ∫ s in (0 : ℝ)..t, X (f s)) :
    ∀ t, HasDerivAt f (X (f t)) t := by
  classical
  let S : Set ℝ := {t | IntervalIntegrable (fun s => X (f s)) volume 0 t}
  have hS : OrdConnected S := by
    constructor
    intro a ha b hb t ht
    exact ha.trans ((ha.symm.trans hb).mono_set
      (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc ht)))
  have hM0 : 0 ≤ M := (norm_nonneg (X x)).trans (hM x)
  have hLip : LipschitzOnWith ⟨M, hM0⟩ f S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    rw [dist_eq_norm, hf a, hf b, add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left ha hb]
    change _ ≤ M * dist a b
    simpa only [Real.dist_eq] using
      intervalIntegral.norm_integral_le_of_norm_le_const (a := b) (b := a)
        (fun t _ => hM (f t))
  have hpiece : S.piecewise f (fun _ => x) = f := by
    funext t
    by_cases ht : t ∈ S
    · simp [ht]
    · simp only [Set.piecewise, ht, ↓reduceIte]
      rw [hf t, intervalIntegral.integral_undef ht, add_zero]
  have hmeas : AEStronglyMeasurable f volume := by
    rw [← hpiece]
    exact (hLip.continuousOn.aestronglyMeasurable hS.measurableSet).piecewise
      hS.measurableSet aestronglyMeasurable_const
  have hint : ∀ a b, IntervalIntegrable (fun s => X (f s)) volume a b := by
    intro a b
    apply (intervalIntegrable_iff').mpr
    exact IntegrableOn.of_bound isCompact_uIcc.measure_lt_top
      ((hX.comp_aestronglyMeasurable hmeas).restrict) M
      (Filter.Eventually.of_forall fun t => hM (f t))
  have hcont : Continuous f := by
    have heq : f = fun t => x + ∫ s in (0 : ℝ)..t, X (f s) := funext hf
    rw [heq]
    exact continuous_const.add (intervalIntegral.continuous_primitive hint 0)
  intro t
  have hd := ((hX.comp hcont).integral_hasStrictDerivAt 0 t).hasDerivAt.const_add x
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall hf)

/-- Local solutions on arbitrarily large intervals agree by ODE uniqueness. -/
private theorem exists_global_curve {X : E → E} {L : ℝ≥0} {M : ℝ}
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) (x : E) :
    ∃ f : ℝ → E, f 0 = x ∧ ∀ t, HasDerivAt f (X (f t)) t := by
  have hM0 : 0 ≤ M := (norm_nonneg (X x)).trans (hM x)
  let B : ℝ≥0 := ⟨M, hM0⟩
  have hlocal (T : ℝ≥0) : ∃ f : ℝ → E, f 0 = x ∧
      ∀ t ∈ Icc (-(T : ℝ)) T, HasDerivWithinAt f (X (f t)) (Icc (-(T : ℝ)) T) t := by
    have hp : IsPicardLindelof (fun _ => X)
        (⟨0, by simp⟩ : Icc (-(T : ℝ)) T) x (B * T) 0 B L := by
      apply IsPicardLindelof.of_time_independent (fun y _ => hM y) hX.lipschitzOnWith
      simp
    exact hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  choose f hf0 hf' using hlocal
  have hd (T : ℝ≥0) (t : ℝ) (ht : |t| < T) : HasDerivAt (f T) (X (f T t)) t :=
    (hf' T t ⟨(abs_lt.mp ht).1.le, (abs_lt.mp ht).2.le⟩).hasDerivAt
      (Icc_mem_nhds (abs_lt.mp ht).1 (abs_lt.mp ht).2)
  have heq (T S : ℝ≥0) (t : ℝ) (hT : |t| < T) (hS : |t| < S) : f T t = f S t := by
    have hpos : (0 : ℝ) < min (T : ℝ) (S : ℝ) := lt_min
      ((abs_nonneg t).trans_lt hT) ((abs_nonneg t).trans_lt hS)
    apply ODE_solution_unique_of_mem_Ioo
      (v := fun _ => X) (s := fun _ => univ)
      (a := -(min (T : ℝ) S)) (b := min (T : ℝ) S) (t₀ := 0)
      (fun _ _ => hX.lipschitzOnWith) ⟨by linarith, hpos⟩
      (fun u hu => ⟨hd T u ((abs_lt.mpr hu).trans_le (min_le_left _ _)), mem_univ _⟩)
      (fun u hu => ⟨hd S u ((abs_lt.mpr hu).trans_le (min_le_right _ _)), mem_univ _⟩)
      ((hf0 T).trans (hf0 S).symm)
    exact abs_lt.mp (lt_min hT hS)
  let R (t : ℝ) : ℝ≥0 := ⟨|t| + 1, by positivity⟩
  have hR (t : ℝ) : |t| < R t := by change |t| < |t| + 1; linarith
  let g : ℝ → E := fun t => f (R t) t
  refine ⟨g, hf0 (R 0), fun t => ?_⟩
  apply (hd (R t) t (hR t)).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (abs_lt.mp (hR t)).1 (abs_lt.mp (hR t)).2] with u hu
  exact heq (R u) (R t) u (hR u) (abs_lt.mpr hu)

/-- A bounded globally Lipschitz vector field on a real Banach space has a unique global
flow satisfying the integral identity. Uniqueness ranges over all functions, without any
additional regularity assumption. -/
theorem exists_unique_globalFlow {X : E → E} {L : ℝ≥0} {M : ℝ}
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) :
    ∃! Φ : ℝ → E → E, ∀ t x, Φ t x = x + ∫ s in (0 : ℝ)..t, X (Φ s x) := by
  choose f hf0 hf' using exists_global_curve hX hM
  have hcont (x : E) : Continuous (f x) := continuous_iff_continuousAt.mpr
    (fun t => (hf' x t).continuousAt)
  have hint (t : ℝ) (x : E) : f x t = x + ∫ s in (0 : ℝ)..t, X (f x s) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hf' x s)
      ((hX.continuous.comp (hcont x)).intervalIntegrable 0 t), hf0 x]
    abel
  refine ⟨fun t x => f x t, hint, ?_⟩
  intro Ψ hΨ
  funext t x
  have hzero : Ψ 0 x = x := by simpa using hΨ 0 x
  have heq : (fun s => Ψ s x) = f x := ODE_solution_unique_univ
    (v := fun _ => X) (s := fun _ => univ) (t₀ := 0)
    (fun _ => hX.lipschitzOnWith)
    (fun s => ⟨hasDerivAt_of_flow_integral hX.continuous hM (fun u => hΨ u x) s, mem_univ _⟩)
    (fun s => ⟨hf' x s, mem_univ _⟩) (hzero.trans (hf0 x).symm)
  exact congrFun heq t

/-- The global flow selected from its existence and uniqueness theorem. -/
noncomputable def globalFlow (X : E → E) {L : ℝ≥0} {M : ℝ}
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) : ℝ → E → E :=
  Classical.choose (exists_unique_globalFlow hX hM)

/-- The selected flow solves the integral equation for every time and initial point. -/
theorem globalFlow_integral {X : E → E} {L : ℝ≥0} {M : ℝ}
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) (t : ℝ) (x : E) :
    globalFlow X hX hM t x = x + ∫ s in (0 : ℝ)..t, X (globalFlow X hX hM s x) :=
  (Classical.choose_spec (exists_unique_globalFlow hX hM)).1 t x

/-- The flow at time zero is the identity. -/
@[simp]
theorem globalFlow_zero {X : E → E} {L : ℝ≥0} {M : ℝ}
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) (x : E) :
    globalFlow X hX hM 0 x = x := by
  simpa using globalFlow_integral hX hM 0 x

/-- Every trajectory has derivative equal to the vector field along the trajectory. -/
theorem hasDerivAt_globalFlow {X : E → E} {L : ℝ≥0} {M : ℝ}
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) (x : E) (t : ℝ) :
    HasDerivAt (fun s => globalFlow X hX hM s x) (X (globalFlow X hX hM t x)) t :=
  hasDerivAt_of_flow_integral hX.continuous hM (fun s => globalFlow_integral hX hM s x) t

/-- Any function satisfying the integral identity agrees with the selected flow. -/
theorem globalFlow_unique {X : E → E} {L : ℝ≥0} {M : ℝ}
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) {Φ : ℝ → E → E}
    (hΦ : ∀ t x, Φ t x = x + ∫ s in (0 : ℝ)..t, X (Φ s x)) :
    Φ = globalFlow X hX hM :=
  (Classical.choose_spec (exists_unique_globalFlow hX hM)).2 Φ hΦ

omit [CompleteSpace E] in
/-- A continuously differentiable compactly supported vector field is globally Lipschitz
and bounded; neither constant needs to be supplied. -/
theorem lipschitz_bounded_of_hasCompactSupport {X : E → E}
    (hX : ContDiff ℝ 1 X) (hs : HasCompactSupport X) :
    ∃ (L : ℝ≥0) (M : ℝ), LipschitzWith L X ∧ ∀ x, ‖X x‖ ≤ M := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hX one_ne_zero
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuous hX.continuous
  exact ⟨L, M, hL, hM⟩

/-- Every continuously differentiable compactly supported vector field has a unique
global flow satisfying the integral identity. -/
theorem exists_unique_globalFlow_of_hasCompactSupport {X : E → E}
    (hX : ContDiff ℝ 1 X) (hs : HasCompactSupport X) :
    ∃! Φ : ℝ → E → E, ∀ t x, Φ t x = x + ∫ s in (0 : ℝ)..t, X (Φ s x) := by
  obtain ⟨L, M, hL, hM⟩ := lipschitz_bounded_of_hasCompactSupport hX hs
  exact exists_unique_globalFlow hL hM

-- BEGIN lem:flow-group, lem:flow-gronwall

omit [CompleteSpace E] in
/-- Two global solutions of the same autonomous ODE with the same initial value agree. -/
private theorem globalCurve_unique {X : E → E} {L : ℝ≥0} (hX : LipschitzWith L X) {f g : ℝ → E}
    (hf : ∀ u, HasDerivAt f (X (f u)) u) (hg : ∀ u, HasDerivAt g (X (g u)) u)
    (h0 : f 0 = g 0) : f = g :=
  ODE_solution_unique_univ (v := fun _ => X) (s := fun _ => univ) (t₀ := 0)
    (fun _ => hX.lipschitzOnWith) (fun u => ⟨hf u, mem_univ _⟩)
    (fun u => ⟨hg u, mem_univ _⟩) h0

omit [CompleteSpace E] in
/-- Reversing time in a curve negates its derivative. -/
private theorem hasDerivAt_comp_neg {f : ℝ → E} {v : E} {u : ℝ} (hf : HasDerivAt f v (-u)) :
    HasDerivAt (fun r => f (-r)) (-v) u := by
  simpa using HasDerivAt.comp_const_sub (0 : ℝ) u (by simpa using hf)

/-- lem:flow-group: the group law. -/
theorem globalFlow_add {X : E → E} {L : ℝ≥0} {M : ℝ}
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) (t s : ℝ) (x : E) :
    globalFlow X hX hM (t + s) x = globalFlow X hX hM t (globalFlow X hX hM s x) := by
  have key : (fun u => globalFlow X hX hM (u + s) x)
      = fun u => globalFlow X hX hM u (globalFlow X hX hM s x) := by
    refine globalCurve_unique hX (fun u => ?_)
      (fun u => hasDerivAt_globalFlow hX hM (globalFlow X hX hM s x) u) (by simp)
    exact HasDerivAt.comp_add_const u s (hasDerivAt_globalFlow hX hM x (u + s))
  exact congrFun key t

theorem globalFlow_neg_left {X : E → E} {L : ℝ≥0} {M : ℝ}
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) (t : ℝ) (x : E) :
    globalFlow X hX hM (-t) (globalFlow X hX hM t x) = x := by
  rw [← globalFlow_add hX hM (-t) t x, neg_add_cancel, globalFlow_zero]

/-- Each time-`t` map is a bijection with inverse the time-`(-t)` map. -/
theorem globalFlow_bijective {X : E → E} {L : ℝ≥0} {M : ℝ}
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) (t : ℝ) :
    Function.Bijective (globalFlow X hX hM t) := by
  refine ⟨Function.LeftInverse.injective (g := globalFlow X hX hM (-t))
    (globalFlow_neg_left hX hM t), fun y => ⟨globalFlow X hX hM (-t) y, ?_⟩⟩
  simpa using globalFlow_neg_left hX hM (-t) y

omit [CompleteSpace E] in
/-- Grönwall estimate for two solutions of the same autonomous ODE, forward in time. -/
private theorem dist_curve_le_exp {X : E → E} {L : ℝ≥0} (hX : LipschitzWith L X) {f g : ℝ → E}
    (hf : ∀ u, HasDerivAt f (X (f u)) u) (hg : ∀ u, HasDerivAt g (X (g u)) u)
    {t : ℝ} (ht : 0 ≤ t) :
    dist (f t) (g t) ≤ Real.exp (L * t) * dist (f 0) (g 0) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun u => (hf u).continuousAt
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun u => (hg u).continuousAt
  have h := dist_le_of_trajectories_ODE (v := fun _ => X) (K := L) (a := 0) (b := t)
    (δ := dist (f 0) (g 0)) (fun _ => hX) hfc.continuousOn
    (fun u _ => (hf u).hasDerivWithinAt) hgc.continuousOn
    (fun u _ => (hg u).hasDerivWithinAt) le_rfl t ⟨ht, le_rfl⟩
  rwa [sub_zero, mul_comm] at h

omit [CompleteSpace E] in
/-- Grönwall estimate for two solutions of the same autonomous ODE, in both time directions. -/
private theorem dist_curve_le_exp_abs {X : E → E} {L : ℝ≥0} (hX : LipschitzWith L X) {f g : ℝ → E}
    (hf : ∀ u, HasDerivAt f (X (f u)) u) (hg : ∀ u, HasDerivAt g (X (g u)) u) (t : ℝ) :
    dist (f t) (g t) ≤ Real.exp (L * |t|) * dist (f 0) (g 0) := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact dist_curve_le_exp hX hf hg ht
  · have hf' : ∀ u, HasDerivAt (fun r => f (-r)) ((-X) ((fun r => f (-r)) u)) u := fun u =>
      hasDerivAt_comp_neg (hf (-u))
    have hg' : ∀ u, HasDerivAt (fun r => g (-r)) ((-X) ((fun r => g (-r)) u)) u := fun u =>
      hasDerivAt_comp_neg (hg (-u))
    have h := dist_curve_le_exp hX.neg hf' hg' (t := -t) (by linarith)
    simpa [abs_of_nonpos ht] using h

/-- lem:flow-gronwall: the Grönwall estimate. -/
theorem dist_globalFlow_le {X : E → E} {L : ℝ≥0} {M : ℝ}
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) (t : ℝ) (x y : E) :
    dist (globalFlow X hX hM t x) (globalFlow X hX hM t y) ≤ Real.exp (L * |t|) * dist x y := by
  have h := dist_curve_le_exp_abs hX (f := fun u => globalFlow X hX hM u x)
    (g := fun u => globalFlow X hX hM u y)
    (hasDerivAt_globalFlow hX hM x) (hasDerivAt_globalFlow hX hM y) t
  simpa using h

theorem lipschitzWith_globalFlow {X : E → E} {L : ℝ≥0} {M : ℝ}
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) (t : ℝ) :
    LipschitzWith (Real.toNNReal (Real.exp (L * |t|))) (globalFlow X hX hM t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.coe_toNNReal _ (Real.exp_pos _).le]
  exact dist_globalFlow_le hX hM t x y

/-- Bi-Lipschitz: the time-`t` map is a homeomorphism of `E` with Lipschitz inverse. -/
noncomputable def globalFlowHomeomorph {X : E → E} {L : ℝ≥0} {M : ℝ}
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) (t : ℝ) : E ≃ₜ E where
  toFun := globalFlow X hX hM t
  invFun := globalFlow X hX hM (-t)
  left_inv := globalFlow_neg_left hX hM t
  right_inv := fun x => by simpa using globalFlow_neg_left hX hM (-t) x
  continuous_toFun := (lipschitzWith_globalFlow hX hM t).continuous
  continuous_invFun := (lipschitzWith_globalFlow hX hM (-t)).continuous

theorem globalFlowHomeomorph_apply {X : E → E} {L : ℝ≥0} {M : ℝ}
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) (t : ℝ) (x : E) :
    globalFlowHomeomorph hX hM t x = globalFlow X hX hM t x := rfl

theorem globalFlowHomeomorph_symm_apply {X : E → E} {L : ℝ≥0} {M : ℝ}
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) (t : ℝ) (x : E) :
    (globalFlowHomeomorph hX hM t).symm x = globalFlow X hX hM (-t) x := rfl

-- END lem:flow-group, lem:flow-gronwall

-- BEGIN lem:flow-variational

open scoped Topology Nat

private noncomputable def variationalExtend (T : ℝ≥0)
    (f : C(Icc (-(T : ℝ)) T, E)) : ℝ → E :=
  fun t => f (projIcc (-(T : ℝ)) T (le_trans (neg_nonpos.mpr T.coe_nonneg) T.coe_nonneg) t)

omit [NormedSpace ℝ E] [CompleteSpace E] in
private theorem variationalExtend_continuous (T : ℝ≥0)
    (f : C(Icc (-(T : ℝ)) T, E)) : Continuous (variationalExtend T f) :=
  f.continuous.comp continuous_projIcc

omit [NormedSpace ℝ E] [CompleteSpace E] in
private theorem variationalExtend_of_mem (T : ℝ≥0)
    (f : C(Icc (-(T : ℝ)) T, E)) (t : ℝ) (ht : t ∈ Icc (-(T : ℝ)) T) :
    variationalExtend T f t = f ⟨t, ht⟩ := by
  simp only [variationalExtend, projIcc_of_mem _ ht]

/-- Picard iteration on continuous curves on a compact interval, with no bound on their range. -/
private noncomputable def variationalPicard (T : ℝ≥0) (K : ℝ → (E →L[ℝ] E))
    (hK : Continuous K) (x : E) : C(Icc (-(T : ℝ)) T, E) → C(Icc (-(T : ℝ)) T, E) :=
  fun f => ⟨fun t => x + ∫ s in (0 : ℝ)..t.1, K s (variationalExtend T f s), by
    have hc : Continuous (fun s => K s (variationalExtend T f s)) :=
      hK.clm_apply (variationalExtend_continuous T f)
    exact (continuous_const.add (intervalIntegral.continuous_primitive
      (fun a b => hc.intervalIntegrable a b) 0)).comp continuous_subtype_val⟩

omit [CompleteSpace E] in
private theorem variationalPicard_iterate_dist (T : ℝ≥0) (K : ℝ → (E →L[ℝ] E))
    (hK : Continuous K) {L : ℝ≥0} (hL : ∀ s, ‖K s‖ ≤ L) (x : E)
    (f g : C(Icc (-(T : ℝ)) T, E)) (n : ℕ) (t : Icc (-(T : ℝ)) T) :
    dist ((variationalPicard T K hK x)^[n] f t)
      ((variationalPicard T K hK x)^[n] g t) ≤
      ((L : ℝ) * |t.1|) ^ n / n ! * dist f g := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f := f) (g := g) t
  | succ n hn =>
    have hc (f : C(Icc (-(T : ℝ)) T, E)) :
        Continuous (fun s => K s (variationalExtend T f s)) :=
      hK.clm_apply (variationalExtend_continuous T f)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', dist_eq_norm]
    change ‖(x + ∫ s in (0 : ℝ)..t.1,
      K s (variationalExtend T ((variationalPicard T K hK x)^[n] f) s)) -
      (x + ∫ s in (0 : ℝ)..t.1,
      K s (variationalExtend T ((variationalPicard T K hK x)^[n] g) s))‖ ≤ _
    rw [add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub
      ((hc _).intervalIntegrable _ _) ((hc _).intervalIntegrable _ _)]
    calc
      _ ≤ ∫ s in uIoc (0 : ℝ) t.1,
          (L : ℝ) ^ (n + 1) * |s| ^ n / n ! * dist f g := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply MeasureTheory.norm_integral_le_of_norm_le
          (Continuous.integrableOn_uIoc (by fun_prop))
        apply (ae_restrict_mem measurableSet_Ioc).mono
        intro s hs
        have hs' : s ∈ Icc (-(T : ℝ)) T :=
          (uIcc_subset_Icc ⟨neg_nonpos.mpr T.coe_nonneg, T.coe_nonneg⟩ t.2) (uIoc_subset_uIcc hs)
        rw [variationalExtend_of_mem T _ s hs', variationalExtend_of_mem T _ s hs',
          ← map_sub]
        calc
          _ ≤ ‖K s‖ * ‖_‖ := (K s).le_opNorm _
          _ ≤ (L : ℝ) * dist
              ((variationalPicard T K hK x)^[n] f ⟨s, hs'⟩)
              ((variationalPicard T K hK x)^[n] g ⟨s, hs'⟩) := by
            rw [dist_eq_norm]
            exact mul_le_mul_of_nonneg_right (hL s) (norm_nonneg _)
          _ ≤ (L : ℝ) ^ (n + 1) * |s| ^ n / n ! * dist f g := by
            calc
              _ ≤ (L : ℝ) * (((L : ℝ) * |s|) ^ n / n ! * dist f g) :=
                mul_le_mul_of_nonneg_left (hn ⟨s, hs'⟩) L.coe_nonneg
              _ = _ := by rw [mul_pow, pow_succ']; ring
      _ ≤ ((L : ℝ) * |t.1|) ^ (n + 1) / (n + 1) ! * dist f g := by
        apply le_of_abs_le
        rw [← intervalIntegral.abs_intervalIntegral_eq, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div, intervalIntegral.integral_const_mul, abs_mul, abs_div,
          abs_mul]
        rw [intervalIntegral.abs_intervalIntegral_eq,
          show (∫ s in uIoc (0 : ℝ) t.1, |s| ^ n) = |t.1| ^ (n + 1) / (n + 1) by
            simpa only [sub_zero] using
              (integral_pow_abs_sub_uIoc (a := (0 : ℝ)) (b := t.1) (n := n)),
          abs_div,
          abs_pow, abs_pow, abs_dist, NNReal.abs_eq, abs_abs, mul_div, div_div, ← abs_mul,
          ← Nat.cast_succ, ← Nat.cast_mul, ← Nat.factorial_succ, Nat.abs_cast, ← mul_pow]

private theorem variational_exists_local (T : ℝ≥0) (K : ℝ → (E →L[ℝ] E))
    (hK : Continuous K) {L : ℝ≥0} (hL : ∀ s, ‖K s‖ ≤ L) (x : E) :
    ∃ f : ℝ → E, f 0 = x ∧
      ∀ t : ℝ, |t| < T → HasDerivAt f (K t (f t)) t := by
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop ((L : ℝ) * T)
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  let C : ℝ≥0 := ⟨((L : ℝ) * T) ^ n / n !, by positivity⟩
  have hcontract : ContractingWith C (variationalPicard T K hK x)^[n] := by
    refine ⟨hn, LipschitzWith.of_dist_le_mul fun f g => ?_⟩
    apply (ContinuousMap.dist_le (by positivity)).mpr
    intro t
    apply (variationalPicard_iterate_dist T K hK hL x f g n t).trans
    change ((L : ℝ) * |t.1|) ^ n / n ! * dist f g ≤
      ((L : ℝ) * T) ^ n / n ! * dist f g
    gcongr
    exact abs_le.mpr t.2
  let f := ContractingWith.fixedPoint _ hcontract
  have hf : variationalPicard T K hK x f = f :=
    hcontract.isFixedPt_fixedPoint_iterate
  let g : ℝ → E := fun t => x + ∫ s in (0 : ℝ)..t, K s (variationalExtend T f s)
  have hgf (t : ℝ) (ht : t ∈ Icc (-(T : ℝ)) T) : g t = variationalExtend T f t := by
    rw [variationalExtend_of_mem T f t ht]
    exact congrArg (fun q : C(Icc (-(T : ℝ)) T, E) => q ⟨t, ht⟩) hf
  refine ⟨g, by simp [g], fun t ht => ?_⟩
  have hc := hK.clm_apply (variationalExtend_continuous T f)
  have hd := (hc.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add x
  change HasDerivAt g (K t (variationalExtend T f t)) t at hd
  rwa [hgf t ⟨(abs_lt.mp ht).1.le, (abs_lt.mp ht).2.le⟩]

private theorem variational_exists_global (K : ℝ → (E →L[ℝ] E))
    (hK : Continuous K) {L : ℝ≥0} (hL : ∀ s, ‖K s‖ ≤ L) (x : E) :
    ∃ f : ℝ → E, f 0 = x ∧ ∀ t, HasDerivAt f (K t (f t)) t := by
  choose f hf0 hf' using fun T => variational_exists_local T K hK hL x
  have hLip (t : ℝ) : LipschitzWith L (K t) :=
    (K t).lipschitzWith.weaken (by exact_mod_cast hL t)
  have heq (T S : ℝ≥0) (t : ℝ) (hT : |t| < T) (hS : |t| < S) : f T t = f S t := by
    have hpos : (0 : ℝ) < min (T : ℝ) (S : ℝ) := lt_min
      ((abs_nonneg t).trans_lt hT) ((abs_nonneg t).trans_lt hS)
    apply ODE_solution_unique_of_mem_Ioo
      (v := fun s y => K s y) (s := fun _ => univ)
      (a := -(min (T : ℝ) S)) (b := min (T : ℝ) S) (t₀ := 0)
      (fun s _ => (hLip s).lipschitzOnWith) ⟨by linarith, hpos⟩
      (fun u hu => ⟨hf' T u ((abs_lt.mpr hu).trans_le (min_le_left _ _)), mem_univ _⟩)
      (fun u hu => ⟨hf' S u ((abs_lt.mpr hu).trans_le (min_le_right _ _)), mem_univ _⟩)
      ((hf0 T).trans (hf0 S).symm)
    exact abs_lt.mp (lt_min hT hS)
  let R (t : ℝ) : ℝ≥0 := ⟨|t| + 1, by positivity⟩
  have hR (t : ℝ) : |t| < R t := by change |t| < |t| + 1; linarith
  let g : ℝ → E := fun t => f (R t) t
  refine ⟨g, hf0 (R 0), fun t => ?_⟩
  apply (hf' (R t) t (hR t)).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (abs_lt.mp (hR t)).1 (abs_lt.mp (hR t)).2] with u hu
  exact heq (R u) (R t) u (hR u) (abs_lt.mpr hu)

private theorem variational_eq_of_integrable (K : ℝ → (E →L[ℝ] E))
    (hK : Continuous K) {L : ℝ≥0} (hL : ∀ s, ‖K s‖ ≤ L) (x : E)
    {f g : ℝ → E} (hf : ∀ t, f t = x + ∫ s in (0 : ℝ)..t, K s (f s))
    (hg0 : g 0 = x) (hg : ∀ t, HasDerivAt g (K t (g t)) t)
    (t : ℝ) (ht : IntervalIntegrable (fun s => K s (f s)) volume 0 t) :
    f t = g t := by
  have hfc : ContinuousOn f (uIcc 0 t) := by
    have he : f = fun u => x + ∫ s in (0 : ℝ)..u, K s (f s) := funext hf
    rw [he]
    exact continuousOn_const.add
      (intervalIntegral.continuousOn_primitive_interval' ht left_mem_uIcc)
  let e : ℝ → E := fun u => f (projIcc (min 0 t) (max 0 t) min_le_max u)
  have hec : Continuous e := hfc.domRestrict.comp continuous_projIcc
  have he (u : ℝ) (hu : u ∈ uIcc 0 t) : e u = f u := by
    simp only [e, projIcc_of_mem _ hu]
  let b : ℝ → E := fun u => x + ∫ s in (0 : ℝ)..u, K s (e s)
  have hb (u : ℝ) (hu : u ∈ uIcc 0 t) : b u = f u := by
    rw [hf u]
    dsimp only [b]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    exact congrArg (K s) (he s ((uIcc_subset_uIcc left_mem_uIcc hu) hs))
  have hb' (u : ℝ) (hu : u ∈ uIcc 0 t) : HasDerivAt b (K u (b u)) u := by
    have hd := ((hK.clm_apply hec).integral_hasStrictDerivAt 0 u).hasDerivAt.const_add x
    change HasDerivAt b (K u (e u)) u at hd
    rwa [he u hu, ← hb u hu] at hd
  have hbc : Continuous b := continuous_const.add
    (intervalIntegral.continuous_primitive
      (fun a c => (hK.clm_apply hec).intervalIntegrable a c) 0)
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun u => (hg u).continuousAt
  have hlip (u : ℝ) : LipschitzWith L (K u) :=
    (K u).lipschitzWith.weaken (by exact_mod_cast hL u)
  have hb0 : b 0 = g 0 := by simp [b, hg0]
  rw [← hb t right_mem_uIcc]
  rcases le_total 0 t with ht0 | ht0
  · have heq := ODE_solution_unique_of_mem_Icc_right
      (v := fun u y => K u y) (s := fun _ => univ)
      (a := 0) (b := t) (fun u _ => (hlip u).lipschitzOnWith)
      hbc.continuousOn
      (fun u hu => (hb' u
        (by simpa [uIcc_of_le ht0] using Ico_subset_Icc_self hu)).hasDerivWithinAt)
      (fun _ _ => mem_univ _) hgc.continuousOn
      (fun u _ => (hg u).hasDerivWithinAt) (fun _ _ => mem_univ _) hb0
    exact heq ⟨ht0, le_rfl⟩
  · have heq := ODE_solution_unique_of_mem_Icc_left
      (v := fun u y => K u y) (s := fun _ => univ)
      (a := t) (b := 0) (fun u _ => (hlip u).lipschitzOnWith)
      hbc.continuousOn
      (fun u hu => (hb' u
        (by simpa [uIcc_of_ge ht0] using Ioc_subset_Icc_self hu)).hasDerivWithinAt)
      (fun _ _ => mem_univ _) hgc.continuousOn
      (fun u _ => (hg u).hasDerivWithinAt) (fun _ _ => mem_univ _) hb0
    exact heq ⟨le_rfl, ht0⟩

/-- An arbitrary integral solution agrees with the differentiable solution on every interval
where its integrand is integrable. Elsewhere it equals the initial value, so the integrand is
a measurable piecewise combination of two continuous functions and is integrable everywhere. -/
private theorem variational_integral_unique (K : ℝ → (E →L[ℝ] E))
    (hK : Continuous K) {L : ℝ≥0} (hL : ∀ s, ‖K s‖ ≤ L) (x : E)
    {f g : ℝ → E} (hf : ∀ t, f t = x + ∫ s in (0 : ℝ)..t, K s (f s))
    (hg0 : g 0 = x) (hg : ∀ t, HasDerivAt g (K t (g t)) t) : f = g := by
  classical
  let S : Set ℝ := {t | IntervalIntegrable (fun s => K s (f s)) volume 0 t}
  have hS : OrdConnected S := by
    constructor
    intro a ha b hb t ht
    exact ha.trans ((ha.symm.trans hb).mono_set
      (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc ht)))
  have he : f = S.piecewise g (fun _ => x) := by
    funext t
    by_cases ht : t ∈ S
    · simp only [Set.piecewise, ht, ↓reduceIte]
      exact variational_eq_of_integrable K hK hL x hf hg0 hg t ht
    · simp only [Set.piecewise, ht, ↓reduceIte]
      rw [hf t, intervalIntegral.integral_undef ht, add_zero]
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun u => (hg u).continuousAt
  have hint (t : ℝ) : IntervalIntegrable (fun s => K s (f s)) volume 0 t := by
    have he' : (fun s => K s (f s)) =
        S.piecewise (fun s => K s (g s)) (fun s => K s x) := by
      funext s
      calc
        K s (f s) = K s (S.piecewise g (fun _ => x) s) :=
          congrArg (K s) (congrFun he s)
        _ = _ := by by_cases hs : s ∈ S <;> simp [hs]
    rw [he', intervalIntegrable_iff']
    exact Integrable.piecewise hS.measurableSet
      ((hK.clm_apply hgc).integrableOn_uIcc).integrableOn
      ((hK.clm_apply continuous_const).integrableOn_uIcc).integrableOn
  funext t
  exact variational_eq_of_integrable K hK hL x hf hg0 hg t (hint t)

private theorem variational_exists_unique_integral (K : ℝ → (E →L[ℝ] E))
    (hK : Continuous K) {L : ℝ≥0} (hL : ∀ s, ‖K s‖ ≤ L) (x : E) :
    ∃! f : ℝ → E, ∀ t, f t = x + ∫ s in (0 : ℝ)..t, K s (f s) := by
  obtain ⟨f, hf0, hf'⟩ := variational_exists_global K hK hL x
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun t => (hf' t).continuousAt
  refine ⟨f, fun t => ?_, fun g hg => variational_integral_unique K hK hL x hg hf0 hf'⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hf' s)
    ((hK.clm_apply hc).intervalIntegrable 0 t), hf0]
  abel

/-- lem:flow-variational: existence and uniqueness of the solution of the variational
 equation along the trajectory through `x`. -/
theorem exists_unique_variationalMatrix {X : E → E} {L : ℝ≥0} {M : ℝ}
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) (hX1 : ContDiff ℝ 1 X) (x : E) :
    ∃! A : ℝ → (E →L[ℝ] E), ∀ t : ℝ,
      A t = ContinuousLinearMap.id ℝ E +
        ∫ s in (0 : ℝ)..t, (fderiv ℝ X (globalFlow X hX hM s x)).comp (A s) := by
  let K : ℝ → (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    fun s => ContinuousLinearMap.compL ℝ E E E (fderiv ℝ X (globalFlow X hX hM s x))
  have hflow : Continuous (fun s => globalFlow X hX hM s x) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_globalFlow hX hM x t).continuousAt
  have hK : Continuous K := (ContinuousLinearMap.compL ℝ E E E).continuous.comp
    ((hX1.continuous_fderiv one_ne_zero).comp hflow)
  have hL (s : ℝ) : ‖K s‖ ≤ L := by
    calc
      ‖K s‖ ≤ ‖ContinuousLinearMap.compL ℝ E E E‖ *
          ‖fderiv ℝ X (globalFlow X hX hM s x)‖ :=
        (ContinuousLinearMap.compL ℝ E E E).le_opNorm _
      _ ≤ 1 * (L : ℝ) := mul_le_mul (ContinuousLinearMap.norm_compL_le ℝ E E E)
        (norm_fderiv_le_of_lipschitz ℝ hX) (norm_nonneg _) zero_le_one
      _ = L := one_mul _
  exact variational_exists_unique_integral K hK hL (ContinuousLinearMap.id ℝ E)

/-- The selected solution of the variational integral equation. -/
noncomputable def variationalMatrix (X : E → E) {L : ℝ≥0} {M : ℝ}
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) (hX1 : ContDiff ℝ 1 X)
    (t : ℝ) (x : E) : E →L[ℝ] E :=
  Classical.choose (exists_unique_variationalMatrix hX hM hX1 x) t

/-- The selected variational matrix satisfies its integral equation. -/
theorem variationalMatrix_integral {X : E → E} {L : ℝ≥0} {M : ℝ}
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) (hX1 : ContDiff ℝ 1 X)
    (t : ℝ) (x : E) :
    variationalMatrix X hX hM hX1 t x = ContinuousLinearMap.id ℝ E +
      ∫ s in (0 : ℝ)..t, (fderiv ℝ X (globalFlow X hX hM s x)).comp
        (variationalMatrix X hX hM hX1 s x) :=
  (Classical.choose_spec (exists_unique_variationalMatrix hX hM hX1 x)).1 t

/-- The variational matrix at time zero is the identity. -/
@[simp] theorem variationalMatrix_zero {X : E → E} {L : ℝ≥0} {M : ℝ}
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) (hX1 : ContDiff ℝ 1 X) (x : E) :
    variationalMatrix X hX hM hX1 0 x = ContinuousLinearMap.id ℝ E := by
  simpa using variationalMatrix_integral hX hM hX1 0 x

/-- Every solution of the variational integral equation is the selected one. -/
theorem variationalMatrix_unique {X : E → E} {L : ℝ≥0} {M : ℝ}
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) (hX1 : ContDiff ℝ 1 X)
    {A : ℝ → (E →L[ℝ] E)} (x : E)
    (hA : ∀ t, A t = ContinuousLinearMap.id ℝ E +
      ∫ s in (0 : ℝ)..t, (fderiv ℝ X (globalFlow X hX hM s x)).comp (A s)) :
    A = fun t => variationalMatrix X hX hM hX1 t x :=
  (Classical.choose_spec (exists_unique_variationalMatrix hX hM hX1 x)).2 A hA

private theorem variational_continuous_fixedPoint {P F : Type*}
    [TopologicalSpace P] [MetricSpace F] {C : ℝ≥0} (G : P → F → F)
    (hG : Continuous (Function.uncurry G)) (hC : ∀ p, ContractingWith C (G p))
    (f : P → F) (hf : ∀ p, G p (f p) = f p) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  have hc : Continuous (fun q => dist (f p) (G q (f p)) / (1 - (C : ℝ))) :=
    (continuous_const.dist (hG.comp (continuous_id.prodMk continuous_const))).div_const _
  have hz : dist (f p) (G p (f p)) / (1 - (C : ℝ)) = 0 := by rw [hf p]; simp
  have hh := hc.continuousAt.tendsto (x := p)
  rw [hz] at hh
  filter_upwards [hh.eventually (gt_mem_nhds hε)] with q hq
  exact lt_of_le_of_lt (by simpa only [dist_comm] using
    (hC q).dist_le_of_fixedPoint (f p) (hf q)) hq

omit [CompleteSpace E] in
private theorem variationalPicard_continuous {P : Type*} [TopologicalSpace P]
    (T : ℝ≥0) (K : P → ℝ → (E →L[ℝ] E))
    (hK : Continuous (Function.uncurry K)) (x : E) :
    Continuous (fun p : P × C(Icc (-(T : ℝ)) T, E) =>
      variationalPicard T (K p.1) (hK.comp (continuous_const.prodMk continuous_id)) x p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : (P × C(Icc (-(T : ℝ)) T, E)) × Icc (-(T : ℝ)) T =>
    x + ∫ s in (0 : ℝ)..p.2.1, K p.1.1 s (variationalExtend T p.1.2 s))
  apply continuous_const.add
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
  · apply Continuous.clm_apply
    · exact hK.comp ((continuous_fst.fst.fst).prodMk continuous_snd)
    · change Continuous (fun p : ((P × C(Icc (-(T : ℝ)) T, E)) ×
          Icc (-(T : ℝ)) T) × ℝ => p.1.1.2
          (projIcc (-(T : ℝ)) T (le_trans (neg_nonpos.mpr T.coe_nonneg) T.coe_nonneg) p.2))
      exact continuous_eval.comp ((continuous_fst.fst.snd).prodMk
        ((continuous_projIcc
          (h := le_trans (neg_nonpos.mpr T.coe_nonneg) T.coe_nonneg)).comp continuous_snd))
  · exact continuous_subtype_val.comp continuous_snd

/-- The factorial estimate gives a common contracting iterate on each compact time interval;
continuous dependence of its fixed point gives joint continuity with respect to parameters. -/
private theorem variational_continuous_solution {P : Type*} [TopologicalSpace P]
    (K : P → ℝ → (E →L[ℝ] E)) (hK : Continuous (Function.uncurry K))
    {L : ℝ≥0} (hL : ∀ p s, ‖K p s‖ ≤ L) (x : E) (f : P → ℝ → E)
    (hf0 : ∀ p, f p 0 = x) (hf' : ∀ p t, HasDerivAt (f p) (K p t (f p t)) t) :
    Continuous (fun p : ℝ × P => f p.2 p.1) := by
  have hfc (p : P) : Continuous (f p) :=
    continuous_iff_continuousAt.mpr fun t => (hf' p t).continuousAt
  have hkc (p : P) : Continuous (K p) := hK.comp (continuous_const.prodMk continuous_id)
  have hint (p : P) (t : ℝ) : f p t = x + ∫ s in (0 : ℝ)..t, K p s (f p s) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hf' p s)
      (((hkc p).clm_apply (hfc p)).intervalIntegrable 0 t), hf0 p]
    abel
  have hc (T : ℝ≥0) : Continuous (fun p =>
      (⟨fun t : Icc (-(T : ℝ)) T => f p t, (hfc p).comp continuous_subtype_val⟩ :
        C(Icc (-(T : ℝ)) T, E))) := by
    let a (p : P) : C(Icc (-(T : ℝ)) T, E) :=
      ⟨fun t => f p t, (hfc p).comp continuous_subtype_val⟩
    let F (p : P) := variationalPicard T (K p) (hkc p) x
    have hF : Continuous (Function.uncurry F) := variationalPicard_continuous T K hK x
    have ha (p : P) : Function.IsFixedPt (F p) (a p) := by
      ext t
      change x + (∫ s in (0 : ℝ)..t.1, K p s (variationalExtend T (a p) s)) = f p t.1
      rw [hint p t.1]
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s ∈ Icc (-(T : ℝ)) T :=
        (uIcc_subset_Icc ⟨neg_nonpos.mpr T.coe_nonneg, T.coe_nonneg⟩ t.2)
          hs
      exact congrArg (K p s) (variationalExtend_of_mem T (a p) s hs')
    obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop ((L : ℝ) * T)
      |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
    let C : ℝ≥0 := ⟨((L : ℝ) * T) ^ n / n !, by positivity⟩
    have hcontract (p : P) : ContractingWith C (F p)^[n] := by
      refine ⟨hn, LipschitzWith.of_dist_le_mul fun g h => ?_⟩
      apply (ContinuousMap.dist_le (by positivity)).mpr
      intro t
      apply (variationalPicard_iterate_dist T (K p) (hkc p) (hL p) x g h n t).trans
      change ((L : ℝ) * |t.1|) ^ n / n ! * dist g h ≤
        ((L : ℝ) * T) ^ n / n ! * dist g h
      gcongr
      exact abs_le.mpr t.2
    have hi (m : ℕ) : Continuous (fun p : P × C(Icc (-(T : ℝ)) T, E) =>
        (F p.1)^[m] p.2) := by
      induction m with
      | zero => exact continuous_snd
      | succ m hm =>
        simpa only [Function.iterate_succ_apply', Function.uncurry, Function.comp_def] using
          hF.comp (continuous_fst.prodMk hm)
    exact variational_continuous_fixedPoint (fun p => (F p)^[n]) (hi n) hcontract a
      (fun p => (ha p).iterate n)
  apply continuous_iff_continuousAt.mpr
  intro p
  let T : ℝ≥0 := ⟨|p.1| + 1, by positivity⟩
  have ht : |p.1| < T := by change |p.1| < |p.1| + 1; linarith
  have hh : Continuous (fun q : ℝ × P =>
      variationalExtend T
        ⟨fun t : Icc (-(T : ℝ)) T => f q.2 t, (hfc q.2).comp continuous_subtype_val⟩ q.1) :=
    continuous_eval.comp ((hc T |>.comp continuous_snd).prodMk
      ((continuous_projIcc
        (h := le_trans (neg_nonpos.mpr T.coe_nonneg) T.coe_nonneg)).comp continuous_fst))
  apply hh.continuousAt.congr_of_eventuallyEq
  filter_upwards [(continuous_fst.abs.continuousAt (x := p)).eventually
    (gt_mem_nhds ht)] with q hq
  exact (variationalExtend_of_mem T
    ⟨fun t : Icc (-(T : ℝ)) T => f q.2 t, (hfc q.2).comp continuous_subtype_val⟩ q.1
    ⟨(abs_lt.mp hq).1.le, (abs_lt.mp hq).2.le⟩).symm

private theorem variational_dist_globalFlow_le {X : E → E} {L : ℝ≥0} {M : ℝ}
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) (t : ℝ) (x y : E) :
    dist (globalFlow X hX hM t x) (globalFlow X hX hM t y) ≤
      dist x y * Real.exp ((L : ℝ) * |t|) := by
  have hc (x : E) : Continuous (fun s => globalFlow X hX hM s x) :=
    continuous_iff_continuousAt.mpr fun s => (hasDerivAt_globalFlow hX hM x s).continuousAt
  rcases le_total 0 t with ht | ht
  · have hh := dist_le_of_trajectories_ODE (v := fun _ => X)
      (a := 0) (b := t) (fun _ => hX) (hc x).continuousOn
      (fun s _ => (hasDerivAt_globalFlow hX hM x s).hasDerivWithinAt) (hc y).continuousOn
      (fun s _ => (hasDerivAt_globalFlow hX hM y s).hasDerivWithinAt)
      (by simp : dist (globalFlow X hX hM 0 x) (globalFlow X hX hM 0 y) ≤ dist x y)
      t ⟨ht, le_rfl⟩
    simpa only [sub_zero, abs_of_nonneg ht] using hh
  · have hd (x : E) (s : ℝ) : HasDerivAt (fun u => globalFlow X hX hM (-u) x)
        (-X (globalFlow X hX hM (-s) x)) s := by
      simpa [Function.comp_def] using
        (hasDerivAt_globalFlow hX hM x (-s)).scomp s (hasDerivAt_neg s)
    have hh := dist_le_of_trajectories_ODE (v := fun _ z => -X z)
      (a := 0) (b := -t) (fun _ => hX.neg) ((hc x).comp continuous_neg).continuousOn
      (fun s _ => (hd x s).hasDerivWithinAt) ((hc y).comp continuous_neg).continuousOn
      (fun s _ => (hd y s).hasDerivWithinAt)
      (by simp : dist (globalFlow X hX hM (-0) x) (globalFlow X hX hM (-0) y) ≤ dist x y)
      (-t) ⟨neg_nonneg.mpr ht, le_rfl⟩
    simpa only [Function.comp_apply, neg_neg, sub_zero, abs_of_nonpos ht] using hh

private theorem variational_continuous_globalFlow {X : E → E} {L : ℝ≥0} {M : ℝ}
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) :
    Continuous (fun p : ℝ × E => globalFlow X hX hM p.1 p.2) := by
  have hc (x : E) : Continuous (fun s => globalFlow X hX hM s x) :=
    continuous_iff_continuousAt.mpr fun s => (hasDerivAt_globalFlow hX hM x s).continuousAt
  apply continuous_iff_continuousAt.mpr
  intro p
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  have hh : Continuous (fun q : ℝ × E => dist q.2 p.2 * Real.exp ((L : ℝ) * |q.1|) +
      dist (globalFlow X hX hM q.1 p.2) (globalFlow X hX hM p.1 p.2)) := by
    fun_prop
  have hz : dist p.2 p.2 * Real.exp ((L : ℝ) * |p.1|) +
      dist (globalFlow X hX hM p.1 p.2) (globalFlow X hX hM p.1 p.2) = 0 := by simp
  have ht := hh.continuousAt.tendsto (x := p)
  rw [hz] at ht
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with q hq
  apply lt_of_le_of_lt (dist_triangle _ (globalFlow X hX hM q.1 p.2) _) ?_
  exact lt_of_le_of_lt (add_le_add (variational_dist_globalFlow_le hX hM q.1 q.2 p.2) le_rfl) hq

/-- The variational matrix depends continuously on time and the initial point. -/
theorem continuous_variationalMatrix {X : E → E} {L : ℝ≥0} {M : ℝ}
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) (hX1 : ContDiff ℝ 1 X) :
    Continuous (fun p : ℝ × E => variationalMatrix X hX hM hX1 p.1 p.2) := by
  let K : E → ℝ → (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    fun x s => ContinuousLinearMap.compL ℝ E E E (fderiv ℝ X (globalFlow X hX hM s x))
  have hK : Continuous (Function.uncurry K) :=
    (ContinuousLinearMap.compL ℝ E E E).continuous.comp
      ((hX1.continuous_fderiv one_ne_zero).comp
        ((variational_continuous_globalFlow hX hM).comp continuous_swap))
  have hL (x : E) (s : ℝ) : ‖K x s‖ ≤ L := by
    calc
      ‖K x s‖ ≤ ‖ContinuousLinearMap.compL ℝ E E E‖ *
          ‖fderiv ℝ X (globalFlow X hX hM s x)‖ :=
        (ContinuousLinearMap.compL ℝ E E E).le_opNorm _
      _ ≤ 1 * (L : ℝ) := mul_le_mul (ContinuousLinearMap.norm_compL_le ℝ E E E)
        (norm_fderiv_le_of_lipschitz ℝ hX) (norm_nonneg _) zero_le_one
      _ = L := one_mul _
  apply variational_continuous_solution K hK hL (ContinuousLinearMap.id ℝ E)
    (fun x t => variationalMatrix X hX hM hX1 t x) (fun x => variationalMatrix_zero hX hM hX1 x)
  intro x t
  have hkc : Continuous (K x) := hK.comp (continuous_const.prodMk continuous_id)
  obtain ⟨f, hf0, hf'⟩ := variational_exists_global (K x) hkc (hL x) (ContinuousLinearMap.id ℝ E)
  have he : (fun t => variationalMatrix X hX hM hX1 t x) = f :=
    variational_integral_unique (K x) hkc (hL x) (ContinuousLinearMap.id ℝ E)
      (fun t => variationalMatrix_integral hX hM hX1 t x) hf0 hf'
  change HasDerivAt (fun t => variationalMatrix X hX hM hX1 t x)
    (K x t (variationalMatrix X hX hM hX1 t x)) t
  simpa only [← he] using hf' t

-- END lem:flow-variational

end LiquidDrop
