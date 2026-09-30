module

public import NoCompromise.Flow.FlowBox

@[expose] public section

/-!
# thm:flow-Ck: `C^k` and smooth dependence of the global flow

For a bounded, globally Lipschitz field `X` on a finite-dimensional real normed space
(the ambient `ℝⁿ` of the blueprint), if `X` is `C^k` with `1 ≤ k ≤ ∞` then the joint map
`(t, x) ↦ Φ_t(x)` is `C^k`.

The proof is the induction of the blueprint. The joint derivative of the flow is
`(s, v) ↦ s X(Φ_t x) + A(t, x) v` (`hasFDerivAt_globalFlow_uncurry`), so it suffices that
`X ∘ Φ` and the variational matrix `A` are `C^{k-1}`. For `A` we use that
`(Φ_t x, A(t, x))` is the trajectory through `(x, I)` of the augmented field
`(y, B) ↦ (X y, DX(y) ∘ B)` on `E × (E →L[ℝ] E)`, which is `C^{k-1}`. Near a compact piece
of that trajectory it agrees with a compactly supported `C^{k-1}` field, whose flow is
`C^{k-1}` by the induction hypothesis (applied on the larger finite-dimensional space).
-/

open Set Filter
open scoped NNReal Topology

namespace LiquidDrop

universe u

section Augmented

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {X : E → E} {L : ℝ≥0} {M : ℝ}

/-- thm:flow-Ck, inductive step for the variational matrix: if every bounded globally
Lipschitz `C^n` field on `E × (E →L[ℝ] E)` has a jointly `C^n` flow, and `X` and `DX` are
`C^n` (`1 ≤ n`), then `(t, x) ↦ A(t, x)` is `C^n`. -/
theorem contDiff_variationalMatrix_of_augmented
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) (hX1 : ContDiff ℝ 1 X)
    {n : ℕ∞} (hn : 1 ≤ n) (hXn : ContDiff ℝ n X) (hDXn : ContDiff ℝ n (fderiv ℝ X))
    (hflow : ∀ (Y : E × (E →L[ℝ] E) → E × (E →L[ℝ] E)) (L' : ℝ≥0) (M' : ℝ)
      (hY : LipschitzWith L' Y) (hM' : ∀ z, ‖Y z‖ ≤ M'), ContDiff ℝ n Y →
      ContDiff ℝ n (fun q : ℝ × (E × (E →L[ℝ] E)) => globalFlow Y hY hM' q.1 q.2)) :
    ContDiff ℝ n (fun q : ℝ × E => variationalMatrix X hX hM hX1 q.1 q.2) := by
  rw [contDiff_iff_contDiffAt]
  intro q₀
  set T : ℝ := |q₀.1| + 1 with hT
  have hT0 : 0 < T := by positivity
  let c : ℝ × E → E × (E →L[ℝ] E) := fun q =>
    (globalFlow X hX hM q.1 q.2, variationalMatrix X hX hM hX1 q.1 q.2)
  have hc : Continuous c :=
    (contDiff_one_globalFlow_uncurry hX hM hX1).continuous.prodMk
      (continuous_variationalMatrix hX hM hX1)
  have hKc : IsCompact (c '' (Icc (-T) T ×ˢ Metric.closedBall q₀.2 1)) :=
    (isCompact_Icc.prod (isCompact_closedBall _ _)).image hc
  obtain ⟨R, hR⟩ := hKc.isBounded.subset_closedBall 0
  let f : ContDiffBump (0 : E × (E →L[ℝ] E)) :=
    ⟨max R 0 + 1, max R 0 + 2, by positivity, by linarith⟩
  let G : E × (E →L[ℝ] E) → E × (E →L[ℝ] E) := fun z => (X z.1, (fderiv ℝ X z.1).comp z.2)
  let Y : E × (E →L[ℝ] E) → E × (E →L[ℝ] E) := fun z => f z • G z
  have hG : ContDiff ℝ n G :=
    (hXn.comp contDiff_fst).prodMk ((hDXn.comp contDiff_fst).clm_comp contDiff_snd)
  have hY : ContDiff ℝ n Y := f.contDiff.smul hG
  have hYc : HasCompactSupport Y := f.hasCompactSupport.smul_right
  have hn' : (1 : WithTop ℕ∞) ≤ n := by exact_mod_cast hn
  obtain ⟨L', M', hL', hM'⟩ := lipschitz_bounded_of_hasCompactSupport (hY.of_le hn') hYc
  have hΨ := hflow Y L' M' hL' hM' hY
  have hYG : ∀ q ∈ Icc (-T) T ×ˢ Metric.closedBall q₀.2 1, Y (c q) = G (c q) := by
    intro q hq
    have hmem : c q ∈ Metric.closedBall (0 : E × (E →L[ℝ] E)) f.rIn := by
      have h1 := hR (mem_image_of_mem c hq)
      rw [Metric.mem_closedBall] at h1 ⊢
      change _ ≤ max R 0 + 1
      linarith [le_max_left R 0]
    change f (c q) • G (c q) = G (c q)
    rw [f.one_of_mem_closedBall hmem, one_smul]
  have hagree : ∀ x ∈ Metric.closedBall q₀.2 1, ∀ t ∈ Icc (-T) T,
      globalFlow Y hL' hM' t (x, ContinuousLinearMap.id ℝ E) = c (t, x) := by
    intro x hx t ht
    refine integralCurve_unique_of_contDiffOn isOpen_univ (hY.of_le hn').contDiffOn
      ordConnected_Icc (t₀ := 0) ⟨by linarith, by linarith⟩
      (γ₁ := fun s => globalFlow Y hL' hM' s (x, ContinuousLinearMap.id ℝ E))
      (γ₂ := fun s => c (s, x))
      (fun s _ => ⟨mem_univ _, hasDerivAt_globalFlow hL' hM' _ s⟩) ?_ ?_ ht
    · intro s hs
      refine ⟨mem_univ _, ?_⟩
      rw [hYG (s, x) ⟨hs, hx⟩]
      exact (hasDerivAt_globalFlow hX hM x s).prodMk (hasDerivAt_variationalMatrix hX hM hX1 x s)
    · simp [c]
  have hev : (fun q : ℝ × E =>
      (globalFlow Y hL' hM' q.1 (q.2, ContinuousLinearMap.id ℝ E)).2) =ᶠ[𝓝 q₀]
      fun q : ℝ × E => variationalMatrix X hX hM hX1 q.1 q.2 := by
    have hnhds : Ioo (-T) T ×ˢ Metric.ball q₀.2 1 ∈ 𝓝 q₀ :=
      prod_mem_nhds (Ioo_mem_nhds (by linarith [neg_abs_le q₀.1]) (by linarith [le_abs_self q₀.1]))
        (Metric.ball_mem_nhds _ one_pos)
    filter_upwards [hnhds] with q hq
    rw [hagree q.2 (Metric.ball_subset_closedBall hq.2) q.1 (Ioo_subset_Icc_self hq.1)]
  have hsmooth : ContDiff ℝ n (fun q : ℝ × E =>
      (globalFlow Y hL' hM' q.1 (q.2, ContinuousLinearMap.id ℝ E)).2) :=
    contDiff_snd.comp (hΨ.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)))
  exact hsmooth.contDiffAt.congr_of_eventuallyEq hev.symm

end Augmented

/-- thm:flow-Ck at finite order `k + 1`, by induction on `k` over all finite-dimensional
spaces at once. -/
theorem contDiff_nat_succ_globalFlow_uncurry : ∀ k : ℕ, ∀ {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    {X : E → E} {L : ℝ≥0} {M : ℝ} (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M),
    ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) X →
    ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞)
      (fun q : ℝ × E => globalFlow X hX hM q.1 q.2) := by
  intro k
  induction k with
  | zero =>
    intro E _ _ _ _ X L M hX hM hXk
    simpa using contDiff_one_globalFlow_uncurry hX hM (by simpa using hXk)
  | succ k ih =>
    intro E _ _ _ _ X L M hX hM hXk
    have hX1 : ContDiff ℝ 1 X := hXk.of_le (by norm_cast; omega)
    have hXk1 : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) X := hXk.of_le (by norm_cast; omega)
    have hDX : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fderiv ℝ X) := by
      have h := hXk
      rw [show ((k + 1 + 1 : ℕ) : WithTop ℕ∞) = ((k + 1 : ℕ) : WithTop ℕ∞) + 1 by
        push_cast; rfl, contDiff_succ_iff_fderiv] at h
      exact h.2.2
    have hΦ := ih hX hM hXk1
    have hA := contDiff_variationalMatrix_of_augmented (n := ((k + 1 : ℕ) : ℕ∞)) hX hM hX1
      (by norm_cast; omega) hXk1 hDX (fun Y L' M' hY hM' hYk => ih hY hM' hYk)
    have hd := hasFDerivAt_globalFlow_uncurry hX hM hX1
    rw [show ((k + 1 + 1 : ℕ) : WithTop ℕ∞) = ((k + 1 : ℕ) : WithTop ℕ∞) + 1 by
      push_cast; rfl, contDiff_succ_iff_fderiv]
    refine ⟨fun q => (hd q).differentiableAt, by simp, ?_⟩
    have heq := funext fun q => (hd q).fderiv
    rw [heq]
    exact ((ContinuousLinearMap.smulRightL ℝ (ℝ × E) E
        (ContinuousLinearMap.fst ℝ ℝ E)).contDiff.comp (hXk1.comp hΦ)).add
      (hA.clm_comp contDiff_const)

section Main

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {X : E → E} {L : ℝ≥0} {M : ℝ}

/-- thm:flow-Ck: for a bounded globally Lipschitz field of class `C^k`, `1 ≤ k ≤ ∞`, on a
finite-dimensional real space, the flow `(t, x) ↦ Φ_t(x)` is jointly `C^k`. -/
theorem contDiff_globalFlow_uncurry (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M)
    {k : ℕ∞} (hk : 1 ≤ k) (hXk : ContDiff ℝ k X) :
    ContDiff ℝ k (fun q : ℝ × E => globalFlow X hX hM q.1 q.2) := by
  induction k using ENat.recTopCoe with
  | top =>
    rw [contDiff_infty] at hXk ⊢
    intro m
    have h := contDiff_nat_succ_globalFlow_uncurry m hX hM (hXk (m + 1))
    exact h.of_le (by norm_cast; omega)
  | coe m =>
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by
      have : 1 ≤ m := by exact_mod_cast hk
      omega⟩
    exact contDiff_nat_succ_globalFlow_uncurry j hX hM hXk

/-- thm:flow-Ck: "in particular a smooth vector field has a smooth flow". -/
theorem contDiff_smooth_globalFlow_uncurry (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M)
    (hXs : ContDiff ℝ (⊤ : ℕ∞) X) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × E => globalFlow X hX hM q.1 q.2) :=
  contDiff_globalFlow_uncurry hX hM le_top hXs

/-- thm:flow-Ck: each time-`t` map of a `C^k` field (`1 ≤ k ≤ ∞`) is a `C^k`
diffeomorphism, with inverse the time-`(-t)` map. -/
theorem contDiff_globalFlow (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M)
    {k : ℕ∞} (hk : 1 ≤ k) (hXk : ContDiff ℝ k X) (t : ℝ) :
    ContDiff ℝ k (globalFlow X hX hM t) ∧ ContDiff ℝ k (globalFlow X hX hM (-t)) ∧
      (∀ x, globalFlow X hX hM (-t) (globalFlow X hX hM t x) = x) ∧
      (∀ x, globalFlow X hX hM t (globalFlow X hX hM (-t) x) = x) := by
  have hΦ := contDiff_globalFlow_uncurry hX hM hk hXk
  refine ⟨hΦ.comp (contDiff_const.prodMk contDiff_id),
    hΦ.comp (contDiff_const.prodMk contDiff_id), fun x => globalFlow_neg_left hX hM t x,
    fun x => by simpa using globalFlow_neg_left hX hM (-t) x⟩

end Main

end LiquidDrop
