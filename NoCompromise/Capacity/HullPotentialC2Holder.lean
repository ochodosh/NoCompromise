module

public import NoCompromise.Capacity.HullPotentialBoundaryC2
public import NoCompromise.Elliptic.HolderInterpolation

@[expose] public section

/-!
# `thm:capacitary-potential`: `u ∈ C^{2,α}_loc(closure (ℝ³ ∖ K))` for the filled hull

For `K = filledHull Ω`, `Ω` a bounded open set with `C³` boundary containing `0`, `u` a
capacitary potential of `K` and `0 < α < 1`: every `C²` function `g` on `ℝ³` with `u = g` on
`closure Kᶜ` (one exists by `hullPotentialBoundaryC2`) has `g`, `∇g` and `∇²g` bounded and
`α`-Hölder on `U ∩ closure Kᶜ` for a neighbourhood `U` of each point of `closure Kᶜ`
(`HasC2HolderOn α g (U ∩ closure Kᶜ)`). On `closure Kᶜ` the derivatives of `g` up to order two
are the continuous extensions of those of `u` from `Kᶜ`, so this is the literal clause
`u ∈ C^{2,α}_loc(closure (ℝ³ ∖ K))`.

Near `p ∈ ∂K` the shear flattening `Θ` of `hullPotential_local_c2_extension` and
`boundary_c2a_local_of_h1` (now with the given `α` in place of `1/2`) give `u = v ∘ Θ⁻¹` at the
points `z ∉ K` with `Θ⁻¹ z` in the reflection slab, where `Θ⁻¹` is `C³` and `v` is `C²` on the
open upper half slab with bounded, `α`-Hölder Hessian entries
(`hullPotential_local_flattening`). The second-order chain rule
`∇²(v ∘ φ)(h, k) = ∇v(φ)(∇²φ(h, k)) + ∇²v(φ)(∇φ h, ∇φ k)` (`fderiv_fderiv_comp_apply`) and
elementary product and composition rules for bounded Hölder functions (`BoundedHolderOn`) give
the Hölder bound on `U ∩ Kᶜ`; at points of `Kᶜ` it follows from smoothness of `u`; continuity
of `∇²g` carries it to `U ∩ closure Kᶜ`. The partition-of-unity gluing is not revisited: the
estimate holds for every `C²` extension, since on `closure Kᶜ` its derivatives are determined
by `u`.
-/

noncomputable section
open MeasureTheory Set Filter Metric Topology InnerProductSpace ContinuousLinearMap
open scoped Gradient

namespace LiquidDrop

section BoundedHolder

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedAddCommGroup H]

/-- `f` is bounded and `α`-Hölder on `S`, with explicit nonnegative constants:
`‖f x‖ ≤ M` and `‖f x - f y‖ ≤ L ‖x - y‖^α` for `x, y ∈ S`. -/
def BoundedHolderOn (α : ℝ) (f : E → F) (S : Set E) : Prop :=
  ∃ M L : ℝ, 0 ≤ M ∧ 0 ≤ L ∧ (∀ x ∈ S, ‖f x‖ ≤ M) ∧
    ∀ x ∈ S, ∀ y ∈ S, ‖f x - f y‖ ≤ L * ‖x - y‖ ^ α

lemma BoundedHolderOn.mono {α : ℝ} {f : E → F} {S T : Set E} (h : BoundedHolderOn α f S)
    (hT : T ⊆ S) : BoundedHolderOn α f T := by
  obtain ⟨M, L, hM, hL, hb, hh⟩ := h
  exact ⟨M, L, hM, hL, fun x hx => hb x (hT hx), fun x hx y hy => hh x (hT hx) y (hT hy)⟩

lemma BoundedHolderOn.congr {α : ℝ} {f g : E → F} {S : Set E} (h : BoundedHolderOn α f S)
    (hfg : EqOn f g S) : BoundedHolderOn α g S := by
  obtain ⟨M, L, hM, hL, hb, hh⟩ := h
  refine ⟨M, L, hM, hL, fun x hx => ?_, fun x hx y hy => ?_⟩
  · rw [← hfg hx]; exact hb x hx
  · rw [← hfg hx, ← hfg hy]; exact hh x hx y hy

lemma BoundedHolderOn.add {α : ℝ} {f g : E → F} {S : Set E} (hf : BoundedHolderOn α f S)
    (hg : BoundedHolderOn α g S) : BoundedHolderOn α (fun x => f x + g x) S := by
  obtain ⟨M, L, hM, hL, hb, hh⟩ := hf
  obtain ⟨M', L', hM', hL', hb', hh'⟩ := hg
  refine ⟨M + M', L + L', add_nonneg hM hM', add_nonneg hL hL',
    fun x hx => (norm_add_le _ _).trans (add_le_add (hb x hx) (hb' x hx)), fun x hx y hy => ?_⟩
  have he : f x + g x - (f y + g y) = (f x - f y) + (g x - g y) := by abel
  rw [he]
  calc ‖(f x - f y) + (g x - g y)‖ ≤ ‖f x - f y‖ + ‖g x - g y‖ := norm_add_le _ _
    _ ≤ L * ‖x - y‖ ^ α + L' * ‖x - y‖ ^ α := add_le_add (hh x hx y hy) (hh' x hx y hy)
    _ = (L + L') * ‖x - y‖ ^ α := by ring

lemma boundedHolderOn_const {α : ℝ} {S : Set E} (c : F) :
    BoundedHolderOn α (fun _ : E => c) S :=
  ⟨‖c‖, 0, norm_nonneg _, le_rfl, fun _ _ => le_rfl, fun _ _ _ _ => by simp⟩

/-- Pointwise application `x ↦ a x (b x)` of bounded Hölder families. -/
lemma BoundedHolderOn.clm_apply [NormedSpace ℝ F] [NormedSpace ℝ G] {α : ℝ}
    {a : E → F →L[ℝ] G} {b : E → F} {S : Set E} (ha : BoundedHolderOn α a S)
    (hb : BoundedHolderOn α b S) : BoundedHolderOn α (fun x => a x (b x)) S := by
  obtain ⟨M, L, hM, hL, hb1, hh1⟩ := ha
  obtain ⟨M', L', hM', hL', hb2, hh2⟩ := hb
  refine ⟨M * M', L * M' + M * L', mul_nonneg hM hM',
    add_nonneg (mul_nonneg hL hM') (mul_nonneg hM hL'),
    fun x hx => ((a x).le_opNorm _).trans (mul_le_mul (hb1 x hx) (hb2 x hx) (norm_nonneg _) hM),
    fun x hx y hy => ?_⟩
  have he : a x (b x) - a y (b y) = (a x - a y) (b x) + a y (b x - b y) := by
    rw [sub_apply, map_sub]; abel
  rw [he]
  have hr : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
  calc ‖(a x - a y) (b x) + a y (b x - b y)‖
        ≤ ‖(a x - a y) (b x)‖ + ‖a y (b x - b y)‖ := norm_add_le _ _
    _ ≤ ‖a x - a y‖ * ‖b x‖ + ‖a y‖ * ‖b x - b y‖ :=
        add_le_add ((a x - a y).le_opNorm _) ((a y).le_opNorm _)
    _ ≤ (L * ‖x - y‖ ^ α) * M' + M * (L' * ‖x - y‖ ^ α) :=
        add_le_add (mul_le_mul (hh1 x hx y hy) (hb2 x hx) (norm_nonneg _) (mul_nonneg hL hr))
          (mul_le_mul (hb1 y hy) (hh2 x hx y hy) (norm_nonneg _) hM)
    _ = (L * M' + M * L') * ‖x - y‖ ^ α := by ring

lemma BoundedHolderOn.comp_lipschitz {α : ℝ} {φ : E → F} {f : F → G} {S : Set E} {T : Set F}
    {Lφ : ℝ} (hα : 0 ≤ α) (hf : BoundedHolderOn α f T) (hST : MapsTo φ S T) (hLφ : 0 ≤ Lφ)
    (hφ : ∀ x ∈ S, ∀ y ∈ S, ‖φ x - φ y‖ ≤ Lφ * ‖x - y‖) :
    BoundedHolderOn α (fun x => f (φ x)) S := by
  obtain ⟨M, L, hM, hL, hb, hh⟩ := hf
  refine ⟨M, L * Lφ ^ α, hM, mul_nonneg hL (Real.rpow_nonneg hLφ α), fun x hx => hb _ (hST hx),
    fun x hx y hy => ?_⟩
  calc ‖f (φ x) - f (φ y)‖ ≤ L * ‖φ x - φ y‖ ^ α := hh _ (hST hx) _ (hST hy)
    _ ≤ L * (Lφ * ‖x - y‖) ^ α :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) (hφ x hx y hy) hα) hL
    _ = L * Lφ ^ α * ‖x - y‖ ^ α := by rw [Real.mul_rpow hLφ (norm_nonneg _)]; ring

/-- A Lipschitz function on a set of diameter at least bounded by `D` is bounded. -/
lemma exists_bound_of_lipschitzOn_diam {f : E → F} {S : Set E} {L D : ℝ} (hL : 0 ≤ L)
    (hl : ∀ x ∈ S, ∀ y ∈ S, ‖f x - f y‖ ≤ L * ‖x - y‖)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ D) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ S, ‖f x‖ ≤ M := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨0, le_rfl, fun x hx => hx.elim⟩
  · have hD : 0 ≤ D := by simpa using hdiam x₀ hx₀ x₀ hx₀
    refine ⟨‖f x₀‖ + L * D, add_nonneg (norm_nonneg _) (mul_nonneg hL hD), fun x hx => ?_⟩
    calc ‖f x‖ = ‖f x₀ + (f x - f x₀)‖ := by congr 1; abel
      _ ≤ ‖f x₀‖ + ‖f x - f x₀‖ := norm_add_le _ _
      _ ≤ ‖f x₀‖ + L * D := add_le_add le_rfl
          ((hl x hx x₀ hx₀).trans (mul_le_mul_of_nonneg_left (hdiam x hx x₀ hx₀) hL))

/-- A Lipschitz function on a set of bounded diameter is bounded and `α`-Hölder, `α ≤ 1`. -/
lemma boundedHolderOn_of_lipschitzOn {α : ℝ} {f : E → F} {S : Set E} {L D : ℝ}
    (hα1 : α ≤ 1) (hL : 0 ≤ L)
    (hl : ∀ x ∈ S, ∀ y ∈ S, ‖f x - f y‖ ≤ L * ‖x - y‖)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ D) : BoundedHolderOn α f S := by
  obtain ⟨M, hM, hb⟩ := exists_bound_of_lipschitzOn_diam hL hl hdiam
  have hD' : 0 ≤ max D 0 := le_max_right _ _
  refine ⟨M, L * max D 0 ^ (1 - α), hM, mul_nonneg hL (Real.rpow_nonneg hD' _), hb,
    fun x hx y hy => ?_⟩
  have hn := norm_nonneg (x - y)
  have hsplit : ‖x - y‖ = ‖x - y‖ ^ (1 - α) * ‖x - y‖ ^ α := by
    rw [← Real.rpow_add' hn (by rw [sub_add_cancel]; exact one_ne_zero), sub_add_cancel,
      Real.rpow_one]
  calc ‖f x - f y‖ ≤ L * ‖x - y‖ := hl x hx y hy
    _ = L * (‖x - y‖ ^ (1 - α) * ‖x - y‖ ^ α) := by rw [← hsplit]
    _ ≤ L * (max D 0 ^ (1 - α) * ‖x - y‖ ^ α) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hn ((hdiam x hx y hy).trans (le_max_left _ _)) (by linarith))
          (Real.rpow_nonneg hn _)) hL
    _ = L * max D 0 ^ (1 - α) * ‖x - y‖ ^ α := by ring

/-- Bounded Hölder functions have finite Hölder norm (`HasFiniteHolderNormOn`). -/
lemma BoundedHolderOn.hasFiniteHolderNormOn {α : ℝ} {f : E → F} {S : Set E}
    (h : BoundedHolderOn α f S) : HasFiniteHolderNormOn α f S := by
  obtain ⟨M, L, hM, hL, hb, hh⟩ := h
  refine HasFiniteHolderNormOn.of_bounds hM hL hb fun x hx y hy => ?_
  rcases eq_or_ne x y with rfl | hxy
  · simpa using hL
  · have hpos : 0 < ‖x - y‖ ^ α :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
    rw [div_le_iff₀ hpos]
    exact hh x hx y hy

/-- A bounded Hölder bound on `S` passes to `closure S` for a continuous function. -/
lemma BoundedHolderOn.closure_of_continuous {α : ℝ} {f : E → F} {S : Set E} (hα : 0 < α)
    (h : BoundedHolderOn α f S) (hf : Continuous f) : BoundedHolderOn α f (closure S) := by
  obtain ⟨M, L, hM, hL, hb, hh⟩ := h
  refine ⟨M, L, hM, hL, fun x hx => ?_, fun x hx y hy => ?_⟩
  · have hc : IsClosed {x : E | ‖f x‖ ≤ M} := isClosed_le hf.norm continuous_const
    exact closure_minimal (fun z hz => hb z hz) hc hx
  · have hc : IsClosed {q : E × E | ‖f q.1 - f q.2‖ ≤ L * ‖q.1 - q.2‖ ^ α} := by
      refine isClosed_le ((hf.comp continuous_fst).sub (hf.comp continuous_snd)).norm
        (continuous_const.mul ?_)
      exact (continuous_fst.sub continuous_snd).norm.rpow_const fun _ => Or.inr hα.le
    have hmem : (x, y) ∈ closure (S ×ˢ S) := by
      rw [closure_prod_eq]; exact ⟨hx, hy⟩
    exact closure_minimal (fun q hq => hh q.1 hq.1 q.2 hq.2) hc hmem

end BoundedHolder

section Ambient

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A function `C¹` on an open set containing a closed ball is Lipschitz on the open ball. -/
lemma exists_lipschitzOn_ball_of_contDiffOn {f : AmbientSpace → F} {U : Set AmbientSpace}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) {p : AmbientSpace} {r : ℝ}
    (hpr : closedBall p r ⊆ U) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ ball p r, ∀ y ∈ ball p r, ‖f x - f y‖ ≤ L * ‖x - y‖ := by
  obtain ⟨L, hL⟩ := (isCompact_closedBall p r).exists_bound_of_continuousOn
    ((hf.continuousOn_fderiv_of_isOpen hU le_rfl).mono hpr)
  refine ⟨max L 0, le_max_right _ _, fun x hx y hy => ?_⟩
  have hd : ∀ z ∈ ball p r, DifferentiableAt ℝ f z := fun z hz =>
    (hf.differentiableOn one_ne_zero z (hpr (ball_subset_closedBall hz))).differentiableAt
      (hU.mem_nhds (hpr (ball_subset_closedBall hz)))
  exact (convex_ball p r).norm_image_sub_le_of_norm_fderiv_le hd
    (fun z hz => (hL z (ball_subset_closedBall hz)).trans (le_max_left _ _)) hy hx

lemma norm_sub_le_of_mem_ball {p x y : AmbientSpace} {r : ℝ} (hx : x ∈ ball p r)
    (hy : y ∈ ball p r) : ‖x - y‖ ≤ 2 * r := by
  rw [← dist_eq_norm]
  have := dist_triangle_right x y p
  rw [mem_ball] at hx hy
  linarith

/-- A function `C¹` on an open set containing a closed ball is bounded and `α`-Hölder on the
open ball, `α ≤ 1`. -/
lemma boundedHolderOn_ball_of_contDiffOn {α : ℝ} (hα1 : α ≤ 1)
    {f : AmbientSpace → F} {U : Set AmbientSpace} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    {p : AmbientSpace} {r : ℝ} (hpr : closedBall p r ⊆ U) : BoundedHolderOn α f (ball p r) := by
  obtain ⟨L, hL, hl⟩ := exists_lipschitzOn_ball_of_contDiffOn hU hf hpr
  exact boundedHolderOn_of_lipschitzOn hα1 hL hl fun x hx y hy => norm_sub_le_of_mem_ball hx hy

/-- The operator norm of a bilinear form on `ℝ³` is at most `9` times a bound on its entries. -/
lemma norm_le_nine_mul_of_entries (T : AmbientSpace →L[ℝ] AmbientSpace →L[ℝ] ℝ) {C : ℝ}
    (hC : 0 ≤ C)
    (hT : ∀ i j : Fin 3, |T (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ C) :
    ‖T‖ ≤ 9 * C := by
  have hrow : ∀ i : Fin 3, ‖T (EuclideanSpace.single i 1)‖ ≤ (3 : ℕ) * C := fun i =>
    nondiv_norm_clm_le_coordinate_bound _ hC fun j => by
      rw [Real.norm_eq_abs]; exact hT i j
  have h := nondiv_norm_clm_le_coordinate_bound T (by positivity) hrow
  have h9 : ((3 : ℕ) : ℝ) * (((3 : ℕ) : ℝ) * C) = 9 * C := by norm_num; ring
  linarith

/-- A family of bilinear forms on `ℝ³` is bounded and `α`-Hölder if all its entries are. -/
lemma boundedHolderOn_of_entries {E : Type*} [NormedAddCommGroup E] {α : ℝ} {S : Set E}
    {f : E → AmbientSpace →L[ℝ] AmbientSpace →L[ℝ] ℝ}
    (h : ∀ i j : Fin 3, BoundedHolderOn α
      (fun x => f x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) S) :
    BoundedHolderOn α f S := by
  unfold BoundedHolderOn at h
  choose M L hM hL hb hh using h
  have hsum : ∀ A : Fin 3 → Fin 3 → ℝ, (∀ i j, 0 ≤ A i j) →
      0 ≤ ∑ i, ∑ j, A i j ∧ ∀ i j, A i j ≤ ∑ i, ∑ j, A i j := by
    intro A hA
    have hrow : ∀ i, 0 ≤ ∑ j, A i j := fun i => Finset.sum_nonneg fun j _ => hA i j
    refine ⟨Finset.sum_nonneg fun i _ => hrow i, fun i j => ?_⟩
    exact (Finset.single_le_sum (fun j _ => hA i j) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, A i j) (fun i _ => hrow i) (Finset.mem_univ i))
  obtain ⟨hM₀, hMle⟩ := hsum M hM
  obtain ⟨hL₀, hLle⟩ := hsum L hL
  refine ⟨9 * ∑ i, ∑ j, M i j, 9 * ∑ i, ∑ j, L i j, by positivity, by positivity,
    fun x hx => ?_, fun x hx y hy => ?_⟩
  · exact norm_le_nine_mul_of_entries _ hM₀ fun i j => by
      have h' := hb i j x hx
      rw [Real.norm_eq_abs] at h'
      exact h'.trans (hMle i j)
  · have hr : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
    have h9 := norm_le_nine_mul_of_entries (f x - f y) (mul_nonneg hL₀ hr) fun i j => by
      have h' := hh i j x hx y hy
      rw [Real.norm_eq_abs] at h'
      rw [sub_apply, sub_apply]
      exact h'.trans (mul_le_mul_of_nonneg_right (hLle i j) hr)
    calc ‖f x - f y‖ ≤ 9 * ((∑ i, ∑ j, L i j) * ‖x - y‖ ^ α) := h9
      _ = 9 * (∑ i, ∑ j, L i j) * ‖x - y‖ ^ α := by ring

/-- A Hessian entry is an entry of the second Fréchet derivative. -/
lemma hullHolder_entry_eq_fderiv_fderiv {w : AmbientSpace → ℝ} {x : AmbientSpace}
    (hw : DifferentiableAt ℝ (fderiv ℝ w) x) (i j : Fin 3) :
    boundaryNeumannC2Entry w x i j = fderiv ℝ (fderiv ℝ w) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) := by
  unfold boundaryNeumannC2Entry
  rw [fderiv_clm_apply hw (differentiableAt_const _)]
  simp

end Ambient

/-- The second-order chain rule: at points of an open set `N` mapped by a `C³` map `φ` into an
open set `T` on which `v` is `C²`,
`∇²(v ∘ φ)(h, k) = ∇v(φ) (∇²φ(h, k)) + ∇²v(φ)(∇φ h, ∇φ k)`. -/
lemma fderiv_fderiv_comp_apply {φ : AmbientSpace → AmbientSpace} (hφ : ContDiff ℝ 3 φ)
    {v : AmbientSpace → ℝ} {T : Set AmbientSpace} (hTo : IsOpen T) (hv : ContDiffOn ℝ 2 v T)
    {N : Set AmbientSpace} (hNo : IsOpen N) (hNT : MapsTo φ N T) {z : AmbientSpace}
    (hz : z ∈ N) (h k : AmbientSpace) :
    fderiv ℝ (fderiv ℝ (v ∘ φ)) z h k =
      fderiv ℝ v (φ z) (fderiv ℝ (fderiv ℝ φ) z h k) +
        fderiv ℝ (fderiv ℝ v) (φ z) (fderiv ℝ φ z h) (fderiv ℝ φ z k) := by
  have hd1 : ∀ x ∈ T, DifferentiableAt ℝ v x := fun x hx =>
    (hv.differentiableOn (by norm_num) x hx).differentiableAt (hTo.mem_nhds hx)
  have hv1 : ContDiffOn ℝ 1 (fderiv ℝ v) T := hv.fderiv_of_isOpen hTo (by norm_num)
  have hd2 : ∀ x ∈ T, DifferentiableAt ℝ (fderiv ℝ v) x := fun x hx =>
    (hv1.differentiableOn one_ne_zero x hx).differentiableAt (hTo.mem_nhds hx)
  have hφ1 : Differentiable ℝ φ := (hφ.of_le (m := 1) (by norm_num)).differentiable one_ne_zero
  have hDφ : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)
  have hev : fderiv ℝ (v ∘ φ) =ᶠ[𝓝 z] fun z' => (fderiv ℝ v (φ z')).comp (fderiv ℝ φ z') := by
    filter_upwards [hNo.mem_nhds hz] with z' hz'
    exact fderiv_comp z' (hd1 _ (hNT hz')) (hφ1 z')
  have hc : DifferentiableAt ℝ (fun z' => fderiv ℝ v (φ z')) z := (hd2 _ (hNT hz)).comp z (hφ1 z)
  have hcomp : fderiv ℝ (fun z' => fderiv ℝ v (φ z')) z =
      (fderiv ℝ (fderiv ℝ v) (φ z)).comp (fderiv ℝ φ z) :=
    fderiv_comp z (hd2 _ (hNT hz)) (hφ1 z)
  rw [hev.fderiv_eq, fderiv_clm_comp hc (hDφ z), hcomp]
  simp

/-- Second-order chain rule bound. If `φ` is `C³` and `v` is `C²` on an open convex set `T` of
bounded diameter, with Hessian entries bounded by `C` and `α`-Hölder with constant `C` on `T`,
then `∇²(v ∘ φ)` is bounded and `α`-Hölder on `ball p r ∩ N` for every open `N` that `φ` maps
into `T`. -/
theorem boundedHolderOn_hessian_comp {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    {φ : AmbientSpace → AmbientSpace} (hφ : ContDiff ℝ 3 φ)
    {v : AmbientSpace → ℝ} {T : Set AmbientSpace} (hTo : IsOpen T) (hTc : Convex ℝ T)
    {D : ℝ} (hTd : ∀ x ∈ T, ∀ y ∈ T, ‖x - y‖ ≤ D) (hv : ContDiffOn ℝ 2 v T) {C : ℝ}
    (hbd : ∀ i j : Fin 3, ∀ x ∈ T, |boundaryNeumannC2Entry v x i j| ≤ C)
    (hhol : ∀ i j : Fin 3, ∀ x ∈ T, ∀ y ∈ T,
      |boundaryNeumannC2Entry v x i j - boundaryNeumannC2Entry v y i j| ≤ C * dist x y ^ α)
    {N : Set AmbientSpace} (hNo : IsOpen N) (hNT : MapsTo φ N T) (p : AmbientSpace) (r : ℝ) :
    BoundedHolderOn α (fderiv ℝ (fderiv ℝ (v ∘ φ))) (ball p r ∩ N) := by
  set C' := max C 0 with hC'
  have hC0 : 0 ≤ C' := le_max_right _ _
  have hv1 : ContDiffOn ℝ 1 (fderiv ℝ v) T := hv.fderiv_of_isOpen hTo (by norm_num)
  have hd2 : ∀ x ∈ T, DifferentiableAt ℝ (fderiv ℝ v) x := fun x hx =>
    (hv1.differentiableOn one_ne_zero x hx).differentiableAt (hTo.mem_nhds hx)
  -- the Hessian of `v` on `T`
  have hH2 : ∀ x ∈ T, ‖fderiv ℝ (fderiv ℝ v) x‖ ≤ 9 * C' := fun x hx =>
    norm_le_nine_mul_of_entries _ hC0 fun i j => by
      rw [← hullHolder_entry_eq_fderiv_fderiv (hd2 x hx)]
      exact (hbd i j x hx).trans (le_max_left _ _)
  have hB2 : BoundedHolderOn α (fderiv ℝ (fderiv ℝ v)) T := by
    refine ⟨9 * C', 9 * C', by positivity, by positivity, hH2, fun x hx y hy => ?_⟩
    have hr : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
    have h9 := norm_le_nine_mul_of_entries
      (fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y) (mul_nonneg hC0 hr) fun i j => by
        rw [sub_apply, sub_apply, ← hullHolder_entry_eq_fderiv_fderiv (hd2 x hx),
          ← hullHolder_entry_eq_fderiv_fderiv (hd2 y hy), ← dist_eq_norm]
        exact (hhol i j x hx y hy).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _))
    calc ‖fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y‖ ≤ 9 * (C' * ‖x - y‖ ^ α) := h9
      _ = 9 * C' * ‖x - y‖ ^ α := by ring
  -- the gradient of `v` is Lipschitz on the convex set `T`
  have hB1 : BoundedHolderOn α (fderiv ℝ v) T :=
    boundedHolderOn_of_lipschitzOn hα1 (by positivity : (0 : ℝ) ≤ 9 * C')
      (fun x hx y hy => hTc.norm_image_sub_le_of_norm_fderiv_le hd2 hH2 hy hx) hTd
  -- `φ` and its first two derivatives on the ball
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hDφ : ContDiff ℝ 2 (fderiv ℝ φ) := hφ.fderiv_right (by norm_num)
  have hD2φ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ φ)) := hDφ.fderiv_right (by norm_num)
  obtain ⟨Lφ, hLφ, hlφ⟩ := exists_lipschitzOn_ball_of_contDiffOn isOpen_univ hφ1.contDiffOn
    (subset_univ (closedBall p r))
  have hBDφ : BoundedHolderOn α (fderiv ℝ φ) (ball p r) :=
    boundedHolderOn_ball_of_contDiffOn hα1 isOpen_univ (hDφ.of_le (by norm_num)).contDiffOn
      (subset_univ _)
  have hBD2φ : BoundedHolderOn α (fderiv ℝ (fderiv ℝ φ)) (ball p r) :=
    boundedHolderOn_ball_of_contDiffOn hα1 isOpen_univ hD2φ.contDiffOn (subset_univ _)
  have hST : MapsTo φ (ball p r ∩ N) T := fun z hz => hNT hz.2
  have hlφS : ∀ x ∈ ball p r ∩ N, ∀ y ∈ ball p r ∩ N, ‖φ x - φ y‖ ≤ Lφ * ‖x - y‖ :=
    fun x hx y hy => hlφ x hx.1 y hy.1
  have hG : BoundedHolderOn α (fun z => fderiv ℝ v (φ z)) (ball p r ∩ N) :=
    hB1.comp_lipschitz hα0.le hST hLφ hlφS
  have hG2 : BoundedHolderOn α (fun z => fderiv ℝ (fderiv ℝ v) (φ z)) (ball p r ∩ N) :=
    hB2.comp_lipschitz hα0.le hST hLφ hlφS
  have hBDφe : ∀ i : Fin 3,
      BoundedHolderOn α (fun z => fderiv ℝ φ z (EuclideanSpace.single i 1)) (ball p r ∩ N) :=
    fun i => (hBDφ.mono inter_subset_left).clm_apply (boundedHolderOn_const _)
  apply boundedHolderOn_of_entries
  intro i j
  have hT1 := hG.clm_apply (((hBD2φ.mono inter_subset_left).clm_apply
    (boundedHolderOn_const (EuclideanSpace.single i 1))).clm_apply
      (boundedHolderOn_const (EuclideanSpace.single j 1)))
  have hT2 := (hG2.clm_apply (hBDφe i)).clm_apply (hBDφe j)
  exact (hT1.add hT2).congr fun z hz => (fderiv_fderiv_comp_apply hφ hTo hv hNo hNT hz.2 _ _).symm

lemma convex_boundaryReflectUpper (a b : ℝ) : Convex ℝ (boundaryReflectUpper a b) := by
  have h : boundaryReflectUpper a b =
      (graphProjectionN 2).toLinearMap ⁻¹' ball 0 a ∩
        (EuclideanSpace.proj (Fin.last 2) : AmbientSpace →L[ℝ] ℝ).toLinearMap ⁻¹' Ioo 0 b := by
    ext y
    simp only [boundaryReflectUpper, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_ball_zero_iff,
      mem_Ioo]
    rfl
  rw [h]
  exact ((convex_ball 0 a).linear_preimage _).inter ((convex_Ioo 0 b).linear_preimage _)

/-- The local structure behind `hullPotential_local_c2_extension`, for a given `0 < α < 1`.
Near `p ∈ ∂K` there are a `C³` map `Θ⁻¹` (the inverse shear flattening), a function `v` and a
constant `C` with `Θ⁻¹ p` in the reflection slab, `Θ⁻¹ z` in its open upper half and
`u z = v (Θ⁻¹ z)` whenever `Θ⁻¹ z` is in the slab and `z ∉ K`, and `v` `C²` on the upper half
with Hessian entries bounded by `C` and `α`-Hölder with constant `C` there
(`boundary_c2a_local_of_h1` with exponent `α`). -/
theorem hullPotential_local_flattening {Ω : Set AmbientSpace} (ho : IsOpen Ω)
    (hbd : Bornology.IsBounded Ω) (h3 : HasCkBoundary 3 Ω) (h0 : (0 : AmbientSpace) ∈ Ω)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ)
    (h1 : ∀ x ∈ filledHull Ω, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0))
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {p : AmbientSpace} (hp : p ∈ frontier (filledHull Ω)) :
    ∃ (Θi : AmbientSpace → AmbientSpace) (v : AmbientSpace → ℝ) (C : ℝ), ContDiff ℝ 3 Θi ∧
      Θi p ∈ boundaryReflectSlab (1 / 8388608) (1 / 8796093022208) ∧
      (∀ z, Θi z ∈ boundaryReflectSlab (1 / 8388608) (1 / 8796093022208) →
        z ∈ (filledHull Ω)ᶜ →
        Θi z ∈ boundaryReflectUpper (1 / 8388608) (1 / 8796093022208) ∧ u z = v (Θi z)) ∧
      ContDiffOn ℝ 2 v (boundaryReflectUpper (1 / 8388608) (1 / 8796093022208)) ∧
      (∀ i j : Fin 3, ∀ x ∈ boundaryReflectUpper (1 / 8388608) (1 / 8796093022208),
        |boundaryNeumannC2Entry v x i j| ≤ C) ∧
      (∀ i j : Fin 3, ∀ x ∈ boundaryReflectUpper (1 / 8388608) (1 / 8796093022208),
        ∀ y ∈ boundaryReflectUpper (1 / 8388608) (1 / 8796093022208),
        |boundaryNeumannC2Entry v x i j - boundaryNeumannC2Entry v y i j| ≤
          C * dist x y ^ α) := by
  set K := filledHull Ω with hKdef
  have hKc : IsClosed K := filledHull_isClosed Ω
  have hKo : IsOpen Kᶜ := hKc.isOpen_compl
  have hsigns := (filledHull_capacitary_properties ho hbd h0 hu hh h1 hinf).1
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) u Kᶜ :=
    hh.contDiffOn_of_continuous (by norm_num) hKo hu.continuousOn
  have hu1 : ContDiffOn ℝ 1 u Kᶜ := hsm.of_le (WithTop.coe_le_coe.mpr le_top)
  have hu2 : ContDiffOn ℝ 2 u Kᶜ := hsm.of_le (WithTop.coe_le_coe.mpr le_top)
  -- a `C³` chart of `Kᶜ` at `p`
  have hpi : p ∈ frontier (interior K) := by rwa [filledHull_frontier_interior ho]
  obtain ⟨c, hc, hpc, hh3⟩ := filledHull_hasCkBoundary_interior h3 ho p hpi
  have hcl : closure (interior (filledHull Ω)) = filledHull Ω :=
    (filledHull_eq_closure_interior ho).symm
  have hc' : c.exteriorChart.IsChartFor Kᶜ := by
    have h := hc.exterior
    rw [hcl] at h
    exact h
  have hpf : p ∈ frontier Kᶜ := by rwa [frontier_compl]
  have hpc' : p ∈ c.exteriorChart.region := hpc
  have hh3' : ContDiff ℝ (3 : ℕ) c.exteriorChart.height := by
    have : ContDiff ℝ 3 (fun x => -c.height x) := hh3.neg
    exact_mod_cast this
  set c' := c.exteriorChart with hc'def
  set a := graphProjectionN 2 (c'.placement.symm p) with hadef
  obtain ⟨ρ, hρ, hreg⟩ := exists_boundaryShearMap_region hc' hpf hpc'
  set Θ := boundaryShearMap c' a ρ with hΘdef
  set Θi := boundaryShearInv c' a ρ with hΘidef
  have hl : Function.LeftInverse Θi Θ := boundaryShearMap_leftInverse c' a hρ.ne'
  have hr : Function.RightInverse Θi Θ := boundaryShearMap_rightInverse c' a hρ.ne'
  have hΘ3 : ContDiff ℝ (3 : ℕ) Θ := contDiff_boundaryShearMap c' a ρ hh3'
  have hΘi3 : ContDiff ℝ (3 : ℕ) Θi := contDiff_boundaryShearInv c' a ρ hh3'
  have hΘ1 : ContDiff ℝ 1 Θ := hΘ3.of_le (by norm_num)
  have hΘi1 : ContDiff ℝ 1 Θi := hΘi3.of_le (by norm_num)
  have hΘ0 : Θ 0 = p := boundaryShearMap_zero hc' hpf hpc' ρ
  have hmem : ∀ y ∈ closedBall (0 : AmbientSpace) 2, (Θ y ∈ Kᶜ ↔ 0 < y (Fin.last 2)) :=
    fun y hy => boundaryShearMap_mem_iff hc' a hρ (hreg y hy)
  have hmemcl : ∀ y ∈ closedBall (0 : AmbientSpace) 2,
      (Θ y ∈ closure Kᶜ ↔ 0 ≤ y (Fin.last 2)) :=
    fun y hy => boundaryShearMap_mem_closure_iff hc' a hρ (hreg y hy)
  have hball12 : ball (0 : AmbientSpace) 1 ⊆ closedBall 0 2 :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))
  -- the flattened potential
  set w : AmbientSpace → ℝ := u ∘ Θ with hwdef
  have hwc : Continuous w := hu.comp hΘ1.continuous
  have hw1 : ∀ y ∈ closedBall (0 : AmbientSpace) 2, y (Fin.last 2) ≤ 0 → w y = 1 := by
    intro y hy ht
    apply h1
    by_contra hK
    exact absurd ((hmem y hy).mp hK) (not_lt.mpr ht)
  have hwb : ∀ y, |w y| ≤ 1 := by
    intro y
    by_cases hy : Θ y ∈ K
    · simp [w, h1 _ hy]
    · obtain ⟨h0', h1'⟩ := hsigns _ hy
      rw [abs_le]
      constructor <;> simp only [w, Function.comp] <;> linarith
  have hhalf : MapsTo Θ (boundaryHalfBall 1) Kᶜ := fun y hy =>
    (hmem y (hball12 hy.1)).mpr hy.2
  have hwC2 : ContDiffOn ℝ 2 w (boundaryHalfBall 1) :=
    hu2.comp (hΘ3.of_le (by norm_num)).contDiffOn hhalf
  have hU1 : IsOpen (boundaryHalfBall 1) := isOpen_boundaryHalfBall 1
  -- weak equation
  have hweak := isWeakDivergenceEquationOn_dirichletPullback hΘ1 hΘi1 hl hr hKo hhalf hu1
    (isWeakDivergenceEquationOn_id_of_harmonic hKo hu.continuousOn hh)
  -- H¹ on the half ball
  have hbdU : Bornology.IsBounded (boundaryHalfBall 1) :=
    isBounded_ball.subset inter_subset_left
  obtain ⟨R, hR⟩ := c'.bounded_region.subset_ball p
  have hL2 : IntegrableOn (fun x => ‖gradient u x‖ ^ 2) (Θ '' boundaryHalfBall 1) := by
    refine (exterior_gradient_sq_integrableOn hKc hu hh h1 hsigns p R).mono_set ?_
    rintro z ⟨y, hy, rfl⟩
    exact ⟨hhalf hy, hR (hreg y (hball12 hy.1))⟩
  have hgradL2 : MemLp (gradient w) 2 (volume.restrict (boundaryHalfBall 1)) :=
    memLp_gradient_comp_dirichletPullback hΘ1 hΘi1 hl hr hKo hU1 hhalf hbdU hu1 hL2
  have : IsFiniteMeasure (volume.restrict (boundaryHalfBall 1)) :=
    isFiniteMeasure_restrict.mpr hbdU.measure_lt_top.ne
  have hwL2 : MemLp w 2 (volume.restrict (boundaryHalfBall 1)) :=
    MemLp.of_bound hwc.aestronglyMeasurable 1
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hwb y)
  have hH1 : HasH1GradientOn w (gradient w) (boundaryHalfBall 1) :=
    ⟨hasWeakGradientOn_of_contDiffOn hU1 (hwC2.of_le (by norm_num)), hwL2, hgradL2⟩
  -- zero trace of `w - 1`
  have hgc : gradient (fun _ : AmbientSpace => (1 : ℝ)) = fun _ => 0 := by
    funext x
    simp [gradient]
  have htr : HasZeroFlatTraceOn (fun x => w x - (fun _ : AmbientSpace => (1 : ℝ)) x)
      (fun x => gradient w x - gradient (fun _ : AmbientSpace => (1 : ℝ)) x) (ball 0 1) := by
    apply hasZeroFlatTraceOn_of_continuousOn
    · exact (hwc.sub continuous_const).continuousOn
    · exact (hwC2.of_le (by norm_num)).sub contDiffOn_const
    · intro x _
      simp only [hgc, sub_zero]
      simp [gradient, fderiv_sub_const]
    · simp only [hgc, sub_zero]
      exact (hgradL2.integrable one_le_two).norm
    · intro x hx ht
      simp [hw1 x (hball12 hx) ht.le]
  -- boundary C²,α from H¹
  set S := closure (boundaryHalfBall 1) with hSdef
  have hScpt : IsCompact S :=
    (isCompact_closedBall (0 : AmbientSpace) 1).of_isClosed_subset isClosed_closure
      (closure_minimal (fun x hx => ball_subset_closedBall hx.1) isClosed_closedBall)
  set A := dirichletPullbackCoefficient Θ with hAdef
  have hA2 : ContDiff ℝ 2 A := contDiff_dirichletPullbackCoefficient hΘ3 hΘi1 hl hr
  obtain ⟨lam, cap, hlam, hlamcap, hbnd⟩ := dirichletPullbackCoefficient_bounds hΘ1 hΘi1 hl hr hScpt
  have hα1' : α ≤ 1 := hα1.le
  have hAh : HasC1HolderOn α A S := hasC1HolderOn_closure_boundaryHalfBall_of_contDiff hα0 hα1' hA2
  have hφh : HasC1HolderOn α (fun _ : AmbientSpace => (1 : ℝ)) S :=
    hasC1HolderOn_closure_boundaryHalfBall_of_contDiff hα0 hα1' contDiff_const
  have hgφh : HasC1HolderOn α (gradient fun _ : AmbientSpace => (1 : ℝ)) S := by
    rw [hgc]
    exact hasC1HolderOn_closure_boundaryHalfBall_of_contDiff hα0 hα1' contDiff_const
  have hGh : HasC1HolderOn α (fun _ : AmbientSpace => (0 : AmbientSpace)) S :=
    hasC1HolderOn_closure_boundaryHalfBall_of_contDiff hα0 hα1' contDiff_const
  obtain ⟨C, _, hmain⟩ := boundary_c2a_local_of_h1 (α := α) (lam := lam) (cap := cap)
    (M := nondivC1HolderNorm α A S)
    (N := nondivC1HolderNorm α (fun _ : AmbientSpace => (1 : ℝ)) S +
      nondivC1HolderNorm α (gradient fun _ : AmbientSpace => (1 : ℝ)) S +
      nondivC1HolderNorm α (fun _ : AmbientSpace => (0 : AmbientSpace)) S)
    (P₁ := 0) (P₂ := 0)
    (E := ∫ x in boundaryHalfBall 1,
      ‖gradient w x - gradient (fun _ : AmbientSpace => (1 : ℝ)) x‖ ^ 2)
    hα0 hα1 hlam hlamcap hAh.norm_nonneg
    (add_nonneg (add_nonneg hφh.norm_nonneg hgφh.norm_nonneg) hGh.norm_nonneg) le_rfl le_rfl
    (integral_nonneg fun _ => by positivity)
  obtain ⟨W, v, hWo, hWslab, hv1, hvae, hvface, hv2⟩ :=
    hmain w (fun _ => 1) (gradient w) (fun _ => 0) A contDiff_const hAh hGh hφh hgφh le_rfl le_rfl
      (fun x hx => (hbnd x hx).1) (fun x hx => (hbnd x hx).2)
      (fun x _ => by simp [hgc]) (fun x _ y _ => by simp [hgc]) hH1 hweak htr le_rfl
  obtain ⟨hv2c, hent⟩ := hv2 0 (by simp) (by simp)
  have hupper : IsOpen (W ∩ {x : AmbientSpace | 0 < x (Fin.last 2)}) :=
    hWo.inter (isOpen_lt continuous_const (EuclideanSpace.proj (Fin.last 2)).continuous)
  have hvw : EqOn v w (W ∩ {x | 0 < x (Fin.last 2)}) :=
    Measure.eqOn_open_of_ae_eq hvae hupper (hv1.continuousOn.mono inter_subset_left)
      hwc.continuousOn
  have h0O : (0 : AmbientSpace) ∈ boundaryReflectSlab (1 / 8388608) (1 / 8796093022208) := by
    refine ⟨?_, ?_⟩ <;> simp
  refine ⟨Θi, v, C, hΘi3, ?_, ?_, hv2c.mono hullPotential_reflectUpper_subset,
    fun i j x hx => (hent i j).1 x (hullPotential_reflectUpper_subset hx),
    fun i j x hx y hy => (hent i j).2 x (hullPotential_reflectUpper_subset hx) y
      (hullPotential_reflectUpper_subset hy)⟩
  · rw [← hΘ0, hl 0]
    exact h0O
  · intro z hzO hzK
    have hyB : Θi z ∈ closedBall (0 : AmbientSpace) 2 :=
      hball12 (hullPotential_reflectSlab_subset_ball hzO)
    have hzy : Θ (Θi z) = z := hr z
    have hpos : 0 < (Θi z) (Fin.last 2) := (hmem _ hyB).mp (by rw [hzy]; exact hzK)
    have hyW : Θi z ∈ W := hWslab (hullPotential_reflectSlab_subset_c1Slab hzO)
    refine ⟨⟨hzO.1, hpos, (abs_lt.mp hzO.2).2⟩, ?_⟩
    rw [hvw ⟨hyW, hpos⟩]
    simp only [w, Function.comp, hzy]

/-- Blueprint `thm:capacitary-potential`, clause `u ∈ C^{2,α}_loc(closure (ℝ³ ∖ K))`, for the
capacitary potential `u` of the filled hull `K` of a bounded open `Ω ∋ 0` with `C³` boundary and
`0 < α < 1`: for every `C²` function `g` on `ℝ³` with `u = g` on `closure Kᶜ`, each point of
`closure Kᶜ` has a neighbourhood `U` with `g`, `∇g`, `∇²g` bounded and `α`-Hölder on
`U ∩ closure Kᶜ` (`HasC2HolderOn α g (U ∩ closure Kᶜ)`). -/
theorem hullPotential_hasC2HolderOn_of_extension {Ω : Set AmbientSpace} (ho : IsOpen Ω)
    (hbd : Bornology.IsBounded Ω) (h3 : HasCkBoundary 3 Ω) (h0 : (0 : AmbientSpace) ∈ Ω)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ)
    (h1 : ∀ x ∈ filledHull Ω, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0))
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {g : AmbientSpace → ℝ} (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure (filledHull Ω)ᶜ)) :
    ∀ p ∈ closure (filledHull Ω)ᶜ, ∃ U ∈ 𝓝 p,
      HasC2HolderOn α g (U ∩ closure (filledHull Ω)ᶜ) := by
  set K := filledHull Ω with hKdef
  have hKo : IsOpen Kᶜ := (filledHull_isClosed Ω).isOpen_compl
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) u Kᶜ :=
    hh.contDiffOn_of_continuous (by norm_num) hKo hu.continuousOn
  have hu3 : ContDiffOn ℝ 3 u Kᶜ := hsm.of_le (WithTop.coe_le_coe.mpr le_top)
  have hu1 : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ u)) Kᶜ :=
    (hu3.fderiv_of_isOpen hKo (m := 2) (by norm_num)).fderiv_of_isOpen hKo (m := 1)
      (by norm_num)
  have hg2c : Continuous (fderiv ℝ (fderiv ℝ g)) :=
    (hg.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  -- `∇²g = ∇²u` on `Kᶜ`
  have hgu : ∀ x ∈ Kᶜ, fderiv ℝ (fderiv ℝ g) x = fderiv ℝ (fderiv ℝ u) x := by
    intro x hx
    have hev : g =ᶠ[𝓝 x] u := by
      filter_upwards [hKo.mem_nhds hx] with y hy
      exact (hug (subset_closure hy)).symm
    exact hev.fderiv.fderiv_eq
  -- the Hessian estimate near each point of `closure Kᶜ`
  have hhess : ∀ p ∈ closure Kᶜ, ∃ U : Set AmbientSpace, IsOpen U ∧ p ∈ U ∧
      BoundedHolderOn α (fderiv ℝ (fderiv ℝ g)) (U ∩ closure Kᶜ) := by
    intro p hp
    by_cases hpK : p ∈ Kᶜ
    · -- interior points: `u` is smooth off `K`
      obtain ⟨ε, hε, hεK⟩ := Metric.isOpen_iff.mp hKo p hpK
      have hcl : closedBall p (ε / 2) ⊆ Kᶜ :=
        (closedBall_subset_ball (half_lt_self hε)).trans hεK
      refine ⟨ball p (ε / 2), isOpen_ball, mem_ball_self (half_pos hε), ?_⟩
      exact ((boundedHolderOn_ball_of_contDiffOn hα1.le hKo hu1 hcl).congr fun x hx =>
        (hgu x (hcl (ball_subset_closedBall hx))).symm).mono inter_subset_left
    · -- boundary points: the flattening and the second-order chain rule
      have hpf : p ∈ frontier K := by
        rw [frontier_eq_closure_inter_closure]
        exact ⟨subset_closure (by simpa using hpK), hp⟩
      obtain ⟨Θi, v, C, hΘi, hp0, hmap, hv2, hvb, hvh⟩ :=
        hullPotential_local_flattening ho hbd h3 h0 hu hh h1 hinf hα0 hα1 hpf
      set O := Θi ⁻¹' boundaryReflectSlab (1 / 8388608) (1 / 8796093022208) with hOdef
      have hOo : IsOpen O := (isOpen_boundaryReflectSlab _ _).preimage hΘi.continuous
      have hNo : IsOpen (O ∩ Kᶜ) := hOo.inter hKo
      have hNT : MapsTo Θi (O ∩ Kᶜ) (boundaryReflectUpper (1 / 8388608) (1 / 8796093022208)) :=
        fun z hz => (hmap z hz.1 hz.2).1
      have hball : boundaryReflectUpper (1 / 8388608) (1 / 8796093022208) ⊆
          ball (0 : AmbientSpace) 1 := fun z hz =>
        hullPotential_reflectSlab_subset_ball ⟨hz.1, abs_lt.mpr ⟨by linarith [hz.2.1], hz.2.2⟩⟩
      have hRd : ∀ x ∈ boundaryReflectUpper (1 / 8388608) (1 / 8796093022208),
          ∀ y ∈ boundaryReflectUpper (1 / 8388608) (1 / 8796093022208), ‖x - y‖ ≤ 2 := by
        intro x hx y hy
        have hx1 := mem_ball_zero_iff.mp (hball hx)
        have hy1 := mem_ball_zero_iff.mp (hball hy)
        linarith [norm_sub_le x y]
      have hB := boundedHolderOn_hessian_comp hα0 hα1.le hΘi (isOpen_boundaryReflectUpper _ _)
        (convex_boundaryReflectUpper _ _) hRd hv2 hvb hvh hNo hNT p 1
      have hBg : BoundedHolderOn α (fderiv ℝ (fderiv ℝ g)) (ball p 1 ∩ (O ∩ Kᶜ)) :=
        hB.congr fun z hz => by
          have hev : v ∘ Θi =ᶠ[𝓝 z] u := by
            filter_upwards [hNo.mem_nhds hz.2] with z' hz'
            exact (hmap z' hz'.1 hz'.2).2.symm
          rw [hev.fderiv.fderiv_eq]
          exact (hgu z hz.2.2).symm
      refine ⟨ball p 1 ∩ O, isOpen_ball.inter hOo, ⟨mem_ball_self one_pos, hp0⟩, ?_⟩
      have hsub : (ball p 1 ∩ O) ∩ closure Kᶜ ⊆ closure (ball p 1 ∩ (O ∩ Kᶜ)) := by
        have h := (isOpen_ball (x := p) (ε := 1)).inter hOo |>.inter_closure (t := Kᶜ)
        simpa only [inter_assoc] using h
      exact (hBg.closure_of_continuous hα0 hg2c).mono hsub
  intro p hp
  obtain ⟨U, hUo, hpU, hU⟩ := hhess p hp
  have hg0 : BoundedHolderOn α g (ball p 1) :=
    boundedHolderOn_ball_of_contDiffOn hα1.le isOpen_univ (hg.of_le (by norm_num)).contDiffOn
      (subset_univ _)
  have hg1 : BoundedHolderOn α (fderiv ℝ g) (ball p 1) :=
    boundedHolderOn_ball_of_contDiffOn hα1.le isOpen_univ
      (hg.fderiv_right (m := 1) (by norm_num)).contDiffOn (subset_univ _)
  refine ⟨U ∩ ball p 1, inter_mem (hUo.mem_nhds hpU) (ball_mem_nhds p one_pos),
    ⟨hg.contDiffOn, ?_, ?_, ?_⟩⟩
  · exact (hg0.mono fun x hx => hx.1.2).hasFiniteHolderNormOn
  · exact (hg1.mono fun x hx => hx.1.2).hasFiniteHolderNormOn
  · exact (hU.mono fun x hx => ⟨hx.1.1, hx.2⟩).hasFiniteHolderNormOn

/-- Blueprint `thm:capacitary-potential`, regularity clause
`u ∈ C^{2,α}_loc(closure (ℝ³ ∖ K))` (`0 < α < 1`), for the capacitary potential `u` of the
filled hull `K` of a bounded open `Ω ∋ 0` with `C³` boundary: there is a `C²` function `g` on
`ℝ³` with `u = g` on `closure Kᶜ` such that, for every `0 < α < 1`, each point of `closure Kᶜ`
has a neighbourhood `U` with `HasC2HolderOn α g (U ∩ closure Kᶜ)` (`g`, `∇g`, `∇²g` bounded
and `α`-Hölder there). -/
theorem hullPotential_c2_holder_extension {Ω : Set AmbientSpace} (ho : IsOpen Ω)
    (hbd : Bornology.IsBounded Ω) (h3 : HasCkBoundary 3 Ω) (h0 : (0 : AmbientSpace) ∈ Ω)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ)
    (h1 : ∀ x ∈ filledHull Ω, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0)) :
    ∃ g : AmbientSpace → ℝ, ContDiff ℝ 2 g ∧ EqOn u g (closure (filledHull Ω)ᶜ) ∧
      ∀ α : ℝ, 0 < α → α < 1 → ∀ p ∈ closure (filledHull Ω)ᶜ, ∃ U ∈ 𝓝 p,
        HasC2HolderOn α g (U ∩ closure (filledHull Ω)ᶜ) := by
  obtain ⟨g, hg, hug⟩ := hullPotentialBoundaryC2 Ω ho hbd h3 h0 u hu hh h1 hinf
  exact ⟨g, hg, hug, fun α hα0 hα1 =>
    hullPotential_hasC2HolderOn_of_extension ho hbd h3 h0 hu hh h1 hinf hα0 hα1 hg hug⟩

end LiquidDrop
