import NoCompromise.Capacity.FluxBoundaryW
import NoCompromise.CapacitaryK.LevelFrame

/-!
# Collar bounds near `∂K` from a `C²` extension across `∂K`

Input to `thm:capacitary-inequalities` (the endpoint `t = 1`). Assume the standing
hypothesis used for regularity up to `∂K` (the `thm:boundary-C2a` stand-in): the capacitary
potential `u` agrees on `closure Kᶜ` with a `C²` function `g`. By the Hopf sign
(`gradient_eq_neg_norm_smul_normal`), `∇g ≠ 0` on the compact set `∂K`, so `|∇g| ≥ c > 0` on a
bounded neighbourhood `V` of `∂K`; since `u < 1` on `Kᶜ` and `u → 0` at infinity, the collar
`{u > t₁} ∩ closure Kᶜ` lies in `V` for some `t₁ < 1`. On `Kᶜ` the potential is harmonic, so
`H|∇u| = D²u(ν, ν)` (`dirHess_unitNormal_unitNormal`), bounded by the operator norm of
`D(∇g)`, which is continuous and hence bounded on the bounded collar.
-/

noncomputable section
open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace

namespace LiquidDrop.CapacitaryK

/-- A continuous field `G` that is nonzero on the frontier of a compact `K` is bounded below
by some `c > 0` on a bounded collar `{u > t₁} ∩ closure Kᶜ`, `t₁ < 1`, provided `u < 1` on
`Kᶜ` and `u → 0` at infinity. -/
theorem collar_norm_lower_bound {K : Set E3} (hK : IsCompact K) {u : E3 → ℝ}
    (hu : Continuous u) (hinf : Tendsto u (cocompact E3) (𝓝 0))
    (hlt : ∀ x ∈ Kᶜ, u x < 1) {G : E3 → E3} (hG : Continuous G)
    (hpos : ∀ p ∈ frontier K, 0 < ‖G p‖) :
    ∃ t₁ < 1, ∃ c > 0, ∃ r : ℝ,
      ∀ x ∈ closure Kᶜ, t₁ < u x → c ≤ ‖G x‖ ∧ x ∈ ball (0 : E3) r := by
  have hfc : IsCompact (frontier K) :=
    hK.of_isClosed_subset isClosed_frontier hK.isClosed.frontier_subset
  obtain ⟨B, hB⟩ := hfc.exists_bound_of_continuousOn (f := fun p => ‖G p‖⁻¹)
    (hG.norm.continuousOn.inv₀ fun p hp => (hpos p hp).ne')
  set c : ℝ := (2 * max B 1)⁻¹ with hcdef
  have hm : 0 < max B 1 := lt_max_of_lt_right one_pos
  have hc : 0 < c := by positivity
  have hfrV : ∀ p ∈ frontier K, c < ‖G p‖ := by
    intro p hp
    have h1 := hB p hp
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hpos p hp))] at h1
    have h2 : ‖G p‖⁻¹ < 2 * max B 1 := by linarith [le_max_left B 1]
    rw [hcdef, inv_lt_comm₀ (by positivity) (hpos p hp)]
    exact h2
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball 0
  let V : Set E3 := {x | c < ‖G x‖} ∩ ball 0 R
  have hVo : IsOpen V := (isOpen_lt continuous_const hG.norm).inter isOpen_ball
  have hfrV' : frontier K ⊆ V := fun p hp => ⟨hfrV p hp, hR (hK.isClosed.frontier_subset hp)⟩
  have hhalf : ∀ᶠ x in cocompact E3, u x < 1 / 2 :=
    hinf.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨T, hT, hTs⟩ := mem_cocompact.mp hhalf
  let L : Set E3 := closure Kᶜ ∩ Vᶜ ∩ u ⁻¹' Ici (1 / 2)
  have hLc : IsCompact L := by
    apply hT.of_isClosed_subset
    · exact (isClosed_closure.inter hVo.isClosed_compl).inter (isClosed_Ici.preimage hu)
    · intro x hx
      by_contra hxT
      have h1 : u x < 1 / 2 := hTs hxT
      have h2 : (1 : ℝ) / 2 ≤ u x := hx.2
      linarith
  have hLK : L ⊆ Kᶜ := by
    rintro x ⟨⟨hxc, hxV⟩, -⟩ hxK
    apply hxV
    apply hfrV'
    rw [frontier_eq_closure_inter_closure]
    exact ⟨subset_closure hxK, hxc⟩
  obtain ⟨t₁, ht₁, ht₁L, ht₁h⟩ : ∃ t₁ < 1, (∀ x ∈ L, u x ≤ t₁) ∧ 1 / 2 ≤ t₁ := by
    rcases L.eq_empty_or_nonempty with hL | hL
    · exact ⟨1 / 2, by norm_num, by simp [hL], le_rfl⟩
    · obtain ⟨x₀, hx₀, hmax⟩ := hLc.exists_isMaxOn hL hu.continuousOn
      exact ⟨max (u x₀) (1 / 2), max_lt (hlt x₀ (hLK hx₀)) (by norm_num),
        fun x hx => (hmax hx).trans (le_max_left _ _), le_max_right _ _⟩
  refine ⟨t₁, ht₁, c, hc, R, ?_⟩
  intro x hx hux
  have hxV : x ∈ V := by
    by_contra hxV
    have hxL : x ∈ L := ⟨⟨hx, hxV⟩, show (1 : ℝ) / 2 ≤ u x by linarith⟩
    linarith [ht₁L x hxL]
  exact ⟨hxV.1.le, hxV.2⟩

/-- Gradient of the extension on the exterior: `∇u = ∇g` near every point of `Kᶜ`. -/
lemma gradient_eventuallyEq_of_eqOn_closure {K : Set E3} (hK : IsClosed K) {u g : E3 → ℝ}
    (hug : EqOn u g (closure Kᶜ)) {x : E3} (hx : x ∈ Kᶜ) :
    u =ᶠ[𝓝 x] g ∧ gradient u =ᶠ[𝓝 x] gradient g := by
  have hev : u =ᶠ[𝓝 x] g :=
    Filter.eventually_of_mem (hK.isOpen_compl.mem_nhds hx) fun y hy => hug (subset_closure hy)
  refine ⟨hev, hev.eventuallyEq_nhds.mono fun y hy => ?_⟩
  unfold gradient
  rw [hy.fderiv_eq]

/-- Collar bounds for the extension itself: `|∇g| ≥ c > 0` on `{u > t₁} ∩ closure Kᶜ`
(including `∂K`, where `u = 1`), inside a ball. -/
theorem capacitary_collar_extension_gradient {K : Set E3} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hKR : K ⊆ closedBall 0 R₀)
    (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {g : E3 → ℝ} (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure Kᶜ))
    (hC2 : HasC2Boundary (interior K)) (hconn : IsPreconnected Kᶜ) :
    ∃ t₁ < 1, ∃ c > 0, ∃ r : ℝ,
      ∀ x ∈ closure Kᶜ, t₁ < u x → c ≤ ‖gradient g x‖ ∧ x ∈ ball (0 : E3) r := by
  have hlt : ∀ x ∈ Kᶜ, u x < 1 := (capacitary_signs hK hzero hu hh hb hinf).2 hconn
  have hG : Continuous (gradient g) :=
    (contDiff_gradient_of_contDiff_succ (r := 1) hg).continuous
  exact collar_norm_lower_bound hK hu hinf hlt hG fun p hp =>
    (gradient_eq_neg_norm_smul_normal hK hreg hC1 hR₀ hKR hzero hu hh hb hinf hg hug hC2
      hconn p hp).2

/-- The collar hypothesis `hcollar` of `capacitary_inequalities_of_potential_far_unconditional`
follows from the `C²` extension across `∂K` (with the Hopf sign): there are `t₁ < 1`, `c > 0`
and `M` with `|∇u| ≥ c` and `|H|∇u|| ≤ M` on `{u > t₁} ∩ Kᶜ`. -/
theorem capacitary_collar_of_C2_extension {K : Set E3} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hKR : K ⊆ closedBall 0 R₀)
    (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {g : E3 → ℝ} (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure Kᶜ))
    (hC2 : HasC2Boundary (interior K)) (hconn : IsPreconnected Kᶜ) :
    ∃ t₁ < 1, ∃ c > 0, ∃ M, ∀ x ∈ Kᶜ, t₁ < u x →
      c ≤ gradNorm u x ∧ |meanCurv u x * gradNorm u x| ≤ M := by
  obtain ⟨t₁, ht₁, c, hc, r, hcol⟩ := capacitary_collar_extension_gradient hK hreg hC1 hR₀
    hKR hzero hu hh hb hinf hg hug hC2 hconn
  have hDG : Continuous (fun y => fderiv ℝ (gradient g) y) :=
    (contDiff_gradient_of_contDiff_succ (r := 1) hg).continuous_fderiv one_ne_zero
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E3) r).exists_bound_of_continuousOn
    hDG.continuousOn
  refine ⟨t₁, ht₁, c, hc, M, ?_⟩
  intro x hx hux
  obtain ⟨hev, hgev⟩ := gradient_eventuallyEq_of_eqOn_closure hK.isClosed hug hx
  have hgx : gradient u x = gradient g x := hgev.eq_of_nhds
  obtain ⟨hcx, hxr⟩ := hcol x (subset_closure hx) hux
  have hwx : gradNorm u x = ‖gradient g x‖ := by rw [gradNorm, hgx]
  refine ⟨hwx ▸ hcx, ?_⟩
  have hu2 : ContDiffAt ℝ 2 u x := hg.contDiffAt.congr_of_eventuallyEq hev
  have hΔ : laplacianN u x = 0 :=
    kelvin_laplacianN_eq_zero_of_distributional hK.isClosed.isOpen_compl hu.continuousOn hh x hx
  have hw : 0 < gradNorm u x := hwx ▸ hc.trans_le hcx
  have hn : ‖unitNormal u x‖ = 1 := by
    rw [unitNormal, norm_neg, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_nonneg (gradNorm_nonneg u x)]
    exact inv_mul_cancel₀ hw.ne'
  rw [← dirHess_unitNormal_unitNormal hu2 hw hΔ, dirHess_eq_inner hu2, hgev.fderiv_eq]
  calc |⟪fderiv ℝ (gradient g) x (unitNormal u x), unitNormal u x⟫|
      ≤ ‖fderiv ℝ (gradient g) x (unitNormal u x)‖ * ‖unitNormal u x‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ ‖fderiv ℝ (gradient g) x‖ * ‖unitNormal u x‖ * ‖unitNormal u x‖ := by
        gcongr
        exact (fderiv ℝ (gradient g) x).le_opNorm _
    _ = ‖fderiv ℝ (gradient g) x‖ := by rw [hn, mul_one, mul_one]
    _ ≤ M := by
        exact hM x (ball_subset_closedBall hxr)

end LiquidDrop.CapacitaryK
