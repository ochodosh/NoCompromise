import NoCompromise.Topology.OneManifoldFlow
import NoCompromise.Topology.Ends
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Maximal integral curves on one-manifolds

For `lem:one-manifold`: a maximal integral curve of a nowhere-zero `C¹` field on a
connected Hausdorff one-manifold is onto; it is either injective on its open interval of
definition, or it is complete and periodic. Hence the manifold is homeomorphic to `ℝ` or to
an additive circle, and a noncompact one has exactly two ends.
-/

namespace LiquidDrop

open Set Function Filter Manifold
open scoped Topology

/-- Two points of an open order-connected set of reals lie in a common open interval
contained in it. -/
theorem exists_Ioo_subset_of_isOpen_ordConnected {J : Set ℝ} (hJ : IsOpen J)
    (hJc : J.OrdConnected) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) :
    ∃ a b : ℝ, Ioo a b ⊆ J ∧ s ∈ Ioo a b ∧ t ∈ Ioo a b := by
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.isOpen_iff.mp hJ s hs
  obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.isOpen_iff.mp hJ t ht
  have hs₁ : s - ε₁ / 2 ∈ J := hb₁ (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
  have hs₂ : s + ε₁ / 2 ∈ J := hb₁ (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
  have ht₁ : t - ε₂ / 2 ∈ J := hb₂ (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
  have ht₂ : t + ε₂ / 2 ∈ J := hb₂ (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
  rcases le_total s t with hst | hst
  · exact ⟨s - ε₁ / 2, t + ε₂ / 2, Ioo_subset_Icc_self.trans (hJc.out hs₁ ht₂),
      ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · exact ⟨t - ε₂ / 2, s + ε₁ / 2, Ioo_subset_Icc_self.trans (hJc.out ht₁ hs₂),
      ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- The union of two order-connected sets of reals with a common point is order-connected. -/
theorem ordConnected_union_of_mem {J K : Set ℝ} (hJ : J.OrdConnected) (hK : K.OrdConnected)
    {c : ℝ} (hcJ : c ∈ J) (hcK : c ∈ K) : (J ∪ K).OrdConnected := by
  rw [← isPreconnected_iff_ordConnected] at hJ hK ⊢
  exact hJ.union c hcJ hcK hK

/-- The translate `{r | r + d ∈ J}` of an order-connected set is order-connected. -/
theorem ordConnected_preimage_add_const {J : Set ℝ} (hJ : J.OrdConnected) (d : ℝ) :
    {r : ℝ | r + d ∈ J}.OrdConnected :=
  ⟨fun _ hx _ hy _ hz => hJ.out hx hy ⟨by linarith [hz.1], by linarith [hz.2]⟩⟩

/-- An open half-line `(a, ∞)` is homeomorphic to the real line. -/
theorem nonempty_homeomorph_Ioi_real (a : ℝ) : Nonempty (Ioi a ≃ₜ ℝ) :=
  ⟨{ toFun := fun t => Real.log (t - a)
     invFun := fun x => ⟨a + Real.exp x, lt_add_of_pos_right a (Real.exp_pos x)⟩
     left_inv := fun t => Subtype.ext (by
       change a + Real.exp (Real.log (t - a)) = t
       rw [Real.exp_log (sub_pos.mpr t.2)]; ring)
     right_inv := fun x => by
       change Real.log (a + Real.exp x - a) = x
       rw [add_sub_cancel_left, Real.log_exp]
     continuous_toFun := (continuous_subtype_val.sub continuous_const).log
       fun t => (sub_pos.mpr t.2).ne'
     continuous_invFun := (continuous_const.add Real.continuous_exp).subtype_mk _ }⟩

/-- An open half-line `(-∞, b)` is homeomorphic to the real line. -/
theorem nonempty_homeomorph_Iio_real (b : ℝ) : Nonempty (Iio b ≃ₜ ℝ) :=
  ⟨{ toFun := fun t => -Real.log (b - t)
     invFun := fun x => ⟨b - Real.exp (-x), sub_lt_self b (Real.exp_pos (-x))⟩
     left_inv := fun t => Subtype.ext (by
       change b - Real.exp (-(-Real.log (b - t))) = t
       rw [neg_neg, Real.exp_log (sub_pos.mpr t.2)]; ring)
     right_inv := fun x => by
       change -Real.log (b - (b - Real.exp (-x))) = x
       rw [sub_sub_cancel, Real.log_exp, neg_neg]
     continuous_toFun := by
       have h : Continuous fun t : Iio b => Real.log (b - t) :=
         (continuous_const.sub continuous_subtype_val).log fun t => (sub_pos.mpr t.2).ne'
       exact h.neg
     continuous_invFun :=
       (continuous_const.sub (Real.continuous_exp.comp continuous_neg)).subtype_mk _ }⟩

/-- A nonempty bounded open interval is homeomorphic to the real line. -/
theorem nonempty_homeomorph_Ioo_real {a b : ℝ} (hab : a < b) : Nonempty (Ioo a b ≃ₜ ℝ) := by
  have hmem : ∀ x : ℝ, (a + b * Real.exp x) / (1 + Real.exp x) ∈ Ioo a b := by
    intro x
    have he := Real.exp_pos x
    have h1 : (0 : ℝ) < 1 + Real.exp x := by positivity
    constructor
    · rw [lt_div_iff₀ h1]; nlinarith
    · rw [div_lt_iff₀ h1]; nlinarith
  refine ⟨{ toFun := fun t => Real.log (t - a) - Real.log (b - t)
            invFun := fun x => ⟨(a + b * Real.exp x) / (1 + Real.exp x), hmem x⟩
            left_inv := fun t => Subtype.ext ?_
            right_inv := fun x => ?_
            continuous_toFun := ((continuous_subtype_val.sub continuous_const).log
              fun t => (sub_pos.mpr t.2.1).ne').sub ((continuous_const.sub
                continuous_subtype_val).log fun t => (sub_pos.mpr t.2.2).ne')
            continuous_invFun := ((continuous_const.add (continuous_const.mul
              Real.continuous_exp)).div (continuous_const.add Real.continuous_exp)
                fun x => (by positivity : (0 : ℝ) < 1 + Real.exp x).ne').subtype_mk _ }⟩
  · have h1 : 0 < (t : ℝ) - a := sub_pos.mpr t.2.1
    have h2 : 0 < b - (t : ℝ) := sub_pos.mpr t.2.2
    change (a + b * Real.exp (Real.log (t - a) - Real.log (b - t))) /
      (1 + Real.exp (Real.log (t - a) - Real.log (b - t))) = t
    rw [Real.exp_sub, Real.exp_log h1, Real.exp_log h2]
    field_simp
    ring
  · have he := Real.exp_pos x
    have h1 : (0 : ℝ) < 1 + Real.exp x := by positivity
    have hA : (0 : ℝ) < (b - a) / (1 + Real.exp x) := div_pos (sub_pos.mpr hab) h1
    change Real.log ((a + b * Real.exp x) / (1 + Real.exp x) - a) -
      Real.log (b - (a + b * Real.exp x) / (1 + Real.exp x)) = x
    have e1 : (a + b * Real.exp x) / (1 + Real.exp x) - a =
        (b - a) / (1 + Real.exp x) * Real.exp x := by
      field_simp; ring
    have e2 : b - (a + b * Real.exp x) / (1 + Real.exp x) = (b - a) / (1 + Real.exp x) := by
      field_simp; ring
    rw [e1, e2, Real.log_mul hA.ne' he.ne', Real.log_exp]
    ring

/-- A nonempty open order-connected set of reals is homeomorphic to the real line. -/
theorem nonempty_homeomorph_real_of_isOpen_ordConnected {J : Set ℝ} (hJo : IsOpen J)
    (hJc : J.OrdConnected) (hne : J.Nonempty) : Nonempty (J ≃ₜ ℝ) := by
  have key : ∀ t, t ∈ J ↔ (∃ x ∈ J, x < t) ∧ (∃ y ∈ J, t < y) := fun t =>
    ⟨fun ht => by
      obtain ⟨a, b, hab, hta, -⟩ := exists_Ioo_subset_of_isOpen_ordConnected hJo hJc ht ht
      obtain ⟨h1, h2⟩ := hta
      exact ⟨⟨(a + t) / 2, hab ⟨by linarith, by linarith⟩, by linarith⟩,
        ⟨(t + b) / 2, hab ⟨by linarith, by linarith⟩, by linarith⟩⟩,
    fun ⟨⟨_, hx, hxt⟩, ⟨_, hy, hty⟩⟩ => hJc.out hx hy ⟨hxt.le, hty.le⟩⟩
  by_cases hb : BddBelow J <;> by_cases ha : BddAbove J
  · have hJ : J = Ioo (sInf J) (sSup J) := ext fun t => by
      rw [key t, mem_Ioo, csInf_lt_iff hb hne, lt_csSup_iff ha hne]
    have hlt : sInf J < sSup J := by
      obtain ⟨t, ht⟩ := hne
      have h := (key t).mp ht
      exact ((csInf_lt_iff hb ⟨t, ht⟩).mpr h.1).trans ((lt_csSup_iff ha ⟨t, ht⟩).mpr h.2)
    obtain ⟨e⟩ := nonempty_homeomorph_Ioo_real hlt
    exact ⟨(Homeomorph.setCongr hJ).trans e⟩
  · have hJ : J = Ioi (sInf J) := ext fun t => by
      rw [key t, mem_Ioi, csInf_lt_iff hb hne, and_iff_left (not_bddAbove_iff.mp ha t)]
    obtain ⟨e⟩ := nonempty_homeomorph_Ioi_real (sInf J)
    exact ⟨(Homeomorph.setCongr hJ).trans e⟩
  · have hJ : J = Iio (sSup J) := ext fun t => by
      rw [key t, mem_Iio, lt_csSup_iff ha hne, and_iff_right (not_bddBelow_iff.mp hb t)]
    obtain ⟨e⟩ := nonempty_homeomorph_Iio_real (sSup J)
    exact ⟨(Homeomorph.setCongr hJ).trans e⟩
  · have hJ : J = univ := eq_univ_of_forall fun t =>
      (key t).mpr ⟨not_bddBelow_iff.mp hb t, not_bddAbove_iff.mp ha t⟩
    exact ⟨(Homeomorph.setCongr hJ).trans (Homeomorph.Set.univ ℝ)⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
  {v : (x : M) → TangentSpace 𝓘(ℝ, ℝ) x}

/-- A local integral curve stays one after changing the curve on a neighbourhood. -/
theorem oneManifold_isMIntegralCurveAt_congr {γ γ₁ : ℝ → M} {t₀ : ℝ}
    (hγ : IsMIntegralCurveAt γ v t₀) (h : γ₁ =ᶠ[𝓝 t₀] γ) : IsMIntegralCurveAt γ₁ v t₀ := by
  filter_upwards [(hγ : ∀ᶠ t in 𝓝 t₀, _), h.eventuallyEq_nhds] with t ht hte
  have h' := ht.congr_of_eventuallyEq_abuse hte
  rwa [← hte.eq_of_nhds] at h'

/-- An integral curve on an open set stays one after changing the curve off the set. -/
theorem oneManifold_isMIntegralCurveOn_congr {γ γ₁ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J)
    (hγ : IsMIntegralCurveOn γ v J) (h : EqOn γ₁ γ J) : IsMIntegralCurveOn γ₁ v J := by
  rw [isMIntegralCurveOn_iff_isMIntegralCurveAt hJ] at hγ ⊢
  exact fun t ht => oneManifold_isMIntegralCurveAt_congr (hγ t ht)
    (eventuallyEq_of_mem (hJ.mem_nhds ht) h)

/-- `γ` is a maximal integral curve of `v` through `x₀` at time `0`, with open interval of
definition `J`: every integral curve of `v` through `x₀` at time `0` on an open
order-connected set of times containing `0` is defined within `J` and agrees with `γ`. -/
def IsMaximalMIntegralCurveOn (v : (x : M) → TangentSpace 𝓘(ℝ, ℝ) x) (x₀ : M) (γ : ℝ → M)
    (J : Set ℝ) : Prop :=
  IsOpen J ∧ J.OrdConnected ∧ (0 : ℝ) ∈ J ∧ γ 0 = x₀ ∧ IsMIntegralCurveOn γ v J ∧
    ∀ (J' : Set ℝ) (γ' : ℝ → M), IsOpen J' → J'.OrdConnected → (0 : ℝ) ∈ J' → γ' 0 = x₀ →
      IsMIntegralCurveOn γ' v J' → J' ⊆ J ∧ EqOn γ' γ J'

variable [IsManifold 𝓘(ℝ, ℝ) 1 M] [T2Space M]
    (hv : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent 1
      (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, ℝ) M)))

include hv

/-- Uniqueness of integral curves on an open order-connected set of times. -/
theorem oneManifold_isMIntegralCurveOn_eqOn {γ γ' : ℝ → M} {J : Set ℝ} (hJ : IsOpen J)
    (hJc : J.OrdConnected) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (hγ : IsMIntegralCurveOn γ v J)
    (hγ' : IsMIntegralCurveOn γ' v J) (h : γ t₀ = γ' t₀) : EqOn γ γ' J := by
  intro t ht
  obtain ⟨a, b, hab, ha, hb⟩ := exists_Ioo_subset_of_isOpen_ordConnected hJ hJc ht₀ ht
  exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless ha hv (hγ.mono hab)
    (hγ'.mono hab) h hb

/-- Two integral curves on overlapping open order-connected sets of times which agree at one
common time glue to an integral curve on the union, equal to the second curve on its domain. -/
theorem oneManifold_isMIntegralCurveOn_piecewise {γ δ : ℝ → M} {J K : Set ℝ}
    [DecidablePred (· ∈ J)]
    (hJ : IsOpen J) (hJc : J.OrdConnected) (hK : IsOpen K) (hKc : K.OrdConnected)
    (hγ : IsMIntegralCurveOn γ v J) (hδ : IsMIntegralCurveOn δ v K) {t₁ : ℝ}
    (ht₁J : t₁ ∈ J) (ht₁K : t₁ ∈ K) (h : γ t₁ = δ t₁) :
    IsMIntegralCurveOn (J.piecewise γ δ) v (J ∪ K) ∧ EqOn (J.piecewise γ δ) δ K := by
  have heq : EqOn (J.piecewise γ δ) δ K := by
    intro t ht
    by_cases htJ : t ∈ J
    · rw [piecewise_eq_of_mem _ _ _ htJ]
      exact oneManifold_isMIntegralCurveOn_eqOn hv (hJ.inter hK) (hJc.inter hKc)
        ⟨ht₁J, ht₁K⟩ (hγ.mono inter_subset_left) (hδ.mono inter_subset_right) h ⟨htJ, ht⟩
    · rw [piecewise_eq_of_notMem _ _ _ htJ]
  refine ⟨?_, heq⟩
  rw [isMIntegralCurveOn_iff_isMIntegralCurveAt (hJ.union hK)]
  rintro t (htJ | htK)
  · exact oneManifold_isMIntegralCurveAt_congr (hγ.isMIntegralCurveAt (hJ.mem_nhds htJ))
      (eventuallyEq_of_mem (hJ.mem_nhds htJ) (piecewise_eqOn _ _ _))
  · exact oneManifold_isMIntegralCurveAt_congr (hδ.isMIntegralCurveAt (hK.mem_nhds htK))
      (eventuallyEq_of_mem (hK.mem_nhds htK) heq)



/-- Every point has a maximal integral curve through it, defined on the union of the open
intervals of definition of all integral curves through it. -/
theorem oneManifold_exists_isMaximalMIntegralCurveOn (x₀ : M) :
    ∃ (γ : ℝ → M) (J : Set ℝ), IsMaximalMIntegralCurveOn v x₀ γ J := by
  classical
  let A : Set (Set ℝ × (ℝ → M)) := {p | IsOpen p.1 ∧ p.1.OrdConnected ∧ (0 : ℝ) ∈ p.1 ∧
    p.2 0 = x₀ ∧ IsMIntegralCurveOn p.2 v p.1}
  have key : ∀ p ∈ A, ∀ q ∈ A, EqOn p.2 q.2 (p.1 ∩ q.1) := fun p hp q hq =>
    oneManifold_isMIntegralCurveOn_eqOn hv (hp.1.inter hq.1) (hp.2.1.inter hq.2.1)
      ⟨hp.2.2.1, hq.2.2.1⟩ (hp.2.2.2.2.mono inter_subset_left)
      (hq.2.2.2.2.mono inter_subset_right) (hp.2.2.2.1.trans hq.2.2.2.1.symm)
  let J : Set ℝ := ⋃ p ∈ A, p.1
  let γ : ℝ → M := fun t => if h : ∃ p ∈ A, t ∈ p.1 then h.choose.2 t else x₀
  have hγ : ∀ p ∈ A, EqOn γ p.2 p.1 := by
    intro p hp t ht
    have h : ∃ p ∈ A, t ∈ p.1 := ⟨p, hp, ht⟩
    simp only [γ, dite_eq_left h]
    exact key _ h.choose_spec.1 p hp ⟨h.choose_spec.2, ht⟩
  have hmemJ : ∀ t, t ∈ J ↔ ∃ p ∈ A, t ∈ p.1 := fun t => by
    simp only [J, mem_iUnion₂, exists_prop]
  obtain ⟨δ, hδ0, hδ⟩ := exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
    (I := 𝓘(ℝ, ℝ)) (v := v) (x₀ := x₀) (0 : ℝ) (hv x₀)
  obtain ⟨ε, hε, hδε⟩ := isMIntegralCurveAt_iff'.mp hδ
  have hball : Metric.ball (0 : ℝ) ε = Ioo (-ε) ε := by
    rw [Real.ball_eq_Ioo]; simp
  rw [hball] at hδε
  have hA0 : (Ioo (-ε) ε, δ) ∈ A :=
    ⟨isOpen_Ioo, ordConnected_Ioo, ⟨by linarith, hε⟩, hδ0, hδε⟩
  have hJo : IsOpen J := isOpen_biUnion fun p hp => hp.1
  have h0J : (0 : ℝ) ∈ J := (hmemJ 0).mpr ⟨_, hA0, hA0.2.2.1⟩
  have hJc : J.OrdConnected := by
    refine ⟨fun x hx y hy z hz => ?_⟩
    obtain ⟨p, hp, hxp⟩ := (hmemJ x).mp hx
    obtain ⟨q, hq, hyq⟩ := (hmemJ y).mp hy
    rcases le_total z 0 with hz0 | hz0
    · exact (hmemJ z).mpr ⟨p, hp, hp.2.1.out hxp hp.2.2.1 ⟨hz.1, hz0⟩⟩
    · exact (hmemJ z).mpr ⟨q, hq, hq.2.1.out hq.2.2.1 hyq ⟨hz0, hz.2⟩⟩
  refine ⟨γ, J, hJo, hJc, h0J, ?_, ?_, ?_⟩
  · rw [hγ _ hA0 hA0.2.2.1]; exact hδ0
  · rw [isMIntegralCurveOn_iff_isMIntegralCurveAt hJo]
    intro t ht
    obtain ⟨p, hp, htp⟩ := (hmemJ t).mp ht
    exact oneManifold_isMIntegralCurveAt_congr
      (hp.2.2.2.2.isMIntegralCurveAt (hp.1.mem_nhds htp))
      (eventuallyEq_of_mem (hp.1.mem_nhds htp) (hγ p hp))
  · intro J' γ' hJ' hJ'c h0 hγ0 hγ'
    have hp : (J', γ') ∈ A := ⟨hJ', hJ'c, h0, hγ0, hγ'⟩
    exact ⟨fun t ht => (hmemJ t).mpr ⟨_, hp, ht⟩, fun t ht => (hγ _ hp ht).symm⟩

/-- If a maximal integral curve takes the same value at times `s` and `t`, its interval of
definition is invariant under translation by `s - t`. -/
theorem IsMaximalMIntegralCurveOn.mem_of_add_mem {x₀ : M} {γ : ℝ → M} {J : Set ℝ}
    (hmax : IsMaximalMIntegralCurveOn v x₀ γ J) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J)
    (hst : γ s = γ t) {r : ℝ} (hr : r + (t - s) ∈ J) : r ∈ J := by
  classical
  obtain ⟨hJo, hJc, h0J, hγ0, hγ, hmaxJ⟩ := hmax
  have hKo : IsOpen {r : ℝ | r + (t - s) ∈ J} := hJo.preimage (continuous_add_const _)
  have hKc := ordConnected_preimage_add_const hJc (t - s)
  have hsK : s ∈ {r : ℝ | r + (t - s) ∈ J} := by
    change s + (t - s) ∈ J
    rwa [add_sub_cancel]
  have hδ : IsMIntegralCurveOn (γ ∘ (· + (t - s))) v {r : ℝ | r + (t - s) ∈ J} :=
    hγ.comp_add _
  have hs' : γ s = (γ ∘ (· + (t - s))) s := by
    simp only [comp_apply, add_sub_cancel, hst]
  obtain ⟨hg, -⟩ :=
    oneManifold_isMIntegralCurveOn_piecewise hv hJo hJc hKo hKc hγ hδ hs hsK hs'
  exact (hmaxJ _ _ (hJo.union hKo) (ordConnected_union_of_mem hJc hKc hs hsK) (Or.inl h0J)
    (by rw [piecewise_eq_of_mem _ _ _ h0J]; exact hγ0) hg).1 (Or.inr hr)

/-- A maximal integral curve which is not injective is complete. -/
theorem IsMaximalMIntegralCurveOn.eq_univ_of_not_injOn {x₀ : M} {γ : ℝ → M} {J : Set ℝ}
    (hmax : IsMaximalMIntegralCurveOn v x₀ γ J) (hinj : ¬ InjOn γ J) :
    J = univ ∧ IsMIntegralCurve γ v := by
  obtain ⟨s, hs, t, ht, hst, hne⟩ : ∃ s ∈ J, ∃ t ∈ J, γ s = γ t ∧ s ≠ t := by
    by_contra hc
    push Not at hc
    exact hinj fun a ha b hb hab => hc a ha b hb hab
  set d := t - s with hd
  have hup : ∀ r ∈ J, r + d ∈ J := fun r hr =>
    hmax.mem_of_add_mem hv ht hs hst.symm (by rwa [show r + d + (s - t) = r by rw [hd]; ring])
  have hdown : ∀ r ∈ J, r - d ∈ J := fun r hr =>
    hmax.mem_of_add_mem hv hs ht hst (by rwa [show r - d + (t - s) = r by rw [hd]; ring])
  have hiter : ∀ n : ℕ, (n : ℝ) * d ∈ J ∧ -((n : ℝ) * d) ∈ J := by
    intro n
    induction n with
    | zero => simpa using hmax.2.2.1
    | succ n ih =>
      constructor
      · have h := hup _ ih.1
        rwa [show (n : ℝ) * d + d = ((n + 1 : ℕ) : ℝ) * d by push_cast; ring] at h
      · have h := hdown _ ih.2
        rwa [show -((n : ℝ) * d) - d = -(((n + 1 : ℕ) : ℝ) * d) by push_cast; ring] at h
  have hJ : J = univ := by
    refine eq_univ_of_forall fun x => ?_
    have hd0 : 0 < |d| := abs_pos.mpr (sub_ne_zero.mpr hne.symm)
    obtain ⟨n, hn⟩ := exists_nat_gt (|x| / |d|)
    have hxc : |x| < |(n : ℝ) * d| := by
      rw [abs_mul, Nat.abs_cast]
      exact (div_lt_iff₀ hd0).mp hn
    obtain ⟨h1, h2⟩ := abs_lt.mp hxc
    apply hmax.2.1.uIcc_subset (hiter n).2 (hiter n).1
    rw [mem_uIcc]
    rcases le_total 0 ((n : ℝ) * d) with h | h
    · rw [abs_of_nonneg h] at h1 h2
      exact Or.inl ⟨h1.le, h2.le⟩
    · rw [abs_of_nonpos h] at h1 h2
      exact Or.inr ⟨by linarith, by linarith⟩
  refine ⟨hJ, isMIntegralCurve_iff_isMIntegralCurveOn.mpr ?_⟩
  rw [← hJ]
  exact hmax.2.2.2.2.1

variable (hv0 : ∀ x, v x ≠ 0)

include hv0

/-- A maximal integral curve of a nowhere-zero field on a connected one-manifold is onto:
its orbit is open, and so is the complement, by local existence and maximality. -/
theorem IsMaximalMIntegralCurveOn.image_eq_univ [ConnectedSpace M] {x₀ : M} {γ : ℝ → M}
    {J : Set ℝ} (hmax : IsMaximalMIntegralCurveOn v x₀ γ J) : γ '' J = univ := by
  classical
  obtain ⟨hJo, hJc, h0J, hγ0, hγ, hmaxJ⟩ := hmax
  have hopen : IsOpen (γ '' J) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨t, ht, rfl⟩
    rw [← oneManifold_integralCurveAt_map_nhds hv hv0 (hγ.isMIntegralCurveAt (hJo.mem_nhds ht))]
    exact image_mem_map (hJo.mem_nhds ht)
  have hclosed : IsOpen (γ '' J)ᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨δ, hδ0, hδ⟩ := exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
      (I := 𝓘(ℝ, ℝ)) (v := v) (x₀ := x) (0 : ℝ) (hv x)
    obtain ⟨ε, hε, hδε⟩ := isMIntegralCurveAt_iff'.mp hδ
    have hball : Metric.ball (0 : ℝ) ε = Ioo (-ε) ε := by
      rw [Real.ball_eq_Ioo]; simp
    rw [hball] at hδε
    have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
    have hn : δ '' Ioo (-ε) ε ∈ 𝓝 x := by
      rw [← hδ0, ← oneManifold_integralCurveAt_map_nhds hv hv0 hδ]
      exact image_mem_map (Ioo_mem_nhds h0.1 h0.2)
    apply mem_of_superset hn
    rintro _ ⟨s, hs, rfl⟩ ⟨u, hu, hus⟩
    apply hx
    have hKo : IsOpen {r : ℝ | r + (s - u) ∈ Ioo (-ε) ε} :=
      isOpen_Ioo.preimage (continuous_add_const _)
    have hKc := ordConnected_preimage_add_const (ordConnected_Ioo (a := -ε) (b := ε)) (s - u)
    have huK : u ∈ {r : ℝ | r + (s - u) ∈ Ioo (-ε) ε} := by
      change u + (s - u) ∈ Ioo (-ε) ε
      rwa [add_sub_cancel]
    have hδ' : IsMIntegralCurveOn (δ ∘ (· + (s - u))) v {r : ℝ | r + (s - u) ∈ Ioo (-ε) ε} :=
      hδε.comp_add _
    have hu' : γ u = (δ ∘ (· + (s - u))) u := by
      simp only [comp_apply, add_sub_cancel, hus]
    obtain ⟨hg, hgK⟩ :=
      oneManifold_isMIntegralCurveOn_piecewise hv hJo hJc hKo hKc hγ hδ' hu huK hu'
    have hmax' := hmaxJ _ _ (hJo.union hKo) (ordConnected_union_of_mem hJc hKc hu huK)
      (Or.inl h0J) (by rw [piecewise_eq_of_mem _ _ _ h0J]; exact hγ0) hg
    have hdK : -(s - u) ∈ {r : ℝ | r + (s - u) ∈ Ioo (-ε) ε} := by
      change -(s - u) + (s - u) ∈ Ioo (-ε) ε
      rwa [neg_add_cancel]
    have hdJ : -(s - u) ∈ J := hmax'.1 (Or.inr hdK)
    refine ⟨-(s - u), hdJ, ?_⟩
    rw [← piecewise_eq_of_mem J γ (δ ∘ (· + (s - u))) hdJ, hgK hdK, comp_apply,
      neg_add_cancel, hδ0]
  exact IsClopen.eq_univ ⟨isOpen_compl_iff.mp hclosed, hopen⟩ ⟨x₀, 0, h0J, hγ0⟩


/-- An injective maximal integral curve of a nowhere-zero field on a connected one-manifold
is a homeomorphism from its interval of definition onto the manifold. -/
theorem IsMaximalMIntegralCurveOn.exists_homeomorph [ConnectedSpace M] {x₀ : M} {γ : ℝ → M}
    {J : Set ℝ} (hmax : IsMaximalMIntegralCurveOn v x₀ γ J) (hinj : InjOn γ J) :
    ∃ e : J ≃ₜ M, ∀ t : J, e t = γ t := by
  have hsurj : Surjective (J.domRestrict γ) := by
    intro x
    obtain ⟨t, ht, rfl⟩ : x ∈ γ '' J := (hmax.image_eq_univ hv hv0).symm ▸ mem_univ x
    exact ⟨⟨t, ht⟩, rfl⟩
  obtain ⟨hJo, -, -, -, hγ, -⟩ := hmax
  have hinj' : Injective (J.domRestrict γ) := fun a b hab => Subtype.ext (hinj a.2 b.2 hab)
  have hopen : IsOpenMap (J.domRestrict γ) := by
    intro U hU
    have hU' : IsOpen ((↑) '' U : Set ℝ) := hJo.isOpenMap_subtype_val U hU
    rw [show J.domRestrict γ '' U = γ '' ((↑) '' U) by rw [image_image]; rfl,
      isOpen_iff_mem_nhds]
    rintro _ ⟨t, ht, rfl⟩
    have htJ : t ∈ J := by
      obtain ⟨u, -, rfl⟩ := ht
      exact u.2
    rw [← oneManifold_integralCurveAt_map_nhds hv hv0
      (hγ.isMIntegralCurveAt (hJo.mem_nhds htJ))]
    exact image_mem_map (hU'.mem_nhds ht)
  exact ⟨Equiv.toHomeomorphOfContinuousOpen (Equiv.ofBijective _ ⟨hinj', hsurj⟩)
    hγ.continuousOn.domRestrict hopen, fun _ => rfl⟩

/-- `lem:one-manifold`, maximal curve form. A maximal integral curve of a nowhere-zero `C¹`
field on a connected Hausdorff one-manifold is onto; either it is injective on its open
interval of definition `J` and parametrizes the manifold homeomorphically by `J`, or it is
complete and periodic, with a least period `τ > 0` giving a homeomorphism from
`AddCircle τ`. -/
theorem IsMaximalMIntegralCurveOn.classification [ConnectedSpace M] {x₀ : M} {γ : ℝ → M}
    {J : Set ℝ} (hmax : IsMaximalMIntegralCurveOn v x₀ γ J) :
    γ '' J = univ ∧
      ((InjOn γ J ∧ ∃ e : J ≃ₜ M, ∀ t : J, e t = γ t) ∨
       (J = univ ∧ IsMIntegralCurve γ v ∧ ∃ τ > 0, Periodic γ τ ∧ InjOn γ (Ico 0 τ) ∧
         ∃ e : AddCircle τ ≃ₜ M, ∀ t : ℝ, e (t : AddCircle τ) = γ t)) := by
  refine ⟨hmax.image_eq_univ hv hv0, ?_⟩
  by_cases hinj : InjOn γ J
  · exact Or.inl ⟨hinj, hmax.exists_homeomorph hv hv0 hinj⟩
  · obtain ⟨hJ, hγ⟩ := hmax.eq_univ_of_not_injOn hv hinj
    refine Or.inr ⟨hJ, hγ, ?_⟩
    rcases (oneManifold_classification_of_isMIntegralCurve hv hv0 hγ).2 with ⟨hinj', -⟩ | h
    · exact absurd (by intro a _ b _ hab; exact hinj' hab) hinj
    · exact h

/-- `lem:one-manifold`. A connected Hausdorff one-manifold carrying a nowhere-zero `C¹`
tangent field is homeomorphic to the real line or to an additive circle. -/
theorem oneManifold_homeomorph_real_or_addCircle [ConnectedSpace M] :
    Nonempty (M ≃ₜ ℝ) ∨ ∃ τ > (0 : ℝ), Nonempty (M ≃ₜ AddCircle τ) := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  obtain ⟨γ, J, hmax⟩ := oneManifold_exists_isMaximalMIntegralCurveOn hv x₀
  rcases (hmax.classification hv hv0).2 with ⟨-, e, -⟩ | ⟨-, -, τ, hτ, -, -, e, -⟩
  · obtain ⟨f⟩ := nonempty_homeomorph_real_of_isOpen_ordConnected hmax.1 hmax.2.1
      ⟨0, hmax.2.2.1⟩
    exact Or.inl ⟨e.symm.trans f⟩
  · exact Or.inr ⟨τ, hτ, ⟨e.symm⟩⟩

/-- `lem:one-manifold`, ends. A noncompact connected Hausdorff one-manifold carrying a
nowhere-zero `C¹` tangent field has exactly two ends. -/
theorem oneManifold_hasExactlyTwoEnds [ConnectedSpace M] (hM : ¬ CompactSpace M) :
    HasExactlyTwoEnds M := by
  rcases oneManifold_homeomorph_real_or_addCircle hv hv0 with h | ⟨τ, hτ, h⟩
  · obtain ⟨e⟩ := h
    exact Homeomorph.hasExactlyTwoEnds e.symm hasExactlyTwoEnds_real
  · obtain ⟨e⟩ := h
    have : Fact (0 < τ) := ⟨hτ⟩
    exact absurd e.symm.compactSpace hM

end LiquidDrop
