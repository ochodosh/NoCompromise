import NoCompromise.Topology.Transversality
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Connected.LocallyConnected

/-!
# Local sides and complementary components

The local sides are constructed using strict increase along parallel segments
and a positive ball around one endpoint. No implicit function theorem is used.
Coverage by two components propagates along the connected surface; a locally
constant parity with a transverse crossing change then distinguishes them.
-/

namespace LiquidDrop
noncomputable section
open Set Filter
open scoped Topology Gradient

private lemma sides_line_deriv {φ : E₃ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (y v : E₃) (t : ℝ) :
    HasDerivAt (fun s : ℝ => φ (y + s • v)) (fderiv ℝ φ (y + t • v) v) t := by
  exact (hφ.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
    (by simpa using (((hasDerivAt_id t).smul_const v).const_add y))

private lemma sides_positive_component {S U : Set E₃} {φ : E₃ → ℝ}
    (hU : IsOpen U) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hzero : S ∩ U = {x ∈ U | φ x = 0}) {p v : E₃}
    (hp : p ∈ U) (hz : φ p = 0) (hv : 0 < fderiv ℝ φ p v) :
    ∃ r > 0, Metric.ball p r ⊆ U ∧ ∃ K : Set E₃,
      IsPreconnected K ∧ K ⊆ Sᶜ ∧ Metric.ball p r ∩ {x | 0 < φ x} ⊆ K := by
  have hopen : IsOpen {x | x ∈ U ∧ 0 < fderiv ℝ φ x v} :=
    hU.inter (isOpen_lt continuous_const ((hφ.continuous_fderiv (by simp)).clm_apply
      continuous_const))
  obtain ⟨R, hR, hRb⟩ := Metric.isOpen_iff.mp hopen p ⟨hp, hv⟩
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr (by
    intro h; simp [h] at hv)
  let L : ℝ := R / (2 * ‖v‖)
  have hL : 0 < L := div_pos hR (by positivity)
  have hLR : L * ‖v‖ = R / 2 := by dsimp [L]; field_simp
  have hline (y : E₃) (hy : y ∈ Metric.ball p (R / 4)) (t : ℝ)
      (ht : t ∈ Icc (0 : ℝ) L) : y + t • v ∈ Metric.ball p R := by
    calc
      dist (y + t • v) p ≤ dist y p + ‖t • v‖ := by
        simpa [dist_eq_norm, add_sub_right_comm] using norm_add_le (y - p) (t • v)
      _ = dist y p + t * ‖v‖ := by rw [norm_smul, Real.norm_of_nonneg ht.1]
      _ ≤ dist y p + L * ‖v‖ := add_le_add_right
        (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg v)) _
      _ < R := by rw [hLR]; have := Metric.mem_ball.mp hy; linarith
  have hmono (y : E₃) (hy : y ∈ Metric.ball p (R / 4)) :
      StrictMonoOn (fun t : ℝ => φ (y + t • v)) (Icc 0 L) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (hφ.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
    intro t ht
    change 0 < deriv (fun s : ℝ => φ (y + s • v)) t
    rw [(sides_line_deriv hφ y v t).deriv]
    exact (hRb (hline y hy t (interior_subset ht))).2
  have hpp : p ∈ Metric.ball p (R / 4) := Metric.mem_ball_self (by positivity)
  have hpos : 0 < φ (p + L • v) := by
    simpa [hz] using hmono p hpp ⟨le_rfl, hL.le⟩ ⟨hL.le, le_rfl⟩ hL
  obtain ⟨δ, hδ, hδb⟩ := Metric.isOpen_iff.mp
    (hU.inter (isOpen_lt continuous_const hφ.continuous)) (p + L • v)
    ⟨(hRb (hline p hpp L ⟨hL.le, le_rfl⟩)).1, hpos⟩
  have hav (x : E₃) (hxU : x ∈ U) (hx : 0 < φ x) : x ∈ Sᶜ := by
    intro hxS
    have := (hzero ▸ (show x ∈ S ∩ U from ⟨hxS, hxU⟩)).2
    linarith
  refine ⟨min (R / 4) δ, lt_min (by positivity) hδ, ?_,
    connectedComponentIn Sᶜ (p + L • v), isPreconnected_connectedComponentIn,
    connectedComponentIn_subset _ _, ?_⟩
  · intro x hx
    exact (hRb (Metric.mem_ball.mpr ((Metric.mem_ball.mp hx).trans_le
      ((min_le_left _ _).trans (by linarith))))).1
  · rintro y ⟨hy, hypos⟩
    have hyr : y ∈ Metric.ball p (R / 4) :=
      Metric.mem_ball.mpr ((Metric.mem_ball.mp hy).trans_le (min_le_left _ _))
    let T := (fun t : ℝ => y + t • v) '' Icc 0 L
    have hT : IsPreconnected T := isPreconnected_Icc.image _
      (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
    have hend : y + L • v ∈ Metric.ball (p + L • v) δ := by
      simpa only [Metric.mem_ball, dist_add_right] using
        (Metric.mem_ball.mp hy).trans_le (min_le_right _ _)
    have hconn := IsPreconnected.union (y + L • v) hend
      (show y + L • v ∈ T from ⟨L, ⟨hL.le, le_rfl⟩, rfl⟩)
      (convex_ball _ _).isPreconnected hT
    apply hconn.subset_connectedComponentIn
      (Or.inl (Metric.mem_ball_self hδ)) ?_ (Or.inr ?_)
    · rintro x (hx | ⟨t, ht, rfl⟩)
      · exact hav x (hδb hx).1 (hδb hx).2
      · apply hav _ (hRb (hline y hyr t ht)).1
        have := (hmono y hyr).monotoneOn ⟨le_rfl, hL.le⟩ ht ht.1
        simpa using hypos.trans_le (by simpa using this)
    · exact ⟨0, ⟨le_rfl, hL.le⟩, by simp⟩

/-- `prop:orientation-parity (ii)`: the positive and negative local sides each lie
in a preconnected subset of the complement. -/
theorem exists_local_sides {S U : Set E₃} {φ : E₃ → ℝ} (hU : IsOpen U)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hzero : S ∩ U = {x ∈ U | φ x = 0})
    {p₀ : E₃} (hp₀U : p₀ ∈ U) (hφp₀ : φ p₀ = 0) (hreg : gradient φ p₀ ≠ 0) :
    ∃ r > 0, Metric.ball p₀ r ⊆ U ∧ ∃ Kpos Kneg : Set E₃,
      IsPreconnected Kpos ∧ IsPreconnected Kneg ∧
      Kpos ⊆ Sᶜ ∧ Kneg ⊆ Sᶜ ∧
      Metric.ball p₀ r ∩ {x | 0 < φ x} ⊆ Kpos ∧ Metric.ball p₀ r ∩ {x | φ x < 0} ⊆ Kneg := by
  have hv : 0 < fderiv ℝ φ p₀ (gradient φ p₀) := by
    rw [← inner_gradient_left, real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hreg)
  obtain ⟨rpos, hrpos, hbpos, Kpos, hcpos, hspos, hkpos⟩ :=
    sides_positive_component hU hφ hzero hp₀U hφp₀ hv
  have hzneg : S ∩ U = {x ∈ U | -φ x = 0} := by simpa using hzero
  have hvneg : 0 < fderiv ℝ (fun x => -φ x) p₀ (-gradient φ p₀) := by
    rw [show (fun x => -φ x) = -φ from rfl, fderiv_neg]
    simpa using hv
  obtain ⟨rneg, hrneg, hbneg, Kneg, hcneg, hsneg, hkneg⟩ :=
    sides_positive_component hU hφ.neg hzneg hp₀U (by simp [hφp₀]) hvneg
  refine ⟨min rpos rneg, lt_min hrpos hrneg,
    (Metric.ball_subset_ball (min_le_left _ _)).trans hbpos, Kpos, Kneg,
    hcpos, hcneg, hspos, hsneg, ?_, ?_⟩
  · exact fun x hx => hkpos ⟨Metric.ball_subset_ball (min_le_left _ _) hx.1, hx.2⟩
  · exact fun x hx => hkneg ⟨Metric.ball_subset_ball (min_le_right _ _) hx.1,
      by simpa only [mem_ofPred_eq, neg_pos] using hx.2⟩

/-- `prop:orientation-parity (ii)`: a sufficiently small punctured neighborhood
of a regular level set is covered by two preconnected subsets of its complement. -/
theorem exists_local_sides_cover {S U : Set E₃} {φ : E₃ → ℝ} (hU : IsOpen U)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hzero : S ∩ U = {x ∈ U | φ x = 0})
    {p₀ : E₃} (hp₀U : p₀ ∈ U) (hφp₀ : φ p₀ = 0) (hreg : gradient φ p₀ ≠ 0) :
    ∃ r > 0, Metric.ball p₀ r ⊆ U ∧ ∃ Kpos Kneg : Set E₃,
      IsPreconnected Kpos ∧ IsPreconnected Kneg ∧ Kpos ⊆ Sᶜ ∧ Kneg ⊆ Sᶜ ∧
      Metric.ball p₀ r \ S ⊆ Kpos ∪ Kneg := by
  obtain ⟨r, hr, hb, Kpos, Kneg, hcpos, hcneg, hspos, hsneg, hkpos, hkneg⟩ :=
    exists_local_sides hU hφ hzero hp₀U hφp₀ hreg
  refine ⟨r, hr, hb, Kpos, Kneg, hcpos, hcneg, hspos, hsneg, ?_⟩
  rintro x ⟨hx, hxs⟩
  have hne : φ x ≠ 0 := by
    intro he
    have : x ∈ S ∩ U := hzero.symm ▸ (show x ∈ {x ∈ U | φ x = 0} from ⟨hb hx, he⟩)
    exact hxs this.1
  rcases lt_or_gt_of_ne hne with hn | hp
  · exact Or.inr (hkneg ⟨hx, hn⟩)
  · exact Or.inl (hkpos ⟨hx, hp⟩)

private lemma sides_signs_near {φ : E₃ → ℝ} (_hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    {p : E₃} (hz : φ p = 0) (hr : gradient φ p ≠ 0)
    {V : Set E₃} (hV : IsOpen V) (hpV : p ∈ V) :
    (∃ x ∈ V, 0 < φ x) ∧ (∃ x ∈ V, φ x < 0) := by
  have hv : 0 < fderiv ℝ φ p (gradient φ p) := by
    rw [← inner_gradient_left, real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hr)
  constructor
  · by_contra h
    push Not at h
    have hm : IsLocalMax φ p := by
      filter_upwards [hV.mem_nhds hpV] with x hx
      simpa [hz] using h x hx
    rw [hm.fderiv_eq_zero] at hv
    simp at hv
  · by_contra h
    push Not at h
    have hm : IsLocalMin φ p := by
      filter_upwards [hV.mem_nhds hpV] with x hx
      simpa [hz] using h x hx
    rw [hm.fderiv_eq_zero] at hv
    simp at hv

private lemma sides_absorb {S K : Set E₃} {a x : E₃}
    (hK : IsPreconnected K) (hKS : K ⊆ Sᶜ) (hxK : x ∈ K)
    (hx : x ∈ connectedComponentIn Sᶜ a) : K ⊆ connectedComponentIn Sᶜ a := by
  rw [connectedComponentIn_eq hx]
  exact hK.subset_connectedComponentIn hxK hKS

private lemma sides_closure_component {S : Set E₃} (hO : IsOpen Sᶜ) {a p : E₃}
    (hp : p ∈ closure (connectedComponentIn Sᶜ a)) (hpS : p ∈ Sᶜ) :
    p ∈ connectedComponentIn Sᶜ a := by
  obtain ⟨y, hyp, hya⟩ := mem_closure_iff.mp hp _ hO.connectedComponentIn
    (mem_connectedComponentIn hpS)
  rw [connectedComponentIn_eq hya, ← connectedComponentIn_eq hyp]
  exact mem_connectedComponentIn hpS

private lemma sides_component_touches {S : Set E₃} (hO : IsOpen Sᶜ)
    (hne : S.Nonempty) {a : E₃} (ha : a ∈ Sᶜ) :
    (closure (connectedComponentIn Sᶜ a) ∩ S).Nonempty := by
  by_contra h
  have hclosed : IsClosed (connectedComponentIn Sᶜ a) := by
    apply isClosed_of_closure_subset
    intro p hp
    exact sides_closure_component hO hp (fun hpS => h ⟨p, hp, hpS⟩)
  have hu := (show IsClopen (connectedComponentIn Sᶜ a) from
    ⟨hclosed, hO.connectedComponentIn⟩).eq_univ ⟨a, mem_connectedComponentIn ha⟩
  obtain ⟨p, hp⟩ := hne
  exact (connectedComponentIn_subset Sᶜ a (hu.symm ▸ mem_univ p)) hp

private lemma sides_cover_all {S : Set E₃} (hS : IsSmoothEmbeddedSurface S)
    (hO : IsOpen Sᶜ) (hconn : IsConnected S) :
    ∃ a ∈ Sᶜ, ∃ b ∈ Sᶜ,
      Sᶜ ⊆ connectedComponentIn Sᶜ a ∪ connectedComponentIn Sᶜ b := by
  obtain ⟨p₀, hp₀⟩ := hconn.nonempty
  obtain ⟨U₀, φ₀, hU₀, hp₀U, hφ₀, hz₀, hr₀⟩ := hS p₀ hp₀
  have hzp₀ : φ₀ p₀ = 0 := (hz₀ ▸ (show p₀ ∈ S ∩ U₀ from ⟨hp₀, hp₀U⟩)).2
  obtain ⟨r₀, hr₀pos, hb₀, Kpos, Kneg, hcpos, hcneg, hspos, hsneg, hkpos, hkneg⟩ :=
    exists_local_sides hU₀ hφ₀ hz₀ hp₀U hzp₀ (hr₀ p₀ ⟨hp₀, hp₀U⟩)
  obtain ⟨⟨a, ha, hapos⟩, ⟨b, hb, hbneg⟩⟩ := sides_signs_near hφ₀ hzp₀
    (hr₀ p₀ ⟨hp₀, hp₀U⟩) Metric.isOpen_ball (Metric.mem_ball_self hr₀pos)
  have haK := hkpos ⟨ha, hapos⟩
  have hbK := hkneg ⟨hb, hbneg⟩
  have haS := hspos haK
  have hbS := hsneg hbK
  let A := connectedComponentIn Sᶜ a
  let B := connectedComponentIn Sᶜ b
  let G : Set E₃ := {p | ∃ r > 0, Metric.ball p r \ S ⊆ A ∪ B}
  have hg₀ : p₀ ∈ G := by
    refine ⟨r₀, hr₀pos, ?_⟩
    rintro x ⟨hx, hxS⟩
    have hxne : φ₀ x ≠ 0 := by
      intro h
      exact hxS (show x ∈ S ∩ U₀ from hz₀.symm ▸ ⟨hb₀ hx, h⟩).1
    rcases lt_or_gt_of_ne hxne with hn | hp
    · exact Or.inr (hcneg.subset_connectedComponentIn hbK hsneg (hkneg ⟨hx, hn⟩))
    · exact Or.inl (hcpos.subset_connectedComponentIn haK hspos (hkpos ⟨hx, hp⟩))
  have hG : IsOpen G := by
    apply Metric.isOpen_iff.mpr
    rintro p ⟨r, hr, hcov⟩
    refine ⟨r / 2, half_pos hr, ?_⟩
    intro q hq
    refine ⟨r / 2, half_pos hr, ?_⟩
    rintro x ⟨hx, hxS⟩
    apply hcov ⟨?_, hxS⟩
    calc
      dist x p ≤ dist x q + dist q p := dist_triangle _ _ _
      _ < r := by have := Metric.mem_ball.mp hx; have := Metric.mem_ball.mp hq; linarith
  let W : Set S := Subtype.val ⁻¹' G
  have hWclosed : IsClosed W := by
    apply isClosed_of_closure_subset
    intro p hp
    obtain ⟨U, φ, hU, hpU, hφ, hz, hr⟩ := hS p p.property
    have hzp : φ p = 0 := (hz ▸ (show (p : E₃) ∈ S ∩ U from ⟨p.property, hpU⟩)).2
    obtain ⟨r, hrpos, hball, Kp, Kn, hKp, hKn, hKpS, hKnS, hkp, hkn⟩ :=
      exists_local_sides hU hφ hz hpU hzp (hr p ⟨p.property, hpU⟩)
    obtain ⟨q, hqr, hqG⟩ := mem_closure_iff.mp hp
      (Subtype.val ⁻¹' Metric.ball (p : E₃) r)
      (Metric.isOpen_ball.preimage continuous_subtype_val) (Metric.mem_ball_self hrpos)
    obtain ⟨ρ, hρ, hρcov⟩ := hqG
    have hqU := hball hqr
    have hzq : φ q = 0 := (hz ▸ (show (q : E₃) ∈ S ∩ U from ⟨q.property, hqU⟩)).2
    obtain ⟨⟨x, hx, hxpos⟩, ⟨y, hy, hyneg⟩⟩ := sides_signs_near hφ hzq
      (hr q ⟨q.property, hqU⟩) (Metric.isOpen_ball.inter Metric.isOpen_ball)
      ⟨Metric.mem_ball_self hρ, hqr⟩
    have hxK := hkp ⟨hx.2, hxpos⟩
    have hyK := hkn ⟨hy.2, hyneg⟩
    have hKpcov : Kp ⊆ A ∪ B := by
      rcases hρcov ⟨hx.1, hKpS hxK⟩ with hxa | hxb
      · exact (sides_absorb hKp hKpS hxK hxa).trans subset_union_left
      · exact (sides_absorb hKp hKpS hxK hxb).trans subset_union_right
    have hKncov : Kn ⊆ A ∪ B := by
      rcases hρcov ⟨hy.1, hKnS hyK⟩ with hya | hyb
      · exact (sides_absorb hKn hKnS hyK hya).trans subset_union_left
      · exact (sides_absorb hKn hKnS hyK hyb).trans subset_union_right
    refine ⟨r, hrpos, ?_⟩
    rintro z ⟨hzball, hzS⟩
    have hzne : φ z ≠ 0 := by
      intro h
      exact hzS (show z ∈ S ∩ U from hz.symm ▸ ⟨hball hzball, h⟩).1
    rcases lt_or_gt_of_ne hzne with hn | hp
    · exact hKncov (hkn ⟨hzball, hn⟩)
    · exact hKpcov (hkp ⟨hzball, hp⟩)
  let : ConnectedSpace S := isConnected_iff_connectedSpace.mp hconn
  have hWall : W = univ :=
    (show IsClopen W from ⟨hWclosed, hG.preimage continuous_subtype_val⟩).eq_univ
      ⟨⟨p₀, hp₀⟩, hg₀⟩
  have hSG : S ⊆ G := fun p hp => show (⟨p, hp⟩ : S) ∈ W from hWall.symm ▸ mem_univ _
  refine ⟨a, haS, b, hbS, ?_⟩
  intro z hz
  obtain ⟨p, hpcl, hpS⟩ := sides_component_touches hO hconn.nonempty hz
  obtain ⟨r, hr, hcov⟩ := hSG hpS
  obtain ⟨w, hwr, hwC⟩ := mem_closure_iff.mp hpcl _ Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hwO := connectedComponentIn_subset Sᶜ z hwC
  rcases hcov ⟨hwr, hwO⟩ with hwa | hwb
  · exact Or.inl (sides_absorb isPreconnected_connectedComponentIn
      (connectedComponentIn_subset _ _) hwC hwa (mem_connectedComponentIn hz))
  · exact Or.inr (sides_absorb isPreconnected_connectedComponentIn
      (connectedComponentIn_subset _ _) hwC hwb (mem_connectedComponentIn hz))

private lemma sides_crossing_pair {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) (hne : S.Nonempty) (I : E₃ → Prop)
    (hcross : ∀ p ∈ S, ∀ ν ∉ tangentPlane S p, ∃ t₀ > 0, ∀ t ∈ Ioo (0 : ℝ) t₀,
      ¬ (I (p - t • ν) ↔ I (p + t • ν))) :
    ∃ x ∈ Sᶜ, ∃ y ∈ Sᶜ, ¬ (I x ↔ I y) := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨U, φ, hU, hpU, hφ, hz, hr⟩ := hS p hp
  have hreg := hr p ⟨hp, hpU⟩
  have hv : 0 < fderiv ℝ φ p (gradient φ p) := by
    rw [← inner_gradient_left, real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hreg)
  have hν : gradient φ p ∉ tangentPlane S p := by
    rw [tangentPlane_eq hU hpU (hφ.contDiffAt.of_le (by simp)) hz hp hreg,
      Submodule.mem_orthogonal_singleton_iff_inner_right, inner_gradient_left]
    exact ne_of_gt hv
  obtain ⟨t₀, ht₀, hcross₀⟩ := hcross p hp (gradient φ p) hν
  have hd : HasDerivAt (fun t : ℝ => φ (p + t • gradient φ p))
      (fderiv ℝ φ p (gradient φ p)) 0 := by
    simpa using sides_line_deriv hφ p (gradient φ p) 0
  have hneq : ∀ᶠ t in 𝓝[≠] (0 : ℝ), φ (p + t • gradient φ p) ≠ 0 :=
    hd.eventually_ne hv.ne'
  have hin : ∀ᶠ t in 𝓝 (0 : ℝ), p + t • gradient φ p ∈ U :=
    (continuous_const.add (continuous_id.smul continuous_const)).continuousAt.preimage_mem_nhds
      (by simpa using hU.mem_nhds hpU)
  have hboth : ∀ᶠ t in 𝓝[≠] (0 : ℝ), p + t • gradient φ p ∉ S := by
    filter_upwards [hneq, nhdsWithin_le_nhds hin] with t ht htU htS
    exact ht (hz ▸ (show p + t • gradient φ p ∈ S ∩ U from ⟨htS, htU⟩)).2
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hboth
  obtain ⟨δ, hδ, hsmall⟩ := hboth
  let t := min δ t₀ / 2
  have ht : 0 < t := half_pos (lt_min hδ ht₀)
  have htδ : t < δ := (half_lt_self (lt_min hδ ht₀)).trans_le (min_le_left _ _)
  have htt₀ : t < t₀ := (half_lt_self (lt_min hδ ht₀)).trans_le (min_le_right _ _)
  have hplus : p + t • gradient φ p ∈ Sᶜ :=
    hsmall (by simpa [Real.dist_eq, abs_of_pos ht] using htδ) ht.ne'
  have hminus : p - t • gradient φ p ∈ Sᶜ := by
    have := hsmall (y := -t)
      (by simpa [Real.dist_eq, abs_of_pos ht] using htδ) (neg_ne_zero.mpr ht.ne')
    change p - t • gradient φ p ∉ S
    simpa only [neg_smul, ← sub_eq_add_neg] using this
  exact ⟨_, hminus, _, hplus, hcross₀ t ⟨ht, htt₀⟩⟩

/-- prop:orientation-parity (iii): a locally constant parity that changes on
every transverse crossing separates the complement of a compact connected smooth
embedded surface into exactly two connected components. -/
theorem card_connectedComponents_compl_eq_two {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hconn : IsConnected S)
    (I : E₃ → Prop)
    (hloc : ∀ x ∉ S, ∀ᶠ y in 𝓝 x, (I y ↔ I x))
    (hcross : ∀ p ∈ S, ∀ ν ∉ tangentPlane S p, ∃ t₀ > 0, ∀ t ∈ Ioo (0 : ℝ) t₀,
      ¬ (I (p - t • ν) ↔ I (p + t • ν))) :
    Nat.card (ConnectedComponents (Sᶜ : Set E₃)) = 2 := by
  obtain ⟨a, ha, b, hb, hcover⟩ := sides_cover_all hS hc.isClosed.isOpen_compl hconn
  have hmem {x y : (Sᶜ : Set E₃)}
      (h : (x : E₃) ∈ connectedComponentIn Sᶜ (y : E₃)) :
      x ∈ connectedComponent y := by
    rw [connectedComponentIn_eq_image y.property] at h
    obtain ⟨z, hz, hzx⟩ := h
    have heq : z = x := Subtype.ext hzx
    simpa [heq] using hz
  let a' : (Sᶜ : Set E₃) := ⟨a, ha⟩
  let b' : (Sᶜ : Set E₃) := ⟨b, hb⟩
  have hcover' (z : (Sᶜ : Set E₃)) :
      ConnectedComponents.mk z = ConnectedComponents.mk a' ∨
      ConnectedComponents.mk z = ConnectedComponents.mk b' := by
    rcases hcover z.property with hza | hzb
    · exact Or.inl (ConnectedComponents.coe_eq_coe'.mpr (hmem hza))
    · exact Or.inr (ConnectedComponents.coe_eq_coe'.mpr (hmem hzb))
  have hI : IsLocallyConstant (fun x : (Sᶜ : Set E₃) => I x) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro x
    filter_upwards [continuous_subtype_val.continuousAt (hloc x x.property)] with y hy
    exact propext hy
  have hIeq {x y : (Sᶜ : Set E₃)}
      (h : ConnectedComponents.mk x = ConnectedComponents.mk y) : I x ↔ I y :=
    iff_of_eq (hI.apply_eq_of_isPreconnected isPreconnected_connectedComponent
      (ConnectedComponents.coe_eq_coe'.mp h) mem_connectedComponent)
  have hne : ConnectedComponents.mk a' ≠ ConnectedComponents.mk b' := by
    intro hab
    have hall (z : (Sᶜ : Set E₃)) : ConnectedComponents.mk z = ConnectedComponents.mk a' :=
      (hcover' z).elim id (fun h => h.trans hab.symm)
    obtain ⟨x, hx, y, hy, hxy⟩ := sides_crossing_pair hS hconn.nonempty I hcross
    exact hxy (hIeq ((hall ⟨x, hx⟩).trans (hall ⟨y, hy⟩).symm))
  apply Nat.card_eq_two_iff.mpr
  refine ⟨ConnectedComponents.mk a', ConnectedComponents.mk b', hne, ?_⟩
  apply eq_univ_of_forall
  intro z
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe z
  exact (hcover' x).elim (fun h => Or.inl h) (fun h => Or.inr h)

end
end LiquidDrop
