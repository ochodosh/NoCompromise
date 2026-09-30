module

public import NoCompromise.Elliptic.HopfComparison
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Topology.Instances.EReal.Lemmas

@[expose] public section

/-!
# Hopf's boundary lemma with the outward sign

The liminf is taken in the extended reals, allowing an infinite inward
derivative. The proof first supplies a strictly positive uniform lower bound
for every sufficiently small positive inward difference quotient.
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped ENNReal Topology
namespace LiquidDrop

theorem hopf_ball_quotient (q p : AmbientSpace) {R : ℝ} (hR : 0 < R)
    (hp : p ∈ sphere q R) {u : AmbientSpace → ℝ}
    (hu : ContinuousOn u (ball q R))
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (ball q R))
    (hpos : ∀ x ∈ ball q R, 0 < u x) (hup : u p = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ s ∈ Ioo 0 (R / 2),
      c ≤ (u (p + (s / R) • (q - p)) - u p) / s := by
  have hr : 0 < R / 2 := half_pos hR
  have hsub : sphere q (R / 2) ⊆ ball q R := by
    intro y hy
    change dist y q < R
    rw [show dist y q = R / 2 from hy]
    linarith
  obtain ⟨y, hy, hmin⟩ := (isCompact_sphere q (R / 2)).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le) (hu.mono hsub)
  have hε : 0 < u y := hpos y (hsub hy)
  refine ⟨u y / R, div_pos hε hR, ?_⟩
  intro s hs
  have hsR : s < R := hs.2.trans (by linarith)
  have hin : p + (s / R) • (q - p) ∈ roundAnnulus q (R / 2) R := by
    rw [mem_roundAnnulus, dist_eq_norm, norm_hopf_inward_point q p hR hp hs.1.le hsR.le]
    constructor <;> linarith [hs.1, hs.2]
  have hb := hopf_annulus_comparison q hR hε.le hu hh hpos
    (fun z hz => hmin hz) hin
  have hquot := hopfBarrier_inward_quotient_lower q p hR hp hs.1 hsR
  rw [hopfBarrier_eq_zero_on_sphere q hR hp, sub_zero] at hquot
  have hq := mul_le_mul_of_nonneg_left hquot hε.le
  have huq := (div_le_div_iff_of_pos_right hs.1).mpr hb
  rw [hup, sub_zero]
  calc
    u y / R = u y * (1 / R) := by ring
    _ ≤ u y * (hopfBarrier q R (p + (s / R) • (q - p)) / s) := hq
    _ = (u y * hopfBarrier q R (p + (s / R) • (q - p))) / s := by ring
    _ ≤ u (p + (s / R) • (q - p)) / s := huq

/-- Blueprint `prop:hopf`, including a quantitative eventual lower bound.
The tangent ball has positive radius and its inward direction is `(q-p)/R`.
The liminf is in `EReal`, so it remains meaningful for an unbounded quotient. -/
theorem hopf_boundary {G : Set AmbientSpace} {q p : AmbientSpace} {R : ℝ}
    (hR : 0 < R) (hball : ball q R ⊆ G) (hp : p ∈ sphere q R)
    {u : AmbientSpace → ℝ} (hu : ContinuousOn u (G ∪ {p}))
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) G)
    (hpos : ∀ x ∈ G, 0 < u x) (hup : u p = 0) :
    (∃ c : ℝ, 0 < c ∧ ∀ s ∈ Ioo 0 (R / 2),
      c ≤ (u (p + (s / R) • (q - p)) - u p) / s) ∧
    (0 : EReal) < Filter.liminf
      (fun s : ℝ => (((u (p + (s / R) • (q - p)) - u p) / s : ℝ) : EReal)) (𝓝[>] 0) := by
  obtain ⟨c, hc, hquot⟩ := hopf_ball_quotient q p hR hp
    (hu.mono (hball.trans subset_union_left)) (hh.mono hball)
    (fun x hx => hpos x (hball hx)) hup
  refine ⟨⟨c, hc, hquot⟩, ?_⟩
  have hle : (c : EReal) ≤ Filter.liminf
      (fun s : ℝ => (((u (p + (s / R) • (q - p)) - u p) / s : ℝ) : EReal)) (𝓝[>] 0) := by
    refine le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [Ioo_mem_nhdsGT (half_pos hR)] with s hs
    exact EReal.coe_le_coe (hquot s hs)
  exact (by exact_mod_cast hc : (0 : EReal) < (c : EReal)).trans_le hle

/-- The same hypotheses give a strictly negative derivative in the outward
unit direction `(p-q)/R` whenever the actual derivative of `u` exists at `p`. -/
theorem hopf_boundary_derivative {G : Set AmbientSpace} {q p : AmbientSpace} {R : ℝ}
    (hR : 0 < R) (hball : ball q R ⊆ G) (hp : p ∈ sphere q R)
    {u : AmbientSpace → ℝ} (hu : ContinuousOn u (G ∪ {p}))
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) G)
    (hpos : ∀ x ∈ G, 0 < u x) (hup : u p = 0)
    {L : AmbientSpace →L[ℝ] ℝ} (hd : HasFDerivAt u L p) :
    L ((1 / R) • (p - q)) < 0 := by
  obtain ⟨c, hc, hquot⟩ := (hopf_boundary hR hball hp hu hh hpos hup).1
  let v : AmbientSpace := (1 / R) • (q - p)
  have hpath : HasDerivAt (fun s : ℝ => p + s • v) v 0 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hdu : HasDerivAt (fun s : ℝ => u (p + s • v)) (L v) 0 := by
    have heq : p + (0 : ℝ) • v = p := by simp
    exact hd.comp_hasDerivAt_of_eq 0 hpath heq.symm
  have hlim : Tendsto
      (fun s : ℝ => (u (p + (s / R) • (q - p)) - u p) / s)
      (𝓝[>] 0) (𝓝 (L v)) := by
    simpa [v, smul_smul, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      hdu.tendsto_slope_zero_right
  have hcL : c ≤ L v := by
    apply ge_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsGT (half_pos hR)] with s hs
    exact hquot s hs
  have hneg : L v = -L ((1 / R) • (p - q)) := by
    dsimp only [v]
    rw [← neg_sub p q, smul_neg, map_neg]
  rw [hneg] at hcL
  linarith

end LiquidDrop
