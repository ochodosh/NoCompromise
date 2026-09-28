import NoCompromise.Regularity.DeformationCaps

/-! # Choosing an exact core and exterior representative of a BV limit -/

noncomputable section
open Set MeasureTheory Filter
namespace LiquidDrop

def nestedPhaseRepresentative (E F H A B : Set AmbientSpace) : Set AmbientSpace :=
  (H ∩ A) ∪ (F ∩ (B \ A)) ∪ (E \ B)

lemma nestedPhaseRepresentative_mem_core (E F H : Set AmbientSpace)
    {A B : Set AmbientSpace} (hAB : A ⊆ B) {x : AmbientSpace} (hx : x ∈ A) :
    x ∈ nestedPhaseRepresentative E F H A B ↔ x ∈ H := by
  simp [nestedPhaseRepresentative, hx, hAB hx]

lemma nestedPhaseRepresentative_mem_exterior (E F H : Set AmbientSpace)
    {A B : Set AmbientSpace} (hAB : A ⊆ B) {x : AmbientSpace} (hx : x ∉ B) :
    x ∈ nestedPhaseRepresentative E F H A B ↔ x ∈ E := by
  have hxA : x ∉ A := fun ha => hx (hAB ha)
  simp [nestedPhaseRepresentative, hx, hxA]

lemma nestedPhaseRepresentative_ae_eq {E F H A B : Set AmbientSpace}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B)
    (hcore : F =ᵐ[volume.restrict A] H) (hext : F =ᵐ[volume.restrict Bᶜ] E) :
    nestedPhaseRepresentative E F H A B =ᵐ[volume] F := by
  have ha := (ae_restrict_iff' hA).mp hcore
  have hb := (ae_restrict_iff' hB.compl).mp hext
  filter_upwards [ha, hb] with x hxa hxb
  change (x ∈ nestedPhaseRepresentative E F H A B) = (x ∈ F)
  apply propext
  by_cases hxA : x ∈ A
  · rw [nestedPhaseRepresentative_mem_core E F H hAB hxA]
    exact (hxa hxA).symm.to_iff
  · by_cases hxB : x ∈ B
    · simp [nestedPhaseRepresentative, hxA, hxB]
    · rw [nestedPhaseRepresentative_mem_exterior E F H hAB hxB]
      exact (hxb hxB).symm.to_iff

theorem locallyFinitePerimeter_of_ae_eq {F G : Set AmbientSpace}
    (hF : HasLocallyFinitePerimeter F) (hFG : G =ᵐ[volume] F) :
    HasLocallyFinitePerimeter G := by
  intro U hU hcU
  rw [perimeterIn_congr_ae U (ae_restrict_of_ae hFG)]
  exact hF U hU hcU

theorem nestedPhaseRepresentative_properties {E F H A B : Set AmbientSpace}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B)
    (hF : HasLocallyFinitePerimeter F) (hmF : NullMeasurableSet F volume)
    (hcore : F =ᵐ[volume.restrict A] H) (hext : F =ᵐ[volume.restrict Bᶜ] E) :
    let G := nestedPhaseRepresentative E F H A B
    G =ᵐ[volume] F ∧ HasLocallyFinitePerimeter G ∧ NullMeasurableSet G volume ∧
      (∀ x ∈ A, x ∈ G ↔ x ∈ H) ∧ (∀ x ∉ B, x ∈ G ↔ x ∈ E) := by
  have he := nestedPhaseRepresentative_ae_eq hA hB hAB hcore hext
  exact ⟨he, locallyFinitePerimeter_of_ae_eq hF he, hmF.congr he.symm,
    fun _ hx => nestedPhaseRepresentative_mem_core E F H hAB hx,
    fun _ hx => nestedPhaseRepresentative_mem_exterior E F H hAB hx⟩

end LiquidDrop
