import Mathlib.Topology.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Data.Set.Function
import Mathlib.Logic.Function.Basic
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Separation.CompletelyRegular

open Set

class Compactification (α β : Type*)
    [TopologicalSpace α]
  extends TopologicalSpace β, CompactSpace β, T2Space β
where
  unit : α → β
  continuous_unit : Continuous unit
  denseRange_unit : DenseRange unit
  extend {α' : Type u} [TopologicalSpace α'] [T2Space α'] {g : α → α'} (hg : Continuous g) [CompactSpace α'] : β → α'
  continuous_extend {α' : Type u} [TopologicalSpace α'] [T2Space α'] {g : α → α'} (hg : Continuous g) [CompactSpace α']: Continuous (extend hg)
  extend_extends {α' : Type u} [TopologicalSpace α'] [T2Space α'] {g : α → α'} (hg : Continuous g) [CompactSpace α'] : (extend hg) ∘ unit = g

variable {α : Type u} [TopologicalSpace α] in
variable {β' : Type v} [TopologicalSpace β'] [T2Space β'] in
variable {g : α → β'} (hg : Continuous g) in
variable [hc : Compactification α β] in

theorem compactification_hom_ext {g₁ g₂ : β → β'} (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (h : g₁ ∘ hc.unit = g₂ ∘ hc.unit) : g₁ = g₂ := by
  apply h₁.ext_on hc.denseRange_unit h₂
  rintro _ ⟨x, rfl⟩
  exact congr_fun h x

section Equiv

noncomputable def hom' [TopologicalSpace α] [hc : Compactification α β] [hc' : Compactification α β'] : β ≃ₜ β' := by
  have hf := hc.continuous_extend hc'.continuous_unit
  have hf' := hc'.continuous_extend hc.continuous_unit
  let equiv : β ≃ β' := by
    apply Equiv.ofBijective (hc.extend hc'.continuous_unit)
    apply Function.bijective_iff_has_inverse.mpr
    use hc'.extend hc.continuous_unit
    apply And.intro
    · apply Function.leftInverse_iff_comp.mpr
      apply compactification_hom_ext _ continuous_id
      · simp [Function.comp_assoc, hc.extend_extends, hc'.extend_extends]
      · exact Continuous.comp hf' hf
    · apply Function.rightInverse_iff_comp.mpr
      apply compactification_hom_ext _ continuous_id
      · simp [Function.comp_assoc, hc.extend_extends, hc'.extend_extends]
      · exact Continuous.comp hf hf'
  have : Continuous equiv := by simpa [equiv] using hf
  apply Continuous.homeoOfEquivCompactToT2 this

end Equiv

@[reducible]
noncomputable def C (α : Type*) [TopologicalSpace α] : Compactification α (StoneCech α) := {
  unit := stoneCechUnit
  continuous_unit := continuous_stoneCechUnit
  denseRange_unit := denseRange_stoneCechUnit
  extend := stoneCechExtend
  continuous_extend := continuous_stoneCechExtend
  extend_extends := stoneCechExtend_extends
}
