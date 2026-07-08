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
  hom_ext {β' : Type*} [TopologicalSpace β'] [T2Space β'] {g₁ g₂ : β → β'} (h₁ : Continuous g₁) (h₂ : Continuous g₂) (h : g₁ ∘ unit = g₂ ∘ unit) : g₁ = g₂
  extend {α' : Type u} [TopologicalSpace α'] [T2Space α'] {g : α → α'} (hg : Continuous g) [CompactSpace α'] : β → α'
  continuous_extend {α' : Type u} [TopologicalSpace α'] [T2Space α'] {g : α → α'} (hg : Continuous g) [CompactSpace α']: Continuous (extend hg)
  extend_extends {α' : Type u} [TopologicalSpace α'] [T2Space α'] {g : α → α'} (hg : Continuous g) [CompactSpace α'] : (extend hg) ∘ unit = g
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
      apply hc.hom_ext _ continuous_id
      · simp [Function.comp_assoc, hc.extend_extends, hc'.extend_extends]
      · exact Continuous.comp hf' hf
    · apply Function.rightInverse_iff_comp.mpr
      apply hc'.hom_ext _ continuous_id
      · simp [Function.comp_assoc, hc.extend_extends, hc'.extend_extends]
      · exact Continuous.comp hf hf'
  have : Continuous equiv := by simpa [equiv] using hf
  apply Continuous.homeoOfEquivCompactToT2 this

end Equiv

@[reducible]
noncomputable def C (α : Type*) [TopologicalSpace α] : Compactification α (StoneCech α) := {
  unit := stoneCechUnit
  continuous_unit := continuous_stoneCechUnit
  hom_ext := stoneCech_hom_ext
  extend := stoneCechExtend
  continuous_extend := continuous_stoneCechExtend
  extend_extends := stoneCechExtend_extends
}
