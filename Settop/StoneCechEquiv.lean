import Mathlib.Topology.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Data.Set.Function
import Mathlib.Logic.Function.Basic
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.ExtremallyDisconnected

open Set

variable (α β : Type*) [TopologicalSpace α] [TopologicalSpace β]
    [CompactSpace β] [T2Space β]

/-- `Compactification α β` says that the compact Hausdorff space `β` is a Stone–Čech
compactification of `α`: it comes with a unit `C(α, β)` along which every continuous map from `α`
into a compact Hausdorff space can be extended uniquely.

Density of the range of the unit is deliberately *not* required. It is a direct consequence of the
existance of unique extensions. -/
class Compactification where
  /-- The unit `α → β` of the compactification. -/
  unit : C(α, β)
  /-- Every continuous map into a compact Hausdorff space can be extended. -/
  extend {γ : Type u} [TopologicalSpace γ] [T2Space γ] [CompactSpace γ] : C(α, γ) → C(β, γ)
  /-- The extension does extend `g` along the `unit`. -/
  extend_comp {γ : Type u} [TopologicalSpace γ] [T2Space γ] [CompactSpace γ] (g : C(α, γ)) :
    (extend g).comp unit = g
  /-- Maps out of `β` are determined by their restriction along the unit. This is uniqueness
  of the extension. -/
  hom_ext {γ : Type u} [TopologicalSpace γ] [T2Space γ] [CompactSpace γ] {g₁ g₂ : C(β, γ)}
    (h : g₁.comp unit = g₂.comp unit) : g₁ = g₂


section Equiv

/-- Any two Stone–Čech compactifications of `α` are homeomorphic.

The homeomorphism is the extension of one unit along the other; the two extensions are mutually
inverse because both composites restrict to the identity along the unit. -/
noncomputable def Compactification.homeomorph
    [TopologicalSpace α] [TopologicalSpace β] [CompactSpace β] [T2Space β]
    [hc : Compactification α β] [TopologicalSpace γ] [CompactSpace γ] [T2Space γ]
    [hc' : Compactification α γ] : β ≃ₜ γ := by
  let equiv : β ≃ γ := by
    apply Equiv.ofBijective (hc.extend hc'.unit)
    apply Function.bijective_iff_has_inverse.mpr
    use hc'.extend hc.unit
    constructor
    · apply Function.leftInverse_iff_comp.mpr
      have : (hc'.extend hc.unit).comp (hc.extend hc'.unit) = ContinuousMap.id β := by
        apply hc.hom_ext
        simp [ContinuousMap.comp_assoc, hc.extend_comp, hc'.extend_comp]
      ext x; simpa using ContinuousMap.congr_fun this x
    · apply Function.rightInverse_iff_comp.mpr
      have : (hc.extend hc'.unit).comp (hc'.extend hc.unit) = ContinuousMap.id γ := by
        apply hc'.hom_ext
        simp [ContinuousMap.comp_assoc, hc.extend_comp, hc'.extend_comp]
      ext x; simpa using ContinuousMap.congr_fun this x
  have : Continuous equiv := by simpa [equiv] using map_continuous (hc.extend hc'.unit)
  apply Continuous.homeoOfEquivCompactToT2 this

end Equiv

/-- Mathlib's `StoneCech α` is a `Compactification`. -/
noncomputable instance {α : Type u} [TopologicalSpace α] : Compactification α (StoneCech α) where
  unit := ⟨stoneCechUnit, continuous_stoneCechUnit⟩
  extend g := ⟨stoneCechExtend (map_continuous g), continuous_stoneCechExtend (map_continuous g)⟩
  extend_comp g := by ext x; exact stoneCechExtend_stoneCechUnit (map_continuous g) x
  hom_ext {γ} _ _ _ g₁ g₂ h := by
    simpa using stoneCech_hom_ext (map_continuous g₁) (map_continuous g₂)
      (by ext x; simpa using ContinuousMap.congr_fun h x)
