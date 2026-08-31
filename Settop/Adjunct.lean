import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Topology.UnitInterval
import Settop.StoneCechEquiv

open CategoryTheory ConcreteCategory CompHausLike

universe u

/-- The unit interval as an object of `CompHaus`, lifted to a universe `u`. -/
abbrev unitIntervalObject : CompHaus.{u} := CompHaus.of (ULift.{u} unitInterval)

/-- The one-element family `{[0,1]}` is a cogenerating family of `CompHaus`. -/
abbrev IsUnitInterval : ObjectProperty CompHaus.{u} :=
  ObjectProperty.singleton unitIntervalObject

/-- `{[0,1]}` is a cogenerating family for `CompHaus`: two morphisms `f` and `g` that are unequal
are unequal at atleast one point `x` in the domain and `f x` and `g x` are differentiated by a
Urysohn function because which exists as all spaces in `CompHaus` are Hausdorff -/
theorem IsUnitInterval.isCoseparating : ObjectProperty.IsCoseparating IsUnitInterval.{u} := by
  intro X Y f g h
  have h := h unitIntervalObject (by simp)
  ext x
  by_contra! hne
  have ⟨v, _, hv, _, hvfx, _⟩ := t2_separation hne
  have hc : IsClosed vᶜ := by simp [hv]
  have hy : IsClosed {f x} := by simp
  have hd : Disjoint {f x} vᶜ := by grind
  have ⟨f', hfp, hfu, hbound⟩ := exists_continuous_zero_one_of_isClosed hy hc hd
  let H : Y ⟶ unitIntervalObject := CompHausLike.ofHom _ ⟨fun x => ⟨f' x, hbound x⟩, by fun_prop⟩
  have hf : f x ∈ ({f x} : Set Y) := by simp
  have hg : g x ∈ vᶜ := by grind
  simpa [H, hfp hf, hfu hg] using congr_hom (h H) x

/-- The one-point space is a detector for `CompHaus` -/
instance : HasDetector.{u} CompHaus.{u} where
  hasDetector := by
    let U := (CompHaus.of (ULift.{u} Unit))
    use U
    intro X Y f h
    specialize h U
    simp only [ObjectProperty.singleton_iff, forall_const, U] at h
    refine isIso_of_bijective f ?_
    apply (Function.bijective_iff_existsUnique f).mpr
    intro y
    let g : U ⟶ Y := CompHausLike.ofHom _ ⟨fun _ => y, continuous_const⟩
    have ⟨u, heq, hu⟩ := h g
    use u (ULift.up ())
    constructor
    · simpa using congr_hom heq (ULift.up ())
    intro x hf
    let g' : U ⟶ X := CompHausLike.ofHom _ ⟨fun _ => x, continuous_const⟩
    have : g' ≫ f = g := by
      ext _; simpa [g, g'] using hf
    simp [← hu g' this, g']

/-- **Special adjoint functor theorem** applied to the forgetful functor: `compHausToTop` has a
left adjoint. -/
instance : Functor.IsRightAdjoint compHausToTop.{u} :=
  isRightAdjoint_of_preservesLimits_of_isCoseparating
    IsUnitInterval.isCoseparating.{u} compHausToTop

/-- The Stone–Čech compactification of `α` definied as `α`s reflection along
`compHausToTop`, i.e. the value at `α` of the left adjoint. -/
noncomputable abbrev AdjStoneCech (α : TopCat) : CompHaus :=
  compHausToTop.leftAdjoint.obj α

variable {α : TopCat}

/-- The unit `η_α : α ⟶ U (βα)` of the reflection. -/
noncomputable def AdjStoneCech.unit : α ⟶ compHausToTop.obj (AdjStoneCech α) :=
  (Adjunction.ofIsRightAdjoint compHausToTop).unit.app α

variable {β : CompHaus}
variable (g : α ⟶ compHausToTop.obj β)

/-- Morphisms out of `βα` are determined by their restriction along the unit. -/
theorem AdjStoneCech.hom_ext {g₁ g₂ : (AdjStoneCech α) ⟶ β}
    (h : AdjStoneCech.unit ≫ compHausToTop.map g₁ = AdjStoneCech.unit ≫ compHausToTop.map g₂) :
    g₁ = g₂ := by
  dsimp only [AdjStoneCech.unit, StoneCech] at *
  rw [← Adjunction.homEquiv_id, ← Adjunction.homEquiv_naturality_right,
      ← Adjunction.homEquiv_naturality_right] at h
  simpa using h

/-- The extension of `g : α ⟶ U β` to `βα ⟶ β`. -/
noncomputable def AdjStoneCech.extend : AdjStoneCech α ⟶ β :=
  (Adjunction.ofIsRightAdjoint compHausToTop).homEquiv α β |>.symm g

/-- The extension extends `g` along the unit. -/
theorem AdjStoneCech.unit_comp_map_extend :
    AdjStoneCech.unit ≫ compHausToTop.map (AdjStoneCech.extend g) = g := by
  let adj := (Adjunction.ofIsRightAdjoint compHausToTop)
  simpa using adj.homEquiv_unit α β (adj.homEquiv α β |>.symm g) |>.symm


/-- The reflection along `compHausToTop` is a Stone–Čech compactification in the sense of
`Compactification`, hence equal up to homeomorphism to the concrete constructions. -/
noncomputable instance : Compactification α (AdjStoneCech α) where
  unit := TopCat.Hom.hom AdjStoneCech.unit
  extend {γ} _ _ _ g := by
    apply TopCat.Hom.hom <|
      compHausToTop.map (AdjStoneCech.extend _ : AdjStoneCech α ⟶ CompHausLike.of _ γ)
    exact TopCat.ofHom g
  extend_comp {γ} _ _ _ g := by
    ext x
    have : g x = (TopCat.ofHom g) x := by simp
    rw [this]
    let f :  α ⟶ compHausToTop.obj (CompHaus.of γ) := TopCat.ofHom g
    simpa [f] using congr_hom (AdjStoneCech.unit_comp_map_extend f) x
  hom_ext := by
    intro γ _ _ _ g₁ g₂ h
    let γ : CompHaus := CompHausLike.of _ γ
    let f₁ : AdjStoneCech α ⟶ γ := CompHausLike.ofHom _ g₁
    let f₂ : AdjStoneCech α ⟶ γ := CompHausLike.ofHom _ g₂
    have : AdjStoneCech.unit ≫ compHausToTop.map f₁
        = AdjStoneCech.unit ≫ compHausToTop.map f₂ := by
      simpa [f₁, f₂] using TopCat.hom_ext_iff.mpr h
    ext x
    simpa [f₁, f₂] using congr_hom (AdjStoneCech.hom_ext this) x
