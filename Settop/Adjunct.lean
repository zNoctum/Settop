import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Topology.UnitInterval

open CategoryTheory CompHausLike

universe u

abbrev unitIntervalObject : CompHaus.{u} := CompHaus.of (ULift.{u} unitInterval)

abbrev IsUnitInterval : ObjectProperty CompHaus.{u} :=
  ObjectProperty.singleton unitIntervalObject

instance : ObjectProperty.Small.{u} IsUnitInterval.{u} :=
  ObjectProperty.instSmallOfObjOfSmall fun _ => unitIntervalObject

theorem IsUnitInterval_isCoseparating : ObjectProperty.IsCoseparating IsUnitInterval.{u} := by
  intro X Y f g h
  specialize h unitIntervalObject (by simp)
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
  simpa [H, hfp hf, hfu hg] using ConcreteCategory.congr_hom (h H) x

instance : Balanced.{u} CompHaus.{u} := by
  refine { isIso_of_mono_of_epi := ?_ }
  intro X Y f mono epi
  have inj : Function.Injective f := (CompHausLike.mono_iff_injective f).mp mono
  have sur : Function.Surjective f := (CompHaus.epi_iff_surjective f).mp epi
  refine isIso_of_bijective f ⟨inj, sur⟩

instance : HasSeparator.{u} CompHaus.{u} := by
  refine { hasSeparator := ⟨unitIntervalObject, ?_⟩ }
  intro X Y f g h
  specialize h unitIntervalObject (by simp)
  ext x
  by_contra! hne
  let c : unitIntervalObject ⟶ X := CompHausLike.ofHom _ (ContinuousMap.const' x)
  absurd hne
  exact ConcreteCategory.congr_hom (h c) 0

instance : Functor.IsRightAdjoint compHausToTop.{u} :=
  isRightAdjoint_of_preservesLimits_of_isCoseparating IsUnitInterval_isCoseparating compHausToTop

noncomputable abbrev StoneCech' (α : TopCat) : CompHaus :=
  compHausToTop.leftAdjoint.obj α

variable {α : TopCat}

noncomputable def stoneCechUnit' : α ⟶ compHausToTop.obj (StoneCech' α) :=
  (Adjunction.ofIsRightAdjoint compHausToTop).unit.app α

variable {β : CompHaus}
variable (g : α ⟶ compHausToTop.obj β)

theorem hom_ext {g₁ g₂ : (StoneCech' α) ⟶ β}
    (h : stoneCechUnit' ≫ compHausToTop.map g₁ = stoneCechUnit' ≫ compHausToTop.map g₂) :
    g₁ = g₂ := by
  dsimp only [stoneCechUnit', StoneCech] at *
  rw [← Adjunction.homEquiv_id, ← Adjunction.homEquiv_naturality_right,
      ← Adjunction.homEquiv_naturality_right] at h
  simpa using h

noncomputable def stoneCechExtend' : StoneCech' α ⟶ β :=
  (Adjunction.ofIsRightAdjoint compHausToTop).homEquiv α β |>.symm g

theorem stoneCechExtend_extends' : stoneCechUnit' ≫ compHausToTop.map (stoneCechExtend' g) = g := by
  let adj := (Adjunction.ofIsRightAdjoint compHausToTop)
  simpa using adj.homEquiv_unit α β (adj.homEquiv α β |>.symm g) |>.symm
