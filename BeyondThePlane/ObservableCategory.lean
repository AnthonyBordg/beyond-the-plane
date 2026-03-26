/-
Copyright (c) 2026 Lagrange Mathematics and Computing Research Center. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Farzad Jafarrahmani (with helpful suggestions from Anthony Bordg regarding the
formulation of `CategoryTheory.Observable`)
-/
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Adjunction.Unique


/-!
# Observable category

This file defines notion of observable category.

## Main results

* `CategoryTheory.Cartesian`: cartesian categories
* `CategoryTheory.Cartesian.pullback_commutes_inf`:  pullback commutes with inf
* `CategoryTheory.Regular`: regular categories
* `CategoryTheory.Regular.frobenius_reciprocity`: Frobenius reciprocity theorem
* `CategoryTheory.Observable`: observable categories
* `CategoryTheory.Observable.distributivity`: distributivity laws of inf over sup


## References

* [P. Johnstone, *Sketches of an Elephant: A Topos Theory Compendium, Volume 2*][Elephant]
* [Carsten Butz, *Regular Categories and Regular Logic*][Butz1998]

## Tags

observable category, categorical logic, category theory
-/

universe u v w w'

open CategoryTheory

variable (C : Type u) [Category.{v, u} C]

namespace CategoryTheory

open CategoryTheory.Limits

/-- A Cartesian category is a category `C` with finite limits.-/
abbrev Cartesian (C : Type u) [Category.{v, u} C] := HasFiniteLimits C

namespace Cartesian

variable [Cartesian C]

/-- Given a morphism `g`, the `MonoOver.pullback g` functor preserves mono ordering. -/
theorem monoPullback_preserve_mono_order {X Y : C} (f1 f2 : MonoOver Y) (g : X ⟶ Y) :
    Nonempty (f1 ⟶ f2) →
    Nonempty ((MonoOver.pullback g).obj f1 ⟶ (MonoOver.pullback g).obj f2) := by
  intro h
  apply Classical.choice at h
  exact ⟨(MonoOver.pullback g).map h⟩

instance sup_stable_monomap {X Y : C} {β : Type w'} (f : X ⟶ Y) [Mono f] (lm : β → MonoOver X) :
    PreservesColimit (Discrete.functor lm) (MonoOver.map f) := by
  let allcoLimit := Adjunction.leftAdjoint_preservesColimits (MonoOver.mapPullbackAdj f)
  let allSahpcoLimit := allcoLimit.preservesColimitsOfShape (J := Discrete β)
  exact allSahpcoLimit.preservesColimit (K := Discrete.functor lm)

/-- Given a morphism `g`, the `MonoOver.pullback g` commutes with `MonoOver.inf`. -/
theorem pullback_commutes_inf {X Y : C} (g : X ⟶ Y) (f₁ f₂ : MonoOver Y) :
  Nonempty (((MonoOver.pullback g).obj ((MonoOver.inf.obj f₁).obj f₂)) ≅
  ((MonoOver.inf.obj ((MonoOver.pullback g).obj f₁)).obj ((MonoOver.pullback g).obj f₂))) := by
  apply Nonempty.intro
  refine MonoOver.isoMk ?_ ?_
  apply Iso.symm
  apply Iso.trans (pullbackLeftPullbackSndIso f₂.arrow g (pullback.snd f₁.arrow g)) ?_
  apply Iso.symm
  apply Iso.trans (pullbackAssoc f₂.arrow f₁.arrow f₁.arrow g)
  apply pullback.congrHom
  rfl
  exact pullback.condition
  simp

end Cartesian

/-- A Regular category is a cartesian category which has all images and stable under base change. -/
class Regular extends Cartesian C, HasImages C where
  image_stable_pullback {X Y X' Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : X' ⟶ X} {g' : Y' ⟶ Y}
    (sq : IsPullback f' g g' f) : (MonoOver.pullback f') ⋙ (MonoOver.«exists» g) ≅
      (MonoOver.«exists» g') ⋙ (MonoOver.pullback f)

namespace Regular

variable [Regular.{u, v} C]

instance {X Y X' Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : X' ⟶ X} {g' : Y' ⟶ Y}
  (sq : IsPullback f' g g' f) :  (MonoOver.pullback f') ⋙ (MonoOver.«exists» g) ≅
      (MonoOver.«exists» g') ⋙ (MonoOver.pullback f) :=
  @Regular.image_stable_pullback C  _ _ X Y X' Y' f f' g g' sq

/-- Given two morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`, the `MonoOver.«exists»` preserves the
composition of `f ≫ g`. -/
lemma exists_preserves_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  Nonempty (MonoOver.«exists» (f ≫ g) ≅ MonoOver.«exists» f ⋙ MonoOver.«exists» g) := by
  obtain adj2 := Adjunction.comp (MonoOver.existsPullbackAdj f) (MonoOver.existsPullbackAdj g)
  obtain adj3 := Adjunction.ofNatIsoRight (MonoOver.existsPullbackAdj (f ≫ g))
    (MonoOver.pullbackComp f g)
  exact ⟨(Adjunction.leftAdjointUniq adj2 adj3).symm⟩

/-- The Frobenius reciprocity shows that `MonoOver.«exists»` commutes with `MonoOver.inf`. -/
lemma frobenius_reciprocity {X Y Z : C} (f : X ⟶ Y) (h : Z ⟶ Y) [Mono h] :
  Nonempty (MonoOver.«exists» f ⋙ MonoOver.inf.obj (MonoOver.mk' h) ≅
    MonoOver.inf.obj ((MonoOver.pullback f).obj (MonoOver.mk' h)) ⋙ MonoOver.«exists» f ) := by
  let IsPull := IsPullback.flip (IsPullback.of_hasPullback h f)
  have aux2 : MonoOver.«exists» (pullback.fst h f) ⋙ MonoOver.map h ≅
    MonoOver.map (pullback.snd h f) ⋙ MonoOver.«exists» f := by
    apply ((Functor.isoWhiskerLeft (MonoOver.«exists» (pullback.fst h f))
      (MonoOver.existsIsoMap h)).symm).trans
    apply Iso.symm
    apply (Functor.isoWhiskerRight (MonoOver.existsIsoMap (pullback.snd h f))
      (MonoOver.«exists» f)).symm.trans
    let u := exists_preserves_comp C (pullback.snd h f) f
    let v := exists_preserves_comp C (pullback.fst h f) h
    apply Classical.choice at u
    apply Classical.choice at v
    apply u.symm.trans
    apply Iso.symm
    apply v.symm.trans
    rw [IsPull.w.symm]
  exact ⟨Iso.trans (Functor.isoWhiskerRight ((image_stable_pullback IsPull).symm) (MonoOver.map h))
    (Functor.isoWhiskerLeft (MonoOver.pullback (pullback.snd h f)) aux2)⟩

end Regular

/-- A Observable category is a regular category such that it is locally small, well-powered, stable
under base change, and for any object `X` the category `MonoOver X` has co-product. -/
class Observable extends Regular C, LocallySmall.{w} C, WellPowered.{w} C where
  sup_in_monoColim (X : C) : HasCoproducts (MonoOver X)
  initial_in_mon (X : C) : HasInitial (MonoOver X)
  /- stability under base change -/
  sup_stable_pullback {X Y : C} {β : Type w'} (f : X ⟶ Y) (lm : β → MonoOver Y) :
    PreservesColimit (Discrete.functor lm) (MonoOver.pullback f)
  pullback_preserve_bot {X Y : C} (f : X ⟶ Y):
    (MonoOver.pullback f).obj (⊥_MonoOver Y)  ≅ ⊥_MonoOver X

namespace Observable

variable [Observable.{u, v, w, w', _} C] {β : Type w'}

instance (X : C) : HasCoproducts (MonoOver X) := sup_in_monoColim X

instance (X : C) : HasInitial (MonoOver X) := initial_in_mon X

instance {X Y : C} (f : X ⟶ Y) (lm : β → MonoOver Y) :
    PreservesColimit (Discrete.functor lm) (MonoOver.pullback f) :=
  @sup_stable_pullback C  _ _ X Y β f lm

instance {X Y : C} (f : X ⟶ Y) :
    (MonoOver.pullback f).obj (⊥_MonoOver Y)  ≅ ⊥_MonoOver X :=
  @pullback_preserve_bot C  _ _ X Y  f

open Cartesian

/-- Let `f` be a monomorphism in `C`. Then `MonoOver.map f` functor preserves co-products. -/
theorem monomap_preserve_coProd {X Y : C} (f : X ⟶ Y) [Mono f] (lm : β → MonoOver X) :
    Nonempty ((MonoOver.map f).obj (∐ lm) ≅ ∐ (fun i ↦ (MonoOver.map f).obj (lm i))) := by
  exact ⟨Limits.PreservesCoproduct.iso (MonoOver.map f) (lm)⟩

/-- Let `f` be a morphism in `C`. Then `MonoOver.pullback f` functor preserves co-products. -/
theorem pullback_preserve_coProd {X Y : C} (f : X ⟶ Y) (lm : β → MonoOver Y) :
    Nonempty ((MonoOver.pullback f).obj (∐ lm) ≅ ∐ (fun i ↦ (MonoOver.pullback f).obj (lm i))) :=
    by exact ⟨Limits.PreservesCoproduct.iso (MonoOver.pullback f) (lm)⟩

/-- This is distributivity of `MonoOver.inf` over `∐`. -/
theorem distributivity {Y : C} (f : MonoOver Y) (lm : β → MonoOver Y) :
    Nonempty ((MonoOver.inf.obj f).obj (∐ lm) ≅ ∐ (fun i ↦ (MonoOver.inf.obj f).obj (lm i))) := by
  have monoPullPresColim := sup_stable_pullback f.arrow lm
  rw [MonoOver.inf_obj]
  have monoMapPresColim := sup_stable_monomap C f.arrow
    (fun i ↦ (MonoOver.pullback f.arrow).obj (lm i))
  have auxh1 : Discrete.functor (fun i ↦ (MonoOver.pullback f.arrow).obj (lm i)) =
    (Discrete.functor lm) ⋙ MonoOver.pullback f.arrow := by
      apply Functor.ext
      aesop_cat
  rw [auxh1] at monoMapPresColim
  have tt := Limits.comp_preservesColimit (K := Discrete.functor lm) (MonoOver.pullback f.arrow)
    (MonoOver.map f.arrow)
  exact ⟨Limits.PreservesCoproduct.iso (MonoOver.pullback f.arrow ⋙ MonoOver.map f.arrow) (lm)⟩

/-- This shows pullback of a morphism `h` with equalizer of `f` and `g` is just the equalizer
of `h ≫ f` and `h ≫ g`. -/
theorem pullback_of_equalizer_is_equalizer {Z X Y : C} (f g : X ⟶ Y) (h : Z ⟶ X) :
  Nonempty ((MonoOver.pullback h).obj (MonoOver.mk' (equalizer.ι f g)) ≅
    MonoOver.mk' (equalizer.ι (h ≫ f) (h ≫ g))) := by
  apply Nonempty.intro
  refine MonoOver.isoMk ?_ ?_
  simp
  refine {
    hom := by
      refine equalizer.lift ?_ ?_
      exact pullback.snd (equalizer.ι f g) h
      rw [<- Category.assoc, <- pullback.condition, <- Category.assoc, <- pullback.condition]
      rw [Category.assoc, Category.assoc, equalizer.condition]
    inv := by
      refine pullback.lift ?_ ?_ ?_
      refine equalizer.lift ?_ ?_
      exact (equalizer.ι (h ≫ f) (h ≫ g)) ≫ h
      rw [Category.assoc, Category.assoc, equalizer.condition]
      exact equalizer.ι (h ≫ f) (h ≫ g)
      aesop_cat
    hom_inv_id := by
      ext <;>
      simp
      rw [pullback.condition]
    inv_hom_id := by
      ext
      simp
  }
  simp

end Observable

end CategoryTheory
