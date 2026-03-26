/-
Copyright (c) 2026 Lagrange Mathematics and Computing Research Center. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Farzad Jafarrahmani (with helpful inputs from Anthony Bordg on the `Str` section)
-/
import BeyondThePlane.Syntax
import BeyondThePlane.ObservableCategory
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Categorical semantics of observable logic

This file defines the categorical semantics of observable logic and prove its soundness.

## Main results

* `Signature.Str`: σ-structure
* `Signature.Ctx.intrpIn`: interpretation of the contexts
* `Signature.Term.intrpIn`: interpretation of the terms
* `Signature.Ctx.Subst.intrpIn`: interpretation of the substitution
* `Signature.Term.substitution`: substitution lemma for terms
* `Signature.Formula.intrpIn`: interpretation of the formulas
* `Signature.Formula.substitution`: substitution lemma for formulas
* `Signature.Sequent.IsSatisfiedIn`: satisfaction of a sequent
* `Signature.Str.IsModelOf`: models of a theory
* `Signature.soundness`: soundness theorem

## Notations

* `Mˢ s` means the interpretation of a sort `s` in a σ-structure `M` (see `Signature.Str`).
* `Mˢ f` means the interpretation of a a function symbol `f` in a σ-structure `M` (see
`Signature.Str`).
* `Mˢ f` means the interpretation of a relational symbol `R` in a σ-structure `M`
(see `Signature.Str`).

## References

* [P. Johnstone, *Sketches of an Elephant: A Topos Theory Compendium, Volume 2*][Elephant]
* [Carsten Butz, *Regular Categories and Regular Logic*][Butz1998]

## Tags

observable category, categorical semantics, first-order logic, observable logic, models
-/


open CategoryTheory CategoryTheory.Limits Category

universe u₁ v₁ w₁

variable (C : Type u₁) [Category.{v₁, u₁} C] [HasFiniteProducts C] (σ : Signature.{u,v,w,w',w''})

namespace Signature

/-- Given a category `C` with finite products and a signature `σ`, a σ-structure is determined
by the following data. -/
structure Str where
  /- A function assigning an object of `C` to each sort `s` -/
  mapSort : σ.Sorts → C
  /- A function assigning a morphism of `C` to each function symbol `f` -/
  mapFun f : ∏ᶜ (fun n => mapSort ((σ.rankF f).1.get n)) ⟶ mapSort (σ.rankF f).2
  /- A function assigning a subobject in `C` to each relation symboll `R` -/
  mapRel R : MonoOver (∏ᶜ (fun n => mapSort ((σ.rankR R).get n)))

notation:110 M:110"ˢ " s:110 => Str.mapSort M s
notation:110 M:110"ᶠ " f:110 => Str.mapFun M f
notation:110 M:110"ʳ " R:110 => Str.mapRel M R

namespace Str

variable {C : Type u₁} [Category.{v₁, u₁} C] [HasFiniteProducts C] {σ : Signature.{u,v,w,w',w''}}

/-- Let `M` and `N` be two σ-structures, `Hom M N` defines the notion of σ-strucure homomorphisms
between `M` and `N`. -/
structure Hom (M N : σ.Str C) where
  /- A collection of morphisms `toFun s : Mˢ s ⟶ Nˢ s` in `C` indexed by `σ.Sorts`. -/
  toFun s : Mˢ s ⟶ Nˢ s
  /- For each function symbol `f`: A_1 ... A_n ⟶ B, the following diagram commutes.

       Mˢ A_1 × ... × Mˢ A_n ------ Mᶠ f ------> Mˢ B
                 |                                |
    toFun A_1 × ... × toFun A_n               toFun B
                 |                                |
                 v                                v
       Nˢ A_1 × ... × Nˢ A_n ------ Nᶠ f ------> Nˢ B

  -/
  map_fun f : Mᶠ f ≫ toFun (σ.rankF f).2 =
    Limits.Pi.map (fun i => toFun ((σ.rankF f).1.get i)) ≫ Nᶠ f
  /- For each relation symbol $R \rightarrowtail A_1 ... A_n$, there exists a (necessarily unique)
  morphism g such that the following diagram commutes.

    M R >---- Mʳ R ----> Mˢ A_1 × ... × Mˢ A_n
     |                             |
     g                toFun A_1 × ... × toFun A_n
     |                             |
     v                             v
    N R >---- Nʳ R ----> Nˢ A_1 × ... × Nˢ A_n

  -/
  map_rel R : ∃ g, (Mʳ R).arrow ≫ Limits.Pi.map (fun i => toFun ((σ.rankR R).get i)) =
    g ≫ (Nʳ R).arrow

namespace Hom

variable {M N : σ.Str C} (u v : M.Hom N)

/-- Extensionality of `Str.Hom.toFun` operation. -/
theorem ext : (∀ s, u.toFun s = v.toFun s) → u = v := by
  intro h
  rcases u with ⟨u_sort, u_fun, u_rel⟩
  rcases v with ⟨v_sort, v_fun, v_rel⟩
  aesop_cat

theorem ext_iff : u = v ↔ (∀ s, u.toFun s = v.toFun s) := by
  apply Iff.intro
  · intros h s
    exact congrFun (congrArg toFun h) s
  · exact Hom.ext u v

theorem eq_map_rel {R : σ.Rel} {g : (Mʳ R).obj.left ⟶ (Nʳ R).obj.left}
    (p : (Mʳ R).arrow ≫ Limits.Pi.map (fun i => u.toFun ((σ.rankR R).get i)) = g ≫ (Nʳ R).arrow) :
    ⟨g, p⟩ = u.map_rel R := by
  let ⟨h, q⟩ := u.map_rel R
  have : g = h := by
    apply (Nʳ R).mono.right_cancellation g h
    rw [← p, ← q]
  simp

end Hom

/-- `strCat` defines the category of σ.structures and their homomorphisms. -/
instance strCat : Category (σ.Str C) where
  Hom M N := Hom M N
  id M := {
    toFun s := 𝟙 (Mˢ s)
    map_fun := by simp
    map_rel R := by use 𝟙 (Mʳ R : C); simp
  }
  comp u v := {
    toFun s := u.toFun s ≫ v.toFun s
    map_fun f := by
      rw [← assoc, ← Limits.Pi.map_comp_map]
      rw [u.map_fun f, assoc, v.map_fun f]
      simp
    map_rel R := by
      let ⟨g, p⟩ := u.map_rel R
      let ⟨h, q⟩ := v.map_rel R
      use g ≫ h
      rw [assoc, ← Limits.Pi.map_comp_map, ← assoc, p, assoc, q]
  }
  id_comp f := by simp;
  comp_id f := by simp;
  assoc u v w := by aesop_cat

end Str

section Interpretation

variable {C : Type u₁} [Category.{v₁, u₁} C] [HasFiniteProducts C] {σ : Signature.{u,v,w,w',w''}}
variable [DecidableEq σ.Base] [DecidableEq (σ.Base × σ.Sorts)]
variable (M : σ.Str C) {Γ : σ.Ctx}

namespace Ctx

/-- This defines the interpretation of a context `Γ`. -/
noncomputable def intrpIn (Γ : σ.Ctx) : C := ∏ᶜ (fun x : Γ.ctx ↦ Mˢ x.1.2)

/-- Given a `x : Γ.ctx`, `intrpInπ` define the projection morphism in `x`. -/
noncomputable def intrpInπ (x : Γ.ctx) : Γ.intrpIn M ⟶ Mˢ x.1.2 :=
  Pi.π (fun y : Γ.ctx ↦ Mˢ y.1.2) x

/-- Given `x : σ.Base × σ.Sorts` such that `x.1 ∉ Γ.Label`, `Γ.intrpForget x p` is the canonic
morphism from `(Γ :: ⟨x, p⟩).intrpIn M` to `Γ.intrpIn M`. -/
noncomputable def intrpForget (x : σ.Base × σ.Sorts) (p : x.1 ∉ Γ.Label) :
  (Γ :: ⟨x, p⟩).intrpIn M ⟶ Γ.intrpIn M :=
  Pi.lift (fun y : Γ.ctx ↦ intrpInπ M ⟨y.1, by simp [Ctx.extended]⟩)

/-- Assuming `Γ.ctx ⊆ Δ.ctx`, `ctxProj` is the canonic morphism from `Δ.intrpIn M` to
`Γ.intrpIn M`. -/
noncomputable def ctxProj {Γ Δ : σ.Ctx} (h : Γ.ctx ⊆ Δ.ctx) :
  Δ.intrpIn M ⟶ Γ.intrpIn M :=
  Pi.lift (fun y : Γ.ctx ↦ intrpInπ M ⟨y.1, Set.mem_of_mem_of_subset y.2 h⟩)

end Ctx

namespace Term

/-- This defines the interpretation of a term `t` in context `Γ`. -/
noncomputable def intrpIn {s : σ.Sorts} (t : σ.Term s) (p : Γ ⊢ t) : Γ.intrpIn M ⟶ Mˢ s :=
  match t with
  | var x => Γ.intrpInπ M ⟨x,p⟩
  | app f ts => Pi.lift (fun i ↦ (ts i).intrpIn (p i)) ≫ Mᶠ f


omit [DecidableEq σ.Base] [DecidableEq (σ.Base × σ.Sorts)] in
/-- Congruence property of `Term.intrpIn`. -/
lemma congr_intrpIn {Γ : σ.Ctx} {s : σ.Sorts} {t t' : σ.Term s} (h' : t = t') (p : Γ ⊢ t)
  (q : Γ ⊢ t') : t.intrpIn M p = t'.intrpIn M q := by subst h'; simp

end Term

namespace Ctx.Subst

/-- This defines the interpretation of a substitutaion `γ : Γ.Subst Δ` as the canonic morphism from
`Δ.intrpIn M` to `Γ.intrpIn M` . -/
noncomputable def intrpIn {Δ : σ.Ctx} (γ : Γ.Subst Δ) : Δ.intrpIn M ⟶ Γ.intrpIn M :=
  Pi.lift (fun x : Γ.ctx ↦ (γ.map x).intrpIn M (γ.inCtx_map x))

omit [DecidableEq σ.Base] [DecidableEq (σ.Base × σ.Sorts)] in
/-- Congruence property of `Subst.intrpIn` respect to `Subst.equal`. -/
lemma congr_intrpIn {Γ Δ : σ.Ctx} {γ γ' : Γ.Subst Δ} (h : γ.equal γ') :
  γ.intrpIn M = γ'.intrpIn M := by
  unfold intrpIn
  have : (fun x ↦ (γ.map x).intrpIn M (γ.inCtx_map x)) =
    (fun x ↦ (γ'.map x).intrpIn M (γ'.inCtx_map x)) := by
    funext x
    unfold equal at h
    rcases h with ⟨rf1, h⟩
    rcases h with ⟨rf2, h⟩
    specialize h x
    simp [h]
  simp [this]

omit [DecidableEq σ.Base] [DecidableEq (σ.Base × σ.Sorts)]
/-- Given a renaming `ρ : Γ.Renaming Δ`, two contexts `Γ` and `Δ` are isomorphic. -/
lemma renaming_is_iso {Γ Δ : σ.Ctx} (ρ : Γ.Renaming Δ) : Nonempty (Γ.intrpIn M ≅ Δ.intrpIn M) := by
  apply Nonempty.intro
  apply Pi.whiskerEquiv (Equiv.ofBijective ρ.map ρ.isBijection)
  intro x
  simp
  rw [ρ.preserve_sort x]

end Ctx.Subst

/-- The interpretaion of the projection substituation `Γ.substπ x p` is the same as
`Γ.intrpForget M x p` morphism. -/
lemma substπ_is_intrpForget {Γ : σ.Ctx} (x : σ.Base × σ.Sorts) (p : x.1 ∉ Γ.Label) :
  (Γ.substπ x p).intrpIn M = Γ.intrpForget M x p := by
  rw [Ctx.intrpForget, Ctx.substπ, Ctx.substπG, Ctx.Subst.intrpIn]
  apply Limits.Pi.hom_ext
  intro a
  rw [Pi.lift_π, Pi.lift_π, Term.intrpIn]


omit [DecidableEq σ.Base] [DecidableEq (σ.Base × σ.Sorts)] in
/-- The interpretaion of the projection substituation `Γ.substπG x p` is the same as
`Γ.ctxProj M h` morphism. -/
lemma substπG_is_ctxProj {Γ Δ : σ.Ctx} (h : Γ.ctx ⊆ Δ.ctx) :
  (Γ.substπG Δ h).intrpIn M = Γ.ctxProj M h := by
  rw [Ctx.ctxProj, Ctx.substπG, Ctx.Subst.intrpIn]
  apply Limits.Pi.hom_ext
  intro a
  rw [Pi.lift_π, Pi.lift_π, Term.intrpIn]

/-- Given a substitution `γ` of type `Γ.Subst Δ` and two new labels `x` and `x'`, the interpretation
of the extended substitution `γ.extended p q s` is the same as the canonic morphism from
interpretation of `Δ :: ⟨⟨x', s⟩, q⟩` to interpretation of `Γ :: ⟨⟨x, s⟩, p⟩`. -/
lemma intrpIn_extended_is_lift {s : σ.Sorts} {Γ Δ : σ.Ctx} {x x' : σ.Base} (p : x ∉ Γ.Label)
  (q : x' ∉ Δ.Label) (γ : Γ.Subst Δ) : (γ.extended p q s).intrpIn M =
  Pi.lift (fun y : (Γ::⟨⟨x, s⟩, p⟩).ctx ↦ if hy : y.1 = ⟨x, s⟩ then
    (Term.var ⟨x', y.1.2⟩).intrpIn M (Γ := (Δ :: ⟨(x',s), q⟩)) (by
      unfold Term.InCtx;unfold Ctx.ctx;unfold Ctx.extended;simp [hy])
    else (γ.map (⟨y.1, Ctx.mem_of_mem_extended_neq y.2 hy⟩)).intrpIn M
      (Δ.inCtx_extended_of_inCtx (x := (x',s)) q
      (γ.inCtx_map ⟨y.1, Ctx.mem_of_mem_extended_neq y.2 hy⟩))) := by
  apply Limits.Pi.hom_ext
  intro b
  rw [Pi.lift_π, Ctx.Subst.intrpIn, Pi.lift_π]
  by_cases hb : b.1 = (x,s)
  rw [Ctx.Subst.extended]
  simp only [hb, ↓reduceDIte]
  rw [Ctx.Subst.extended]
  simp only [hb, ↓reduceDIte]

namespace Term

omit [DecidableEq σ.Base] [DecidableEq (σ.Base × σ.Sorts)] in
/-- This is Lemma D.1.2.4 in [Elephant] which is bassically the substitution lemma for terms. -/
lemma substitution : ∀ (t : σ.Term s) (p : Γ ⊢ t) (γ : Γ.Subst Δ),
    (t[γ] p).intrpIn M (γ.term_inCtx p) = γ.intrpIn M ≫ t.intrpIn M p := by
  intro t
  induction t with
  | var x => intros p γ
             unfold Ctx.Subst.term
             rw [intrpIn, Ctx.intrpInπ, Ctx.Subst.intrpIn]
             simp
  | app f ts hts => intros p γ
                    rw [intrpIn, ← assoc]
                    refine eq_whisker ?_ (Mᶠ f)
                    apply Limits.Pi.hom_ext
                    intro i
                    rw [Pi.lift_π, assoc, Pi.lift_π]
                    exact hts i (p i) γ

omit [DecidableEq σ.Base] [DecidableEq (σ.Base × σ.Sorts)] in
/-- Let `t` be a term and `Γ` and `Δ` two contexts s.t. `Γ.ctx ⊆ Δ.ctx`. Then the interpretation of
`t` in context `Γ` is related to the interpretation of `t` in context `Δ` via the
projection substitution. -/
lemma intrpIn_extended_ctx : ∀ (s : σ.Sorts) (t : σ.Term s) (pΓ : Γ ⊢ t) (pΔ : Δ ⊢ t)
  (h : Γ.ctx ⊆ Δ.ctx), t.intrpIn M pΔ = (t [Γ.substπG Δ h] pΓ).intrpIn M
  ((Γ.substπG Δ h).term_inCtx pΓ) := by
  intros s t
  induction t with
  | var x => intros pΓ pΔ h
             unfold Ctx.Subst.term Ctx.substπG intrpIn Ctx.intrpInπ
             simp
  | app f ts hts => intros pΓ pΔ h
                    unfold Ctx.Subst.term Ctx.substπG intrpIn
                    apply eq_whisker (h := Mᶠ f)
                    congr
                    funext i
                    specialize hts i (pΓ i) (pΔ i) h
                    exact hts

end Term

namespace Ctx.Subst

omit [DecidableEq σ.Base] [DecidableEq (σ.Base × σ.Sorts)] in
/-- The interpretation of substitution preserves the compoistion `Subst.Comp` of substitutions. -/
lemma intrpIn_substComp {Γ Δ Γ' : σ.Ctx} (γ : Γ.Subst Δ) (γ' : Δ.Subst Γ') : γ'.intrpIn M ≫
  γ.intrpIn M  = (γ.Comp γ').intrpIn M := by
  rw [intrpIn, intrpIn, intrpIn, Comp]
  simp
  apply Limits.Pi.hom_ext
  intro x
  rw [Category.assoc, Pi.lift_π, Pi.lift_π]
  exact ((γ.map x).substitution M (γ.inCtx_map x) γ').symm

end Ctx.Subst

variable [Observable.{u₁, v₁, w₁, w'', _} C]

/-- The followign square is a pullback square (we have used [[.]] as a notation for
the interpretation):

    [[Δ :: ⟨⟨x', s⟩, q⟩`]] ---- [[γ.extended p q s]] ----> [[Γ :: ⟨⟨x, s⟩, p⟩`]]
     |                             |
 [[Δ.substπ (x',s) q]]        [[Γ.substπ (x,s) p]]
     |                             |
     v                             v
    [[Δ]] ---- [[γ]] -----------> [[Γ]]

This is a crucial lemma for proving `Formula.substitution` in the case of `∃'`.
-/
lemma intrpIn_subst_extended_is_pullback {Γ Δ : σ.Ctx} {x x' : σ.Base} (p : x ∉ Γ.Label)
  (q : x' ∉ Δ.Label) (s : σ.Sorts) (γ : Γ.Subst Δ) : IsPullback ((γ.extended p q s).intrpIn M)
    ((Δ.substπ (x',s) q).intrpIn M) ((Γ.substπ (x,s) p).intrpIn M) (γ.intrpIn M) := by
  rw [substπ_is_intrpForget M (x,s) p, substπ_is_intrpForget M (x',s) q]
  rw [intrpIn_extended_is_lift M p q γ, Ctx.intrpForget, Ctx.intrpForget, Ctx.Subst.intrpIn]
  let rw1 := substπ_is_intrpForget M (x,s) p
  let rw2 := substπ_is_intrpForget M (x',s) q
  rw [Ctx.intrpForget] at rw1
  rw [Ctx.intrpForget] at rw2
  have rlemma : (γ.extended p q s).intrpIn M ≫ Γ.intrpForget M (x, s) p =
      (Δ.substπ (x', s) q).intrpIn M ≫ Pi.lift fun x ↦ (γ.map x).intrpIn M (γ.inCtx_map x) := by
    rw [Ctx.intrpForget, <- rw1, (Γ.substπ (x,s) p).intrpIn_substComp]
    rw [<- Ctx.Subst.intrpIn , γ.intrpIn_substComp]
    apply congr_arg
    rw [Ctx.Subst.Comp, Ctx.Subst.Comp, Ctx.Subst.extended, Ctx.substπ, Ctx.substπG]
    simp
    ext y
    rw [Ctx.Subst.term]
    simp
    by_cases hy : y.1 = (x,s)
    simp only [hy]
    dsimp
    have ctr: x ∈ Γ.Label := by
      unfold Ctx.Label
      simp
      use s
      rw [<- hy]
      exact y.2
    exfalso
    exact absurd ctr p
    simp only [hy]
    dsimp
    rw [Ctx.Subst.substπ_preserve_term Δ (x',s) q (γ.map y) (γ.inCtx_map y)]
  refine IsPullback.of_iso_pullback ?_ ?_ ?_ ?_
  refine ⟨?_⟩
  rw [<- intrpIn_extended_is_lift M p q γ, <- rw1, <- rw2, <- Ctx.Subst.intrpIn]
  exact rlemma
  rw [Ctx.intrpIn]
  refine ⟨?_, ?_, ?_, ?_⟩
  refine pullback.lift ?_ ?_ ?_
  exact (γ.extended p q s).intrpIn M
  exact (Δ.substπ (x',s) q).intrpIn M
  exact rlemma
  refine Pi.lift ?_
  intro bΔx
  by_cases hbΔx : bΔx.1 ∈ Δ.ctx
  exact pullback.snd (Γ.intrpForget M (x,s) p)
    (Pi.lift fun (x : Γ.ctx) ↦ (γ.map x).intrpIn M (γ.inCtx_map x)) ≫ (Δ.intrpInπ M ⟨bΔx.1, hbΔx⟩)
  have aux1 : Mˢ (x,s).2 = Mˢ (bΔx.1).2 := by
    apply congr_arg
    have : bΔx.1 = (x',s) := by
      let aux1 := bΔx.2
      unfold Ctx.extended at aux1
      rw [Finset.mem_insert] at aux1
      rcases aux1 with (h1 | h2)
      exact h1
      exfalso
      exact hbΔx h2
    rw [this]
  exact pullback.fst (Γ.intrpForget M (x,s) p)
    (Pi.lift fun (x : Γ.ctx) ↦ (γ.map x).intrpIn M (γ.inCtx_map x)) ≫
    ((Γ::⟨⟨x, s⟩, p⟩).intrpInπ M ⟨(x,s), by unfold Ctx.extended;simp⟩) ≫ eqToHom aux1
  apply Limits.Pi.hom_ext
  intro bΔx
  by_cases hbΔx : bΔx.1 ∈ Δ.ctx
  simp [hbΔx, ↓reduceDIte]
  rw [<- assoc]
  erw [pullback.lift_snd (f := Γ.intrpForget M (x, s) p)
    (g := (Pi.lift fun x ↦ (γ.map x).intrpIn M (γ.inCtx_map x))) ((γ.extended p q s).intrpIn M)
    ((Δ.substπ (x',s) q).intrpIn M) rlemma]
  have aux2 : Pi.π (fun x ↦ Mˢ x.1.2) bΔx = (Δ.intrpForget M (x',s) q) ≫
    (Δ.intrpInπ M ⟨bΔx.1,hbΔx⟩) := by
    rw [Ctx.intrpForget, Ctx.intrpInπ, Pi.lift_π, Ctx.intrpInπ]
  rw [aux2]
  apply eq_whisker
  rw [substπ_is_intrpForget M (x',s) q]
  simp [hbΔx, ↓reduceDIte]
  rw [<- assoc]
  erw [pullback.lift_fst (f := Γ.intrpForget M (x, s) p)
    (g := (Pi.lift fun x ↦ (γ.map x).intrpIn M (γ.inCtx_map x))) ((γ.extended p q s).intrpIn M)
    ((Δ.substπ (x',s) q).intrpIn M) rlemma]
  rw [Ctx.Subst.intrpIn, Ctx.intrpInπ, <- assoc, Pi.lift_π]
  have Int : (Γ :: ⟨(x,s),p⟩) ⊢ Term.var (x,s) := by unfold Ctx.extended; unfold Term.InCtx;simp
  have Int2 : (Δ :: ⟨(x',s),q⟩) ⊢ Term.var (x',s) := by unfold Ctx.extended; unfold Term.InCtx;simp
  have Int3 : (x',s) ∈ (Δ :: ⟨(x',s),q⟩).ctx := by unfold Ctx.extended;simp
  have aux3 : (γ.extended p q s).map ⟨(x,s), by unfold Ctx.extended;simp⟩ = Term.var (x',s) := by
    rw [Ctx.Subst.extended]; simp
  have aux44 := Term.congr_intrpIn M aux3 (((γ.extended p q s)).term_inCtx Int) Int2
  rw [aux44, Term.intrpIn, Ctx.intrpInπ]
  have aux6 : bΔx.1 = (x',s) := by
    let aux1 := bΔx.2
    unfold Ctx.extended at aux1
    rw [Finset.mem_insert] at aux1
    rcases aux1 with (h1 | h2)
    exact h1
    exfalso
    exact hbΔx h2
  have aux5 : bΔx = ⟨(x',s),Int3⟩ := by
    exact Subtype.ext aux6
  simp [aux5]
  apply pullback.hom_ext
  rw [id_comp]
  rw [assoc]
  erw [pullback.lift_fst (f := Γ.intrpForget M (x, s) p)
    (g := (Pi.lift fun x ↦ (γ.map x).intrpIn M (γ.inCtx_map x))) ((γ.extended p q s).intrpIn M)
    ((Δ.substπ (x',s) q).intrpIn M) rlemma]
  apply Limits.Pi.hom_ext
  intro bΓx
  rw [assoc, Ctx.Subst.intrpIn, Pi.lift_π]
  by_cases hbΓx : bΓx.1 ∈ Γ.ctx
  have aux1 : Pi.π (fun x_1 ↦ Mˢ (x_1).1.2) bΓx = Γ.intrpForget M (x,s) p ≫
    Γ.intrpInπ M ⟨bΓx.1,hbΓx⟩ := by
    rw [Ctx.intrpForget, Ctx.intrpInπ, Pi.lift_π, Ctx.intrpInπ]
  rw [aux1]
  have aux00 : bΓx.1 ≠ (x,s) := by
    by_contra!
    have this1 : bΓx.1 ∉ Γ.ctx := by
      by_contra this3
      rw [this] at this3
      have : x ∈ Γ.Label := by
        unfold Ctx.Label
        simp
        use s
      exact p this
    exact this1 hbΓx
  have aux2 : ((γ.extended p q s).map bΓx).intrpIn M ((γ.extended p q s).inCtx_map bΓx) =
    Δ.intrpForget M (x',s) q ≫ γ.intrpIn M ≫ Γ.intrpInπ M ⟨bΓx.1,hbΓx⟩ := by
    have aux0 : Γ ⊢ Term.var bΓx.1 := hbΓx
    have aux1 : (γ.extended p q s).map bΓx = (Term.var bΓx.1) [γ] aux0 := by
      rw [Ctx.Subst.extended, Ctx.Subst.term]
      simp [aux00]
    have aux2 : (Δ :: ⟨(x', s), q⟩) ⊢ (γ.extended p q s).map bΓx := (γ.extended p q s).inCtx_map bΓx
    have aux5 : Δ.ctx ⊆ (Δ ::⟨(x', s), q⟩).ctx := by unfold Ctx.extended;simp
    have aux3 : (Δ :: ⟨(x', s), q⟩) ⊢ (Term.var bΓx.1) [γ] aux0 :=
      ((Term.var bΓx.1) [γ] aux0).weakening Δ (Δ ::⟨(x', s), q⟩) aux5 (γ.term_inCtx aux0)
    let aux4 := Term.congr_intrpIn M aux1 aux2 aux3
    rw [aux4]
    let aux6 := ((.var bΓx.1) [γ] aux0).intrpIn_extended_ctx M bΓx.1.2 (γ.term_inCtx aux0) aux3 aux5
    rw [((Term.var bΓx.1) [γ] aux0).substitution M] at aux6
    rw [(Term.var bΓx.1).substitution M aux0 γ] at aux6
    rw [substπG_is_ctxProj, Ctx.ctxProj] at aux6
    rw [aux6, <- Ctx.intrpForget]
    rfl
  rw [aux2, <- assoc, <- assoc, <- assoc]
  apply eq_whisker
  erw [pullback.condition]
  rw [<- Ctx.Subst.intrpIn]
  apply eq_whisker
  apply Limits.Pi.hom_ext
  intro bΔ
  unfold Ctx.intrpForget
  rw [assoc, Pi.lift_π, Ctx.intrpInπ, Ctx.intrpInπ, Pi.lift_π]
  split_ifs with hbΔx
  rfl
  simp at hbΔx
  have aux0 : bΓx.1 = (x,s) := by
    let aux1 := bΓx.2
    unfold Ctx.extended at aux1
    rw [Finset.mem_insert] at aux1
    rcases aux1 with (h1 | h2)
    exact h1
    exfalso
    exact hbΓx h2
  have aux1 : (γ.extended p q s).map bΓx = Term.var (x',bΓx.1.2) := by
    rw [Ctx.Subst.extended]
    simp [aux0]
  have Int : (Δ :: ⟨(x', s), q⟩) ⊢ Term.var (x',bΓx.1.2) := by
    unfold Ctx.extended
    unfold Term.InCtx
    simp
    left
    simp [aux0]
  have aux2 := Term.congr_intrpIn M aux1 ((γ.extended p q s).inCtx_map bΓx) Int
  rw [aux2, Term.intrpIn, Ctx.intrpInπ, Ctx.intrpInπ, Pi.lift_π]
  have aux3 : (x', bΓx.1.2) ∉ Δ.ctx := Ctx.notin_ctx_of_notin_label (Γ := Δ) (x := (x', bΓx.1.2)) q
  simp [aux3]
  apply whisker_eq
  have Int3 : (x,s) ∈ (Γ :: ⟨(x,s),p⟩).ctx := by unfold Ctx.extended;simp
  have aux6 : bΓx.1 = (x,s) := by
    let aux1 := bΓx.2
    unfold Ctx.extended at aux1
    rw [Finset.mem_insert] at aux1
    rcases aux1 with (h1 | h2)
    exact h1
    exfalso
    exact hbΓx h2
  have aux5 : bΓx = ⟨(x,s),Int3⟩ := by
    exact Subtype.ext aux6
  simp [aux5]
  rw [id_comp, assoc]
  erw [pullback.lift_snd (f := Γ.intrpForget M (x, s) p)
    (g := (Pi.lift fun x ↦ (γ.map x).intrpIn M (γ.inCtx_map x))) ((γ.extended p q s).intrpIn M)
    ((Δ.substπ (x',s) q).intrpIn M) rlemma]
  apply Limits.Pi.hom_ext
  intro bΔx
  rw [assoc, Ctx.Subst.intrpIn, Pi.lift_π]
  have aux1 : ((Δ.substπ (x', s) q).map bΔx).intrpIn M ((Δ.substπ (x', s) q).inCtx_map bΔx) =
    Δ.intrpForget M (x',s) q ≫ Δ.intrpInπ M bΔx := by
    rw [Ctx.intrpForget, Ctx.intrpInπ, Pi.lift_π]
    have this1 : (Δ.substπ (x', s) q).map bΔx = Term.var bΔx.1 := by
      unfold Ctx.substπ Ctx.substπG; simp
    have this2 : (Δ :: ⟨(x',s),q⟩) ⊢ Term.var bΔx.1 := by unfold Term.InCtx Ctx.extended; simp
    rw [Term.congr_intrpIn M this1 ((Δ.substπ (x', s) q).inCtx_map bΔx) this2, Term.intrpIn]
  rw [aux1, <- Ctx.intrpInπ, <- assoc]
  apply eq_whisker
  apply Limits.Pi.hom_ext
  intro bΔ
  unfold Ctx.intrpForget
  rw [assoc, Pi.lift_π, Ctx.intrpInπ, Ctx.intrpInπ, Pi.lift_π]
  split_ifs with hbΔx
  rfl
  simp at hbΔx
  simp
  rw [intrpIn_extended_is_lift M p q γ]
  simp
  rw [substπ_is_intrpForget M (x',s) q, Ctx.intrpForget]

namespace Formula open Subobject

/-- The interpretation of a formula `φ` in context `Γ` as a monomorphism.-/
noncomputable def intrpIn {Γ : σ.Ctx} (φ : σ.Formula) (p : Γ ⊢ φ) : MonoOver (Γ.intrpIn M) :=
  match φ with
  | ⊤ => ⊤
  | ⊥ => ⊥_(MonoOver (Γ.intrpIn M))
  | t₁ ≃ t₂ : _ => MonoOver.mk' (equalizer.ι (t₁.intrpIn M p.1) (t₂.intrpIn M p.2))
  | φ₁ ∧' φ₂ => (MonoOver.inf.obj (φ₁.intrpIn p.1)).obj (φ₂.intrpIn p.2)
  | ⋁ I, fs => sigmaObj (fun i : I ↦ (fs i).intrpIn (p.1 i))
  | (∃'x) φ => (MonoOver.«exists» ((Γ.substπ x p.1).intrpIn M)).obj (φ.intrpIn p.2)
  | .rel R ts => (MonoOver.pullback (Pi.lift (fun i => (ts i).intrpIn M (p i)))).obj (Mʳ R)


/- This is Lemma D.1.2.7 in [Elephant]. This is only an iso, not an equality, if one uses `MonoOver`
instead of `Subobject`.-/
lemma substitution : ∀ (φ : σ.Formula) {Γ Δ : σ.Ctx} (p : Γ ⊢ φ) (γ : Γ.Subst Δ),
    Nonempty ((MonoOver.pullback (γ.intrpIn M)).obj (φ.intrpIn M p) ≅
    (φ[γ] p).intrpIn M (γ.formula_inCtx p)) := by
  intro φ
  induction φ with
  | truth => intros Γ Δ p γ
             unfold Ctx.Subst.formula
             rw [intrpIn, intrpIn]
             exact (Nonempty.intro (MonoOver.pullbackTop (Ctx.Subst.intrpIn M γ)))
  | falsum => intros Γ Δ p γ
              unfold Ctx.Subst.formula
              rw [intrpIn, intrpIn]
              exact ⟨Observable.pullback_preserve_bot (γ.intrpIn M)⟩
  | equal s t u => intros Γ Δ p γ
                   obtain tt := t.substitution M p.1 γ
                   obtain uu := u.substitution M p.2 γ
                   unfold Ctx.Subst.formula
                   rw [intrpIn, intrpIn]
                   apply Nonempty.intro
                   have aux1 : MonoOver.mk' (equalizer.ι
                    ((t [γ] p.1).intrpIn M (γ.term_inCtx p.1))
                    ((u [γ] p.2).intrpIn M (γ.term_inCtx p.2))) ≅ MonoOver.mk' (equalizer.ι
                    (γ.intrpIn M ≫ t.intrpIn M p.1) (γ.intrpIn M ≫ u.intrpIn M p.2)) := by
                    rw [tt, uu]
                   apply Iso.trans ?_ aux1.symm
                   let G := MonoOver.pullback (γ.intrpIn M)
                   let f := t.intrpIn M p.1
                   let g := u.intrpIn M p.2
                   let h := γ.intrpIn M
                   let mainIso := Observable.pullback_of_equalizer_is_equalizer C f g h
                   apply Classical.choice at mainIso
                   exact mainIso
  | binConj φ ψ hφ hψ => intros Γ Δ p γ
                         unfold Ctx.Subst.formula
                         specialize hφ p.1 γ
                         specialize hψ p.2 γ
                         rw [intrpIn, intrpIn]
                         let ⟨hφ⟩ := hφ
                         let ⟨hψ⟩ := hψ
                         apply Nonempty.intro
                         obtain isoFun := MonoOver.inf.mapIso hφ
                         obtain iso2 := isoFun.app ((MonoOver.pullback (γ.intrpIn M)).obj
                          (ψ.intrpIn M p.2))
                         obtain iso3 := (MonoOver.inf.obj
                          ((φ [γ] p.1).intrpIn M (γ.formula_inCtx p.1))).mapIso hψ
                         obtain iso := iso2 ≪≫ iso3
                         apply Iso.trans ?_ iso
                         let g := γ.intrpIn M
                         let f₁ := φ.intrpIn M p.1
                         let f₂ := ψ.intrpIn M p.2
                         apply Classical.choice
                         exact Cartesian.pullback_commutes_inf C g f₁ f₂
  | infDisj I fs hfs => intros Γ Δ p γ
                        unfold Ctx.Subst.formula
                        rw [intrpIn, intrpIn]
                        apply Nonempty.intro
                        have aux1 : ∀ i, ((fs i) [γ] (p.1 i)).intrpIn M (γ.formula_inCtx (p.1 i))
                         ≅ (MonoOver.pullback (γ.intrpIn M)).obj ((fs i).intrpIn M (p.1 i)) := by
                         intro i
                         specialize hfs i (p.1 i) γ
                         apply Classical.choice at hfs
                         exact hfs.symm
                        have : ∐ (fun i ↦ ((fs i) [γ] p.1 i).intrpIn M
                         (γ.formula_inCtx (p.1 i))) ≅ ∐ (fun i ↦
                            (MonoOver.pullback (γ.intrpIn M)).obj ((fs i).intrpIn M (p.1 i))) := by
                          exact Limits.Sigma.mapIso aux1
                        apply Iso.trans ?_ this.symm
                        let lm := fun i ↦ (fs i).intrpIn M (p.1 i)
                        apply Classical.choice
                        exact Observable.pullback_preserve_coProd C (γ.intrpIn M) lm
  | exist x φ hφ => intros Γ Δ p γ
                    unfold Ctx.Subst.formula
                    rw [intrpIn]
                    apply Nonempty.intro
                    by_cases hx : x.1 ∈ Δ.Label
                    simp only [hx, ↓reduceDIte]
                    rw [intrpIn]
                    specialize hφ p.2 (γ.extended p.1 (Δ.newLabel_notin_label) x.2)
                    apply Classical.choice at hφ
                    let h2 := (MonoOver.exists
                      ((Δ.substπ (σ.newLabel Δ.ctx, x.2) Δ.newLabel_notin_label).intrpIn M)).mapIso hφ
                    apply Iso.trans ?_ h2
                    let f := (Γ.substπ x p.1).intrpIn M
                    let h := (γ.extended p.1 (Δ.newLabel_notin_label) x.2).intrpIn M
                    let k := (Δ.substπ (σ.newLabel Δ.ctx, x.2) (Δ.newLabel_notin_label)).intrpIn M
                    let g := γ.intrpIn M
                    have l2 : (Γ.substπ x p.1).Comp (γ.extended p.1 (Δ.newLabel_notin_label) x.2) =
                      γ.Comp (Δ.substπ (σ.newLabel Δ.ctx, x.2) (Δ.newLabel_notin_label)) := by
                      rw [Ctx.Subst.Comp, Ctx.Subst.Comp, Ctx.Subst.extended]
                      rw [Ctx.substπ, Ctx.substπG]
                      simp
                      ext y
                      rw [Ctx.Subst.term]
                      simp
                      by_cases hx : y = x
                      simp only [hx]
                      dsimp
                      have ctr: x.1 ∈ Γ.Label := by
                       rw [<- hx]
                       let kkk := y.2
                       unfold Ctx.Label
                       simp
                       use y.1.2
                      exfalso
                      exact absurd ctr p.1
                      simp only [hx]
                      dsimp
                      rw [Ctx.Subst.substπ_preserve_term Δ (σ.newLabel Δ.ctx, x.2)
                        Δ.newLabel_notin_label (γ.map y) (γ.inCtx_map y)]
                    have : h ≫ f = k ≫ g := by
                      rw [(Γ.substπ x p.1).intrpIn_substComp, γ.intrpIn_substComp, l2]
                    let isPull :=  intrpIn_subst_extended_is_pullback M p.1 (Δ.newLabel_notin_label)
                       x.2 γ
                    let aux := (Regular.image_stable_pullback isPull).symm
                    rw [<- Functor.comp_obj, <- Functor.comp_obj]
                    apply aux.app
                    simp only [hx, ↓reduceDIte]
                    rw [intrpIn]
                    specialize hφ p.2 (γ.extended p.1 hx x.2)
                    apply Classical.choice at hφ
                    let h2 := (MonoOver.exists ((Δ.substπ x hx).intrpIn M)).mapIso hφ
                    apply Iso.trans ?_ h2
                    let f := (Γ.substπ x p.1).intrpIn M
                    let h := (γ.extended p.1 hx x.2).intrpIn M
                    let k := (Δ.substπ x hx).intrpIn M
                    let g := γ.intrpIn M
                    have l2 : (Γ.substπ x p.1).Comp (γ.extended p.1 hx x.2) =
                      γ.Comp (Δ.substπ x hx) := by
                      rw [Ctx.Subst.Comp, Ctx.Subst.Comp, Ctx.Subst.extended]
                      rw [Ctx.substπ, Ctx.substπG]
                      simp
                      ext y
                      rw [Ctx.Subst.term]
                      simp
                      by_cases hxc : y = x
                      simp only [hxc]
                      dsimp
                      have ctr: x.1 ∈ Γ.Label := by
                       rw [<- hxc]
                       let kkk := y.2
                       unfold Ctx.Label
                       simp
                       use y.1.2
                      exfalso
                      exact absurd ctr p.1
                      simp only [hxc]
                      dsimp
                      rw [Ctx.Subst.substπ_preserve_term Δ x hx (γ.map y) (γ.inCtx_map y)]
                    have : h ≫ f = k ≫ g := by
                      rw [(Γ.substπ x p.1).intrpIn_substComp, γ.intrpIn_substComp, l2]
                    let isPull := intrpIn_subst_extended_is_pullback M p.1 hx x.2 γ
                    let aux := (Regular.image_stable_pullback isPull).symm
                    rw [<- Functor.comp_obj, <- Functor.comp_obj]
                    apply aux.app
  | rel R ts => intros Γ Δ p γ
                unfold Ctx.Subst.formula
                rw [intrpIn, intrpIn]
                apply Nonempty.intro
                let iso1 := (MonoOver.pullbackComp (γ.intrpIn M)
                  (Pi.lift fun i ↦ (ts i).intrpIn M (p i))).app (Mʳ R)
                apply Iso.trans iso1.symm ?_
                have aux1 : γ.intrpIn M ≫ (Pi.lift fun i ↦ (ts i).intrpIn M (p i)) =
                  (Pi.lift fun i ↦ γ.intrpIn M ≫ (ts i).intrpIn M (p i)) := by
                  ext x
                  simp
                have : γ.intrpIn M ≫ (Pi.lift fun i ↦ (ts i).intrpIn M (p i)) =
                  Pi.lift fun i ↦ ((ts i) [γ] (p i)).intrpIn M (γ.term_inCtx (p i)) := by
                  rw [aux1]
                  have : (fun i ↦ γ.intrpIn M ≫ (ts i).intrpIn M (p i)) =
                    fun i ↦ ((ts i) [γ] (p i)).intrpIn M (γ.term_inCtx (p i)) := by
                    funext i
                    rw [(ts i).substitution M (p i) γ]
                  rw [this]
                rw [this]

/-- Ther interpretation of `φ [γ]` and `φ [γ']` are the same if we have a proof of `γ.equal γ'`. -/
lemma congr_intrpIn_subst {Γ Δ : σ.Ctx} (φ : σ.Formula) (γ γ' : Γ.Subst Δ) (h : γ.equal γ')
  (p : Γ ⊢ φ) : (φ[γ] p).intrpIn M (γ.formula_inCtx p) = ((φ[γ'] p).intrpIn M
  (γ'.formula_inCtx p)) := by simp [subst_ext φ Γ Γ Δ Δ γ γ' p p h]

/-- Let `φ` be a formula and `Γ` and `Δ` two contexts s.t. `Γ.ctx ⊆ Δ.ctx`. Then the interpretation
of `φ` in context `Γ` is related to the interpretation of `φ` in context `Δ` via the
projection substitution. -/
lemma intrpIn_extended_ctx : ∀ (φ : σ.Formula) (Γ Δ : σ.Ctx) (pΓ : Γ ⊢ φ) (pΔ : Δ ⊢ φ)
  (h : Γ.ctx ⊆ Δ.ctx), φ.intrpIn M pΔ = (φ [Γ.substπG Δ h] pΓ).intrpIn M
  ((Γ.substπG Δ h).formula_inCtx pΓ) := by
  intros φ
  induction φ with
  | truth => intros Γ Δ pΓ pΔ h
             unfold Ctx.Subst.formula
             rfl
  | falsum => intros Γ Δ pΓ pΔ h
              unfold Ctx.Subst.formula
              rfl
  | equal s t u => intros Γ Δ pΓ pΔ h
                   unfold Ctx.Subst.formula
                   rw [intrpIn, intrpIn]
                   obtain teq := t.intrpIn_extended_ctx M s pΓ.1 pΔ.1 h
                   obtain ueq := u.intrpIn_extended_ctx M s pΓ.2 pΔ.2 h
                   congr! 2
  | binConj φ ψ hφ hψ => intros Γ Δ pΓ pΔ h
                         rw [intrpIn]
                         unfold Ctx.Subst.formula
                         rw [intrpIn]
                         specialize hφ Γ Δ pΓ.1 pΔ.1 h
                         specialize hψ Γ Δ pΓ.2 pΔ.2 h
                         rw [hφ,hψ]
  | infDisj I fs hfs => intros Γ Δ pΓ pΔ h
                        rw [intrpIn]
                        unfold Ctx.Subst.formula
                        rw [intrpIn]
                        have aux : ∀ i, Δ ⊢ ((fs i) [Γ.substπG Δ h] (pΓ.1 i)) := by
                          intro i
                          exact ((Γ.substπG Δ h).formula_inCtx pΓ).1 i
                        have : (fun i ↦ (fs i).intrpIn M (pΔ.1 i)) =
                          (fun i ↦ ((fs i) [Γ.substπG Δ h] (pΓ.1 i)).intrpIn M (aux i)) := by
                          funext i
                          specialize hfs i Γ Δ (pΓ.1 i) (pΔ.1 i) h
                          exact hfs
                        simp [this]
  | exist x φ hφ => intros Γ Δ pΓ pΔ h
                    rw [intrpIn]
                    unfold Ctx.Subst.formula
                    by_cases hx : x.1 ∈ Δ.Label
                    let hxc := pΔ.1
                    contradiction
                    simp only [hx, ↓reduceDIte]
                    rw [intrpIn]
                    have aauux1 : (Γ :: ⟨x, pΓ.1⟩).ctx ⊆ (Δ :: ⟨x, pΔ.1⟩).ctx := by
                      unfold Ctx.extended
                      simp
                      exact Finset.insert_subset_insert x (s := Γ.ctx) (t := Δ.ctx) h
                    specialize hφ (Γ :: ⟨x, pΓ.1⟩) (Δ :: ⟨x, pΔ.1⟩) pΓ.2 pΔ.2 aauux1
                    have haux : ((Γ :: ⟨x, pΓ.1⟩).substπG (Δ :: ⟨x, pΔ.1⟩) aauux1).equal
                      ((Γ.substπG Δ h).extended pΓ.1 pΔ.1 x.2) := by
                      unfold Ctx.Subst.equal
                      use rfl
                      use rfl
                      intro y
                      unfold Ctx.substπG
                      unfold Ctx.Subst.extended
                      simp
                      by_cases h : y = x
                      simp [h]
                      rw [h]
                      simp [h]
                    let aauux2 := congr_intrpIn_subst M φ
                      ((Γ :: ⟨x, pΓ.1⟩).substπG (Δ :: ⟨x, pΔ.1⟩) aauux1)
                      ((Γ.substπG Δ h).extended pΓ.1 pΔ.1 x.2) haux pΓ.2
                    rw [<- aauux2, hφ]
  | rel R ts => intros Γ Δ pΓ pΔ h
                unfold Ctx.Subst.formula
                rw [intrpIn,intrpIn]
                have aux : ∀ i, Δ ⊢ (ts i) [Γ.substπG Δ h] (pΓ i) := by
                  intro i
                  exact ((Γ.substπG Δ h).term_inCtx (pΓ i))
                have : (fun i ↦ (ts i).intrpIn M (pΔ i)) =
                  (fun i ↦ ((ts i) [Γ.substπG Δ h] (pΓ i)).intrpIn M (aux i)) := by
                  funext i
                  rw [<- (ts i).intrpIn_extended_ctx M _ (pΓ i) (pΔ i) h]
                rw [this]

/-- This is a semantical version of lemma `intrpIn_extended_ctx` which relationship is made
via `MonoOver.pullback ((Γ.substπG Δ h).intrpIn M))` functor. -/
lemma substitution_substπG : ∀ {φ : σ.Formula} {Γ Δ : σ.Ctx} (pΓ : Γ ⊢ φ) (pΔ : Δ ⊢ φ)
  (h : Γ.ctx ⊆ Δ.ctx), Nonempty ((MonoOver.pullback ((Γ.substπG Δ h).intrpIn M)).obj
  (φ.intrpIn M pΓ) ≅ φ.intrpIn M pΔ) := by
  intros φ Γ Δ pΓ pΔ h
  let aux2 := φ.intrpIn_extended_ctx M Γ Δ pΓ pΔ h
  rw [aux2]
  let γ := Γ.substπG Δ h
  let aux3 := substitution M φ pΓ γ
  exact aux3

/-- Let `φ` be a formula in both context `Γ` and `(Γ::⟨y,q⟩)`. Then the interpretation of `φ` in
context `Γ` is related to the interpretation of `φ` in context `(Γ::⟨y,q⟩)` via the projection
substitution. -/
lemma intrpIn_extended_ctx_substπ : ∀ {φ : σ.Formula} {Γ : σ.Ctx} (p : Γ ⊢ φ) (y : σ.Base × σ.Sorts)
  (q : y.1 ∉ Γ.Label) (h : (Γ::⟨y,q⟩) ⊢ φ),  (φ.intrpIn M h = (φ[Γ.substπ y q] p).intrpIn M
  ((Γ.substπ y q).formula_inCtx p)) := by
  intros φ Γ p y q h1
  unfold Ctx.substπ
  have : Γ.ctx ⊆ (Γ :: ⟨y, q⟩).ctx := by
    unfold Ctx.extended; simp
  exact φ.intrpIn_extended_ctx M Γ (Γ::⟨y,q⟩) p h1 this

/-- This lemmas gives us a formula for the interpretaion of `⋀' lf` where `lf` is a list of
formulas. -/
lemma intrpIn_finConj : ∀ (lf : List σ.Formula) (Γ : σ.Ctx) (h : Γ ⊢ ⋀' lf)
  (j : Fin lf.length), ∃ (f : (intrpIn M (⋀'lf) h).obj.left ⟶ ((lf.get j).intrpIn M
  ((ctx_finConj h) j)).obj.left) , ((⋀' lf).intrpIn M h).arrow = f ≫ ((lf.get j).intrpIn M
  ((ctx_finConj h) j)).arrow := by
  intro lf
  induction lf with
  | nil => intros Γ h j
           exfalso
           exact j.elim0
  | cons φ tail ih => intros Γ h j
                      have aux2 : (intrpIn M (⋀'φ :: tail) h) =
                        (φ ∧' (⋀' tail)).intrpIn M h := by congr
                      rw [aux2, intrpIn]
                      specialize ih Γ h.2
                      by_cases hj : j.val = 0
                      have aux3 : (φ :: tail).get j = φ := by simp [hj]
                      have aux4 : ((φ :: tail).get j).intrpIn M (ctx_finConj h j) =
                        φ.intrpIn M h.1 := by congr
                      rw [aux4]
                      use pullback.snd ((⋀' tail).intrpIn M h.2).arrow (φ.intrpIn M h.1).arrow
                      rfl
                      have aux5 : j.val - 1 < tail.length := by
                        refine Nat.sub_lt_left_of_lt_add (Nat.pos_of_ne_zero hj) ?_
                        rw [add_comm]
                        exact j.2
                      specialize ih ⟨(j.val -1), aux5⟩
                      have aux6 : (φ :: tail).get j = tail.get ⟨(j.val -1), aux5⟩ := by
                        have : ∃ k, j.val = k + 1 := Nat.exists_eq_succ_of_ne_zero hj
                        rcases this with ⟨k, hk⟩
                        have : j = ⟨k + 1, by rw [← hk]; exact j.2⟩ := by
                          ext; simp [hk]
                        simp [this]
                      let aux7 : Γ ⊢ tail.get ⟨(j.val -1), aux5⟩ := ctx_finConj h.2 ⟨j.val-1, aux5⟩
                      have aux8 : ((φ :: tail).get j).intrpIn M (ctx_finConj h j) =
                        (tail.get ⟨(j.val -1), aux5⟩).intrpIn M aux7 := by congr
                      rw [aux8]
                      rcases ih with ⟨f', pf'⟩
                      use pullback.fst ((⋀' tail).intrpIn M h.2).arrow (φ.intrpIn M h.1).arrow ≫ f'
                      rw [assoc, <- pf', pullback.condition]
                      rfl

end Formula

/-- The defines the satisfiability relation between a seqeunt `σ` and a σ-structures `M` over a
category `C`. This is usually denoted by `M ⊧ φ` in the litrature. -/
def Sequent.IsSatisfiedIn (seq : σ.Sequent) : Prop :=
  Nonempty (seq.left.intrpIn M seq.isFormula_left ⟶ seq.right.intrpIn M seq.isFormula_right)

/-- This defines the notion of a model of a theory. Given a σ-structures `M` and a theory `𝕋`, we
say `M` is a model of `𝕋` if `M` satisfies all sequent in `𝕋`. This is usually denoted
by `M ⊧ 𝕋` in the litrature. -/
def Str.IsModelOf (𝕋 : σ.Theory) : Prop := ∀ seq ∈ 𝕋.axioms, seq.IsSatisfiedIn M

open Sequent Formula

variable (𝕋 : σ.Theory)

/-- Let `φ` and `ψ` be two formulas in a context `Γ`, and `𝕋` be a theory such that there is a term
of type `𝕋.Proof Γ φ ψ`. Then all models `M` of the theory `𝕋` satisifes the
sequent `Sequent.mk Γ φ ψ hφ hψ`.-/
theorem provable_sequent_isSatisfied : ∀ {Γ : σ.Ctx} {φ ψ : σ.Formula} (_ : 𝕋.Proof Γ φ ψ)
  (hφ : Γ ⊢ φ) (hψ : Γ ⊢ ψ) (_ : M.IsModelOf 𝕋), (Sequent.mk Γ φ ψ hφ hψ).IsSatisfiedIn M := by
  intros Γ φ ψ π
  induction π with
  | ax seq hseq=> intros hφ hψ m
                  unfold Str.IsModelOf at m
                  specialize m seq hseq
                  exact m
  | id Γ φ => unfold IsSatisfiedIn
              intros hφ hψ m
              exact ⟨𝟙 (φ.intrpIn M hφ)⟩
  | subst γ hπ p q IH => unfold IsSatisfiedIn
                         intro hφ hψ m
                         specialize IH p q
                         unfold IsSatisfiedIn at IH
                         specialize IH m
                         rcases IH with ⟨f⟩
                         have ⟨fψ⟩ := substitution M _ q γ
                         have ⟨fφ⟩ := substitution M _ p γ
                         exact ⟨fφ.inv ≫ ((MonoOver.pullback (γ.intrpIn M)).map f) ≫ fψ.hom⟩
  | cut Γ φ ψ χ hψ π1 π2 IH1 IH2 => intros hφ hχ m
                                    specialize IH1 hφ hψ
                                    specialize IH2 hψ hχ
                                    unfold IsSatisfiedIn at IH1 IH2
                                    specialize IH1 m
                                    specialize IH2 m
                                    rcases IH1 with ⟨u1⟩
                                    rcases IH2 with ⟨u2⟩
                                    unfold IsSatisfiedIn
                                    exact ⟨u1 ≫ u2⟩
  | top Γ φ => intros hφ hψ m
               unfold IsSatisfiedIn
               rw [intrpIn]
               exact ⟨MonoOver.leTop (φ.intrpIn M hφ)⟩
  | conjElimLeft Γ φ ψ => intros hφ hψ m
                          unfold IsSatisfiedIn
                          rw [intrpIn]
                          exact ⟨MonoOver.infLELeft (φ.intrpIn M hψ) (ψ.intrpIn M hφ.2)⟩
  | conjElimRight Γ φ ψ => intros hφ hψ m
                           unfold IsSatisfiedIn
                           rw [intrpIn]
                           exact ⟨MonoOver.infLERight (φ.intrpIn M hφ.1) (ψ.intrpIn M hψ)⟩
  | conjIntro Γ φ ψ χ hπ1 hπ2 IH1 IH2 => intros hφ hφψ m
                                         unfold IsSatisfiedIn
                                         rw [intrpIn]
                                         specialize IH1 hφ hφψ.1
                                         specialize IH2 hφ hφψ.2
                                         unfold IsSatisfiedIn at IH1 IH2
                                         specialize IH1 m
                                         specialize IH2 m
                                         rcases IH1 with ⟨f1⟩
                                         rcases IH2 with ⟨f2⟩
                                         let f := ψ.intrpIn M hφψ.1
                                         let g := χ.intrpIn M hφψ.2
                                         let h := φ.intrpIn M hφ
                                         exact ⟨MonoOver.leInf f g h f1 f2⟩
  | bot Γ φ => intros hφ hψ m
               unfold IsSatisfiedIn
               rw [intrpIn]
               let φ' := φ.intrpIn M hψ
               exact ⟨initial.to φ'⟩
  | infDisjIntro Γ I fs i => intros hφ hψ m
                             unfold IsSatisfiedIn
                             rw [intrpIn]
                             exact ⟨Sigma.ι (fun i ↦ (fs i).intrpIn M (hψ.1 i)) i⟩
  | disL Γ I fs φ hπ IH => intros hφ hψ m
                           unfold IsSatisfiedIn
                           rw [intrpIn]
                           let φ' := φ.intrpIn M hψ
                           have auxh1 : ∀ i, Nonempty ((fs i).intrpIn M (hφ.1 i) ⟶ φ') := by
                            intro i
                            specialize IH i (hφ.1 i) hψ
                            unfold IsSatisfiedIn at IH
                            specialize IH m
                            rcases IH with ⟨IH⟩
                            exact ⟨IH⟩
                           exact ⟨Sigma.desc (fun i ↦ Classical.choice (auxh1 i))⟩
  | existIntro Γ y p φ ψ hψΓ hπ IH => intros hφ hψ m
                                      unfold IsSatisfiedIn
                                      rw [intrpIn]
                                      let adj := MonoOver.existsPullbackAdj
                                        ((Γ.substπ y p).intrpIn M)
                                      let X := φ.intrpIn M (hφ.2)
                                      let Y := ψ.intrpIn M hψ
                                      specialize IH (hφ.2) hψΓ
                                      unfold IsSatisfiedIn at IH
                                      specialize IH m
                                      rcases IH with ⟨fIH⟩
                                      have auxh2 : Nonempty (ψ.intrpIn M hψΓ ≅
                                        (MonoOver.pullback ((Γ.substπ y p).intrpIn M)).obj Y) := by
                                        have ⟨α⟩ := ψ.substitution M hψ (Γ.substπ y p)
                                        let aux := intrpIn_extended_ctx_substπ  M hψ y p hψΓ
                                        rw [<- aux] at α
                                        exact ⟨α.symm⟩
                                      rcases auxh2 with ⟨auxh2⟩
                                      exact ⟨(Adjunction.homEquiv adj X Y).invFun (fIH ≫ auxh2.hom)⟩
  | existElim Γ y p φ ψ hψΓ hπ IH => intros hφ hψ m
                                     unfold IsSatisfiedIn
                                     let adj := MonoOver.existsPullbackAdj ((Γ.substπ y p).intrpIn M)
                                     let X := φ.intrpIn M hφ
                                     let Y := ψ.intrpIn M hψΓ
                                     specialize IH ⟨p,hφ⟩ hψΓ
                                     unfold IsSatisfiedIn at IH
                                     specialize IH m
                                     rcases IH with ⟨fIH⟩
                                     rw [intrpIn] at fIH
                                     have auxh2 : Nonempty (ψ.intrpIn M hψ ≅
                                         (MonoOver.pullback ((Γ.substπ y p).intrpIn M)).obj Y) := by
                                         let aux := intrpIn_extended_ctx_substπ  M hψΓ y p hψ
                                         have ⟨β⟩ := ψ.substitution M hψΓ (Γ.substπ y p)
                                         rw [<- aux] at β
                                         exact ⟨β.symm⟩
                                     rcases auxh2 with ⟨auxh2⟩
                                     exact ⟨(Adjunction.homEquiv adj X Y).toFun fIH ≫ auxh2.inv⟩
  | distributive Γ φ I fs => intros hφ hψ m
                             unfold IsSatisfiedIn
                             let f := φ.intrpIn M hφ.1
                             let lm := fun i ↦ (fs i).intrpIn M (hφ.2.1 i)
                             let ⟨dist⟩ := Observable.distributivity C f lm
                             exact ⟨dist.hom⟩
  | frobenius Γ φ x ψ => intros hφ hψ m
                         unfold IsSatisfiedIn
                         rw [intrpIn,intrpIn,intrpIn,intrpIn]
                         let f := (Γ.substπ x hφ.2.1).intrpIn M
                         let g := ψ.intrpIn M hφ.2.2
                         let h := φ.intrpIn M hφ.1
                         let ⟨com⟩ := Regular.frobenius_reciprocity C f h.arrow
                         have : Nonempty (φ.intrpIn M hψ.2.1 ≅ (MonoOver.pullback f).obj h) := by
                          rw [intrpIn_extended_ctx_substπ  M hφ.1 x hψ.1 hψ.2.1]
                          let ⟨mor⟩ := φ.substitution M hφ.1 (Γ.substπ x hφ.2.1)
                          exact ⟨Iso.symm mor⟩
                         have aux2 : Nonempty ((MonoOver.exists f).obj
                          ((MonoOver.inf.obj ((MonoOver.pullback f).obj h)).obj g) ≅
                            (MonoOver.exists f).obj
                            ((MonoOver.inf.obj (φ.intrpIn M hψ.2.1)).obj g)) := by
                          let ⟨i⟩ := this
                          have inf_iso : MonoOver.inf.obj ((MonoOver.pullback f).obj h) ≅
                            MonoOver.inf.obj (φ.intrpIn M hψ.2.1) := by
                            exact (MonoOver.inf.mapIso i).symm
                          have inf_iso_obj : (MonoOver.inf.obj ((MonoOver.pullback f).obj h)).obj
                            g ≅ (MonoOver.inf.obj (φ.intrpIn M hψ.2.1)).obj g := by
                            exact inf_iso.app g
                          exact ⟨(MonoOver.exists f).mapIso inf_iso_obj⟩
                         rcases aux2 with ⟨aux2⟩
                         exact ⟨(Iso.trans (com.app g) aux2).hom⟩
  | substOfEq Γ₁ Γ₂ Δ ρ φ p h1 h2 => intros hφ hψ m
                                     unfold IsSatisfiedIn
                                     simp
                                     let gg := φ.substitution M p ρ.substOfRenaming
                                     apply Classical.choice at gg
                                     apply Nonempty.intro
                                     let kk2 := (φ [ρ.substOfRenaming] p).substitution_substπG M
                                      (ρ.substOfRenaming.formula_inCtx p) hψ h2
                                     apply Classical.choice at kk2
                                     let aux44 := φ.substitution_substπG M p hφ.2 h1
                                     apply Classical.choice at aux44
                                     let hh2 := (MonoOver.pullback
                                      ((Γ₂.substπG Δ h2).intrpIn M)).mapIso gg
                                     rw [intrpIn]
                                     let gg2 := hh2.trans kk2
                                     refine ?_ ≫ gg2.hom
                                     refine MonoOver.homMk ?_ ?_
                                     let ll := pullbackLeftPullbackSndIso (φ.intrpIn M p).arrow
                                      (ρ.substOfRenaming.intrpIn M) ((Γ₂.substπG Δ h2).intrpIn M)
                                     simp
                                     refine ?_ ≫ ll.inv
                                     refine pullback.lift ?_ ?_ ?_
                                     exact pullback.fst (φ.intrpIn M hφ.2).arrow
                                      (((⋀'ρ.listEq)).intrpIn M hφ.1).arrow ≫ aux44.inv.left ≫
                                      pullback.fst (φ.intrpIn M p).arrow
                                      ((Γ₁.substπG Δ h1).intrpIn M)
                                     exact (pullback.snd (φ.intrpIn M hφ.2).arrow
                                      ((⋀' ρ.listEq).intrpIn M hφ.1).arrow) ≫
                                      (((⋀'ρ.listEq)).intrpIn M hφ.1).arrow
                                     simp
                                     rw [pullback.condition (f := (intrpIn M φ p).arrow)
                                      (g := (Ctx.Subst.intrpIn M (Γ₁.substπG Δ h1)))]
                                     have l1 : aux44.inv.left ≫ pullback.snd (intrpIn M φ p).arrow
                                      (Ctx.Subst.intrpIn M (Γ₁.substπG Δ h1)) =
                                      (intrpIn M φ hφ.2).arrow := Over.w aux44.inv
                                     rw [<- assoc (aux44.inv.left)
                                      (pullback.snd (intrpIn M φ p).arrow
                                      (Ctx.Subst.intrpIn M (Γ₁.substπG Δ h1)))
                                      (Ctx.Subst.intrpIn M (Γ₁.substπG Δ h1)), l1, <- assoc]
                                     rw [pullback.condition (f := (φ.intrpIn M hφ.2).arrow)
                                      (g := ((⋀'ρ.listEq).intrpIn M hφ.1).arrow), assoc]
                                     apply whisker_eq
                                     apply Limits.Pi.hom_ext
                                     intro bΓ1
                                     rw [substπG_is_ctxProj, substπG_is_ctxProj]
                                     rw [Ctx.ctxProj, Ctx.ctxProj, assoc, Pi.lift_π]
                                     rw [Ctx.Subst.intrpIn, assoc, assoc, Pi.lift_π]
                                     have l2 : ρ.substOfRenaming.map bΓ1 =
                                      Term.var ((ρ.map bΓ1).1.1, bΓ1.1.2) := by
                                      rw [Ctx.Renaming.substOfRenaming]
                                     let l3 : Γ₂ ⊢ Term.var ((ρ.map bΓ1).1.1, bΓ1.1.2) :=
                                      (ρ.substOfRenaming).inCtx_map bΓ1
                                     rw [Term.congr_intrpIn M l2
                                      (ρ.substOfRenaming.inCtx_map bΓ1) l3, Term.intrpIn]
                                     rw [Ctx.intrpInπ, Ctx.intrpInπ, Pi.lift_π, <- Ctx.intrpInπ]
                                     rw [<- Term.intrpIn, <- Term.intrpIn]
                                     have fi := ρ.getIndex_listEq bΓ1
                                     let l4 : Δ ⊢ .var bΓ1.1 ≃ .var ⟨(ρ.map bΓ1).1.1, bΓ1.1.2⟩ :
                                      bΓ1.1.2 := by
                                      unfold Formula.InCtx
                                      constructor
                                      exact Set.mem_of_mem_of_subset bΓ1.2 h1
                                      unfold Term.InCtx
                                      exact Set.mem_of_mem_of_subset
                                        (ρ.substOfRenaming.inCtx_map bΓ1)  h2
                                     rcases fi with ⟨fi1,fi2⟩
                                     let auxf := intrpIn_finConj M ρ.listEq Δ hφ.1 fi1
                                     rcases auxf with ⟨auxf1, auxf2⟩
                                     rw [auxf2, assoc, assoc]
                                     apply whisker_eq
                                     have auxf2 : (ρ.listEq.get fi1).intrpIn M
                                      (ctx_finConj hφ.left fi1) =
                                      (.var bΓ1.1 ≃ .var ⟨(ρ.map bΓ1).1.1, bΓ1.1.2⟩ :
                                      bΓ1.1.2).intrpIn M l4 := by congr
                                     rw [auxf2, intrpIn]
                                     simp
                                     rw [equalizer.condition]
                                     simp

/-- The main theorem of this file which shows all provable sequent in a theory `𝕋` are
satisfied in any model `M` of `𝕋`. In another words, our system will not prove "wrong" statements.-/
theorem soundness : ∀ (seq : σ.Sequent), M.IsModelOf 𝕋 → 𝕋.Provable seq → seq.IsSatisfiedIn M := by
  intros seq m h
  rcases h with ⟨π⟩
  unfold IsSatisfiedIn
  apply  provable_sequent_isSatisfied
  exact π
  exact m

end Interpretation

end Signature
