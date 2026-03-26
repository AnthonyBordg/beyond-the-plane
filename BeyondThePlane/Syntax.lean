/-
Copyright (c) 2025 Lagrange Mathematics and Computing Research Center. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Bordg, Farzad Jafarrahmani
-/
import Mathlib.Data.Finset.Image
import Mathlib.Order.SetNotation
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin


/-!
# Observable logic

This file defines observable logic.

## Main results

* `Signature`: first-order signatures
* `Signature.Term`: the collection of terms over a signature
* `Signature.Formula`: the class of observable formulae over a signature
* `Signature.Context`: contexts, we will often consider terms and formulae in contexts
* `Signature.Context.Subst`: the operation of substituting variables from a given context with terms
in a possibly different context
* `Signature.Ctx.Subst.term`: the operation of substituting variables of a term with terms according
to a given substitution
* `Signature.Ctx.Subst.term_inCtx`: A substitution from context `Γ` to context `Δ`
maps terms-in-context `Γ` to terms-in-context `Δ`.
* `Signature.Ctx.Subst.formula`: the operation of substituting variables of a formula with terms
according to a given substitution
* `Signature.Ctx.Subst.formula_inCtx`: A substitution from a context `Γ` to a context `Δ`
maps formulae-in-context `Γ` to formulae-in-context `Δ`.
* `Signature.Ctx.Renaming`: the operation of renaming variables of a given context
* `Signature.Ctx.Renaming.substOfRenaming`: the substitution associated with a renaming,
i.e. renaming is a particular case of substitution where the terms are variables
* `Signature.Context.Proof`: the deduction system for observable logic
* `Signature.Sequent`: sequents in observable logic
* `Signature.Sequent.Theory`: observable theories over a signature

## Notations

* `Γ ⊢ t` means that every variable of the term `t` occurs in the context `Γ`
(see `Signature.Ctx.Var_subset_ctx_of_inCtx`).
* `Γ ⊢ φ` means that every free variable of the formula `φ` occurs in the context `Γ` (see
`Signature.Ctx.freeVar_subset_ctx_of_InCtx`).
* `Γ :: x` denotes the context `Γ` extended with a new variable `x`.
* `t [γ] p` denotes the term resulting from substituting the variables of term `t` according to the
substitution `γ` (see `Signature.Ctx.Subst.term`).
* `φ [γ] p` denotes the formula resulting from substituting the variables of formula `φ` with
the corresponding terms of substitution `γ` (see `Signature.Ctx.Subst.formula`).

## References

* [P. Johnstone, *Sketches of an Elephant: A Topos Theory Compendium, Volume 2*][Elephant]

## Tags

first-order logic, observable logic, observable theory, syntax à la Church
-/

universe u v w w' w''

/-! First-order signatures -/

/-- A first-order signature consists mainly of a type of sorts, a type of function symbols and a
type of relation symbols. -/
structure Signature where
  /- A base type for labels -/
  Base : Type w'
  /- A type for the indexing set of infinite disjunction of formulae -/
  Index : Type w''
  /- Two indices for handling syntactic sugar for binary disjunctions -/
  leftIndex : Index
  rightIndex : Index
  /-- A type of sorts -/
  Sorts : Type u
  /- For every finite set of variables, i.e. a pair made of a label and a sort, we can select a
  label that does not belong to this set -/
  newLabel : (X : Finset (Base × Sorts)) → {x : Base | ∀ v, v ∈ X → x ≠ v.1}
  /-- A type of function symbols -/
  Fun : Type v
  /-- A type of relation symbols -/
  Rel : Type w
  /-- Each function symbol is equipped with a list of source sorts and a single output sort. -/
  rankF : Fun → List Sorts × Sorts
  /-- Each relation symbol is equipped with a list of sorts. -/
  rankR : Rel → List Sorts

namespace Signature

variable (σ : Signature.{u,v,w,w',w''})

/-! Terms, formulae and contexts over a signature -/

/-- The type `Signature.Term` of terms over `σ` is defined inductively, a term being either a
variable or a function symbol applied to previous terms. -/
inductive Term : σ.Sorts → Type max u v w'
  | var (x : σ.Base × σ.Sorts) : Term x.2
  | app f (arg : (i : Fin (σ.rankF f).1.length) → Term ((σ.rankF f).1.get i)) : Term (σ.rankF f).2

notation:100 f "(" ts ")" => Term.app f ts

/-- We define the class of observable formulae as the inductive type `Signature.Formula`. -/
inductive Formula : Type _
  | truth : Formula
  | falsum : Formula
  | equal s : σ.Term s → σ.Term s → Formula
  | binConj : Formula → Formula → Formula
  | infDisj : (I : Set σ.Index) → (I → Formula) → Formula
  | exist : σ.Base × σ.Sorts → Formula → Formula
  | rel R (arg : (i : Fin (σ.rankR R).length) → σ.Term ((σ.rankR R).get i)) : Formula

notation:100 "⊤" => Formula.truth
notation:100 "⊥" => Formula.falsum
notation:110 t " ≃ " u:110 " : " s:110  => Formula.equal s t u
infix:120 " ∧' " => Formula.binConj
notation:120 "⋁ " I ", " fs => Formula.infDisj I fs
notation:110 "(∃' " x:110 " ) " φ:110 => Formula.exist x φ


namespace Formula

variable {σ : Signature.{u,v,w,w',w''}}

section binDisj

variable [DecidableEq σ.Index]

def binDisj (φ ψ : σ.Formula) : σ.Formula :=
  infDisj {σ.leftIndex, σ.rightIndex} (fun k => if k = σ.leftIndex then φ else ψ)

infix:120 " ∨' " => Formula.binDisj

end binDisj

section Exist2

def exist2 (x y : σ.Base × σ.Sorts) (φ : σ.Formula) : σ.Formula := (∃' x) (∃' y) φ

notation:110 "(∃' " x:110  "," y:110 " ) " φ:110 => Formula.exist2 x y φ

def exist2EqSort (x y : σ.Base) (s : σ.Sorts) (φ : σ.Formula) : σ.Formula := (∃'⟨x, s⟩) (∃'⟨y, s⟩) φ

notation:110 "(∃' " x:110 " , " y:110 " : " s:110 " ) " φ:110 => Formula.exist2EqSort x y s φ

end Exist2

section Existn

variable [DecidableEq σ.Base] [DecidableEq (σ.Base × σ.Sorts)]

noncomputable def existn (ctx : List (σ.Base × σ.Sorts)) (φ : σ.Formula) : σ.Formula :=
  match ctx with
  | [] => φ
  | List.cons x fs => existn (fs) ((∃' x) φ)

notation:110 "(∃ⁿ" ctx:110 " ) " φ:110 => Formula.existn ctx φ

end Existn

end Formula


/-- A context is a list of distinct variables. -/
structure Ctx where
  /-- The underlying finite set of sorted labels, to model the aforementioned list of distinct
  variables. -/
  ctx : Finset (σ.Base × σ.Sorts)
  /-- The labels in a context are distinct. -/
  single_sort : ∀ x y, x ∈ ctx → y ∈ ctx → x.1 = y.1 → x.2 = y.2

variable {σ : Signature.{u,v,w,w',w''}}

variable [DecidableEq σ.Base] [DecidableEq (σ.Base × σ.Sorts)]

namespace Ctx

variable (Γ : σ.Ctx)

/-- The finite set of labels of a given context -/
def Label : Finset σ.Base := Γ.ctx.image (fun x => x.1)

open Finset

/-- `Γ.extended y` is the context `Γ` extended with a new label `y.1` together with its sort `y.2`.
-/
def extended (y : σ.Base × σ.Sorts) (p : y.1 ∉ Γ.Label) : σ.Ctx where
  ctx := insert y Γ.ctx
  single_sort x x' p q eq := by
    rw [mem_insert] at p q
    rcases p with pxy |px <;> rcases q with  qx'y | qx'
    · rw [pxy, qx'y]
    · have : y.1 ∈ Γ.Label := by
        rw [← pxy, eq]
        exact mem_image_of_mem _ qx'
      exfalso
      exact p this
    · have : y.1 ∈ Γ.Label := by
        rw [← qx'y, eq.symm]
        exact mem_image_of_mem _ px
      exfalso
      exact p this
    · exact Γ.single_sort x x' px qx' eq

notation:110 Γ " ::" " ⟨" y:110 ", " p:110 "⟩" => extended Γ y p


/- sum (coproduct) of two disjoint contexts -/
def sum (Δ : σ.Ctx) (h : Disjoint Γ.Label Δ.Label) : σ.Ctx where
  ctx := Γ.ctx ∪ Δ.ctx
  single_sort x x' p q eq := by
    rw [mem_union] at p
    rw [mem_union] at q
    by_cases hx : x ∈ Γ.ctx
    by_cases hx' : x' ∈ Γ.ctx
    exact Γ.single_sort x x' hx hx' eq
    have auxh := Or.resolve_left q hx'
    have aux1 : x'.1 ∈ Δ.Label := by
      unfold Label
      simp
      use x'.2
    have aux2 : x.1 ∈ Γ.Label := by
      unfold Label
      simp
      use x.2
    rw [disjoint_iff_inter_eq_empty] at h
    have aux3 : (Γ.Label ∩ Δ.Label).Nonempty := by
      rw [nonempty_iff_ne_empty]
      by_contra hc
      rw [<- eq] at aux1
      have cont := mem_inter.mpr ⟨aux2,aux1⟩
      have hx_inter : x.1 ∈ (Γ.Label ∩ Δ.Label) := Finset.mem_inter.mpr ⟨aux2,aux1⟩
      rw [hc] at hx_inter
      have aux := notMem_empty x.1
      contradiction
    rw [h] at aux3
    obtain ⟨z,hz⟩ := aux3
    have auxh3 := notMem_empty z hz
    contradiction
    have auxh := Or.resolve_left p hx
    by_cases hx' : x' ∈ Γ.ctx
    have aux1 : x.1 ∈ Δ.Label := by
      unfold Label
      simp
      use x.2
    have aux2 : x'.1 ∈ Γ.Label := by
      unfold Label
      simp
      use x'.2
    rw [<- eq] at aux2
    have aux3 : (Γ.Label ∩ Δ.Label).Nonempty := by
      rw [nonempty_iff_ne_empty]
      by_contra hc
      have cont := mem_inter.mpr ⟨aux2,aux1⟩
      have hx_inter : x.1 ∈ (Γ.Label ∩ Δ.Label) := Finset.mem_inter.mpr ⟨aux2,aux1⟩
      rw [hc] at hx_inter
      have aux := notMem_empty x.1
      contradiction
    rw [disjoint_iff_inter_eq_empty] at h
    rw [h] at aux3
    obtain ⟨z,hz⟩ := aux3
    have auxh3 := notMem_empty z hz
    contradiction
    have auxh' := Or.resolve_left q hx'
    exact (Δ.single_sort x x' auxh auxh' eq)

/-- sum of context with a singleton contex. -/
def extendedsing (y : σ.Base × σ.Sorts) (p : y.1 ∉ Γ.Label) := Γ.sum (Ctx.mk {y} (by simp))
    (by simp [Label]; intro hx; by_contra hc
        have : y.1 ∈ Γ.Label := by unfold Label; simp; use hx
        contradiction)

/-- Both defeinitions of extended and extendedsing conincide. -/
lemma extendedsing_is_extended (y : σ.Base × σ.Sorts) (p : y.1 ∉ Γ.Label) :
  Γ.sum (Ctx.mk {y} (by simp))
    (by unfold Label
        simp
        intro hx
        by_contra hc
        have : y.1 ∈ Γ.Label := by unfold Label; simp; use hx
        contradiction) = Γ.extended y p := by
  unfold extended
  unfold sum
  simp

/-- extensoin of context with two fresh variables is a commutative opertaion.-/
lemma extended_commute (x y : σ.Base × σ.Sorts) (py : y.1 ∉ Γ.Label) (px : x.1 ∉ Γ.Label)
  (qy : y.1 ∉ (Γ::⟨x,px⟩).Label) (qx : x.1 ∉ (Γ::⟨y,py⟩).Label) :
    (Γ::⟨y,py⟩)::⟨x,qx⟩ = (Γ::⟨x,px⟩)::⟨y,qy⟩ := by
    unfold Ctx.extended
    simp
    exact Finset.insert_comm x y Γ.ctx

omit [DecidableEq (σ.Base × σ.Sorts)] in
lemma notin_ctx_of_notin_label {x : σ.Base × σ.Sorts} (h : x.1 ∉ Γ.Label) : x ∉ Γ.ctx := by
  by_contra hc
  have : x.1 ∈ Γ.Label := mem_image_of_mem _ hc
  exact h this

end Ctx

namespace Term

/-- The proposition `Γ.InCtx t` basically asserts that the variables of the term `t` belong to Γ.
This allows us to consider terms-in-context.-/
def InCtx (Γ : σ.Ctx) {s : σ.Sorts} (t : σ.Term s) : Prop :=
  match t with
  | var x => x ∈ Γ.ctx
  | app f ts => ∀ (i : Fin (σ.rankF f).1.length), (ts i).InCtx Γ

notation:80 Γ " ⊢ " t:90 => InCtx Γ t

/-- `Var t` is the set of variables occuring in the term `t`. -/
def Var {s : σ.Sorts} : σ.Term s → Set (σ.Base × σ.Sorts)
  | var x => {x}
  | app f ts => ⋃ (i : Fin (σ.rankF f).1.length), (ts i).Var

omit [DecidableEq σ.Base] [DecidableEq (σ.Base × σ.Sorts)]
lemma weakening (Γ Δ : σ.Ctx) {s : σ.Sorts} (t : σ.Term s) (h : Γ.ctx ⊆ Δ.ctx) (p : Γ ⊢ t) :
  Δ ⊢ t := by
  induction t with
  | var x => unfold InCtx at p
             unfold InCtx
             exact Set.mem_of_mem_of_subset p h
  | app f ts hts => unfold InCtx
                    unfold InCtx at p
                    intro i
                    specialize p i
                    exact hts i p

end Term

namespace Formula

/-- `freeVar φ` is the set of free variables occuring in the formula `φ`. -/
def freeVar : σ.Formula → Set (σ.Base × σ.Sorts)
  | ⊤ => ∅
  | ⊥ => ∅
  | t ≃ u : _ => t.Var ∪ u.Var
  | φ ∧' ψ => φ.freeVar ∪ ψ.freeVar
  | ⋁ I, fs => ⋃ (i : I), (fs i).freeVar
  | (∃'x)φ => φ.freeVar \ {x}
  | rel R ts => ⋃ (i : Fin (σ.rankR R).length), (ts i).Var

/-- `boundVar φ` is the set of bound variables occuring in the formula `φ`. -/
def boundVar : σ.Formula → Set (σ.Base × σ.Sorts)
  | ⊤ => ∅
  | ⊥ => ∅
  | _ ≃ _ : _ => ∅
  | φ ∧' ψ => φ.boundVar ∪ ψ.boundVar
  | ⋁ I, fs => ⋃ (i : I), (fs i).boundVar
  | (∃'x)φ => φ.boundVar ∪ {x}
  | rel _ _ => ∅

/-- The proposition `Γ.InCtx φ` basically asserts that the free variables of formula `φ` belong to
context `Γ`. This allows us to consider formulae-in-context. -/
def InCtx (Γ : σ.Ctx) (φ : σ.Formula) : Prop :=
  match φ with
  | ⊤ => True
  | ⊥ => True
  | t ≃ u : _ => Γ ⊢ t ∧ Γ ⊢ u
  | φ ∧' ψ => φ.InCtx Γ ∧ ψ.InCtx Γ
  | ⋁ I, fs => (∀ i : I, (fs i).InCtx Γ) ∧ (⋁ I, fs).freeVar ⊆ Γ.ctx
  | (∃'x)φ => ∃ p : x.1 ∉ Γ.Label, φ.InCtx (Γ::⟨x, p⟩)
  | .rel _ ts => ∀ i, Γ ⊢ ts i

infix:80 " ⊢ " => InCtx

end Formula

namespace Ctx

variable (Γ : σ.Ctx)

open Set Term

omit [DecidableEq σ.Base] [DecidableEq (σ.Base × σ.Sorts)] in
/-- Assuming `Γ ⊢ t`, we can conclude the variables of term `t` belong to context `Γ`. -/
theorem Var_subset_ctx_of_inCtx {s : σ.Sorts} {t : σ.Term s} (p : Γ ⊢ t) : t.Var ⊆ Γ.ctx := by
  induction t with
  | var x => unfold Var
             rw [singleton_subset_iff]
             exact p
  | app f ts hts => unfold Var
                    apply iUnion_subset
                    intro i
                    exact hts i (p i)



omit [DecidableEq σ.Base] [DecidableEq (σ.Base × σ.Sorts)] in
theorem newLabel_notin_ctx (s : σ.Sorts) : ⟨σ.newLabel Γ.ctx, s⟩ ∉ Γ.ctx := by
  by_contra hc
  have aux1: ∀ v ∈ Γ.ctx, (σ.newLabel Γ.ctx).1 ≠ v.1 := by
    intro v hv
    exact (σ.newLabel Γ.ctx).2 v hv
  have aux2 : (σ.newLabel Γ.ctx).1 = ((σ.newLabel Γ.ctx).1, s).1 := by rfl
  exact aux1 ((σ.newLabel Γ.ctx).1, s) hc aux2

omit [DecidableEq (σ.Base × σ.Sorts)] in
theorem newLabel_notin_label : (σ.newLabel Γ.ctx).1 ∉ Γ.Label := by
  by_contra hc
  unfold Label at hc
  rw [Finset.mem_image] at hc
  obtain ⟨x, p, eq⟩ := hc
  have : ⟨σ.newLabel Γ.ctx, x.2⟩ ∈ Γ.ctx := by
    rw [← eq]
    exact p
  exact Γ.newLabel_notin_ctx x.2 this

variable {Γ : σ.Ctx}

/-- The lemma `mem_of_mem_extended_neq hy hyx` asserts that a variable `y` belonging to the
extended context `Γ.extended x`, and not equal to the variable `x`, belongs to `Γ.ctx`. -/
lemma mem_of_mem_extended_neq {x y : σ.Base × σ.Sorts} {hx : x.1 ∉ Γ.Label}
    (hy : y ∈ (Γ::⟨x,hx⟩).ctx) (hyx : y ≠ x) : y ∈ Γ.ctx := by
  unfold extended at hy
  rw [Finset.mem_insert] at hy
  rcases hy with hy1 | hy2
  · exfalso
    exact hyx hy1
  · exact hy2

/-- The lemma `inCtx_extended_of_inCtx hx` asserts a term `t` in context `Γ` is also a term in every
context that extends `Γ` with a new variable `x`. -/
lemma inCtx_extended_of_inCtx {s : σ.Sorts} {t : σ.Term s} {x : σ.Base × σ.Sorts}
    (h : x.1 ∉ Γ.Label) : Γ ⊢ t → (Γ::⟨x,h⟩) ⊢ t := by
  induction t with
  | var y => intro h; exact Finset.mem_insert_of_mem h
  | app f ts hts => intro h; exact (fun i => hts i (h i))

open Formula

/-- If `Γ ⊢ φ`, then every free variable of formula `φ` occurs in context `Γ`. -/
theorem freeVar_subset_ctx_of_InCtx : ∀ {φ : σ.Formula} {Γ : σ.Ctx}, Γ ⊢ φ → φ.freeVar ⊆ Γ.ctx := by
  intro φ
  induction φ with
  | truth => intros; apply empty_subset
  | falsum => intros; apply empty_subset
  | equal s t u => intros Γ h
                   exact union_subset (Γ.Var_subset_ctx_of_inCtx h.1)
                    (Γ.Var_subset_ctx_of_inCtx h.2)
  | binConj φ ψ hφ hψ => intros Γ h; exact union_subset (hφ h.1) (hψ h.2)
  | infDisj I fs hfs => intros Γ h
                        apply iUnion_subset
                        exact fun i => hfs i (h.1 i)
  | exist x φ hφ => intros Γ h
                    unfold freeVar
                    rw [diff_singleton_subset_iff]
                    obtain ⟨p, h⟩ := h
                    specialize hφ h
                    unfold extended at hφ
                    simpa using hφ
  | rel R ts => intros Γ h
                apply iUnion_subset
                exact fun i => Γ.Var_subset_ctx_of_inCtx (h i)

/-- If `Γ ⊢ φ`, then the set of bound variables of `φ` and `Γ.ctx`are disjoint. -/
theorem boundVar_inter_ctx_empty :
    ∀ {φ : σ.Formula} {Γ : σ.Ctx}, Γ ⊢ φ → φ.boundVar ∩ Γ.ctx = ∅ := by
  intro φ
  induction φ with
  | truth => unfold boundVar; simp
  | falsum => unfold boundVar; simp
  | equal t u s => unfold boundVar; simp
  | binConj φ ψ hφ hψ => intros Γ h
                         unfold boundVar
                         rw [union_inter_distrib_right, hφ h.1, hψ h.2]
                         simp
  | infDisj I fs hfs => intros Γ h
                        rcases h with ⟨h1, h2⟩
                        unfold boundVar
                        by_contra hc
                        rw [eq_empty_iff_forall_notMem] at hc
                        push_neg at hc
                        obtain ⟨x, px⟩ := hc
                        rw [mem_inter_iff] at px
                        rcases px with ⟨px1, px2⟩
                        rw [mem_iUnion] at px1
                        obtain ⟨i, pi⟩ := px1
                        specialize h1 i
                        specialize hfs i h1
                        rw [← mem_empty_iff_false x, ← hfs]
                        exact ⟨pi, px2⟩
  | exist x φ hφ => intros Γ h
                    unfold boundVar
                    rw [union_inter_distrib_right, union_empty_iff]
                    obtain ⟨p, h⟩ := h
                    constructor
                    · specialize hφ h
                      unfold extended at hφ
                      simp only [Finset.coe_insert] at hφ
                      rw [insert_eq, inter_union_distrib_left, union_empty_iff] at hφ
                      exact hφ.2
                    · rw [singleton_inter_eq_empty]
                      exact Γ.notin_ctx_of_notin_label p
  | rel R ts => unfold boundVar; simp


/-! Substitution -/

/- A substitution `Subst Γ Δ` between two contexts `Γ` and `Δ` is an assignment of each variable `x`
of `Γ` to a term of the corresponding sort in context `Δ`. -/
structure Subst (Γ Δ : σ.Ctx) where
  /- A mapping of each variable `x` of `Γ.ctx` to a term `map x` of the same sort -/
  map : (x : Γ.ctx) → σ.Term x.1.2
  /- such that `Δ ⊢ map x -/
  inCtx_map x : Δ ⊢ map x

/- `Γ.substπG Δ` is the projection substitution from `Δ` to `Γ` -/
def substπG (Γ Δ : σ.Ctx) (h : Γ.ctx ⊆ Δ.ctx) :
  Γ.Subst Δ where
  map x := var x.1
  inCtx_map x := by
    unfold Term.InCtx
    apply mem_of_mem_of_subset x.2 h

/- `Γ.substπ y` is the projection substitution from `Γ::⟨y,p⟩` to `Γ` -/
def substπ (Γ : σ.Ctx) (y : σ.Base × σ.Sorts) (p : y.1 ∉ Γ.Label) :=
  Γ.substπG (Γ::⟨y, p⟩) (by unfold extended; simp)

namespace Subst

variable {Γ Δ : σ.Ctx} (γ : Γ.Subst Δ)

def equal2 {Γ' Δ' : σ.Ctx} (γ : Γ.Subst Δ) (γ' : Γ'.Subst Δ') : Prop :=
  ∃ (h1 : Γ = Γ') (_ : Δ = Δ'), γ.map = h1 ▸ γ'.map

def equal {Γ' Δ' : σ.Ctx} (γ : Γ.Subst Δ) (γ' : Γ'.Subst Δ') : Prop :=
  ∃ (h1 : Γ = Γ') (_ : Δ = Δ'), ∀ (x : Γ.ctx), γ.map x = γ'.map (⟨x.1, h1 ▸ x.2⟩)

/- `γ.term t` is the term resulting from substituting the variables of the term `t` with some terms
according to the substitution `γ`. -/
def term {s : σ.Sorts} (t : σ.Term s) (p : Γ ⊢ t) : σ.Term s :=
  match t with
  | .var x => γ.map ⟨x, p⟩
  | .app f ts => f (fun i => term (ts i) (p i))

notation:101 t " [" γ "] " p => term γ t p

/- Given a term `t`, we will have the same term `t` after the projection substitution -/
lemma substπ_preserve_term {s : σ.Sorts} (Γ : σ.Ctx) (y : σ.Base × σ.Sorts) (p : y.1 ∉ Γ.Label)
  (t : σ.Term s) (h : Γ ⊢ t) : (t [Γ.substπ y p] h) = t := by
  induction t with
  | var x => unfold substπ
             unfold substπG
             unfold term
             simp
  | app f arg ih => unfold substπ
                    unfold substπG
                    unfold term
                    simp
                    ext i
                    specialize ih i (h i)
                    exact ih

omit [DecidableEq σ.Base] [DecidableEq (σ.Base × σ.Sorts)] in
/- Given a term `t` in context `Γ` and a substitution `γ` from `Γ` to `Δ`, the resulting term `t[γ]`
is a term in context `Δ`. -/
theorem term_inCtx {s : σ.Sorts} {t : σ.Term s} (h : Γ ⊢ t) : Δ ⊢ t[γ] h := by
  induction t with
  | var x => exact γ.inCtx_map ⟨x, h⟩
  | app f ts hts => intro i; exact hts i (h i)

/- composition of substitutions -/
def Comp {Γ' : σ.Ctx} (γ : Γ.Subst Δ) (γ' : Δ.Subst Γ') : Γ.Subst Γ' where
  map x := (γ.map x) [γ'] (γ.inCtx_map x)
  inCtx_map x := γ'.term_inCtx (γ.inCtx_map x)


/- Given a substitution `γ : Γ.Subst Δ`, a sort `s` and two new labels `x` and `x'`, `γ.extended`
extends the substitution `γ` by mapping the new variable `⟨x, s⟩` to the term `var ⟨x', s⟩`. -/
def extended {x x' : σ.Base} (p : x ∉ Γ.Label) (q : x' ∉ Δ.Label) (s : σ.Sorts) :
    (Γ::⟨⟨x, s⟩, p⟩).Subst (Δ::⟨⟨x', s⟩, q⟩) where
  map y := if h : y.1 = ⟨x, s⟩ then var ⟨x', y.1.2⟩ else γ.map ⟨y.1, mem_of_mem_extended_neq y.2 h⟩
  inCtx_map y := by
    by_cases hyx : y.1 = ⟨x, s⟩
    · simp only [hyx, ↓reduceDIte]
      rw [hyx]
      exact Finset.mem_insert_self ⟨x', s⟩ Δ.ctx
    · simp only [hyx, ↓reduceDIte]
      exact inCtx_extended_of_inCtx q (γ.inCtx_map ⟨y.1, mem_of_mem_extended_neq y.2 hyx⟩)

def extendedGen (Δ' : σ.Ctx) (q : Δ.ctx ⊆ Δ'.ctx) (_ : Γ.ctx ⊆ Δ'.ctx) : Δ'.Subst Δ' where
  map y := if h : y.1 ∈ Γ.ctx then γ.map ⟨y.1,h⟩ else var y.1
  inCtx_map y := by
    by_cases hy : y.1 ∈ Γ.ctx
    simp only [hy, ↓reduceDIte]
    let ff := γ.inCtx_map
    specialize ff ⟨y.1,hy⟩
    exact (γ.map ⟨y.1,hy⟩).weakening Δ Δ' q ff
    simp only [hy, ↓reduceDIte]
    exact y.2


/- Given a substitution `γ : Γ.Subst Δ` and a formula `φ` in context `Γ`, `γ.formula φ` denotes the
formula resulting from substituting the variables of `Γ` with the corresponding terms of `γ`. -/
def formula {Γ Δ : σ.Ctx} (γ : Γ.Subst Δ) (φ : σ.Formula) (p : Γ ⊢ φ) : σ.Formula :=
  match φ with
  | ⊤ => ⊤
  | ⊥ => ⊥
  | t ≃ u : s => (t[γ] p.1) ≃ (u[γ] p.2) : s
  | φ ∧' ψ => (γ.formula φ p.1) ∧' (γ.formula ψ p.2)
  | ⋁ I, fs => ⋁ I, fun i => γ.formula (fs i) (p.1 i)
  | (∃'x)φ => if h : x.1 ∈ Δ.Label
              then (∃'⟨σ.newLabel Δ.ctx, x.2⟩) (γ.extended p.1 Δ.newLabel_notin_label x.2).formula
              φ p.2
              else (∃'x) (γ.extended p.1 h x.2).formula φ p.2
  | rel R ts => rel R (fun i => (ts i)[γ] (p i))

notation:101 φ " [" γ "] " p => formula γ φ p

/- Given a formula `φ` in context `Γ` and a substitution `γ : Γ.Subst Δ`, the resulting formula
`φ[γ]` is a formula in context `Δ`. -/
theorem formula_inCtx : ∀ {φ : σ.Formula} {Γ Δ : σ.Ctx} (γ : Γ.Subst Δ) (p : Γ ⊢ φ),
    Δ ⊢ φ[γ] p := by
  intro φ
  induction φ with
  | truth => intros; exact ⟨⟩
  | falsum => intros; exact ⟨⟩
  | equal s t u => intros _ _ γ p; exact ⟨γ.term_inCtx p.1, γ.term_inCtx p.2⟩
  | binConj φ ψ hφ hψ => intros _ _ γ p; exact ⟨hφ γ p.1, hψ γ p.2⟩
  | infDisj I fs hfs => intros _ _ γ p
                        constructor
                        · exact fun i => hfs i γ (p.1 i)
                        · apply Set.iUnion_subset
                          exact fun i => freeVar_subset_ctx_of_InCtx (hfs i γ (p.1 i))
  | exist x φ hφ => intros Γ Δ γ p
                    by_cases hx : x.1 ∈ Δ.Label
                    · unfold formula
                      simp only [hx, ↓reduceDIte]
                      exact ⟨Δ.newLabel_notin_label, by apply hφ⟩
                    · unfold formula
                      simp only [hx, ↓reduceDIte]
                      exact ⟨hx, by apply hφ⟩
  | rel R ts => intros _ _ γ p; exact (fun i => γ.term_inCtx (p i))

end Subst

end Ctx


omit [DecidableEq σ.Base] [DecidableEq (σ.Base × σ.Sorts)] in
lemma subst_ext_term : ∀ (s : σ.Sorts) (t : σ.Term s) (Γ Γ' Δ Δ' : σ.Ctx) (γ : Γ.Subst Δ)
  (γ' : Γ'.Subst Δ') (p : Γ ⊢ t) (p' : Γ' ⊢ t) (_ : γ.equal γ'), (t[γ] p) = (t[γ'] p') := by
  intros s t
  induction t with
  | var x => intros Γ Γ' Δ Δ' γ γ' p p' h
             unfold Ctx.Subst.term
             unfold Ctx.Subst.equal at h
             rcases h with ⟨h1, h2, h3⟩
             unfold Term.InCtx at p
             specialize h3 ⟨x,p⟩
             exact h3
  | app f ts hts => intros Γ Γ' Δ Δ' γ γ' p p' h
                    unfold Ctx.Subst.term
                    congr
                    ext i
                    specialize hts i Γ Γ' Δ Δ' γ γ' (p i) (p' i) h
                    exact hts

lemma subst_ext : ∀ (φ : σ.Formula) (Γ Γ' Δ Δ' : σ.Ctx) (γ : Γ.Subst Δ) (γ' : Γ'.Subst Δ')
  (p : Γ ⊢ φ) (p' : Γ' ⊢ φ) (_ : γ.equal γ'), (φ[γ] p) = (φ[γ'] p') := by
  intros φ
  induction φ with
  | truth => intros Γ Γ' Δ Δ' γ γ' p p' h
             unfold Ctx.Subst.formula
             rfl
  | falsum => intros Γ Γ' Δ Δ' γ γ' p p' h
              unfold Ctx.Subst.formula
              rfl
  | equal s t u => intros Γ Γ' Δ Δ' γ γ' p p' h
                   unfold Ctx.Subst.formula
                   rw [subst_ext_term s t Γ Γ' Δ Δ' γ γ' p.1 p'.1 h]
                   rw [subst_ext_term s u Γ Γ' Δ Δ' γ γ' p.2 p'.2 h]
  | binConj φ ψ hφ hψ => intros Γ Γ' Δ Δ' γ γ' p p' h
                         unfold Ctx.Subst.formula
                         specialize hφ Γ Γ' Δ Δ' γ γ' p.1 p'.1 h
                         specialize hψ Γ Γ' Δ Δ' γ γ' p.2 p'.2 h
                         rw [hφ,hψ]
  | infDisj I fs hfs => intros Γ Γ' Δ Δ' γ γ' p p' h
                        unfold Ctx.Subst.formula
                        congr
                        ext a
                        specialize hfs a Γ Γ' Δ Δ' γ γ' (p.1 a) (p'.1 a) h
                        exact hfs
  | exist x φ hφ => intros Γ Γ' Δ Δ' γ γ' p p' h
                    have auxh1 : (σ.newLabel Δ.ctx).1 = (σ.newLabel Δ'.ctx).1 := by rw [h.2.1]
                    by_cases hxΔ : x.1 ∈ Δ.Label
                    have hxΔ' : x.1 ∈ Δ'.Label := by
                      rw [<- h.2.1]
                      exact hxΔ
                    · unfold Ctx.Subst.formula
                      simp only[hxΔ,hxΔ',↓reduceDIte]
                      have auxh2 : (γ.extended p.1 (Δ.newLabel_notin_label) x.2).equal
                        (γ'.extended p'.1 (Δ'.newLabel_notin_label) x.2) := by
                        unfold Ctx.Subst.equal
                        have this1 :  (Γ::⟨(x.1,x.2),p.1⟩) =  (Γ'::⟨(x.1,x.2),p'.1⟩) := by
                          unfold Ctx.extended
                          simp
                          rw [h.1]
                        use this1
                        use (by rw [h.2.1])
                        intro z
                        unfold Ctx.Subst.extended
                        by_cases hz : z = x
                        simp [hz]
                        rw [h.2.1]
                        simp [hz]
                        unfold Ctx.Subst.equal at h
                        rcases h with ⟨h1, h2⟩
                        rcases h2 with ⟨h21, h22⟩
                        have hzΓ : z.1 ∈ Γ.ctx := by apply Ctx.mem_of_mem_extended_neq z.2 hz
                        specialize h22 ⟨z.1,hzΓ⟩
                        exact h22
                      specialize hφ (Γ::⟨⟨x.1,x.2⟩,p.1⟩) (Γ'::⟨⟨x.1,x.2⟩,p'.1⟩)
                        (Δ::⟨⟨σ.newLabel Δ.ctx,x.2⟩, Δ.newLabel_notin_label⟩)
                        (Δ'::⟨⟨σ.newLabel Δ'.ctx,x.2⟩, Δ'.newLabel_notin_label⟩)
                        (γ.extended p.1 (Δ.newLabel_notin_label) x.2)
                        (γ'.extended p'.1 (Δ'.newLabel_notin_label) x.2) p.2 p'.2 auxh2
                      rw [hφ]
                      apply congr
                      rw [h.2.1]
                      rfl
                    · unfold Ctx.Subst.formula
                      have hxΔ' : x.1 ∉ Δ'.Label := by
                        rw [<- h.2.1]
                        exact hxΔ
                      simp only[hxΔ,hxΔ',↓reduceDIte]
                      have auxh2 : (γ.extended p.1 hxΔ x.2).equal
                        (γ'.extended (p'.1) hxΔ' x.2) := by
                        unfold Ctx.Subst.equal
                        have this2 :  (Γ::⟨(x.1,x.2),p.1⟩) =  (Γ'::⟨(x.1,x.2),p'.1⟩) := by
                          unfold Ctx.extended
                          simp
                          rw [h.1]
                        use this2
                        have this : (Δ::⟨(x.1,x.2),hxΔ⟩) = (Δ'::⟨(x.1,x.2),hxΔ'⟩) := by
                          unfold Ctx.extended
                          simp
                          rw [h.2.1]
                        use this
                        intro z
                        unfold Ctx.Subst.extended
                        by_cases hz : z = x
                        simp [hz]
                        simp [hz]
                        unfold Ctx.Subst.equal at h
                        rcases h with ⟨h1, h2⟩
                        rcases h2 with ⟨h21, h22⟩
                        have hzΓ : z.1 ∈ Γ.ctx := by apply Ctx.mem_of_mem_extended_neq z.2 hz
                        specialize h22 ⟨z.1,hzΓ⟩
                        exact h22
                      specialize hφ (Γ::⟨⟨x.1,x.2⟩,p.1⟩) (Γ'::⟨⟨x.1,x.2⟩,p'.1⟩)
                        (Δ::⟨⟨x.1,x.2⟩,hxΔ⟩) (Δ'::⟨⟨x.1,x.2⟩,hxΔ'⟩)
                        (γ.extended p.1 hxΔ x.2) (γ'.extended p'.1 hxΔ' x.2) p.2 p'.2 auxh2
                      rw [hφ]
  | rel R ts => intros Γ Γ' Δ Δ' γ γ' p p' h
                unfold Ctx.Subst.formula
                congr
                ext i
                rw [subst_ext_term ((σ.rankR R).get i) (ts i) Γ Γ' Δ Δ' γ γ' (p i) (p' i) h]


/- Given a list `lf` of formulae, `finconj lf` returns the finite conjunction of its elements. -/
def finConj (lf : List σ.Formula) : σ.Formula :=
  match lf with
  | [] => .truth
--  | [φ] => φ
  | List.cons φ fs => φ ∧' (finConj fs)

notation "⋀'" lf => finConj lf

lemma ctx_finConj {Γ : σ.Ctx} {lf : List σ.Formula} (h : Γ ⊢ ⋀' lf) : ∀ i, Γ ⊢ (lf.get i) := by
  intros i
  induction lf with
  | nil => exfalso
           exact i.elim0
  | cons head tail ih => unfold finConj at h
                         specialize ih h.2
                         by_cases hi : i.val = 0
                         simp [hi]
                         exact h.1
                         have this1 : i.1-1 < tail.length := by
                          refine Nat.sub_lt_left_of_lt_add (Nat.pos_of_ne_zero hi) ?_
                          rw [Nat.add_comm]
                          exact i.2
                         specialize ih ⟨i.1-1,this1⟩
                         have : (head :: tail).get i = tail.get ⟨i.1 -1, this1⟩ := by
                          have : ∃ k, i.val = k + 1 := Nat.exists_eq_succ_of_ne_zero hi
                          rcases this with ⟨k, hk⟩
                          have aux1 : i = ⟨k + 1, by rw [← hk]; exact i.2⟩ := by
                            ext; simp [hk]
                          simp [aux1]
                         rw [this]
                         exact ih

/- Given two list of variables, `zipVar` returns list of equality of the variables in the lists. -/
def zipVar (lb1 lb2 : List σ.Base) (ls : List σ.Sorts) (h1 : lb1.length = lb2.length)
  (h2 : lb2.length = ls.length)  : List σ.Formula :=
  match lb1, lb2, ls with
  | [], [], [] => []
  | [x], [y], [s] => [(.var (x,s) ≃ .var (y,s) : s)]
  | x :: xs, y :: ys, s :: ls =>  (.var (x,s) ≃ .var (y,s) : s) ::
    (zipVar xs ys ls (by simp [List.length_cons] at h1; exact h1)
      (by simp [List.length_cons] at h2; exact h2))
  | _, _, _ => []


/- A variable renaming `Renaming Γ Δ` consists of an bijective map between `Γ.ctx` and `Δ.ctx`
perserving the sorts -/
structure Ctx.Renaming (Γ Δ : σ.Ctx) where
  /- A map from `Γ.ctx` to this set of new labels -/
  map : Γ.ctx → Δ.ctx
  /- such that this map is injective -/
  isBijection : map.Bijective
  /- such that this map preserves sorts -/
  preserve_sort : ∀ (x : Γ.ctx), (map x).1.2 = x.1.2


namespace Ctx.Renaming

variable {Γ Δ : σ.Ctx} (ρ : Γ.Renaming Δ)

open Term

/- Given `ρ : Γ.Renaming Δ`, `listEq ρ` returns the list of formulae of the form
`Term.var x = Term.var (ρ.map x)` for every `x ∈ Γ.ctx`. -/
noncomputable def listEq : List σ.Formula :=
  List.map (fun x => if p : x ∈ Γ.ctx then var x ≃ var ⟨(ρ.map ⟨x, p⟩).1.1, x.2⟩ : x.2 else ⊥)
  Γ.ctx.toList

noncomputable def listEq2 : List σ.Formula :=
  List.map (fun (x : Γ.ctx) => var x.1 ≃ var ⟨(ρ.map x).1.1, x.1.2⟩ : x.1.2)
  Γ.ctx.attach.toList

omit [DecidableEq σ.Base]
lemma getIndex_listEq (x : Γ.ctx) : ∃ i, (ρ.listEq).get i =
  .var x.1 ≃ .var ⟨(ρ.map x).1.1, x.1.2⟩ : x.1.2 := by
  have h_mem : x.1 ∈ Γ.ctx.toList := by
    simp [x.2]
  let jj := List.mem_iff_get.1 h_mem
  rcases jj with ⟨i, hi⟩
  let n := i.1
  have thisf : ρ.listEq.length = Γ.ctx.toList.length := by
    rw [listEq, List.length_map]
  have : i.1 < ρ.listEq.length := by rw [thisf]; exact i.2
  use ⟨i.1, this⟩
  have auxf : ρ.listEq.get ⟨i.1, this⟩ = if p : Γ.ctx.toList.get ⟨i,i.2⟩ ∈ Γ.ctx then
    var (Γ.ctx.toList.get ⟨i,i.2⟩) ≃ var (((ρ.map ⟨Γ.ctx.toList.get ⟨i,i.2⟩, p⟩).1).1,
    (Γ.ctx.toList.get ⟨i,i.2⟩).2) : (Γ.ctx.toList.get ⟨i,i.2⟩).2 else ⊥ := by
    unfold listEq
    simp
  rw [auxf]
  have p : Γ.ctx.toList.get ⟨i,i.2⟩ ∈ Γ.ctx := by rw [hi]; exact x.2
  simp only [p, ↓reduceDIte]
  congr




/-- To every renaming `ρ` of the variables of a context `Γ` and `Δ`, we can associate a substitution
`ρ.substOfRenaming` between `Γ` and `Δ`. -/
def substOfRenaming (ρ : Γ.Renaming Δ): Γ.Subst Δ where
  map x := var ⟨(ρ.map x).1.1, x.1.2⟩
  inCtx_map x := by
    unfold Term.InCtx
    rw [<- ρ.preserve_sort x]
    exact (ρ.map x).2

instance Subst.instCoeRenaming : CoeDep (Γ.Renaming Δ) ρ (Γ.Subst Δ) where
  coe := ρ.substOfRenaming


end Renaming

end Ctx

/- A `Sequent` is made of a context and two formulae in this context. -/
structure Sequent where
  /- a context -/
  ctx : σ.Ctx
  /- a "left" formula -/
  left : σ.Formula
  /- a "right" formula -/
  right : σ.Formula
  /- a proof that the left formula is a formula in the given context -/
  isFormula_left : ctx ⊢ left
  /- a proof that the right formula is a formula in the given context -/
  isFormula_right : ctx ⊢ right

/- A (observable) first-order `Theory` over a signature `σ` is a set of (observable) sequents over
`σ` whose elements are called the (non-logical) axioms of the said theory. -/
structure Theory where
  /- a set of sequents called axioms -/
  axioms : Set σ.Sequent

namespace Theory

/-! Deduction system for observable first-order logic -/

variable (𝕋 : σ.Theory)

/- The type `Proof Γ φ ψ` is the type of proofs that formula φ implies formula ψ in context `Γ`. -/
inductive Proof : σ.Ctx → σ.Formula → σ.Formula → Type _
  | ax : (seq : σ.Sequent) → seq ∈ 𝕋.axioms → Proof seq.ctx seq.left seq.right
  | id Γ (φ : σ.Formula) : Proof Γ φ φ
  | subst {Γ Δ : σ.Ctx} (γ : Γ.Subst Δ) : Proof Γ φ ψ → (p : Γ ⊢ φ) → (q : Γ ⊢ ψ) →
      Proof Δ (φ[γ] p) (ψ[γ] q)
  | cut Γ φ (ψ : σ.Formula) χ (h : Γ ⊢ ψ) :  Proof Γ φ ψ → Proof Γ ψ χ → Proof Γ φ χ
  | top Γ φ : Proof Γ φ (⊤)
  | conjElimLeft Γ φ ψ : Proof Γ (φ ∧' ψ) φ
  | conjElimRight Γ φ ψ : Proof Γ (φ ∧' ψ) ψ
  | conjIntro Γ φ ψ χ : Proof Γ φ ψ → Proof Γ φ χ → Proof Γ φ (ψ ∧' χ)
  | bot Γ φ : Proof Γ (⊥) φ
  | infDisjIntro Γ I fs i : Proof Γ (fs i) (⋁ I, fs)
  | disL Γ I fs φ : (∀ i, Proof Γ (fs i) φ) → Proof Γ (⋁ I, fs) φ
  | existIntro Γ y p φ (ψ : σ.Formula) (h : (Γ :: ⟨y, p⟩) ⊢ ψ) : Proof (Γ :: ⟨y, p⟩) φ ψ →
      Proof Γ ((∃'y) φ) ψ
  | existElim Γ y p φ (ψ : σ.Formula) (h : Γ ⊢ ψ) : Proof Γ ((∃'y) φ) ψ → Proof (Γ :: ⟨y, p⟩) φ ψ
  | distributive Γ φ I fs : Proof Γ (φ ∧' (⋁ I, fs)) (⋁ I, fun i => φ ∧' fs i)
  | frobenius Γ φ x ψ : Proof Γ (φ ∧' ((∃'x) ψ)) ((∃'x) φ ∧' ψ)
  | substOfEq (Γ₁ Γ₂ Δ : σ.Ctx) (ρ : Γ₁.Renaming Γ₂) (φ : σ.Formula) (p : Γ₁ ⊢ φ)
    (h1 : Γ₁.ctx ⊆ Δ.ctx) (h2 : Γ₂.ctx ⊆ Δ.ctx):
      Proof Δ (finConj ρ.listEq ∧' φ) (φ[ρ.substOfRenaming] p)

notation "✂" => Signature.Theory.Proof

/- Given a sequent, the `Provable` predicate asserts that the corresponding `Proof` type is
nonempty. -/
def Provable (seq : σ.Sequent) : Prop := Nonempty (𝕋.Proof seq.ctx seq.left seq.right)

end Theory
