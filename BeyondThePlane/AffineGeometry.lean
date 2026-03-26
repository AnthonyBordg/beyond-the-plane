/-
Copyright (c) 2025 Lagrange Mathematics and Computing Research Center. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Bordg
-/

import BeyondThePlane.Syntax
import Mathlib.Data.Finset.Lattice.Fold

/-!
This file defines the underlying signature for affine geometry following the syntax in the
`Syntax.lean` file.
-/

namespace Signature.AffGeom

inductive Sorts where
  | 𝓟 : Sorts
  | 𝓛 : Sorts

inductive Fun where
  | O : Fun
  | I : Fun
  | J : Fun

inductive Rel where
  | belong : Rel
  | parallel : Rel
  | nonParallel  : Rel
  | distinctPoints : Rel
  | distinctLines : Rel

notation "∈'" => Signature.AffGeom.Rel.belong
notation "∥" => Signature.AffGeom.Rel.parallel
notation "∦" => Signature.AffGeom.Rel.nonParallel
notation "≠ₚ" => Signature.AffGeom.Rel.distinctPoints
notation "≠ₗ" => Signature.AffGeom.Rel.distinctLines

def instSignature : Signature where
  Base := ℕ
  Index := ℕ
  leftIndex := 0
  rightIndex := 1
  Sorts := Signature.AffGeom.Sorts
  newLabel X := ⟨X.sup Prod.fst + 1, by
    intro v hv
    have := Finset.le_sup (f := Prod.fst) hv
    exact ne_of_gt (Nat.lt_succ_of_le (n := v.1) (m := X.sup Prod.fst) this)⟩
  Fun := Signature.AffGeom.Fun
  Rel := Signature.AffGeom.Rel
  rankF f := match f with
           | .O => ([], .𝓟)
           | .I => ([], .𝓟)
           | .J => ([], .𝓟)
  rankR R := match R with
             | ∈' => [.𝓟, .𝓛]
             | ∥ => [.𝓛, .𝓛]
             | ∦ => [.𝓛, .𝓛]
             | ≠ₚ => [.𝓟, .𝓟]
             | ≠ₗ => [.𝓛, .𝓛]

end Signature.AffGeom
