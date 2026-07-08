/-
Copyright (c) 2026 Maximiliano Onofre Martínez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximiliano Onofre Martínez
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.StandardReduction

/-! # The Leftmost Reduction Theorem

## Reference

* [M. Copes, *A machine-checked proof of the Standardization Theorem in λ-calculus*][Copes2018]

-/

@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-- The number of β-redexes occurring in a term. -/
def countRedexes : Term Var → Nat
| fvar _        => 0
| bvar _        => 0
| abs m         => countRedexes m
| app (abs m) n => (countRedexes (abs m) + countRedexes n) + 1
| app m n       => countRedexes m + countRedexes n

/-- A term is in normal form when it contains no β-redexes. -/
def NormalForm (m : Term Var) : Prop := countRedexes m = 0

/-- `IsAbs m` holds when `m` is an abstraction. -/
inductive IsAbs : Term Var → Prop
| abs (m : Term Var) : IsAbs (abs m)

/-- `BetaAt M N i` reduces the redex at position `i` of `M` to obtain `N`;
    positions are counted from left to right. -/
inductive BetaAt : Term Var → Term Var → Nat → Prop
/-- The outermost redex sits at position `0`. -/
| outer : LC (abs M) → LC N → BetaAt (app (abs M) N) (M ^ N) 0
/-- Reducing a non-abstraction operator keeps the position. -/
| appNoAbsL : BetaAt M M' i → ¬IsAbs M → BetaAt (app M N) (app M' N) i
/-- Reducing an abstraction operator advances the position by one. -/
| appAbsL : BetaAt M M' i → IsAbs M → BetaAt (app M N) (app M' N) (i + 1)
/-- Reducing the operand adds the redex count of a non-abstraction operator. -/
| appNoAbsR : BetaAt M M' i → ¬IsAbs N → BetaAt (app N M) (app N M') (i + countRedexes N)
/-- Reducing the operand adds the redex count of an abstraction operator, plus one. -/
| appAbsR : BetaAt M M' i → IsAbs N → BetaAt (app N M) (app N M') (i + countRedexes N + 1)
/-- Reducing under a binder keeps the position. -/
| abs (xs : Finset Var) :
    (∀ x ∉ xs, BetaAt (M ^ fvar x) (M' ^ fvar x) i) → BetaAt (abs M) (abs M') i

/-- Leftmost reduction: a β-reduction contracting the redex at position 0. -/
@[reduction_sys "ℓ"]
abbrev Leftmost (M N : Term Var) : Prop := BetaAt M N 0

variable {L L' M M' N : Term Var} {i : Nat}

/-- Opening with a free variable preserves the number of redexes. -/
lemma countRedexes_openRec_fvar (M : Term Var) (k : Nat) (x : Var) :
    countRedexes (M⟦k ↝ fvar x⟧) = countRedexes M := by
  induction M generalizing k with
  | bvar j => simp only [openRec_bvar]; split <;> rfl
  | fvar => rfl
  | abs M ih => grind [openRec_abs, countRedexes]
  | app L R ihL ihR => cases L <;> grind [countRedexes, openRec_bvar, openRec_app, openRec_abs]

/-- In a normal-form application, both sides are normal and the operator is not an
    abstraction. -/
lemma NormalForm.app_inv (h : NormalForm (app L M)) :
    ¬IsAbs L ∧ NormalForm L ∧ NormalForm M := by
  cases L <;> grind [NormalForm, countRedexes, IsAbs]

/-- The body of a normal-form abstraction opens to a normal form. -/
lemma NormalForm.abs_open {x : Var} (h : NormalForm (abs M)) : NormalForm (M ^ fvar x) := by
  have e : countRedexes (M ^ fvar x) = countRedexes M := countRedexes_openRec_fvar M 0 x
  rw [NormalForm, e]
  exact h

/-- The source of a Call-by-Name step is never an abstraction. -/
lemma cbn_not_isAbs (h : M ⭢ₙ N) : ¬IsAbs M := by
  intro ha
  cases ha
  trivial

variable [DecidableEq Var]

/-- Renaming a free variable preserves the number of redexes. -/
lemma countRedexes_subst_fvar (M : Term Var) (x y : Var) :
    countRedexes (M[x := fvar y]) = countRedexes M := by
  induction M with
  | fvar z => simp only [subst_fvar]; split <;> rfl
  | bvar => rfl
  | abs M ih => grind [countRedexes]
  | app L R ihL ihR => cases L <;> grind [countRedexes]

/-- Renaming a free variable preserves being an abstraction. -/
lemma isAbs_subst_fvar {x y : Var} : IsAbs (M[x := fvar y]) ↔ IsAbs M := by
  cases M <;> grind [IsAbs]

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
