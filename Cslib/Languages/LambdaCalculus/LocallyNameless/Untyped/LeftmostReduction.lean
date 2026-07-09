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
def BetaNormal (m : Term Var) : Prop := countRedexes m = 0

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
lemma BetaNormal.app_inv (h : BetaNormal (app L M)) :
    ¬IsAbs L ∧ BetaNormal L ∧ BetaNormal M := by
  cases L <;> grind [BetaNormal, countRedexes, IsAbs]

/-- The body of a normal-form abstraction opens to a normal form. -/
lemma BetaNormal.abs_open {x : Var} (h : BetaNormal (abs M)) : BetaNormal (M ^ fvar x) := by
  have e : countRedexes (M ^ fvar x) = countRedexes M := countRedexes_openRec_fvar M 0 x
  rw [BetaNormal, e]
  exact h

/-- Contracting a redex of an abstraction yields an abstraction. -/
lemma BetaAt.isAbs_r (h : BetaAt M N i) (ha : IsAbs M) : IsAbs N := by
  cases ha
  cases h
  exact .abs _

/-- Leftmost reduction preserves being an abstraction. -/
lemma Leftmost.steps_isAbs_r (h : M ↠ℓ N) (ha : IsAbs M) : IsAbs N := by
  induction h with
  | refl => exact ha
  | tail _ step ih => exact step.isAbs_r ih

/-- Left congruence for leftmost reduction, provided the target is not an abstraction. -/
lemma Leftmost.steps_app_l_cong (h : L ↠ℓ L') (hna : ¬IsAbs L') :
    app L M ↠ℓ app L' M := by
  induction h
  case refl => rfl
  case tail P _ _ step ih =>
    have hnb : ¬IsAbs P := mt step.isAbs_r hna
    exact (ih hnb).tail (step.appNoAbsL hnb)

/-- Reducing the operand across a non-abstraction normal form keeps the position. -/
lemma BetaAt.app_r_cong (h : BetaAt M M' i) (hL : BetaNormal L) (hna : ¬IsAbs L) :
    BetaAt (app L M) (app L M') i := by
  have := h.appNoAbsR hna
  rwa [hL] at this

/-- Right congruence for leftmost reduction, provided the operator is a non-abstraction
    normal form. -/
lemma Leftmost.steps_app_r_cong (h : M ↠ℓ M') (hL : BetaNormal L) (hna : ¬IsAbs L) :
    app L M ↠ℓ app L M' := by
  induction h with
  | refl => rfl
  | tail _ step ih => exact ih.tail (step.app_r_cong hL hna)

/-- Congruence for leftmost reduction on applications whose reduced operator is a
    non-abstraction normal form. -/
lemma Leftmost.steps_app_cong (hL : L ↠ℓ L') (hM : M ↠ℓ M')
    (hnf : BetaNormal L') (hna : ¬IsAbs L') : app L M ↠ℓ app L' M' :=
  (steps_app_l_cong hL hna).trans (steps_app_r_cong hM hnf hna)

/-- The source of a Call-by-Name step is never an abstraction. -/
lemma cbn_not_isAbs (h : M ⭢ₙ N) : ¬IsAbs M := by
  intro ha
  cases ha
  trivial

/-- A single Call-by-Name step contracts the leftmost redex. -/
lemma Leftmost.of_cbn_step (h : M ⭢ₙ N) : M ⭢ℓ N := by
  induction h with
  | base h_beta =>
    cases h_beta with
    | beta lc_M lc_N => exact .outer lc_M lc_N
  | app _ step_M ih => exact .appNoAbsL ih (cbn_not_isAbs step_M)

/-- Call-by-Name reduction is contained in leftmost reduction. -/
lemma Leftmost.of_cbn (h : M ↠ₙ N) : M ↠ℓ N := by
  induction h with
  | refl => rfl
  | tail _ step ih => exact ih.tail (of_cbn_step step)

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

variable [HasFresh Var]

/-- Renaming a free variable preserves the position of the contracted redex. -/
lemma BetaAt.rename (h : BetaAt M M' i) (x y : Var) :
    BetaAt (M[x := fvar y]) (M'[x := fvar y]) i := by
  induction h
  case outer lc_M lc_N =>
    rw [subst_open x (fvar y) _ _ (.fvar y)]
    exact .outer (subst_lc lc_M (.fvar y)) (subst_lc lc_N (.fvar y))
  case appNoAbsL _ hna ih =>
    exact .appNoAbsL ih (mt isAbs_subst_fvar.mp hna)
  case appAbsL _ ha ih =>
    exact .appAbsL ih (isAbs_subst_fvar.mpr ha)
  case appNoAbsR M M' i N _ hna ih =>
    rw [← countRedexes_subst_fvar N x y]
    exact .appNoAbsR ih (mt isAbs_subst_fvar.mp hna)
  case appAbsR M M' i N _ ha ih =>
    rw [← countRedexes_subst_fvar N x y]
    exact .appAbsR ih (isAbs_subst_fvar.mpr ha)
  case abs =>
    apply BetaAt.abs <| free_union [fv] Var
    grind

/-- Contracting a redex preserves local closure. -/
lemma BetaAt.lc_r (h : BetaAt M M' i) (lc : LC M) : LC M' := by
  induction h with
  | outer lc_M lc_N => exact beta_lc lc_M lc_N
  | appNoAbsL _ _ ih | appAbsL _ _ ih =>
    cases lc with
    | app lc_L lc_R => exact .app (ih lc_L) lc_R
  | appNoAbsR _ _ ih | appAbsR _ _ ih =>
    cases lc with
    | app lc_L lc_R => exact .app lc_L (ih lc_R)
  | abs xs _ ih =>
    cases lc with
    | abs ys _ h_body =>
      apply LC.abs (xs ∪ ys)
      intro z hz
      exact ih z (by grind) (h_body z (by grind))

/-- Closing a variable and abstracting preserves the position of the contracted redex. -/
lemma BetaAt.abs_close {x : Var} (h : BetaAt M M' i) (lc : LC M) :
    BetaAt (M⟦0 ↜ x⟧.abs) (M'⟦0 ↜ x⟧.abs) i := by
  apply BetaAt.abs ∅
  intro z _
  have lc' := h.lc_r lc
  have hr : BetaAt (M[x := fvar z]) (M'[x := fvar z]) i := h.rename x z
  grind

/-- Leftmost reduction preserves local closure. -/
lemma Leftmost.steps_lc_r (h : M ↠ℓ M') (lc : LC M) : LC M' := by
  induction h with
  | refl => exact lc
  | tail _ step ih => exact step.lc_r ih

/-- Leftmost reduction is preserved by closing a variable and abstracting. -/
lemma Leftmost.steps_abs_close {x : Var} (h : M ↠ℓ M') (lc : LC M) :
    (M⟦0 ↜ x⟧.abs) ↠ℓ (M'⟦0 ↜ x⟧.abs) := by
  induction h with
  | refl => rfl
  | tail hs step ih => exact ih.tail (step.abs_close (steps_lc_r hs lc))

/-- Cofinite congruence rule for leftmost reduction under an abstraction. -/
lemma Leftmost.steps_abs_cong (xs : Finset Var)
    (cofin : ∀ x ∉ xs, (M ^ fvar x) ↠ℓ (M' ^ fvar x)) (lc : LC (abs M)) :
    abs M ↠ℓ abs M' := by
  have ⟨w, _⟩ := fresh_exists <| free_union [fv] Var
  rw [open_close w M 0 (by grind), open_close w M' 0 (by grind)]
  have hstep := cofin w (by grind)
  have hlc := beta_lc lc (.fvar w)
  exact steps_abs_close hstep hlc

/-- A standard reduction to a normal form is a leftmost reduction. -/
theorem Leftmost.of_standard (h : M ⭢ₛ N) (hn : BetaNormal N) : M ↠ℓ N := by
  induction h
  case fvar x => rfl
  case app _ _ ihL ihM =>
    have ⟨hna, hL', hM'⟩ := hn.app_inv
    exact steps_app_cong (ihL hL') (ihM hM') hL' hna
  case abs xs h_body ih =>
    have lc := (Standard.abs xs h_body).lc_l
    apply steps_abs_cong xs _ lc
    intro x hx
    exact ih x hx hn.abs_open
  case rdx M N M' _ lc_M lc_N cbn std_P ih =>
    have s1 : M.app N ↠ℓ M'.abs.app N := of_cbn (CBN.steps_app_l_cong cbn lc_N)
    have s2 : M'.abs.app N ⭢ℓ M' ^ N := .outer (CBN.steps_lc_r lc_M cbn) lc_N
    exact (s1.tail s2).trans (ih hn)

/-- The leftmost reduction theorem: if a term β-reduces to a normal form, then leftmost
    reduction reaches it. -/
theorem Leftmost.normalization (lc : LC M) (h : M ↠βᶠ N) (hn : BetaNormal N) : M ↠ℓ N :=
  of_standard (.standardization lc h) hn

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
