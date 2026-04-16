/-
Copyright (c) 2026 Maximiliano Onofre Martínez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximiliano Onofre Martínez
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta

@[expose] public section

set_option linter.unusedDecidableInType false

/-! # η-confluence for the λ-calculus

## Reference

* [T. Nipkow, *More Church-Rosser Proofs (in Isabelle/HOL)*][Nipkow2001]

-/

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Untyped.Term

open Relation

variable [HasFresh Var] [DecidableEq Var]

open FullEta in
lemma stronglyConfluent_eta : StronglyConfluent (@FullEta Var) := by
  intro M M₁ M₂ h₁ h₂
  suffices ∃ M₃, ReflGen FullEta M₁ M₃ ∧ ReflGen FullEta M₂ M₃ by grind
  induction h₁ generalizing M₂
  case base _ _ p P st =>
    cases st
    case eta =>
      cases h₂
      case base =>
        use (disch := grind) P
      case abs _ _ _ _ _ h =>
        have ⟨w, _⟩ := fresh_exists <| free_union [fv] Var
        have ⟨P', _, _⟩ := invert_step_app_fvar <| h w <| by grind
        use P'
        grind [→ Eta.eta, step_not_fv, open_eq_app]
  case appL Z P P' _ _ ih =>
    cases h₂
    case base => contradiction
    case appL _ _ _ _ P'' _ h =>
      let P''' := (ih h).choose
      use (disch := grind) app Z P'''
    case appR _ _ _ _ Z' _ _ => use (disch := grind) app Z' P'
  case appR _ _ Z P _ _ _ ih =>
    cases h₂
    case base => contradiction
    case appR _ _ P' _ _ P'' h _ =>
      let i := ih h
      let P''' := i.choose
      use (disch := grind) app P''' Z
    case appL _ _ P' _ _ Z' _ _ => use (disch := grind) app P' Z'
  case abs _ _ p p' _ h ih =>
    cases h₂
    case base st =>
      cases st
      have ⟨w, _⟩ := fresh_exists <| free_union [fv] Var
      have ⟨p', _, _⟩ := invert_step_app_fvar <| h w (by grind)
      use p'
      grind [→ Eta.eta, step_not_fv, open_eq_app]
    case abs _ _ xs p'' _ st =>
      have ⟨x, _⟩ := fresh_exists <| free_union [fv] Var
      have hP'' := st x (by aesop)
      have i : ∀ {M₂ : Term Var}, (p ^ fvar x) ⭢ηᶠ M₂ → ∃ M₃,
        ReflGen FullEta (p' ^ fvar x) M₃ ∧ ReflGen FullEta M₂ M₃ := ih x (by aesop)
      let p''' := (i hP'').choose
      use abs (p''' ^* x)
      grind [close_eta_steps]

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
