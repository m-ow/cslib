/-
Copyright (c) 2026 Maximiliano Onofre Martínez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximiliano Onofre Martínez
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.CallByName

/-! # Standard Reduction and the Standardization Theorem

## References

* [B. Calisto, *Formalization in Coq of the Standardization Theorem for λ-calculus*][Calisto2022]
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
| app (abs m) n => countRedexes m + countRedexes n + 1
| app m n       => countRedexes m + countRedexes n

/-- `BetaAt i M N` reduces the redex at position `i` of `M` to obtain `N`;
    positions are counted from left to right. -/
inductive BetaAt : Nat → Term Var → Term Var → Prop
/-- The outermost redex sits at position `0`. -/
| outer : LC (abs M) → LC N → BetaAt 0 (app (abs M) N) (M ^ N)
/-- Reducing a non-abstraction operator keeps the position. -/
| appNoAbsL : BetaAt i M M' → ¬IsAbs M → BetaAt i (app M N) (app M' N)
/-- Reducing an abstraction operator advances the position by one. -/
| appAbsL : BetaAt i M M' → IsAbs M → BetaAt (i + 1) (app M N) (app M' N)
/-- Reducing the operand adds the redex count of a non-abstraction operator. -/
| appNoAbsR : BetaAt i M M' → ¬IsAbs N → BetaAt (i + countRedexes N) (app N M) (app N M')
/-- Reducing the operand adds the redex count of an abstraction operator, plus one. -/
| appAbsR : BetaAt i M M' → IsAbs N → BetaAt (i + countRedexes N + 1) (app N M) (app N M')
/-- Reducing under a binder keeps the position. -/
| abs (xs : Finset Var) :
    (∀ x ∉ xs, BetaAt i (M ^ fvar x) (M' ^ fvar x)) → BetaAt i (abs M) (abs M')

/-- A standard β-reduction sequence from `M` to `N`: the contracted redex positions are
    non-decreasing and all at least `n`. -/
inductive StandardSeq : Nat → Term Var → Term Var → Prop
/-- The empty sequence is standard for any lower bound. -/
| refl : StandardSeq n M M
/-- A first step at position `i ≥ n`, followed by a standard sequence bounded below by `i`. -/
| head : BetaAt i M P → n ≤ i → StandardSeq i P N → StandardSeq n M N

/-- The Standard reduction relation. -/
@[reduction_sys "ₛ"]
inductive Standard : Term Var → Term Var → Prop
/-- Free variables standardly reduce to themselves. -/
| fvar (x : Var) : Standard (fvar x) (fvar x)
/-- Congruence rule for application. -/
| app  : Standard L L' → Standard M M' → Standard (app L M) (app L' M')
/-- Congruence rule for lambda terms. -/
| abs (xs : Finset Var) :
    (∀ x ∉ xs, Standard (m ^ fvar x) (m' ^ fvar x)) → Standard (abs m) (abs m')
/-- Standard reduction of a head redex. -/
| rdx : LC m → LC n → m ↠ₙ (abs m') → Standard (m' ^ n) p → Standard (app m n) p

variable {L L' M M' N N' P : Term Var} {i m n : Nat}

/-- The left side of a standard reduction is locally closed. -/
lemma Standard.lc_l (step : M ⭢ₛ N) : LC M := by
  induction step
  case abs xs _ ih => exact LC.abs xs _ ih
  all_goals grind

/-- Standard reduction is reflexive for locally closed terms. -/
lemma Standard.lc_refl (M : Term Var) (lc : LC M) : M ⭢ₛ M := by
  induction lc
  all_goals constructor <;> assumption

/-- The right side of a standard reduction is locally closed. -/
lemma Standard.lc_r (step : M ⭢ₛ N) : LC N := by
  induction step
  case abs xs _ ih => exact LC.abs xs _ ih
  all_goals grind

/-- A single Call-by-Name step is a standard reduction. -/
lemma Standard.of_cbn_step (step : M ⭢ₙ N) (lc_N : LC N) : M ⭢ₛ N := by
  induction step
  case base h_beta =>
    cases h_beta
    exact rdx (by assumption) (by assumption) .refl (lc_refl _ lc_N)
  case app L _ _ lc_L _ ih =>
    cases lc_N
    exact app (ih (by assumption)) (lc_refl L lc_L)

/-- A Call-by-Name step followed by a standard reduction is a standard reduction. -/
lemma Standard.cbn_step_trans (step : M ⭢ₙ P) (std : P ⭢ₛ N) : M ⭢ₛ N := by
  induction step generalizing N
  case base h_beta =>
    cases h_beta
    exact rdx (by assumption) (by assumption) .refl std
  case app step_M ih =>
    cases std with
    | app std_L' std_M => exact app (ih std_L') std_M
    | rdx _ lc_Z cbn_m std_body => exact rdx step_M.lc_l lc_Z (.head step_M cbn_m) std_body

/-- A Call-by-Name reduction followed by a standard reduction is a standard reduction. -/
lemma Standard.cbn_trans (h1 : M ↠ₙ P) (h2 : P ⭢ₛ N) : M ⭢ₛ N := by
  induction h1 with
  | refl => exact h2
  | tail _ h_step ih => exact ih (cbn_step_trans h_step h2)

/-- Call-by-Name reduction is contained in standard reduction. -/
lemma Standard.of_cbn (step : M ↠ₙ N) (lc_N : LC N) : M ⭢ₛ N :=
  cbn_trans step (lc_refl N lc_N)

/-- Opening with a free variable preserves the number of redexes. -/
lemma countRedexes_openRec_fvar (M : Term Var) (k : Nat) (x : Var) :
    countRedexes (M⟦k ↝ fvar x⟧) = countRedexes M := by
  induction M generalizing k with
  | bvar j => simp only [openRec_bvar]; split <;> rfl
  | fvar => rfl
  | abs M ih => grind [openRec_abs, countRedexes]
  | app L R ihL ihR => cases L <;> grind [countRedexes, openRec_bvar, openRec_app, openRec_abs]

/-- Opening the outermost binder with a free variable preserves the number of redexes. -/
lemma countRedexes_open_fvar (M : Term Var) (x : Var) :
    countRedexes (M ^ fvar x) = countRedexes M :=
  countRedexes_openRec_fvar M 0 x

/-- An application has at least as many redexes as its operator and operand combined. -/
lemma countRedexes_app_le (M N : Term Var) :
    countRedexes M + countRedexes N ≤ countRedexes (app M N) := by
  cases M <;> grind [countRedexes]

/-- An application with an abstraction operator has one more redex than its parts. -/
lemma countRedexes_app_abs {M : Term Var} (ha : IsAbs M) (N : Term Var) :
    countRedexes (app M N) = countRedexes M + countRedexes N + 1 := by
  cases ha; grind [countRedexes]

/-- Contracting a redex of an abstraction yields an abstraction. -/
lemma BetaAt.isAbs_r (h : BetaAt i M N) (ha : IsAbs M) : IsAbs N := by
  cases ha
  cases h
  exact .abs _

/-- The source of a Call-by-Name step is never an abstraction. -/
lemma cbn_not_isAbs (h : M ⭢ₙ N) : ¬IsAbs M := by
  intro ha
  cases ha
  trivial

/-- A single Call-by-Name step contracts the redex at position `0`. -/
lemma BetaAt.of_cbn_step (h : M ⭢ₙ N) : BetaAt 0 M N := by
  induction h with
  | base h_beta =>
    cases h_beta with
    | beta lc_M lc_N => exact .outer lc_M lc_N
  | app _ step_M ih => exact .appNoAbsL ih (cbn_not_isAbs step_M)

/-- A standard sequence remains standard under a smaller lower bound. -/
lemma StandardSeq.mono (h : StandardSeq n M N) (hmn : m ≤ n) : StandardSeq m M N := by
  cases h with
  | refl => exact .refl
  | head step hni tail => exact .head step (le_trans hmn hni) tail

/-- Standard sequences preserve being an abstraction. -/
lemma StandardSeq.isAbs_r (h : StandardSeq n M N) (ha : IsAbs M) : IsAbs N := by
  induction h with
  | refl => exact ha
  | head step _ _ ih => exact ih (step.isAbs_r ha)

/-- A standard sequence stays standard when preceded by a Call-by-Name reduction. -/
lemma StandardSeq.cbn_head (h : M ↠ₙ P) (hseq : StandardSeq 0 P N) :
    StandardSeq 0 M N := by
  induction h with
  | refl => exact hseq
  | tail _ step ih => exact ih (.head (BetaAt.of_cbn_step step) (Nat.le_refl 0) hseq)

/-- Right congruence for standard sequences when the operator is an abstraction. -/
lemma StandardSeq.app_r_abs (h : StandardSeq n M M') (ha : IsAbs L) :
    StandardSeq (n + countRedexes L + 1) (app L M) (app L M') := by
  induction h with
  | refl => exact .refl
  | head step hni tail ih => exact .head (step.appAbsR ha) (by omega) ih

/-- Right congruence for standard sequences when the operator is a non-abstraction. -/
lemma StandardSeq.app_r_noAbs (h : StandardSeq n M M') (hna : ¬IsAbs L) :
    StandardSeq (n + countRedexes L) (app L M) (app L M') := by
  induction h with
  | refl => exact .refl
  | head step hni tail ih => exact .head (step.appNoAbsR hna) (by omega) ih

/-- Renaming a free variable preserves the number of redexes. -/
lemma countRedexes_subst_fvar [DecidableEq Var] (M : Term Var) (x y : Var) :
    countRedexes (M[x := fvar y]) = countRedexes M := by
  induction M with
  | fvar z => simp only [subst_fvar]; split <;> rfl
  | bvar => rfl
  | abs M ih => grind [countRedexes]
  | app L R ihL ihR => cases L <;> grind [countRedexes]

/-- Renaming a free variable preserves being an abstraction. -/
lemma isAbs_subst_fvar [DecidableEq Var] {x y : Var} : IsAbs (M[x := fvar y]) ↔ IsAbs M := by
  cases M <;> grind

/-- A `BetaAt` step is a full β-step. -/
lemma BetaAt.to_step [DecidableEq Var] (h : BetaAt i M N) (lc : LC M) : M ⭢βᶠ N := by
  induction h with
  | outer lc_M lc_N => exact .base (.beta lc_M lc_N)
  | appNoAbsL _ _ ih | appAbsL _ _ ih =>
    cases lc with
    | app lc_L lc_R => exact .appR lc_R (ih lc_L)
  | appNoAbsR _ _ ih | appAbsR _ _ ih =>
    cases lc with
    | app lc_L lc_R => exact .appL lc_L (ih lc_R)
  | abs xs _ ih =>
    cases lc with
    | abs ys _ h_body =>
      apply Xi.abs (xs ∪ ys)
      intro z hz
      exact ih z (by grind) (h_body z (by grind))

variable [HasFresh Var]

/-- The position of a contracted redex is at most the redex count of the result. -/
lemma BetaAt.le_countRedexes (h : BetaAt i M N) : i ≤ countRedexes N := by
  induction h with
  | outer => exact Nat.zero_le _
  | appNoAbsL => exact le_trans (by omega) (countRedexes_app_le _ _)
  | appAbsL step ha => rw [countRedexes_app_abs (step.isAbs_r ha)]; omega
  | appNoAbsR => exact le_trans (by omega) (countRedexes_app_le _ _)
  | appAbsR _ ha => rw [countRedexes_app_abs ha]; omega
  | abs xs => have := fresh_exists xs; grind [countRedexes_open_fvar, countRedexes]

/-- In a nonempty standard sequence the lower bound is at most the target's redex count. -/
lemma StandardSeq.bound_le (h : StandardSeq n M N) : n ≤ countRedexes N ∨ M = N := by
  induction h with
  | refl => exact .inr rfl
  | head step hni _ ih =>
    left
    rcases ih with hle | rfl
    · omega
    · exact le_trans hni step.le_countRedexes

/-- The leading position of a standard sequence is at most the redex count of its target. -/
lemma StandardSeq.head_le (step : BetaAt i M P) (tail : StandardSeq i P N) :
    i ≤ countRedexes N := by
  rcases tail.bound_le with h | rfl
  · exact h
  · exact step.le_countRedexes

/-- The reduction of an abstraction operator followed by an application sequence
  is a standard sequence. -/
lemma StandardSeq.app_l_trans_abs (hL : StandardSeq n L L') (ha : IsAbs L)
    (hm : countRedexes L' + 1 ≤ m) (hnm : n + 1 ≤ m)
    (hM : StandardSeq m (app L' M) (app L' M')) :
    StandardSeq (n + 1) (app L M) (app L' M') := by
  induction hL with
  | refl => exact hM.mono hnm
  | head step hni tail ih =>
    have hseam := StandardSeq.head_le step tail
    exact .head (step.appAbsL ha) (by omega) (ih (step.isAbs_r ha) hm (by omega) hM)

/-- The reduction of an operator ending in an abstraction followed by an application sequence
  is a standard sequence. -/
lemma StandardSeq.app_l_trans (hL : StandardSeq n L L') (ha : IsAbs L')
    (hm : countRedexes L' + 1 ≤ m) (hnm : n ≤ m)
    (hM : StandardSeq m (app L' M) (app L' M')) : StandardSeq n (app L M) (app L' M') := by
  induction hL
  case refl => exact hM.mono hnm
  case head _ K _ _ _ step hni tail ih =>
    have hseam := StandardSeq.head_le step tail
    by_cases haK : IsAbs K
    · exact .head (step.appAbsL haK) (by omega)
        (app_l_trans_abs tail (step.isAbs_r haK) hm (by omega) hM)
    · exact .head (step.appNoAbsL haK) hni (ih ha hm (by omega) hM)

/-- The reduction of a non-abstraction operator followed by an application sequence
  is a standard sequence. -/
lemma StandardSeq.app_l_trans_noAbs (hL : StandardSeq n L L') (hna : ¬IsAbs L')
    (hm : countRedexes L' ≤ m) (hnm : n ≤ m)
    (hM : StandardSeq m (app L' M) (app L' M')) : StandardSeq n (app L M) (app L' M') := by
  induction hL with
  | refl => exact hM.mono hnm
  | head step hni tail ih =>
    have hseam := StandardSeq.head_le step tail
    have hP := mt tail.isAbs_r hna
    exact .head (step.appNoAbsL (mt step.isAbs_r hP)) hni (ih hna hm (by omega) hM)

/-- If operator and operand each reduce by a standard sequence, so does the application. -/
lemma StandardSeq.app_cong (hL : StandardSeq 0 L L') (hM : StandardSeq 0 M M') :
    StandardSeq 0 (app L M) (app L' M') := by
  by_cases ha : IsAbs L'
  · exact hL.app_l_trans ha (by omega) (Nat.zero_le _) (hM.app_r_abs ha)
  · exact hL.app_l_trans_noAbs ha (by omega) (Nat.zero_le _) (hM.app_r_noAbs ha)

variable [DecidableEq Var]

/-- Standard reduction is preserved by substitution. -/
lemma Standard.subst (hM : M ⭢ₛ M') (hN : N ⭢ₛ N') (x : Var) (lc_N : LC N) (lc_N' : LC N') :
    (M[x := N]) ⭢ₛ (M'[x := N']) := by
  induction hM generalizing N N'
  case fvar =>
    simp only [Term.subst_fvar]
    split
    · exact hN
    · exact fvar _
  case app ihL ihM => exact app (ihL hN lc_N lc_N') (ihM hN lc_N lc_N')
  case abs m m' _ _ ih =>
    apply abs <| free_union [fv] Var
    grind
  case rdx n m' _ lc_m lc_n cbn_m std_p ih =>
    rw [Term.subst_app]
    have std_p_subst := ih hN lc_N lc_N'
    rw [Term.subst_open x N n m' lc_N] at std_p_subst
    exact rdx (subst_lc lc_m lc_N) (subst_lc lc_n lc_N) (CBN.steps_subst x cbn_m lc_N) std_p_subst

/-- A single full β-step is a standard reduction. -/
lemma Standard.of_beta_step (step : M ⭢βᶠ N) (lc_M : LC M) : M ⭢ₛ N := by
  induction step
  case base h_beta => grind [rdx, lc_refl]
  case appL Z A B lc_Z _ ih =>
    cases lc_M
    exact app (lc_refl Z lc_Z) (ih (by assumption))
  case appR Z A B lc_Z _ ih =>
    cases lc_M
    exact app (ih (by assumption)) (lc_refl Z lc_Z)
  case abs ih =>
    apply abs <| free_union [fv] Var
    intro x hx
    exact ih x (by grind) (Term.beta_lc lc_M (by constructor))

open FullBeta in
/-- Standard reduction is contained in full β-reduction. -/
lemma Standard.to_redex (step : M ⭢ₛ N) : M ↠βᶠ N := by
  induction step
  case fvar => rfl
  case app step_L step_M ih_L ih_M =>
    exact .trans (redex_app_l_cong ih_L step_M.lc_l) (redex_app_r_cong ih_M step_L.lc_r)
  case abs xs _ ih => exact FullBeta.redex_abs_cong xs ih
  case rdx n m' _ lc_m lc_n cbn_m std_p ih =>
    have step1 := redex_app_l_cong (CBN.to_redex cbn_m) lc_n
    have step2 : m'.abs.app n ↠βᶠ m' ^ n := .single (.base (.beta (CBN.steps_lc_r lc_m cbn_m) lc_n))
    exact .trans step1 (.trans step2 ih)

/-- If a standard reduction reaches an abstraction, then its leading Call-by-Name
    reduction reaches an abstraction that standardly reduces to the same target. -/
lemma Standard.abs_inv (h : M ⭢ₛ N) (M' : Term Var) (eq : N = Term.abs M') :
    ∃ M'', M ↠ₙ Term.abs M'' ∧ Term.abs M'' ⭢ₛ Term.abs M' := by
  induction h generalizing M'
  case fvar => trivial
  case app => trivial
  case abs m_body m_target xs h_body ih =>
    cases eq
    exact ⟨m_body, .refl, .abs xs h_body⟩
  case rdx m1 n1 m1' p1 lc_m1 lc_n1 cbn_m1 _ ih =>
    have ⟨p'', cbn_body, std_p''⟩ := ih M' eq
    have step1 : m1.app n1 ↠ₙ m1'.abs.app n1 := CBN.steps_app_l_cong cbn_m1 lc_n1
    have step2 : m1'.abs.app n1 ⭢ₙ m1' ^ n1 := .base (.beta (CBN.steps_lc_r lc_m1 cbn_m1) lc_n1)
    exact ⟨p'', .trans step1 (.head step2 cbn_body), std_p''⟩

/-- Standard reduction of abstractions is preserved by opening. -/
lemma Standard.abs_subst
    (h_abs : Term.abs M ⭢ₛ Term.abs M') (hN : N ⭢ₛ N') (lc_N : LC N) (lc_N' : LC N') :
    (M ^ N) ⭢ₛ (M' ^ N') := by
  cases h_abs
  case abs h_body =>
    have ⟨y, _⟩ := fresh_exists <| free_union [fv] Var
    have := subst (h_body y (by grind)) hN y lc_N lc_N'
    grind

/-- A standard reduction followed by a full β-step is a standard reduction. -/
lemma Standard.trans_step (h1 : M ⭢ₛ P) (h2 : P ⭢βᶠ N) : M ⭢ₛ N := by
  induction h1 generalizing N
  case fvar => contradiction
  case rdx lc_L lc_M cbn _ ih => exact .rdx lc_L lc_M cbn (ih h2)
  case abs p_body ih =>
    cases h2
    · grind
    · apply abs <| free_union [fv] Var
      grind
  case app L' _ M _ std_L std_M ih_L ih_M =>
    cases h2
    case appL step_M => exact .app std_L (ih_M step_M)
    case appR step_L _ => exact .app (ih_L step_L) std_M
    case base h_beta =>
      cases h_beta
      have ⟨L, cbn_L1, std_abs⟩ := abs_inv std_L _ rfl
      have std_subst := std_abs.abs_subst std_M std_M.lc_l std_M.lc_r
      have s1 : L'.app M ↠ₙ L.abs.app M := CBN.steps_app_l_cong cbn_L1 std_M.lc_l
      have s2 : L.abs.app M ⭢ₙ L ^ M := .base (.beta (CBN.steps_lc_r std_L.lc_l cbn_L1) std_M.lc_l)
      exact Standard.cbn_trans (.trans s1 (.single s2)) std_subst

/-- A standard reduction followed by a full β-reduction is a standard reduction. -/
lemma Standard.trans_redex (h1 : M ⭢ₛ P) (h2 : P ↠βᶠ N) : M ⭢ₛ N := by
  induction h2 with
  | refl => exact h1
  | tail _ step ih => exact trans_step ih step

/-- Standard reduction is transitive. -/
lemma Standard.trans (h1 : M ⭢ₛ P) (h2 : P ⭢ₛ N) : M ⭢ₛ N :=
  trans_redex h1 (to_redex h2)

instance : Trans (· ⭢ₛ · : Term Var → Term Var → Prop) (· ⭢βᶠ ·) (· ⭢ₛ ·) where
  trans := Standard.trans_step

instance : Trans (· ⭢ₛ · : Term Var → Term Var → Prop) (· ↠βᶠ ·) (· ⭢ₛ ·) where
  trans := Standard.trans_redex

instance : Trans (· ⭢ₛ · : Term Var → Term Var → Prop) (· ⭢ₛ ·) (· ⭢ₛ ·) where
  trans := Standard.trans

/-- The standardization theorem: every full β-reduction is a standard reduction. -/
theorem Standard.standardization (lc_M : LC M) (step : M ↠βᶠ N) : M ⭢ₛ N := by
  induction step with
  | refl => exact lc_refl M lc_M
  | tail _ h_step ih => exact ih.trans (of_beta_step h_step h_step.step_lc_l)

/-- Standard reduction coincides with full β-reduction on locally closed terms. -/
theorem Standard.iff_redex (lc_M : LC M) : M ⭢ₛ N ↔ M ↠βᶠ N :=
  ⟨to_redex, standardization lc_M⟩

/-- Renaming a free variable preserves the position of the contracted redex. -/
lemma BetaAt.rename (h : BetaAt i M M') (x y : Var) :
    BetaAt i (M[x := fvar y]) (M'[x := fvar y]) := by
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
lemma BetaAt.lc_r (h : BetaAt i M M') (lc : LC M) : LC M' := by
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
lemma BetaAt.abs_close {x : Var} (h : BetaAt i M M') (lc : LC M) :
    BetaAt i (M⟦0 ↜ x⟧.abs) (M'⟦0 ↜ x⟧.abs) := by
  apply BetaAt.abs ∅
  intro z _
  have lc' := h.lc_r lc
  have hr : BetaAt i (M[x := fvar z]) (M'[x := fvar z]) := h.rename x z
  grind

/-- Closing a variable and abstracting preserves a standard sequence. -/
lemma StandardSeq.abs_close {x : Var} (h : StandardSeq i M M') (lc : LC M) :
    StandardSeq i (M⟦0 ↜ x⟧.abs) (M'⟦0 ↜ x⟧.abs) := by
  induction h with
  | refl => exact .refl
  | head step hni tail ih => exact .head (step.abs_close lc) hni (ih (step.lc_r lc))

/-- Cofinite congruence rule for standard sequences under an abstraction. -/
lemma StandardSeq.abs_cong (xs : Finset Var)
    (cofin : ∀ x ∉ xs, StandardSeq i (M ^ fvar x) (M' ^ fvar x)) (lc : LC (abs M)) :
    StandardSeq i (abs M) (abs M') := by
  have ⟨w, _⟩ := fresh_exists <| free_union [fv] Var
  rw [open_close w M 0 (by grind), open_close w M' 0 (by grind)]
  have hseq := cofin w (by grind)
  have hlc := beta_lc lc (.fvar w)
  exact hseq.abs_close hlc

/-- A standard sequence is a full β-reduction. -/
lemma StandardSeq.to_redex (h : StandardSeq i M N) (lc_M : LC M) : M ↠βᶠ N := by
  induction h with
  | refl => rfl
  | head step _ _ ih => exact (ih (step.lc_r lc_M)).head (step.to_step lc_M)

/-- A standard reduction gives a standard β-reduction sequence. -/
theorem Standard.to_seq (h : M ⭢ₛ N) : StandardSeq 0 M N := by
  induction h
  case fvar x => exact .refl
  case app _ _ ihL ihM => exact ihL.app_cong ihM
  case abs xs h_body ih => exact .abs_cong xs ih ((Standard.abs xs h_body).lc_l)
  case rdx K P K' _ lc_K lc_P cbn _ ih =>
    have cbn_full : K.app P ↠ₙ K' ^ P :=
      (CBN.steps_app_l_cong cbn lc_P).tail (.base (.beta (CBN.steps_lc_r lc_K cbn) lc_P))
    exact StandardSeq.cbn_head cbn_full ih

/-- A standard β-reduction sequence gives a standard reduction. -/
theorem StandardSeq.to_standard (h : StandardSeq i M N) (lc_M : LC M) : M ⭢ₛ N := by
  induction h with
  | refl => exact Standard.lc_refl _ lc_M
  | head step _ _ ih =>
    exact (Standard.of_beta_step (step.to_step lc_M) lc_M).trans (ih (step.lc_r lc_M))

/-- Standard reduction coincides with the existence of a standard β-reduction sequence. -/
theorem Standard.iff_seq (lc_M : LC M) : M ⭢ₛ N ↔ StandardSeq 0 M N := by
  constructor
  · exact Standard.to_seq
  · intro h
    exact h.to_standard lc_M

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
