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

/-! ## Main definitions -/

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
/-- Reducing the operator advances the position by one when the operator is an abstraction. -/
| appL : BetaAt i M M' → BetaAt (i + if IsAbs M then 1 else 0) (app M N) (app M' N)
/-- Reducing the operand adds the operator's redex count, plus one when it is an abstraction. -/
| appR : BetaAt i M M' →
    BetaAt (i + countRedexes N + if IsAbs N then 1 else 0) (app N M) (app N M')
/-- Reducing under a binder keeps the position. -/
| abs (xs : Finset Var) :
    (∀ x ∉ xs, BetaAt i (M ^ fvar x) (M' ^ fvar x)) → BetaAt i (abs M) (abs M')

/-- A standard β-reduction sequence from `M` to `N`, with lower bound `n` and
    final contracted position `i`. -/
inductive StandardSeq : Nat → Nat → Term Var → Term Var → Prop
/-- The empty reduction sequence. -/
| refl : StandardSeq n n M M
/-- Append a β-step at position `i`, provided the preceding position is at most `i`. -/
| tail : StandardSeq n i M P → BetaAt m P N → i ≤ m → StandardSeq n m M N

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

variable {L L' M M' N N' P : Term Var} {a b i m n : Nat}

/-! ## Basic properties -/

/-- Reducing a non-abstraction operator keeps the position. -/
lemma BetaAt.appNoAbsL (h : BetaAt i M M') (hna : ¬IsAbs M) :
    BetaAt i (app M N) (app M' N) := by
  simpa [if_neg hna] using h.appL

/-- Reducing an abstraction operator advances the position by one. -/
lemma BetaAt.appAbsL (h : BetaAt i M M') (ha : IsAbs M) :
    BetaAt (i + 1) (app M N) (app M' N) := by
  simpa [if_pos ha] using h.appL

/-- Reducing the operand adds the redex count of a non-abstraction operator. -/
lemma BetaAt.appNoAbsR (h : BetaAt i M M') (hna : ¬IsAbs N) :
    BetaAt (i + countRedexes N) (app N M) (app N M') := by
  simpa [if_neg hna] using h.appR (N := N)

/-- Reducing the operand adds the redex count of an abstraction operator, plus one. -/
lemma BetaAt.appAbsR (h : BetaAt i M M') (ha : IsAbs N) :
    BetaAt (i + countRedexes N + 1) (app N M) (app N M') := by
  simpa [if_pos ha] using h.appR (N := N)

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

/-! ## Redex positions -/

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

/-! ## Standard sequences -/

/-- Standard sequences preserve being an abstraction. -/
lemma StandardSeq.isAbs_r (h : StandardSeq m n M N) (ha : IsAbs M) : IsAbs N := by
  induction h with
  | refl => exact ha
  | tail _ step _ ih => exact step.isAbs_r (ih ha)

/-- Prepend a β-step to a standard sequence. -/
lemma StandardSeq.head (step : BetaAt i M P) (hmi : m ≤ i)
    (seq : StandardSeq i n P N) : StandardSeq m n M N := by
  induction seq with
  | refl => exact StandardSeq.refl.tail step hmi
  | tail _ step' hni ih => exact (ih step).tail step' hni

/-- A standard sequence stays standard when preceded by a Call-by-Name reduction. -/
lemma StandardSeq.cbn_head (h : M ↠ₙ P) (hseq : StandardSeq 0 n P N) :
    StandardSeq 0 n M N := by
  induction h with
  | refl => exact hseq
  | tail _ step ih =>
    exact ih (hseq.head (BetaAt.of_cbn_step step) (Nat.le_refl 0))

/-- Right congruence for standard sequences when the operator is an abstraction. -/
lemma StandardSeq.app_r_abs (h : StandardSeq m n M M') (ha : IsAbs L) :
    StandardSeq (m + countRedexes L + 1) (n + countRedexes L + 1)
      (app L M) (app L M') := by
  induction h with
  | refl => exact .refl
  | tail _ step hni ih => exact ih.tail (step.appAbsR ha) (by omega)

/-- Right congruence for standard sequences when the operator is a non-abstraction. -/
lemma StandardSeq.app_r_noAbs (h : StandardSeq m n M M') (hna : ¬IsAbs L) :
    StandardSeq (m + countRedexes L) (n + countRedexes L) (app L M) (app L M') := by
  induction h with
  | refl => exact .refl
  | tail _ step hni ih => exact ih.tail (step.appNoAbsR hna) (by omega)

/-- Right application congruence for standard sequences. -/
lemma StandardSeq.app_r_cong (h : StandardSeq m n M M') :
    ∃ k, StandardSeq 0 k (app L M) (app L M') ∧
      k ≤ n + countRedexes L + (if IsAbs L then 1 else 0) := by
  induction h with
  | refl => exact ⟨0, .refl, Nat.zero_le _⟩
  | tail _ step hni ih =>
    have ⟨k, hseq, hk⟩ := ih
    have happ := step.appR (N := L)
    exact ⟨_, hseq.tail happ (by omega), by omega⟩

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
  | appL _ ih =>
    cases lc with
    | app lc_L lc_R => exact .appR lc_R (ih lc_L)
  | appR _ ih =>
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
  | appL step =>
    split
    · rw [countRedexes_app_abs (step.isAbs_r (by assumption))]
      omega
    · exact le_trans (by omega) (countRedexes_app_le _ _)
  | appR =>
    split
    · rw [countRedexes_app_abs (by assumption)]
      omega
    · exact le_trans (by omega) (countRedexes_app_le _ _)
  | abs xs =>
    have := fresh_exists xs
    grind [countRedexes_open_fvar, countRedexes]

/-- The final position of a nontrivial standard sequence is bounded by its target's redex count. -/
lemma StandardSeq.bound_le_of_ne (h : StandardSeq m n M N) (hne : M ≠ N) :
    n ≤ countRedexes N := by
  cases h with
  | refl => contradiction
  | tail _ step _ => exact step.le_countRedexes

omit [HasFresh Var] in
/-- Left application congruence for standard sequences, including a bound on the final position. -/
lemma StandardSeq.app_l_cong (h : StandardSeq m n L L') :
    ∃ k, StandardSeq 0 k (app L M) (app L' M) ∧
      k ≤ n + (if IsAbs L' then 1 else 0) := by
  induction h
  case refl => exact ⟨0, .refl, Nat.zero_le _⟩
  case tail Q _ _ seq step hni ih =>
    have ⟨c, hc, hc_le⟩ := ih
    by_cases hQ : IsAbs Q
    · have hL' := step.isAbs_r hQ
      have hseq := hc.tail (step.appAbsL hQ) (by simp only [if_pos hQ] at hc_le; omega)
      exact ⟨_, hseq, by rw [if_pos hL']⟩
    · have hseq := hc.tail (step.appNoAbsL hQ) (by simp only [if_neg hQ] at hc_le; omega)
      exact ⟨_, hseq, by split <;> omega⟩

/-- Left application congruence bounded by the redex count of the resulting operator. -/
lemma StandardSeq.app_l_cong_bound (h : StandardSeq m n L L') (hne : L ≠ L') :
    ∃ k, StandardSeq 0 k (app L M) (app L' M) ∧
      k ≤ countRedexes L' + (if IsAbs L' then 1 else 0) := by
  have hn := h.bound_le_of_ne hne
  have ⟨k, hseq, hk⟩ := h.app_l_cong (M := M)
  exact ⟨k, hseq, by omega⟩

omit [HasFresh Var] in
/-- Append an operand step to a standard sequence of applications. -/
lemma StandardSeq.app_r_tail (h : StandardSeq m n (app L M) (app L' N))
    (step : BetaAt i N N')
    (hle : n ≤ i + countRedexes L' + (if IsAbs L' then 1 else 0)) :
    StandardSeq m (i + countRedexes L' + (if IsAbs L' then 1 else 0))
      (app L M) (app L' N') :=
  h.tail step.appR hle

omit [HasFresh Var] in
/-- Compose an application sequence with a standard reduction of its operand. -/
lemma StandardSeq.app_r_trans (h : StandardSeq m n M M')
    (happ : StandardSeq 0 i (app L M) (app L' M))
  (hc : i ≤ countRedexes L' + (if IsAbs L' then 1 else 0)) :
    ∃ d, StandardSeq 0 d (app L M) (app L' M') ∧
      d ≤ n + countRedexes L' + (if IsAbs L' then 1 else 0) := by
  induction h with
  | refl => exact ⟨i, happ, by omega⟩
  | tail _ step hni ih =>
    have ⟨d, hd, hd_le⟩ := ih happ
    have hseq := hd.app_r_tail step (by omega)
    exact ⟨_, hseq, by omega⟩

/-- If operator and operand each reduce by a standard sequence, so does the application. -/
lemma StandardSeq.app_cong (hL : StandardSeq m n L L') (hM : StandardSeq a b M M') :
    ∃ k, StandardSeq 0 k (app L M) (app L' M') := by
  by_cases hLL : L = L'
  · subst hLL
    have ⟨k, hseq, _⟩ := hM.app_r_cong (L := L)
    exact ⟨k, hseq⟩
  · have ⟨_, happ, hbound⟩ := hL.app_l_cong_bound (M := M) hLL
    have ⟨k, hseq, _⟩ := hM.app_r_trans happ hbound
    exact ⟨k, hseq⟩

variable [DecidableEq Var]

/-! ## Standardization -/

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

/-! ## Equivalence with standard sequences -/

/-- Renaming a free variable preserves the position of the contracted redex. -/
lemma BetaAt.rename (h : BetaAt i M M') (x y : Var) :
    BetaAt i (M[x := fvar y]) (M'[x := fvar y]) := by
  induction h with
  | outer lc_M lc_N =>
    rw [subst_open x (fvar y) _ _ (.fvar y)]
    exact .outer (subst_lc lc_M (.fvar y)) (subst_lc lc_N (.fvar y))
  | appL _ ih =>
    split
    · exact ih.appAbsL (isAbs_subst_fvar.mpr (by assumption))
    · exact ih.appNoAbsL (mt isAbs_subst_fvar.mp (by assumption))
  | appR _ ih =>
    rw [← countRedexes_subst_fvar _ x y]
    split
    · exact ih.appAbsR (isAbs_subst_fvar.mpr (by assumption))
    · exact ih.appNoAbsR (mt isAbs_subst_fvar.mp (by assumption))
  | abs =>
    apply BetaAt.abs <| free_union [fv] Var
    grind

/-- Contracting a redex preserves local closure. -/
lemma BetaAt.lc_r (h : BetaAt i M M') (lc : LC M) : LC M' := by
  induction h with
  | outer lc_M lc_N => exact beta_lc lc_M lc_N
  | appL _ ih =>
    cases lc with
    | app lc_L lc_R => exact .app (ih lc_L) lc_R
  | appR _ ih =>
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

/-- Standard sequences preserve local closure. -/
lemma StandardSeq.lc_r (h : StandardSeq m n M N) (lc : LC M) : LC N := by
  induction h with
  | refl => exact lc
  | tail _ step _ ih => exact step.lc_r (ih lc)

/-- Closing a variable and abstracting preserves a standard sequence. -/
lemma StandardSeq.abs_close {x : Var} (h : StandardSeq m n M M') (lc : LC M) :
    StandardSeq m n (M⟦0 ↜ x⟧.abs) (M'⟦0 ↜ x⟧.abs) := by
  induction h with
  | refl => exact .refl
  | tail seq step hni ih => exact (ih lc).tail (step.abs_close (seq.lc_r lc)) hni

/-- Abstraction congruence for standard sequences. -/
lemma StandardSeq.abs_cong (xs : Finset Var)
    (cofin : ∀ x ∉ xs, ∃ n, StandardSeq 0 n (M ^ fvar x) (M' ^ fvar x))
    (lc : LC (abs M)) : ∃ n, StandardSeq 0 n (abs M) (abs M') := by
  have ⟨w, _⟩ := fresh_exists <| free_union [fv] Var
  have ⟨n, hseq⟩ := cofin w (by grind)
  have hlc := beta_lc lc (.fvar w)
  have habs : StandardSeq 0 n (abs M) (abs M') := by
    rw [open_close w M 0 (by grind), open_close w M' 0 (by grind)]
    exact hseq.abs_close hlc
  exact ⟨n, habs⟩

/-- A standard sequence is a full β-reduction. -/
lemma StandardSeq.to_redex (h : StandardSeq m n M N) (lc_M : LC M) : M ↠βᶠ N := by
  induction h with
  | refl => rfl
  | tail seq step _ ih => exact (ih lc_M).tail (step.to_step (seq.lc_r lc_M))

/-- A standard reduction gives a standard β-reduction sequence. -/
theorem Standard.to_seq (h : M ⭢ₛ N) : ∃ n, StandardSeq 0 n M N := by
  induction h
  case fvar x => exact ⟨0, .refl⟩
  case app _ _ ihL ihM =>
    have ⟨_, hL⟩ := ihL
    have ⟨_, hM⟩ := ihM
    exact hL.app_cong hM
  case abs xs h_body ih => exact StandardSeq.abs_cong xs ih ((Standard.abs xs h_body).lc_l)
  case rdx K P K' _ lc_K lc_P cbn _ ih =>
    have ⟨_, hk⟩ := ih
    have cbn_full : K.app P ↠ₙ K' ^ P :=
      (CBN.steps_app_l_cong cbn lc_P).tail (.base (.beta (CBN.steps_lc_r lc_K cbn) lc_P))
    exact ⟨_, StandardSeq.cbn_head cbn_full hk⟩

/-- A standard β-reduction sequence gives a standard reduction. -/
theorem StandardSeq.to_standard (h : StandardSeq m n M N) (lc_M : LC M) : M ⭢ₛ N := by
  induction h with
  | refl => exact Standard.lc_refl _ lc_M
  | tail seq step _ ih => exact (ih lc_M).trans_step (step.to_step (seq.lc_r lc_M))

/-- Standard reduction coincides with the existence of a standard β-reduction sequence. -/
theorem Standard.iff_seq (lc_M : LC M) : M ⭢ₛ N ↔ ∃ n, StandardSeq 0 n M N := by
  constructor
  · exact Standard.to_seq
  · intro ⟨_, h⟩
    exact h.to_standard lc_M

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
