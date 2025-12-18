/-
Copyright (c) 2025 Maximiliano Onofre Martínez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximiliano Onofre Martínez
-/

import Cslib.Algorithms.Lean.TimeM
import Mathlib.Data.Nat.Cast.Order.Ring

namespace Cslib.Algorithms.Lean.TimeM

variable {α : Type} [LinearOrder α]

def insert : α → List α → TimeM (List α)
  | x, [] => return [x]
  | x, y :: ys => do
    let c ← ✓ (x ≤ y : Bool)
    if c then
      return (x :: y :: ys)
    else
      let rest ← insert x ys
      return (y :: rest)

def insertionSort : List α → TimeM (List α)
  | [] => return []
  | x :: xs => do
    let sorted ← insertionSort xs
    insert x (sorted)

section Correctness

open List

abbrev IsSorted (l : List α) : Prop := List.Pairwise (· ≤ ·) l

theorem insert_perm (x : α) (l : List α) : ⟪insert x l⟫ ~ x :: l := by
  fun_induction insert x l
  · rfl
  · simp only [Bind.bind, Pure.pure]
    grind

theorem insert_sorted {x : α} {l : List α} (h : IsSorted l) : IsSorted ⟪insert x l⟫ := by
  fun_induction insert x l
  · simp
  · simp only [bind, pure, Bind.bind, Pure.pure]
    split_ifs
    · grind
    · constructor
      · intro a ha
        rw [List.Perm.mem_iff (insert_perm _ _)] at ha
        simp only [IsSorted, List.pairwise_cons] at h
        grind
      · grind

theorem insertionSort_perm (xs : List α) : ⟪insertionSort xs⟫ ~ xs := by
  fun_induction insertionSort xs with
  | case1 => rfl
  | case2 y ys ih =>
    simp only [Bind.bind, ret_bind]
    trans y :: ⟪insertionSort ys⟫
    · apply insert_perm
    · apply Perm.cons
      exact ih

theorem insertionSort_sorted (xs : List α) : IsSorted ⟪insertionSort xs⟫ := by
  fun_induction insertionSort xs with
  | case1 => simp
  | case2 x xs ih =>
    apply insert_sorted
    exact ih

theorem insertionSort_correct (xs : List α) :
  IsSorted ⟪insertionSort xs⟫ ∧ ⟪insertionSort xs⟫ ~ xs :=
    ⟨insertionSort_sorted xs, insertionSort_perm xs⟩

end Correctness

section TimeComplexity

def timeInsertionSortRec : ℕ → ℕ
  | 0 => 0
  | n + 1 => timeInsertionSortRec n + n

@[simp] theorem insert_length (x : α) (xs : List α) :
    ⟪insert x xs⟫.length = xs.length + 1 := by
  fun_induction insert
  · rfl
  · simp only [bind, pure, Bind.bind, Pure.pure]
    split_ifs <;> grind

theorem insertionSort_length (xs : List α) :
    ⟪insertionSort xs⟫.length = xs.length := by
  fun_induction insertionSort xs with
  | case1 => rfl
  | case2 _ _ ih => simp [ih]

theorem insert_time_le (x : α) (ys : List α) : (insert x ys).time ≤ ys.length := by
  fun_induction insert x ys
  · simp
  · simp only [Bind.bind, time_of_bind]
    split_ifs
    · aesop
    · simp only [Pure.pure]
      grind

theorem insertionSort_time_le_rec (xs : List α) :
    (insertionSort xs).time ≤ timeInsertionSortRec xs.length := by
  fun_induction insertionSort xs with
  | case1 => simp
  | case2 x xs _ =>
    simp only [Bind.bind]
    have h_ins := insert_time_le x ⟪insertionSort xs⟫
    rw [insertionSort_length] at h_ins
    unfold timeInsertionSortRec
    grind

theorem timeInsertionSortRec_eq (n : ℕ) : timeInsertionSortRec n = n * (n - 1) / 2 := by
  induction n with
  | zero => rw [timeInsertionSortRec]
  | succ n ih =>
    simp only [timeInsertionSortRec, ih, Nat.add_sub_cancel]
    apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2)
    rw [Nat.add_mul]
    rw [Nat.div_mul_cancel, Nat.div_mul_cancel]
    · rw [←Nat.mul_add]
      cases n with
      | zero =>
        simp
      | succ k =>
        simp only [Nat.add_sub_cancel]
        rw [Nat.mul_comm]
    · rw [Nat.mul_comm]
      exact (Nat.even_mul_succ_self n).two_dvd
    · cases n with
      | zero =>
        simp
      | succ k =>
        simp only [Nat.add_sub_cancel]
        rw [Nat.mul_comm]
        exact (Nat.even_mul_succ_self k).two_dvd

theorem insertionSort_time (xs : List α) :
    (insertionSort xs).time ≤ xs.length * xs.length := by
  have h := insertionSort_time_le_rec xs
  rw [timeInsertionSortRec_eq] at h
  apply Nat.le_trans h
  have h_div : xs.length * (xs.length - 1) / 2 ≤ xs.length * (xs.length - 1) :=
    Nat.div_le_self _ 2
  apply Nat.le_trans h_div
  apply Nat.mul_le_mul_left
  apply Nat.sub_le

end TimeComplexity

end Cslib.Algorithms.Lean.TimeM
