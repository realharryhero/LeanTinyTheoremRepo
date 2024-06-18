import «Leanprojectcoolio2»

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Floor
import Mathlib.Algebra.Associated
import Mathlib.Algebra.BigOperators.Basic

import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.GeomSum
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Commute.Hom
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Algebra.GroupPower.Identities
import Mathlib.Algebra.Order.Floor
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card

import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Parity
import Mathlib.Data.List.Intervals
import Mathlib.Data.List.Palindrome
import Mathlib.Data.Multiset.Basic

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Digits
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Fib.Zeckendorf
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Nat.Prime
import Mathlib.Data.PNat.Basic
import Mathlib.Data.PNat.Prime

import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Denumerable
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Rat.Field
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rat.Order
import Mathlib.Data.Rat.Sqrt

import Mathlib.Data.Rat.Star
import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Real.Sqrt

import Mathlib.Data.Set.Finite
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.FixedPoints.Basic

import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.AffineSpace.Ordered
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Logic.Equiv.Basic

import Mathlib.Order.Filter.Basic

import Mathlib.Order.WellFounded
import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.NNReal

import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Int.Basic


import Aesop
import ProofWidgets
open BigOperators

open Nat

open Real

open Rat


theorem lean_workbook_18_0 : (29 * 31 + 37 - 41) % 4 = 3 := by
  simp [Nat.mod_lt]
theorem lean_workbook_18_1 : (29 * 31 + 37 - 41) % 4 = 3 := by
  simp only [Nat.add_mod_left, Nat.mod_eq_zero_of_dvd, dvd_pow]
theorem lean_workbook_18_2 : (29 * 31 + 37 - 41) % 4 = 3 := by
  simp only [Nat.gcd_add_self_right]
theorem lean_workbook_18_3 : (29 * 31 + 37 - 41) % 4 = 3 := by
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
theorem lean_workbook_18_4 : (29 * 31 + 37 - 41) % 4 = 3 := by
  simp only [Nat.mod_add_div]
theorem lean_workbook_18_5 : (29 * 31 + 37 - 41) % 4 = 3 := by
  exact (by norm_num : (29 * 31 + 37 - 41) % 4 = 3)
theorem lean_workbook_18_6 : (29 * 31 + 37 - 41) % 4 = 3 := by
  simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
theorem lean_workbook_18_7 : (29 * 31 + 37 - 41) % 4 = 3 := by
  norm_num [Int.add_emod]
theorem lean_workbook_18_8 : (29 * 31 + 37 - 41) % 4 = 3 := by
  simp only [Nat.mul_mod_right]
theorem lean_workbook_18_9 : (29 * 31 + 37 - 41) % 4 = 3 := by
  simp only [add_comm]
theorem lean_workbook_18_10 : (29 * 31 + 37 - 41) % 4 = 3 := by
  simp only [Nat.gcd]
theorem lean_workbook_18_11 : (29 * 31 + 37 - 41) % 4 = 3 := by
  simp only [Nat.mod_eq_zero_of_dvd, dvd_pow]
theorem lean_workbook_18_12 : (29 * 31 + 37 - 41) % 4 = 3 := by
  simp only [Nat.mul_mod, Nat.mod_mod]
theorem lean_workbook_18_13 : (29 * 31 + 37 - 41) % 4 = 3 := by
  simp [Mod.mod]
theorem lean_workbook_18_14 : (29 * 31 + 37 - 41) % 4 = 3 := by
  simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.sub_sub]
theorem lean_workbook_18_15 : (29 * 31 + 37 - 41) % 4 = 3 := by
  simp only [Nat.add_comm, Nat.add_left_comm]
theorem lean_workbook_18_16 : (29 * 31 + 37 - 41) % 4 = 3 := by
  simp only [Nat.add_sub_assoc, Nat.mod_self]
theorem lean_workbook_18_17 : (29 * 31 + 37 - 41) % 4 = 3 := by
  simp only [mod_eq_sub_mod]
theorem lean_workbook_18_18 : (29 * 31 + 37 - 41) % 4 = 3 := by
  norm_num [Nat.mod_eq_of_lt]
theorem lean_workbook_18_19 : (29 * 31 + 37 - 41) % 4 = 3 := by
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, Nat.mod_eq_zero_of_dvd]
theorem lean_workbook_18_20 : (29 * 31 + 37 - 41) % 4 = 3 := by
  exact Nat.mod_mod 3 4
theorem lean_workbook_18_21 : (29 * 31 + 37 - 41) % 4 = 3 := by
  norm_num [Nat.mul_mod, Nat.add_mod, Nat.mod_mod]
theorem lean_workbook_18_22 : (29 * 31 + 37 - 41) % 4 = 3 := by
  simp only [Nat.mod_mod]
theorem lean_workbook_18_23 : (29 * 31 + 37 - 41) % 4 = 3 := by
  exact rfl
theorem lean_workbook_18_24 : (29 * 31 + 37 - 41) % 4 = 3 := by
  simp only [Nat.add_sub_assoc]

theorem lean_workbook_26_0 (x : ℝ) (hx : 0 < x) : x - 1 ≥ Real.log x := by
  have h1 : 0 ≤ (x - 1)^2 := sq_nonneg (x - 1)
  nlinarith [log_le_sub_one_of_pos hx]
theorem lean_workbook_26_1 (x : ℝ) (hx : 0 < x) : x - 1 ≥ Real.log x := by
  nlinarith [log_le_sub_one_of_pos hx]
theorem lean_workbook_26_2 (x : ℝ) (hx : 0 < x) : x - 1 ≥ Real.log x := by
  rw [ge_iff_le]
  simpa using log_le_sub_one_of_pos hx
theorem lean_workbook_26_3 (x : ℝ) (hx : 0 < x) : x - 1 ≥ Real.log x := by
  have := log_le_sub_one_of_pos hx
  linarith [this]
theorem lean_workbook_26_4 (x : ℝ) (hx : 0 < x) : x - 1 ≥ Real.log x := by
  nlinarith [Real.log_le_sub_one_of_pos (by linarith : 0 < x)]
theorem lean_workbook_26_5 (x : ℝ) (hx : 0 < x) : x - 1 ≥ Real.log x := by
  nlinarith [log_le_sub_one_of_pos (by assumption : 0 < x)]
theorem lean_workbook_26_6 (x : ℝ) (hx : 0 < x) : x - 1 ≥ Real.log x := by
  have := log_le_sub_one_of_pos hx
  linarith
theorem lean_workbook_26_7 (x : ℝ) (hx : 0 < x) : x - 1 ≥ Real.log x := by
  nlinarith [Real.log_le_sub_one_of_pos hx]
theorem lean_workbook_26_8 (x : ℝ) (hx : 0 < x) : x - 1 ≥ Real.log x := by
  have h1 : 0 ≤ (x - 1) ^ 2 := sq_nonneg (x - 1)
  rw [pow_two] at h1
  nlinarith [log_le_sub_one_of_pos hx]
theorem lean_workbook_26_9 (x : ℝ) (hx : 0 < x) : x - 1 ≥ Real.log x := by
  linarith [log_le_sub_one_of_pos hx]
theorem lean_workbook_26_10 (x : ℝ) (hx : 0 < x) : x - 1 ≥ Real.log x := by
  rw [ge_iff_le]
  exact log_le_sub_one_of_pos hx
theorem lean_workbook_26_11 (x : ℝ) (hx : 0 < x) : x - 1 ≥ Real.log x := by
  rw [ge_iff_le]
  nlinarith [log_le_sub_one_of_pos hx]
theorem lean_workbook_26_12 (x : ℝ) (hx : 0 < x) : x - 1 ≥ Real.log x := by
  linarith only [log_le_sub_one_of_pos hx]
theorem lean_workbook_26_13 (x : ℝ) (hx : 0 < x) : x - 1 ≥ Real.log x := by
  have h1 : 0 ≤ (x - 1) ^ 2 := sq_nonneg (x - 1)
  nlinarith [Real.log_le_sub_one_of_pos hx]
theorem lean_workbook_26_14 (x : ℝ) (hx : 0 < x) : x - 1 ≥ Real.log x := by
  nlinarith [Real.log_le_sub_one_of_pos (by positivity : 0 < x)]

theorem lean_workbook_29_0 (a b c : ℝ) : (a + c) ^ 2 + 3 * b ^ 2 ≥ 3 * a * b + 3 * b * c + a * c := by
  have h1 : 0 ≤ (a - b)^2 + (b - c)^2 := by nlinarith
  nlinarith
theorem lean_workbook_29_1 (a b c : ℝ) : (a + c) ^ 2 + 3 * b ^ 2 ≥ 3 * a * b + 3 * b * c + a * c := by
  rw [add_comm]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_29_2 (a b c : ℝ) : (a + c) ^ 2 + 3 * b ^ 2 ≥ 3 * a * b + 3 * b * c + a * c := by
  ring_nf
  field_simp
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c)]
theorem lean_workbook_29_3 (a b c : ℝ) : (a + c) ^ 2 + 3 * b ^ 2 ≥ 3 * a * b + 3 * b * c + a * c := by
  rw [add_comm]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c)]
theorem lean_workbook_29_4 (a b c : ℝ) : (a + c) ^ 2 + 3 * b ^ 2 ≥ 3 * a * b + 3 * b * c + a * c := by
  ring_nf
  ring_nf
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c)]
theorem lean_workbook_29_5 (a b c : ℝ) : (a + c) ^ 2 + 3 * b ^ 2 ≥ 3 * a * b + 3 * b * c + a * c := by
  rw [add_sq]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_29_6 (a b c : ℝ) : (a + c) ^ 2 + 3 * b ^ 2 ≥ 3 * a * b + 3 * b * c + a * c := by
  simp [sq]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_29_7 (a b c : ℝ) : (a + c) ^ 2 + 3 * b ^ 2 ≥ 3 * a * b + 3 * b * c + a * c := by
  nlinarith [sq_nonneg (a - c), sq_nonneg (a - b), sq_nonneg (c - b)]
theorem lean_workbook_29_8 (a b c : ℝ) : (a + c) ^ 2 + 3 * b ^ 2 ≥ 3 * a * b + 3 * b * c + a * c := by
  ring_nf
  nlinarith [sq_nonneg (b - a), sq_nonneg (b - c)]
theorem lean_workbook_29_9 (a b c : ℝ) : (a + c) ^ 2 + 3 * b ^ 2 ≥ 3 * a * b + 3 * b * c + a * c := by
  ring_nf
  ring_nf
  ring_nf
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c)]
theorem lean_workbook_29_10 (a b c : ℝ) : (a + c) ^ 2 + 3 * b ^ 2 ≥ 3 * a * b + 3 * b * c + a * c := by
  nlinarith [sq_nonneg (a + c), sq_nonneg (b - a), sq_nonneg (b - c)]

theorem lean_workbook_31_0 (a b c : ℝ) : a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
  ring_nf
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_31_1 (a b c : ℝ) : a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
  simp [sq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_comm, mul_assoc, mul_left_comm]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_31_2 (a b c : ℝ) : a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
  simp [sq]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c)]
theorem lean_workbook_31_3 (a b c : ℝ) : a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
  simp [sq, sub_eq_add_neg]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_31_4 (a b c : ℝ) : a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
  have h₁ : 0 ≤ (a - b)^2 + (b - c)^2 + (c - a)^2 := by nlinarith
  linarith
theorem lean_workbook_31_5 (a b c : ℝ) : a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
  have : 0 ≤ (a - b)^2 + (b - c)^2 + (c - a)^2 := by nlinarith
  linarith
theorem lean_workbook_31_6 (a b c : ℝ) : a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
  have h₁ : 0 ≤ (a - b)^2 + (b - c)^2 + (c - a)^2 := by positivity
  linarith
theorem lean_workbook_31_7 (a b c : ℝ) : a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
  nlinarith [pow_two_nonneg (a - b), pow_two_nonneg (b - c), pow_two_nonneg (c - a)]
theorem lean_workbook_31_8 (a b c : ℝ) : a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
  have h₁ := sq_nonneg (a - b)
  have h₂ := sq_nonneg (b - c)
  have h₃ := sq_nonneg (c - a)
  linarith
theorem lean_workbook_31_9 (a b c : ℝ) : a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_31_10 (a b c : ℝ) : a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
  simp [add_comm]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_31_11 (a b c : ℝ) : a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
  ring_nf
  simp [sq]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_31_12 (a b c : ℝ) : a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
  rw [sq]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_31_13 (a b c : ℝ) : a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
  simp [sq]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_31_14 (a b c : ℝ) : a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
  have h1 : 0 ≤ (a - b)^2 + (b - c)^2 + (a - c)^2 := by positivity
  linarith
theorem lean_workbook_31_15 (a b c : ℝ) : a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
  ring_nf
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_31_16 (a b c : ℝ) : a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
  have := sq_nonneg (a - b + c)
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_31_17 (a b c : ℝ) : a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
  have h0 := sq_nonneg (a - b)
  have h1 := sq_nonneg (b - c)
  have h2 := sq_nonneg (a - c)
  linarith [h0, h1, h2]
theorem lean_workbook_31_18 (a b c : ℝ) : a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
  simp [sq, mul_comm, mul_assoc, mul_left_comm]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_31_19 (a b c : ℝ) : a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_31_20 (a b c : ℝ) : a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
  have : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ 0 := by nlinarith
  linarith
theorem lean_workbook_31_21 (a b c : ℝ) : a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
  simp [sq, add_comm, add_left_comm, add_assoc]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_31_22 (a b c : ℝ) : a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
  have h : 0 ≤ (a - b)^2 + (b - c)^2 + (c - a)^2 := by nlinarith
  linarith

theorem lean_workbook_32_0 : 2 * 1^2 + 1 ≤ 3^1 := by
  simp [Nat.pow_one]
theorem lean_workbook_32_1 : 2 * 1^2 + 1 ≤ 3^1 := by
  rw [pow_one]
  norm_num
theorem lean_workbook_32_2 : 2 * 1^2 + 1 ≤ 3^1 := by
  simp only [pow_one, mul_one, add_comm]
  norm_num
theorem lean_workbook_32_3 : 2 * 1^2 + 1 ≤ 3^1 := by
  simp [sq]
theorem lean_workbook_32_4 : 2 * 1^2 + 1 ≤ 3^1 := by
  simp [Nat.pow_succ]
theorem lean_workbook_32_5 : 2 * 1^2 + 1 ≤ 3^1 := by
  simp [pow_two, mul_add, mul_one, add_mul, one_mul, mul_comm, mul_left_comm]
theorem lean_workbook_32_6 : 2 * 1^2 + 1 ≤ 3^1 := by
  norm_num [Nat.pow_zero, Nat.pow_one]
theorem lean_workbook_32_7 : 2 * 1^2 + 1 ≤ 3^1 := by
  simp [show 3 ^ 1 = 3 from rfl]
theorem lean_workbook_32_8 : 2 * 1^2 + 1 ≤ 3^1 := by
  simp [Nat.pow_succ, Nat.pow_zero]
theorem lean_workbook_32_9 : 2 * 1^2 + 1 ≤ 3^1 := by
  norm_num [pow_one, pow_two, mul_one]
theorem lean_workbook_32_10 : 2 * 1^2 + 1 ≤ 3^1 := by
  simp [mul_one]
theorem lean_workbook_32_11 : 2 * 1^2 + 1 ≤ 3^1 := by
  simp [Nat.pow_succ, Nat.mul_succ, Nat.add_succ, Nat.add_zero, Nat.mul_zero, Nat.zero_le]
theorem lean_workbook_32_12 : 2 * 1^2 + 1 ≤ 3^1 := by
  rw [pow_two]
  linarith [pow_two (3 : ℕ)]
theorem lean_workbook_32_13 : 2 * 1^2 + 1 ≤ 3^1 := by
  norm_num [pow_two, pow_one, mul_one]
theorem lean_workbook_32_14 : 2 * 1^2 + 1 ≤ 3^1 := by
  simp only [Nat.one_pow, Nat.mul_one, Nat.add_one]
  norm_num
theorem lean_workbook_32_15 : 2 * 1^2 + 1 ≤ 3^1 := by
  simp only [pow_one, mul_one]
  norm_num
theorem lean_workbook_32_16 : 2 * 1^2 + 1 ≤ 3^1 := by
  norm_num [show (1 : ℤ) = 1 by rfl]
theorem lean_workbook_32_17 : 2 * 1^2 + 1 ≤ 3^1 := by
  simp [Nat.pow_zero]
theorem lean_workbook_32_18 : 2 * 1^2 + 1 ≤ 3^1 := by
  norm_num [Nat.pow_zero]
theorem lean_workbook_32_19 : 2 * 1^2 + 1 ≤ 3^1 := by
  simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
theorem lean_workbook_32_20 : 2 * 1^2 + 1 ≤ 3^1 := by
  simp [sq, mul_add, mul_comm, mul_left_comm]
theorem lean_workbook_32_21 : 2 * 1^2 + 1 ≤ 3^1 := by
  norm_num [pow_succ]
theorem lean_workbook_32_22 : 2 * 1^2 + 1 ≤ 3^1 := by
  simp [add_comm]
theorem lean_workbook_32_23 : 2 * 1^2 + 1 ≤ 3^1 := by
  norm_num [Nat.pow_succ]
theorem lean_workbook_32_24 : 2 * 1^2 + 1 ≤ 3^1 := by
  simp [sq, mul_add, mul_one, add_mul, one_mul]
theorem lean_workbook_32_25 : 2 * 1^2 + 1 ≤ 3^1 := by
  norm_num [show (2 : ℤ) * 1^2 + 1 = 3 by norm_num]
theorem lean_workbook_32_26 : 2 * 1^2 + 1 ≤ 3^1 := by
  simp [Nat.zero_eq]
theorem lean_workbook_32_27 : 2 * 1^2 + 1 ≤ 3^1 := by
  norm_num [show (2 : ℤ) * 1^2 + 1 = 3 by norm_num1]
theorem lean_workbook_32_28 : 2 * 1^2 + 1 ≤ 3^1 := by
  simp [Nat.pow_succ, Nat.mul_succ, Nat.add_succ, Nat.add_assoc]

theorem lean_workbook_43_0 (a b : ℝ) : a ^ 4 + b ^ 4 + 2 ≥ 4 * a * b := by
  have h1 := sq_nonneg (a ^ 2 - b ^ 2)
  have h2 := sq_nonneg (a ^ 2 + b ^ 2 - 2)
  ring_nf at h1 h2
  nlinarith
theorem lean_workbook_43_1 (a b : ℝ) : a ^ 4 + b ^ 4 + 2 ≥ 4 * a * b := by
  ring_nf
  ring_nf
  nlinarith [sq_nonneg (a ^ 2 + b ^ 2 - 2), sq_nonneg (a ^ 2 - b ^ 2)]
theorem lean_workbook_43_2 (a b : ℝ) : a ^ 4 + b ^ 4 + 2 ≥ 4 * a * b := by
  field_simp [pow_two]
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (2 * a * b - 2)]

theorem lean_workbook_96_0 (x y : ℝ) : |(abs x) - (abs y)| ≤ abs (x - y) := by
  eta_reduce at *
  rw [abs_sub_comm]
  eta_reduce at *
  rw [abs_sub_comm]
  rw [← abs_neg, neg_sub]
  eta_reduce at *
  rw [abs_sub_comm]
  exact?
theorem lean_workbook_96_1 (x y : ℝ) : |(abs x) - (abs y)| ≤ abs (x - y) := by
  have h₁ := abs_abs_sub_abs_le_abs_sub x y
  exact h₁
theorem lean_workbook_96_2 (x y : ℝ) : |(abs x) - (abs y)| ≤ abs (x - y) := by
  rw [abs_sub_comm]
  rw [abs_sub_comm]
  apply abs_abs_sub_abs_le_abs_sub

theorem lean_workbook_98_0 : 2^(0 + 1) = 2 := by
  simp only [Nat.zero_add, pow_one, eq_self_iff_true, and_self_iff]
theorem lean_workbook_98_1 : 2^(0 + 1) = 2 := by
  simp [Nat.pow_succ, Nat.pow_zero, Nat.mul_one]
theorem lean_workbook_98_2 : 2^(0 + 1) = 2 := by
  simp only [Nat.zero_add, pow_one]
theorem lean_workbook_98_3 : 2^(0 + 1) = 2 := by
  norm_num [Nat.pow_zero, Nat.pow_succ]
theorem lean_workbook_98_4 : 2^(0 + 1) = 2 := by
  simp [pow_succ, pow_zero, mul_one]
theorem lean_workbook_98_5 : 2^(0 + 1) = 2 := by
  field_simp [pow_zero]
theorem lean_workbook_98_6 : 2^(0 + 1) = 2 := by
  simp [show (0 : ℕ) = 0 from rfl]
theorem lean_workbook_98_7 : 2^(0 + 1) = 2 := by
  norm_num [Nat.pow_zero]
theorem lean_workbook_98_8 : 2^(0 + 1) = 2 := by
  simp [add_comm, pow_succ]
theorem lean_workbook_98_9 : 2^(0 + 1) = 2 := by
  norm_num [pow_add, pow_one]
theorem lean_workbook_98_10 : 2^(0 + 1) = 2 := by
  norm_num [pow_succ, pow_zero]
theorem lean_workbook_98_11 : 2^(0 + 1) = 2 := by
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
theorem lean_workbook_98_12 : 2^(0 + 1) = 2 := by
  norm_num [Nat.pow_succ, Nat.pow_zero]
theorem lean_workbook_98_13 : 2^(0 + 1) = 2 := by
  norm_num [pow_succ]
theorem lean_workbook_98_14 : 2^(0 + 1) = 2 := by
  simp [Nat.pow_succ]
theorem lean_workbook_98_15 : 2^(0 + 1) = 2 := by
  simp only [Nat.succ_eq_add_one, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
theorem lean_workbook_98_16 : 2^(0 + 1) = 2 := by
  rw [pow_succ]
  norm_num
theorem lean_workbook_98_17 : 2^(0 + 1) = 2 := by
  simp [Nat.pow_zero]
theorem lean_workbook_98_18 : 2^(0 + 1) = 2 := by
  simp [Nat.pow_add, Nat.pow_one]
theorem lean_workbook_98_19 : 2^(0 + 1) = 2 := by
  norm_num [Nat.zero_add, Nat.pow_succ]
theorem lean_workbook_98_20 : 2^(0 + 1) = 2 := by
  simp [Nat.pow_zero, Nat.pow_succ]
theorem lean_workbook_98_21 : 2^(0 + 1) = 2 := by
  simp only [Nat.pow_zero, Nat.pow_succ, Nat.one_mul]
theorem lean_workbook_98_22 : 2^(0 + 1) = 2 := by
  rw [pow_one]
theorem lean_workbook_98_23 : 2^(0 + 1) = 2 := by
  simp only [pow_succ, pow_zero, one_mul]
theorem lean_workbook_98_24 : 2^(0 + 1) = 2 := by
  norm_num [Nat.pow_succ]
theorem lean_workbook_98_25 : 2^(0 + 1) = 2 := by
  norm_num [←Nat.pow_succ]
theorem lean_workbook_98_26 : 2^(0 + 1) = 2 := by
  simp [Nat.add_zero, Nat.pow_one]

theorem lean_workbook_101_0 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  rw [hx]
  norm_num [pow_succ, pow_zero, mul_one]
theorem lean_workbook_101_1 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  subst hx
  norm_num
theorem lean_workbook_101_2 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  simp [hx, show 2 ^ 9 = 512 by norm_num]
theorem lean_workbook_101_3 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  simp only [hx, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
theorem lean_workbook_101_4 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  linarith [hx]
theorem lean_workbook_101_5 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  linarith [pow_one 2]
theorem lean_workbook_101_6 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  rw [hx, show (2:ℕ)^9 + 1 = 513 by norm_num1]
theorem lean_workbook_101_7 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  field_simp [hx]
  ring
theorem lean_workbook_101_8 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  subst hx
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
theorem lean_workbook_101_9 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  conv_lhs => rw [hx]; norm_num
theorem lean_workbook_101_10 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  subst hx
  rfl
theorem lean_workbook_101_11 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  rw [hx]
  ring_nf
theorem lean_workbook_101_12 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  rw [hx]
  norm_num [Nat.pow_succ]
theorem lean_workbook_101_13 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  simp only [hx, add_comm]
  norm_num [hx]
theorem lean_workbook_101_14 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  simp only [hx, show 2 ^ 9 + 1 = 513 by norm_num]
theorem lean_workbook_101_15 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  simp [hx, show (2 : ℕ) ^ 9 + 1 = 513 by norm_num]
theorem lean_workbook_101_16 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  simp [hx] at *
: ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  simp only [hx, Nat.pow_succ]
theorem lean_workbook_101_23 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  exact hx.trans (by norm_num)
theorem lean_workbook_101_24 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  rw [hx, add_comm]
  norm_num [pow_succ, pow_zero]
theorem lean_workbook_101_25 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  rw [hx]
  norm_num [show 2^9 = 512 by rfl]
theorem lean_workbook_101_26 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  conv_lhs => rw [hx]
theorem lean_workbook_101_27 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  norm_num at hx ⊢
  exact hx
theorem lean_workbook_101_28 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  rw [hx, show (2^9 + 1 : ℕ) = 513 by norm_num1]
theorem lean_workbook_101_29 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  simp [hx, pow_succ, mul_one]

theorem lean_workbook_102_0 (p : ℝ) (h₀ : 8 * p^2 - 8 * p - 3 ≠ 0) (h₁ : 3 - (4 * p + 3) ≠ 0) : (3 - (4 * p + 3)) / (8 * p^2 - 8 * p - 3) = (-4 * p) / (8 * p^2 - 8 * p - 3) := by
  rw [div_eq_mul_inv]
  field_simp
theorem lean_workbook_102_1 (p : ℝ) (h₀ : 8 * p^2 - 8 * p - 3 ≠ 0) (h₁ : 3 - (4 * p + 3) ≠ 0) : (3 - (4 * p + 3)) / (8 * p^2 - 8 * p - 3) = (-4 * p) / (8 * p^2 - 8 * p - 3) := by
  have h₂ : 3 - (4 * p + 3) = -4 * p := by linarith
  rw [h₂]

theorem lean_workbook_136_0 (n : ℕ) : (4*n ≡ 4 [ZMOD 12] → n-1 ≡ 0 [ZMOD 3] → n ≡ 1 [ZMOD 3]) := by
  simp [Int.ModEq]
  intro h₁ h₂
  omega
theorem lean_workbook_136_1 (n : ℕ) : (4*n ≡ 4 [ZMOD 12] → n-1 ≡ 0 [ZMOD 3] → n ≡ 1 [ZMOD 3]) := by
  intros h₁ h₂
  rw [Int.ModEq] at *
  omega
theorem lean_workbook_136_2 (n : ℕ) : (4*n ≡ 4 [ZMOD 12] → n-1 ≡ 0 [ZMOD 3] → n ≡ 1 [ZMOD 3]) := by
  intro h₀ h₁
  rw [Int.ModEq] at h₀ h₁ ⊢
  omega
theorem lean_workbook_136_3 (n : ℕ) : (4*n ≡ 4 [ZMOD 12] → n-1 ≡ 0 [ZMOD 3] → n ≡ 1 [ZMOD 3]) := by
  intro h₁ h₂
  rw [Int.ModEq] at h₁ h₂ ⊢
  omega
theorem lean_workbook_136_4 (n : ℕ) : (4*n ≡ 4 [ZMOD 12] → n-1 ≡ 0 [ZMOD 3] → n ≡ 1 [ZMOD 3]) := by
  intro p q
  simp [Int.ModEq] at *
  omega
