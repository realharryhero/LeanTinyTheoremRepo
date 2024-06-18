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
theorem lean_workbook_101_17 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  simp only [hx, Nat.pow_succ, Nat.pow_zero, Nat.pow_one, Nat.add_zero, Nat.add_one]
theorem lean_workbook_101_18 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  rw [hx, show (2 : ℕ)^9 + 1 = 513 by decide]
theorem lean_workbook_101_19 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  rw [hx]
  norm_num [Nat.pow_succ, Nat.pow_zero, Nat.pow_one]
theorem lean_workbook_101_20 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  ring_nf at hx
  exact hx
theorem lean_workbook_101_21 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
  rw [hx, show (2 : ℕ) ^ 9 + 1 = 513 by norm_num]
theorem lean_workbook_101_22 (x : ℕ) (hx : x = 2^9 + 1) : x = 513 := by
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
theorem lean_workbook_136_5 (n : ℕ) : (4*n ≡ 4 [ZMOD 12] → n-1 ≡ 0 [ZMOD 3] → n ≡ 1 [ZMOD 3]) := by
  intro h4 h3
  rw [Int.modEq_iff_dvd] at h4 h3 ⊢
  omega
theorem lean_workbook_136_6 (n : ℕ) : (4*n ≡ 4 [ZMOD 12] → n-1 ≡ 0 [ZMOD 3] → n ≡ 1 [ZMOD 3]) := by
  intro h₁ h₂
  rw [Int.modEq_iff_dvd] at *
  omega
theorem lean_workbook_136_7 (n : ℕ) : (4*n ≡ 4 [ZMOD 12] → n-1 ≡ 0 [ZMOD 3] → n ≡ 1 [ZMOD 3]) := by
  simp [Nat.ModEq, Int.ModEq, Int.emod_eq_emod_iff_emod_sub_eq_zero]
  intro h1 h2
  omega
theorem lean_workbook_136_8 (n : ℕ) : (4*n ≡ 4 [ZMOD 12] → n-1 ≡ 0 [ZMOD 3] → n ≡ 1 [ZMOD 3]) := by
  intro h h'
  simp only [Int.ModEq] at *
  omega
theorem lean_workbook_136_9 (n : ℕ) : (4*n ≡ 4 [ZMOD 12] → n-1 ≡ 0 [ZMOD 3] → n ≡ 1 [ZMOD 3]) := by
  intro h1 h2
  simp only [Int.ModEq] at *
  omega
theorem lean_workbook_136_10 (n : ℕ) : (4*n ≡ 4 [ZMOD 12] → n-1 ≡ 0 [ZMOD 3] → n ≡ 1 [ZMOD 3]) := by
  intro h h'
  simp only [Int.ModEq] at h h' ⊢
  omega
theorem lean_workbook_136_11 (n : ℕ) : (4*n ≡ 4 [ZMOD 12] → n-1 ≡ 0 [ZMOD 3] → n ≡ 1 [ZMOD 3]) := by
  simp [Int.ModEq, Int.emod]
  omega
theorem lean_workbook_136_12 (n : ℕ) : (4*n ≡ 4 [ZMOD 12] → n-1 ≡ 0 [ZMOD 3] → n ≡ 1 [ZMOD 3]) := by
  intro h1 h2
  simp [Int.ModEq] at h1 h2 ⊢
  omega
theorem lean_workbook_136_13 (n : ℕ) : (4*n ≡ 4 [ZMOD 12] → n-1 ≡ 0 [ZMOD 3] → n ≡ 1 [ZMOD 3]) := by
  simp [Int.ModEq, Int.emod_eq_emod_iff_emod_sub_eq_zero]
  intro h1 h2
  omega
theorem lean_workbook_136_14 (n : ℕ) : (4*n ≡ 4 [ZMOD 12] → n-1 ≡ 0 [ZMOD 3] → n ≡ 1 [ZMOD 3]) := by
  simp [Nat.ModEq, Int.ModEq]
  intro h₁ h₂
  omega
theorem lean_workbook_136_15 (n : ℕ) : (4*n ≡ 4 [ZMOD 12] → n-1 ≡ 0 [ZMOD 3] → n ≡ 1 [ZMOD 3]) := by
  intro h1 h2
  simp only [Int.ModEq, Int.ofNat_mod] at *
  omega
theorem lean_workbook_136_16 (n : ℕ) : (4*n ≡ 4 [ZMOD 12] → n-1 ≡ 0 [ZMOD 3] → n ≡ 1 [ZMOD 3]) := by
  rintro h1 h2
  rw [Int.ModEq] at h1 h2 ⊢
  omega
theorem lean_workbook_136_17 (n : ℕ) : (4*n ≡ 4 [ZMOD 12] → n-1 ≡ 0 [ZMOD 3] → n ≡ 1 [ZMOD 3]) := by
  intro h₁ h₂
  simp only [Int.ModEq, Int.ofNat_mul, Int.ofNat_succ, Int.ofNat_zero] at *
  omega
theorem lean_workbook_136_18 (n : ℕ) : (4*n ≡ 4 [ZMOD 12] → n-1 ≡ 0 [ZMOD 3] → n ≡ 1 [ZMOD 3]) := by
  intro h₁ h₂
  rw [Int.ModEq] at *
  omega
theorem lean_workbook_136_19 (n : ℕ) : (4*n ≡ 4 [ZMOD 12] → n-1 ≡ 0 [ZMOD 3] → n ≡ 1 [ZMOD 3]) := by
  intro h h'
  simp [Int.ModEq] at *
  omega
theorem lean_workbook_136_20 (n : ℕ) : (4*n ≡ 4 [ZMOD 12] → n-1 ≡ 0 [ZMOD 3] → n ≡ 1 [ZMOD 3]) := by
  simp [Int.ModEq, Int.ofNat_mod]
  intro h₁ h₂
  omega

theorem lean_workbook_139_0 (a b c d : ℤ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) (habc : a + b + c + d = 0) : a + b + c + d = 0 := by
  norm_num at ha
  norm_num [ha.1, ha.2.1, ha.2.2.1, ha.2.2.2, habc]
theorem lean_workbook_139_1 (a b c d : ℤ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) (habc : a + b + c + d = 0) : a + b + c + d = 0 := by
  revert habc
  rintro h
  linarith [ha.1, ha.2.1, ha.2.2.1, ha.2.2.2]
theorem lean_workbook_139_2 (a b c d : ℤ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) (habc : a + b + c + d = 0) : a + b + c + d = 0 := by
  simp only [ha, habc, gt_iff_lt, not_lt, ge_iff_le, not_le, Int.lt_add_one_iff]
theorem lean_workbook_139_3 (a b c d : ℤ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) (habc : a + b + c + d = 0) : a + b + c + d = 0 := by
  linarith [ha]
theorem lean_workbook_139_4 (a b c d : ℤ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) (habc : a + b + c + d = 0) : a + b + c + d = 0 := by
  norm_cast at ha habc ⊢
theorem lean_workbook_139_5 (a b c d : ℤ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) (habc : a + b + c + d = 0) : a + b + c + d = 0 := by
  norm_num at ha
  linarith [ha.1, ha.2.1, ha.2.2.1, ha.2.2.2, habc]
theorem lean_workbook_139_6 (a b c d : ℤ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) (habc : a + b + c + d = 0) : a + b + c + d = 0 := by
  linarith only [ha.1, ha.2.1, ha.2.2.1, ha.2.2.2, habc]
theorem lean_workbook_139_7 (a b c d : ℤ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) (habc : a + b + c + d = 0) : a + b + c + d = 0 := by
  norm_num at ha
  linarith [ha.1, ha.2.1, ha.2.2]
theorem lean_workbook_139_8 (a b c d : ℤ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) (habc : a + b + c + d = 0) : a + b + c + d = 0 := by
  linarith [ha.1, ha.2.1, ha.2.2.1, ha.2.2.2]
theorem lean_workbook_139_9 (a b c d : ℤ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) (habc : a + b + c + d = 0) : a + b + c + d = 0 := by
  linarith [ha.1, ha.2.1, ha.2.2.1, habc]
theorem lean_workbook_139_10 (a b c d : ℤ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) (habc : a + b + c + d = 0) : a + b + c + d = 0 := by
  have h1 := add_nonneg ha.1.le ha.2.1.le
  have h2 := add_nonneg ha.2.1.le ha.2.2.1.le
  have h3 := add_nonneg ha.2.2.1.le ha.2.2.2.le
  linarith [ha.1, ha.2.1, ha.2.2.1, ha.2.2.2]
theorem lean_workbook_139_11 (a b c d : ℤ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) (habc : a + b + c + d = 0) : a + b + c + d = 0 := by
  simp only [add_assoc, add_comm, add_left_comm] at habc ⊢
  linarith [ha.1, ha.2.1, ha.2.2.1, ha.2.2.2]
theorem lean_workbook_139_12 (a b c d : ℤ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) (habc : a + b + c + d = 0) : a + b + c + d = 0 := by
  exact habc
theorem lean_workbook_139_13 (a b c d : ℤ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) (habc : a + b + c + d = 0) : a + b + c + d = 0 := by
  ring_nf at ha habc ⊢
  omega
theorem lean_workbook_139_14 (a b c d : ℤ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) (habc : a + b + c + d = 0) : a + b + c + d = 0 := by
  norm_num at ha
  linarith only [ha, habc]
theorem lean_workbook_139_15 (a b c d : ℤ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) (habc : a + b + c + d = 0) : a + b + c + d = 0 := by
  simp [habc, ha.1, ha.2.1, ha.2.2.1, ha.2.2.2]
theorem lean_workbook_139_16 (a b c d : ℤ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) (habc : a + b + c + d = 0) : a + b + c + d = 0 := by
  simp [ha.1, ha.2.1, ha.2.2.1, ha.2.2.2, habc]
theorem lean_workbook_139_17 (a b c d : ℤ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) (habc : a + b + c + d = 0) : a + b + c + d = 0 := by
  linarith only [habc, ha.1, ha.2.1, ha.2.2.1, ha.2.2.2]
theorem lean_workbook_139_18 (a b c d : ℤ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) (habc : a + b + c + d = 0) : a + b + c + d = 0 := by
  simp only [ha, habc, Int.add_zero, Int.add_neg_one, Int.neg_add, Int.neg_neg, Int.neg_zero]
theorem lean_workbook_139_19 (a b c d : ℤ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) (habc : a + b + c + d = 0) : a + b + c + d = 0 := by
  linarith [ha.1, ha.2.1, ha.2.2.1, ha.2.2.2, habc]
theorem lean_workbook_139_20 (a b c d : ℤ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) (habc : a + b + c + d = 0) : a + b + c + d = 0 := by
  revert ha habc
  rintro ⟨ha, hb, hc, hd⟩ habc
  linarith [ha, hb, hc, hd, habc]
theorem lean_workbook_139_21 (a b c d : ℤ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) (habc : a + b + c + d = 0) : a + b + c + d = 0 := by
  linarith [ha.left, ha.right.left, ha.right.right.left, ha.right.right.right]
theorem lean_workbook_139_22 (a b c d : ℤ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) (habc : a + b + c + d = 0) : a + b + c + d = 0 := by
  linarith [ha, habc]
theorem lean_workbook_139_23 (a b c d : ℤ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) (habc : a + b + c + d = 0) : a + b + c + d = 0 := by
  linarith [ha.1, ha.2.1, ha.2.2, habc]
theorem lean_workbook_139_24 (a b c d : ℤ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) (habc : a + b + c + d = 0) : a + b + c + d = 0 := by
  simpa only [Int.add_zero] using habc

theorem lean_workbook_140_0 (x : ℝ) : x^2 + 4*x - 1 = (x + 2 + Real.sqrt 5) * (x + 2 - Real.sqrt 5) := by
  ring_nf
  rw [add_comm]
  rw [← sub_eq_zero]
  field_simp [Real.sqrt_eq_iff_sq_eq]
  ring_nf
theorem lean_workbook_140_1 (x : ℝ) : x^2 + 4*x - 1 = (x + 2 + Real.sqrt 5) * (x + 2 - Real.sqrt 5) := by
  field_simp [add_mul, mul_add]
  ring_nf
  field_simp [add_mul, mul_add]
  ring_nf
theorem lean_workbook_140_2 (x : ℝ) : x^2 + 4*x - 1 = (x + 2 + Real.sqrt 5) * (x + 2 - Real.sqrt 5) := by
  simp only [sq, sub_mul, mul_sub]
  ring_nf
  field_simp
  ring_nf
theorem lean_workbook_140_3 (x : ℝ) : x^2 + 4*x - 1 = (x + 2 + Real.sqrt 5) * (x + 2 - Real.sqrt 5) := by
  simp [mul_add, add_mul, mul_comm, mul_assoc, mul_left_comm]
  ring_nf
  field_simp
  ring_nf
theorem lean_workbook_140_4 (x : ℝ) : x^2 + 4*x - 1 = (x + 2 + Real.sqrt 5) * (x + 2 - Real.sqrt 5) := by
  ring_nf
  simp [add_mul, mul_add, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_140_5 (x : ℝ) : x^2 + 4*x - 1 = (x + 2 + Real.sqrt 5) * (x + 2 - Real.sqrt 5) := by
  field_simp [add_mul, mul_add]
  ring_nf
  field_simp [add_assoc, add_comm, add_left_comm]
  ring_nf
theorem lean_workbook_140_6 (x : ℝ) : x^2 + 4*x - 1 = (x + 2 + Real.sqrt 5) * (x + 2 - Real.sqrt 5) := by
  ring_nf
  simp [Real.sqrt_eq_iff_sq_eq]
  ring_nf
theorem lean_workbook_140_7 (x : ℝ) : x^2 + 4*x - 1 = (x + 2 + Real.sqrt 5) * (x + 2 - Real.sqrt 5) := by
  ring_nf
  rw [← sub_eq_zero]
  field_simp [Real.sqrt_eq_iff_sq_eq]
  ring
theorem lean_workbook_140_8 (x : ℝ) : x^2 + 4*x - 1 = (x + 2 + Real.sqrt 5) * (x + 2 - Real.sqrt 5) := by
  ring_nf
  field_simp [Real.sqrt_sq_eq_abs]
  ring_nf
theorem lean_workbook_140_9 (x : ℝ) : x^2 + 4*x - 1 = (x + 2 + Real.sqrt 5) * (x + 2 - Real.sqrt 5) := by
  ring_nf
  norm_num [Real.sqrt_sq_eq_abs, abs_of_pos]
  ring
theorem lean_workbook_140_10 (x : ℝ) : x^2 + 4*x - 1 = (x + 2 + Real.sqrt 5) * (x + 2 - Real.sqrt 5) := by
  have h₁ : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  ring_nf at h₁ ⊢
  field_simp [h₁]
  nlinarith
theorem lean_workbook_140_11 (x : ℝ) : x^2 + 4*x - 1 = (x + 2 + Real.sqrt 5) * (x + 2 - Real.sqrt 5) := by
  simp [sq]
  ring_nf
  field_simp
  ring_nf
theorem lean_workbook_140_12 (x : ℝ) : x^2 + 4*x - 1 = (x + 2 + Real.sqrt 5) * (x + 2 - Real.sqrt 5) := by
  simp [sq, mul_add, add_mul, mul_comm, mul_left_comm]
  ring_nf
  field_simp
  ring_nf
theorem lean_workbook_140_13 (x : ℝ) : x^2 + 4*x - 1 = (x + 2 + Real.sqrt 5) * (x + 2 - Real.sqrt 5) := by
  simp [sq, add_mul, mul_add, mul_comm, mul_left_comm]
  ring_nf
  field_simp
  ring_nf
theorem lean_workbook_140_14 (x : ℝ) : x^2 + 4*x - 1 = (x + 2 + Real.sqrt 5) * (x + 2 - Real.sqrt 5) := by
  ring_nf
  rw [Real.sq_sqrt] <;> linarith
theorem lean_workbook_140_15 (x : ℝ) : x^2 + 4*x - 1 = (x + 2 + Real.sqrt 5) * (x + 2 - Real.sqrt 5) := by
  ring_nf
  rw [add_comm]
  field_simp [Real.sqrt_eq_iff_sq_eq]
  ring
theorem lean_workbook_140_16 (x : ℝ) : x^2 + 4*x - 1 = (x + 2 + Real.sqrt 5) * (x + 2 - Real.sqrt 5) := by
  rw [mul_comm]
  ring_nf
  field_simp
  ring_nf
theorem lean_workbook_140_17 (x : ℝ) : x^2 + 4*x - 1 = (x + 2 + Real.sqrt 5) * (x + 2 - Real.sqrt 5) := by
  simp [pow_two]
  ring_nf
  simp [Real.sqrt_sq]
  ring_nf
theorem lean_workbook_140_18 (x : ℝ) : x^2 + 4*x - 1 = (x + 2 + Real.sqrt 5) * (x + 2 - Real.sqrt 5) := by
  ring_nf
  field_simp [Real.sqrt_eq_iff_sq_eq]
  ring
theorem lean_workbook_140_19 (x : ℝ) : x^2 + 4*x - 1 = (x + 2 + Real.sqrt 5) * (x + 2 - Real.sqrt 5) := by
  nlinarith [show (Real.sqrt 5)^2 = 5 by norm_num]
theorem lean_workbook_140_20 (x : ℝ) : x^2 + 4*x - 1 = (x + 2 + Real.sqrt 5) * (x + 2 - Real.sqrt 5) := by
  rw [add_mul]
  ring_nf
  field_simp
  ring_nf
theorem lean_workbook_140_21 (x : ℝ) : x^2 + 4*x - 1 = (x + 2 + Real.sqrt 5) * (x + 2 - Real.sqrt 5) := by
  ring_nf
  simp [add_mul, mul_add, mul_comm, mul_left_comm]
  ring_nf
theorem lean_workbook_140_22 (x : ℝ) : x^2 + 4*x - 1 = (x + 2 + Real.sqrt 5) * (x + 2 - Real.sqrt 5) := by
  rw [mul_comm]
  ring_nf
  field_simp [Real.sqrt_sq]
  ring_nf
theorem lean_workbook_140_23 (x : ℝ) : x^2 + 4*x - 1 = (x + 2 + Real.sqrt 5) * (x + 2 - Real.sqrt 5) := by
  ring_nf
  rw [add_comm]
  field_simp [Real.sqrt_eq_iff_sq_eq]
  ring_nf

theorem lean_workbook_141_0 : (5:ℝ)^(1/3) + Real.sqrt 2 < (4:ℝ)^(1/3) + Real.sqrt 3 := by
  norm_num [cos_pi_div_two]
theorem lean_workbook_141_1 : (5:ℝ)^(1/3) + Real.sqrt 2 < (4:ℝ)^(1/3) + Real.sqrt 3 := by
  simp [pow_one]
  norm_num
theorem lean_workbook_141_2 : (5:ℝ)^(1/3) + Real.sqrt 2 < (4:ℝ)^(1/3) + Real.sqrt 3 := by
  norm_num [Real.sqrt_sq_eq_abs]
theorem lean_workbook_141_3 : (5:ℝ)^(1/3) + Real.sqrt 2 < (4:ℝ)^(1/3) + Real.sqrt 3 := by
  simp [Real.sqrt_lt]
  norm_num
theorem lean_workbook_141_4 : (5:ℝ)^(1/3) + Real.sqrt 2 < (4:ℝ)^(1/3) + Real.sqrt 3 := by
  norm_num [Real.sqrt_lt_sqrt_iff, Real.rpow_lt_rpow_iff]
theorem lean_workbook_141_5 : (5:ℝ)^(1/3) + Real.sqrt 2 < (4:ℝ)^(1/3) + Real.sqrt 3 := by
  norm_num [show (5:ℝ) = (5:ℚ) by norm_num, show (2:ℝ) = (2:ℚ) by norm_num]
theorem lean_workbook_141_6 : (5:ℝ)^(1/3) + Real.sqrt 2 < (4:ℝ)^(1/3) + Real.sqrt 3 := by
  norm_num [pow_one]
theorem lean_workbook_141_7 : (5:ℝ)^(1/3) + Real.sqrt 2 < (4:ℝ)^(1/3) + Real.sqrt 3 := by
  norm_num [Real.sqrt_eq_iff_sq_eq]
theorem lean_workbook_141_8 : (5:ℝ)^(1/3) + Real.sqrt 2 < (4:ℝ)^(1/3) + Real.sqrt 3 := by
  norm_num [show (5:ℝ) = 1 * 5 by norm_num, show (4:ℝ) = 1 * 4 by norm_num]
theorem lean_workbook_141_9 : (5:ℝ)^(1/3) + Real.sqrt 2 < (4:ℝ)^(1/3) + Real.sqrt 3 := by
  norm_num at *
theorem lean_workbook_141_10 : (5:ℝ)^(1/3) + Real.sqrt 2 < (4:ℝ)^(1/3) + Real.sqrt 3 := by
  norm_num [show (2:ℝ).sqrt ≠ 0 by norm_num]
theorem lean_workbook_141_11 : (5:ℝ)^(1/3) + Real.sqrt 2 < (4:ℝ)^(1/3) + Real.sqrt 3 := by
  norm_num [Real.sqrt_lt, show (0:ℝ) < 3 by norm_num, show (0:ℝ) < 2 by norm_num]
theorem lean_workbook_141_12 : (5:ℝ)^(1/3) + Real.sqrt 2 < (4:ℝ)^(1/3) + Real.sqrt 3 := by
  norm_num [show (5:ℝ) = 4 + 1 by norm_num, show (4:ℝ) = 3 + 1 by norm_num]
theorem lean_workbook_141_13 : (5:ℝ)^(1/3) + Real.sqrt 2 < (4:ℝ)^(1/3) + Real.sqrt 3 := by
  ring_nf
  norm_num [Real.sqrt_sq_eq_abs, abs_of_pos]
theorem lean_workbook_141_14 : (5:ℝ)^(1/3) + Real.sqrt 2 < (4:ℝ)^(1/3) + Real.sqrt 3 := by
  norm_num [Real.rpow_pos_of_pos]

theorem lean_workbook_190_0 (x y z : ℝ) (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) (hxy : x + y ≤ 1) (hz : z ≥ 1) : 8 * x ^ 2 * y ^ 2 + z * (x + y) ^ 2 ≥ 4 * x * y * z := by
  have h1 : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
  nlinarith [hx.1, hx.2, hy.1, hy.2, hxy, hz, h1]
theorem lean_workbook_190_1 (x y z : ℝ) (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) (hxy : x + y ≤ 1) (hz : z ≥ 1) : 8 * x ^ 2 * y ^ 2 + z * (x + y) ^ 2 ≥ 4 * x * y * z := by
  have h1 := sq_nonneg (x + y)
  have h2 := sq_nonneg (x - y)
  nlinarith
theorem lean_workbook_190_2 (x y z : ℝ) (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) (hxy : x + y ≤ 1) (hz : z ≥ 1) : 8 * x ^ 2 * y ^ 2 + z * (x + y) ^ 2 ≥ 4 * x * y * z := by
  have h1 : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
  nlinarith [hxy, hz, h1]
theorem lean_workbook_190_3 (x y z : ℝ) (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) (hxy : x + y ≤ 1) (hz : z ≥ 1) : 8 * x ^ 2 * y ^ 2 + z * (x + y) ^ 2 ≥ 4 * x * y * z := by
  have : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
  nlinarith [hz, hxy]

theorem lean_workbook_211_0 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  simp [add_mul, mul_add, mul_comm, mul_left_comm, sq, pow_add, pow_bit0, pow_bit1, mul_assoc]
  ring
theorem lean_workbook_211_1 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  simp [add_mul, mul_add, mul_comm, mul_left_comm, sq, pow_two, pow_mul]
  ring
theorem lean_workbook_211_2 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  rw [add_assoc]
  ring
theorem lean_workbook_211_3 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  simp [sq, pow_mul, mul_comm, mul_assoc, mul_left_comm]
  ring
theorem lean_workbook_211_4 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  simp only [sq, mul_add, mul_sub, add_mul, add_sub, sub_mul, sub_sub]
  ring
theorem lean_workbook_211_5 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  ring
theorem lean_workbook_211_6 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  simp [sq, pow_mul, mul_add, add_mul, add_comm, add_left_comm]
  ring
theorem lean_workbook_211_7 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  rw [add_mul, mul_add]
  ring
theorem lean_workbook_211_8 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  simp [sq, mul_add, mul_comm, mul_left_comm, pow_add, pow_mul]
  ring
theorem lean_workbook_211_9 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  simp [mul_add, mul_comm, mul_left_comm, pow_add, pow_mul, mul_pow]
  ring
theorem lean_workbook_211_10 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  rw [add_mul, mul_add, mul_add, add_comm]
  ring
theorem lean_workbook_211_11 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  simp [add_mul, mul_add, mul_comm, mul_left_comm, sq, pow_add, pow_mul]
  ring
theorem lean_workbook_211_12 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  simp [sq, mul_add, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  ring
theorem lean_workbook_211_13 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  simp [sq, pow_add, mul_add, add_mul, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_211_14 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  simp [pow_mul, add_mul, mul_add, mul_comm, sub_eq_add_neg, sub_mul]
  ring
theorem lean_workbook_211_15 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  simp [add_mul, mul_add, mul_comm, mul_left_comm, sq, pow_add, pow_mul, mul_pow]
  ring
theorem lean_workbook_211_16 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  simp [mul_add, add_mul, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_211_17 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  simp only [add_mul, mul_add]
  ring
theorem lean_workbook_211_18 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  simp only [mul_add, mul_sub, pow_add, pow_one]
  ring
theorem lean_workbook_211_19 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  simp [mul_add, add_mul, mul_comm, mul_left_comm, sq, pow_add, pow_mul]
  ring
theorem lean_workbook_211_20 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  rw [add_mul]
  ring_nf
theorem lean_workbook_211_21 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  simp [add_mul, mul_add, mul_comm, sub_eq_add_neg, sub_mul]
  ring
theorem lean_workbook_211_22 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  simp [← sub_eq_add_neg, sub_mul, add_mul, mul_assoc, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_211_23 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  simp only [sq, mul_add, mul_sub, sub_mul, add_mul, add_sub, sub_sub_sub_cancel_right]
  ring
theorem lean_workbook_211_24 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  simp [sq, pow_add, mul_add, add_mul, add_comm, add_left_comm, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_211_25 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  simp [sq, pow_mul, mul_add, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_211_26 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  simp [sq, mul_add, add_mul, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_211_27 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  simp only [add_mul, mul_sub, mul_add, sub_add, mul_one, one_mul, pow_add, pow_one, ← add_assoc]
  ring
theorem lean_workbook_211_28 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  simp [sq, pow_mul, add_mul, mul_add, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_211_29 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  simp only [add_mul, mul_add, mul_sub, sub_mul]
  ring
theorem lean_workbook_211_30 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  repeat' rw [sq]
  ring
theorem lean_workbook_211_31 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  simp [mul_add, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_211_32 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1) := by
  simp [pow_mul, add_mul, mul_add, mul_comm, mul_left_comm]
  ring

theorem lean_workbook_214_0 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  simp only [ge_iff_le, sq_nonneg]
theorem lean_workbook_214_1 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  simp [sq, mul_self_nonneg]
theorem lean_workbook_214_2 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  simp [sq_nonneg, sub_nonneg]
theorem lean_workbook_214_3 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  simp [sq]
  nlinarith [sq_nonneg (x - y)]
theorem lean_workbook_214_4 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  simp [sq_nonneg]
theorem lean_workbook_214_5 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  norm_cast
  exact pow_two_nonneg (x - y)
theorem lean_workbook_214_6 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  simp [sq, sub_eq_add_neg, add_comm, add_left_comm]
  nlinarith [sq_nonneg (x - y)]
theorem lean_workbook_214_7 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  rw [sq]
  apply mul_self_nonneg
theorem lean_workbook_214_8 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  nlinarith [pow_two_nonneg (x - y)]
theorem lean_workbook_214_9 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  apply sq_nonneg (x - y)
theorem lean_workbook_214_10 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  simp only [sq, sub_nonneg]
  apply mul_self_nonneg
theorem lean_workbook_214_11 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  simp only [sq_nonneg, sub_self]
theorem lean_workbook_214_12 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  simp [sq]
  exact mul_self_nonneg (x - y)
theorem lean_workbook_214_13 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  simp [sq, sub_eq_add_neg, add_comm, add_left_comm]
  apply mul_self_nonneg
theorem lean_workbook_214_14 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  simp only [sq, sub_nonneg]
  nlinarith [sq_nonneg (x - y)]
theorem lean_workbook_214_15 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  simp [sq]
  nlinarith only [sq_nonneg (x - y)]
theorem lean_workbook_214_16 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  exact pow_two_nonneg _
theorem lean_workbook_214_17 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  apply_rules [sq_nonneg, sub_nonneg]
theorem lean_workbook_214_18 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  rw [pow_two]
  nlinarith
theorem lean_workbook_214_19 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  simp only [sq_nonneg, sub_eq_add_neg, add_comm]
theorem lean_workbook_214_20 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  nlinarith only [sq_nonneg (x - y)]
theorem lean_workbook_214_21 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  simp only [sq_nonneg, sub_self, mul_zero]
theorem lean_workbook_214_22 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  simp only [pow_two, sub_nonneg]
  exact mul_self_nonneg _
theorem lean_workbook_214_23 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  rw [sq]
  exact mul_self_nonneg (x - y)
theorem lean_workbook_214_24 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  refine' pow_two_nonneg (x - y)
theorem lean_workbook_214_25 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  rw [sq]
  nlinarith [sq_nonneg (x - y)]
theorem lean_workbook_214_26 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  simp only [pow_two, sub_eq_add_neg, add_comm]
  nlinarith
theorem lean_workbook_214_27 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  simp only [sq_nonneg, sub_nonneg]
theorem lean_workbook_214_28 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  rw [pow_two]
  nlinarith [sq_nonneg (x - y)]
theorem lean_workbook_214_29 (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by
  have : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
  exact this

theorem lean_workbook_242_0 (x y a : ℝ) : (3 * a + 2 * x + y) ^ 2 ≤ 9 * (a + x) * (a + x + y) ↔ 3 * a * (2 * x + y) + 5 * x ^ 2 + 5 * x * y ≥ y ^ 2 := by
  rw [pow_two]
  constructor <;> intro h <;> linarith
theorem lean_workbook_242_1 (x y a : ℝ) : (3 * a + 2 * x + y) ^ 2 ≤ 9 * (a + x) * (a + x + y) ↔ 3 * a * (2 * x + y) + 5 * x ^ 2 + 5 * x * y ≥ y ^ 2 := by
  refine' ⟨fun h => _, fun h => _⟩
  nlinarith [h]
  nlinarith [h]
theorem lean_workbook_242_2 (x y a : ℝ) : (3 * a + 2 * x + y) ^ 2 ≤ 9 * (a + x) * (a + x + y) ↔ 3 * a * (2 * x + y) + 5 * x ^ 2 + 5 * x * y ≥ y ^ 2 := by
  simp [add_assoc]
  ring_nf
  constructor <;> intro h <;> linarith
theorem lean_workbook_242_3 (x y a : ℝ) : (3 * a + 2 * x + y) ^ 2 ≤ 9 * (a + x) * (a + x + y) ↔ 3 * a * (2 * x + y) + 5 * x ^ 2 + 5 * x * y ≥ y ^ 2 := by
  constructor <;> intro h
  linarith [h]
  nlinarith
theorem lean_workbook_242_4 (x y a : ℝ) : (3 * a + 2 * x + y) ^ 2 ≤ 9 * (a + x) * (a + x + y) ↔ 3 * a * (2 * x + y) + 5 * x ^ 2 + 5 * x * y ≥ y ^ 2 := by
  rw [sq, add_assoc]
  constructor <;> intro h
  linarith [sq_nonneg (a + x)]
  nlinarith
theorem lean_workbook_242_5 (x y a : ℝ) : (3 * a + 2 * x + y) ^ 2 ≤ 9 * (a + x) * (a + x + y) ↔ 3 * a * (2 * x + y) + 5 * x ^ 2 + 5 * x * y ≥ y ^ 2 := by
  constructor <;> intro h
  linarith [h]
  nlinarith [h]
theorem lean_workbook_242_6 (x y a : ℝ) : (3 * a + 2 * x + y) ^ 2 ≤ 9 * (a + x) * (a + x + y) ↔ 3 * a * (2 * x + y) + 5 * x ^ 2 + 5 * x * y ≥ y ^ 2 := by
  simp [sq, add_assoc, add_comm, add_left_comm]
  ring_nf
  constructor <;> intro h
  linarith
  linarith [h]
theorem lean_workbook_242_7 (x y a : ℝ) : (3 * a + 2 * x + y) ^ 2 ≤ 9 * (a + x) * (a + x + y) ↔ 3 * a * (2 * x + y) + 5 * x ^ 2 + 5 * x * y ≥ y ^ 2 := by
  field_simp [sq]
  ring_nf
  constructor <;> intro h
  linarith
  nlinarith
theorem lean_workbook_242_8 (x y a : ℝ) : (3 * a + 2 * x + y) ^ 2 ≤ 9 * (a + x) * (a + x + y) ↔ 3 * a * (2 * x + y) + 5 * x ^ 2 + 5 * x * y ≥ y ^ 2 := by
  field_simp [mul_assoc]
  ring_nf
  constructor <;> intro h <;> linarith
theorem lean_workbook_242_9 (x y a : ℝ) : (3 * a + 2 * x + y) ^ 2 ≤ 9 * (a + x) * (a + x + y) ↔ 3 * a * (2 * x + y) + 5 * x ^ 2 + 5 * x * y ≥ y ^ 2 := by
  field_simp [mul_add, add_mul, mul_comm, mul_assoc, mul_left_comm]
  ring_nf
  constructor <;> intro h <;> linarith
theorem lean_workbook_242_10 (x y a : ℝ) : (3 * a + 2 * x + y) ^ 2 ≤ 9 * (a + x) * (a + x + y) ↔ 3 * a * (2 * x + y) + 5 * x ^ 2 + 5 * x * y ≥ y ^ 2 := by
  constructor
  intro h
  linarith
  intro h
  nlinarith
theorem lean_workbook_242_11 (x y a : ℝ) : (3 * a + 2 * x + y) ^ 2 ≤ 9 * (a + x) * (a + x + y) ↔ 3 * a * (2 * x + y) + 5 * x ^ 2 + 5 * x * y ≥ y ^ 2 := by
  rw [sq]
  constructor <;> intro h <;> linarith
theorem lean_workbook_242_12 (x y a : ℝ) : (3 * a + 2 * x + y) ^ 2 ≤ 9 * (a + x) * (a + x + y) ↔ 3 * a * (2 * x + y) + 5 * x ^ 2 + 5 * x * y ≥ y ^ 2 := by
  field_simp [pow_two]
  ring_nf
  constructor <;> intro h
  linarith
  nlinarith
theorem lean_workbook_242_13 (x y a : ℝ) : (3 * a + 2 * x + y) ^ 2 ≤ 9 * (a + x) * (a + x + y) ↔ 3 * a * (2 * x + y) + 5 * x ^ 2 + 5 * x * y ≥ y ^ 2 := by
  ring_nf
  constructor <;> intro h <;> linarith
theorem lean_workbook_242_14 (x y a : ℝ) : (3 * a + 2 * x + y) ^ 2 ≤ 9 * (a + x) * (a + x + y) ↔ 3 * a * (2 * x + y) + 5 * x ^ 2 + 5 * x * y ≥ y ^ 2 := by
  rw [sq, mul_add]
  constructor <;> intro h
  linarith
  nlinarith
theorem lean_workbook_242_15 (x y a : ℝ) : (3 * a + 2 * x + y) ^ 2 ≤ 9 * (a + x) * (a + x + y) ↔ 3 * a * (2 * x + y) + 5 * x ^ 2 + 5 * x * y ≥ y ^ 2 := by
  unfold_let
  rw [add_comm]
  ring_nf
  constructor <;> intro h <;> linarith
theorem lean_workbook_242_16 (x y a : ℝ) : (3 * a + 2 * x + y) ^ 2 ≤ 9 * (a + x) * (a + x + y) ↔ 3 * a * (2 * x + y) + 5 * x ^ 2 + 5 * x * y ≥ y ^ 2 := by
  field_simp [pow_two]
  constructor <;> intro h <;> linarith
theorem lean_workbook_242_17 (x y a : ℝ) : (3 * a + 2 * x + y) ^ 2 ≤ 9 * (a + x) * (a + x + y) ↔ 3 * a * (2 * x + y) + 5 * x ^ 2 + 5 * x * y ≥ y ^ 2 := by
  constructor
  intro h
  linarith [h]
  intro h
  linarith
theorem lean_workbook_242_18 (x y a : ℝ) : (3 * a + 2 * x + y) ^ 2 ≤ 9 * (a + x) * (a + x + y) ↔ 3 * a * (2 * x + y) + 5 * x ^ 2 + 5 * x * y ≥ y ^ 2 := by
  constructor <;> intro h <;> linarith
theorem lean_workbook_242_19 (x y a : ℝ) : (3 * a + 2 * x + y) ^ 2 ≤ 9 * (a + x) * (a + x + y) ↔ 3 * a * (2 * x + y) + 5 * x ^ 2 + 5 * x * y ≥ y ^ 2 := by
  field_simp [sq]
  constructor
  repeat' intro h; linarith
theorem lean_workbook_242_20 (x y a : ℝ) : (3 * a + 2 * x + y) ^ 2 ≤ 9 * (a + x) * (a + x + y) ↔ 3 * a * (2 * x + y) + 5 * x ^ 2 + 5 * x * y ≥ y ^ 2 := by
  rw [sq, sq]
  ring_nf
  constructor <;> intro h <;> linarith

theorem lean_workbook_248_0 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  field_simp [mul_add, add_mul, mul_comm, mul_assoc, mul_left_comm]
  ring
theorem lean_workbook_248_1 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  rw [sub_eq_add_neg]
  ring
theorem lean_workbook_248_2 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  simp [sub_mul]
  simp only [add_assoc]
  ring
theorem lean_workbook_248_3 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  simp [sub_mul]
  ring
theorem lean_workbook_248_4 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  simp [sub_mul]
  simp only [pow_succ]
  ring
theorem lean_workbook_248_5 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  linear_combination (norm := (norm_num1; ring1)) x^5 - y^5
theorem lean_workbook_248_6 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  simp [mul_add, add_mul, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_248_7 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  simp [mul_add, mul_left_comm, mul_comm]
  ring_nf
theorem lean_workbook_248_8 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  linarith [pow_succ x 4, pow_succ y 4]
theorem lean_workbook_248_9 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  rw [← sub_eq_zero]
  field_simp [sub_eq_zero]
  ring
theorem lean_workbook_248_10 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  simp [sq]
  ring
theorem lean_workbook_248_11 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  simp [add_mul, mul_add]
  ring
theorem lean_workbook_248_12 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  simp only [sub_mul, mul_add]
  ring
theorem lean_workbook_248_13 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  simp [sub_mul, mul_add, add_mul]
  ring
theorem lean_workbook_248_14 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  simp [sub_mul, mul_sub, mul_comm, mul_assoc, mul_left_comm]
  ring_nf
theorem lean_workbook_248_15 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  simp [sq, pow_succ]
  ring_nf
theorem lean_workbook_248_16 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  rw [sub_eq_add_neg, add_comm]
  simp [add_mul, mul_add, mul_comm, mul_left_comm]
  ring_nf
theorem lean_workbook_248_17 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  rw [mul_add, mul_add, mul_add, mul_add]
  ring
theorem lean_workbook_248_18 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  symm
  simp [mul_add, add_mul, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_248_19 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  rw [← sub_eq_zero]
  simp [sub_eq_zero]
  ring_nf
theorem lean_workbook_248_20 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  simp only [sub_mul, mul_sub, mul_comm, mul_assoc, mul_left_comm]
  ring
theorem lean_workbook_248_21 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  simp [sub_mul, mul_add]
  ring
theorem lean_workbook_248_22 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  simp [sub_mul, mul_sub]
  ring
theorem lean_workbook_248_23 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  simp [sub_mul, mul_add, mul_sub, add_mul, add_sub, pow_succ]
  ring
theorem lean_workbook_248_24 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  rw [mul_comm]
  simp [sub_mul, mul_comm, mul_assoc, mul_left_comm]
  ring
theorem lean_workbook_248_25 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  rw [sub_eq_add_neg, ← sub_eq_add_neg]
  ring
theorem lean_workbook_248_26 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  rw [sub_eq_add_neg]
  ring_nf
theorem lean_workbook_248_27 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by
  simp only [sub_mul, mul_add]
  ring_nf

theorem lean_workbook_251_0 (x : ℝ) (h₀ : 9 - x^2 ≥ 0) : -3 ≤ x ∧ x ≤ 3 := by
  constructor
  all_goals nlinarith
theorem lean_workbook_251_1 (x : ℝ) (h₀ : 9 - x^2 ≥ 0) : -3 ≤ x ∧ x ≤ 3 := by
  norm_num at h₀
  refine' ⟨by nlinarith [h₀], by nlinarith [h₀]⟩
theorem lean_workbook_251_2 (x : ℝ) (h₀ : 9 - x^2 ≥ 0) : -3 ≤ x ∧ x ≤ 3 := by
  have h₁ : 0 ≤ 3^2 - x^2 := by linarith
  rw [pow_two, pow_two] at h₁
  constructor <;> nlinarith
theorem lean_workbook_251_3 (x : ℝ) (h₀ : 9 - x^2 ≥ 0) : -3 ≤ x ∧ x ≤ 3 := by
  apply And.intro
  nlinarith
  nlinarith [h₀]
theorem lean_workbook_251_4 (x : ℝ) (h₀ : 9 - x^2 ≥ 0) : -3 ≤ x ∧ x ≤ 3 := by
  have h₁ : 0 ≤ 3^2 - x^2 := by linarith
  constructor <;> nlinarith
theorem lean_workbook_251_5 (x : ℝ) (h₀ : 9 - x^2 ≥ 0) : -3 ≤ x ∧ x ≤ 3 := by
  constructor
  nlinarith
  nlinarith [h₀]
theorem lean_workbook_251_6 (x : ℝ) (h₀ : 9 - x^2 ≥ 0) : -3 ≤ x ∧ x ≤ 3 := by
  exact ⟨by linarith [sq_nonneg (x + 3), h₀], by linarith [sq_nonneg (x - 3), h₀]⟩
theorem lean_workbook_251_7 (x : ℝ) (h₀ : 9 - x^2 ≥ 0) : -3 ≤ x ∧ x ≤ 3 := by
  refine' ⟨_, _⟩
  nlinarith only [h₀]
  nlinarith only [h₀]
theorem lean_workbook_251_8 (x : ℝ) (h₀ : 9 - x^2 ≥ 0) : -3 ≤ x ∧ x ≤ 3 := by
  apply And.intro
  apply le_of_sub_nonneg
  nlinarith
  apply le_of_sub_nonneg
  nlinarith
theorem lean_workbook_251_9 (x : ℝ) (h₀ : 9 - x^2 ≥ 0) : -3 ≤ x ∧ x ≤ 3 := by
  constructor
  nlinarith only [h₀]
  nlinarith only [h₀]
theorem lean_workbook_251_10 (x : ℝ) (h₀ : 9 - x^2 ≥ 0) : -3 ≤ x ∧ x ≤ 3 := by
  constructor
  norm_num at h₀
  nlinarith only [h₀]
  norm_num at h₀
  nlinarith only [h₀]
theorem lean_workbook_251_11 (x : ℝ) (h₀ : 9 - x^2 ≥ 0) : -3 ≤ x ∧ x ≤ 3 := by
  apply And.intro <;> nlinarith only [h₀]
theorem lean_workbook_251_12 (x : ℝ) (h₀ : 9 - x^2 ≥ 0) : -3 ≤ x ∧ x ≤ 3 := by
  constructor <;> nlinarith
theorem lean_workbook_251_13 (x : ℝ) (h₀ : 9 - x^2 ≥ 0) : -3 ≤ x ∧ x ≤ 3 := by
  refine' ⟨_, _⟩
  nlinarith [h₀]
  nlinarith [h₀]
theorem lean_workbook_251_14 (x : ℝ) (h₀ : 9 - x^2 ≥ 0) : -3 ≤ x ∧ x ≤ 3 := by
  apply And.intro
  norm_num at h₀ ⊢
  nlinarith
  norm_num at h₀ ⊢
  nlinarith
theorem lean_workbook_251_15 (x : ℝ) (h₀ : 9 - x^2 ≥ 0) : -3 ≤ x ∧ x ≤ 3 := by
  constructor <;> norm_num at h₀
  all_goals nlinarith
theorem lean_workbook_251_16 (x : ℝ) (h₀ : 9 - x^2 ≥ 0) : -3 ≤ x ∧ x ≤ 3 := by
  rw [ge_iff_le] at h₀
  constructor <;> nlinarith [h₀]
theorem lean_workbook_251_17 (x : ℝ) (h₀ : 9 - x^2 ≥ 0) : -3 ≤ x ∧ x ≤ 3 := by
  have h₁ : 0 ≤ 9 - x^2 := by linarith
  constructor <;> nlinarith
theorem lean_workbook_251_18 (x : ℝ) (h₀ : 9 - x^2 ≥ 0) : -3 ≤ x ∧ x ≤ 3 := by
  apply And.intro
  nlinarith
  nlinarith only [h₀]
theorem lean_workbook_251_19 (x : ℝ) (h₀ : 9 - x^2 ≥ 0) : -3 ≤ x ∧ x ≤ 3 := by
  refine' ⟨_, _⟩
  all_goals nlinarith
theorem lean_workbook_251_20 (x : ℝ) (h₀ : 9 - x^2 ≥ 0) : -3 ≤ x ∧ x ≤ 3 := by
  refine' ⟨_, _⟩
  nlinarith
  nlinarith only [h₀]
theorem lean_workbook_251_21 (x : ℝ) (h₀ : 9 - x^2 ≥ 0) : -3 ≤ x ∧ x ≤ 3 := by
  refine' ⟨by nlinarith, by nlinarith⟩
theorem lean_workbook_251_22 (x : ℝ) (h₀ : 9 - x^2 ≥ 0) : -3 ≤ x ∧ x ≤ 3 := by
  apply And.intro
  nlinarith only [h₀]
  nlinarith only [h₀]
theorem lean_workbook_251_23 (x : ℝ) (h₀ : 9 - x^2 ≥ 0) : -3 ≤ x ∧ x ≤ 3 := by
  refine' ⟨ _, _ ⟩
  nlinarith
  nlinarith [h₀]

theorem lean_workbook_261_0 : ∀ a b : ℝ, sin a * sin b = 1/2 * (cos (a - b) - cos (a + b)) := by
  intro x y
  simp [sub_eq_add_neg, sin_add, cos_add, cos_neg, sin_neg]
  ring
theorem lean_workbook_261_1 : ∀ a b : ℝ, sin a * sin b = 1/2 * (cos (a - b) - cos (a + b)) := by
  intro a b
  simp [cos_sub, cos_add, sin_sub, sin_add, mul_sub, mul_add, mul_one, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_261_2 : ∀ a b : ℝ, sin a * sin b = 1/2 * (cos (a - b) - cos (a + b)) := by
  refine' fun a b => _
  simp [sin_add, cos_add, cos_sub]
  ring
theorem lean_workbook_261_3 : ∀ a b : ℝ, sin a * sin b = 1/2 * (cos (a - b) - cos (a + b)) := by
  refine' fun a b => _
  simp [cos_sub, cos_add, sin_add, sin_sub, mul_add, mul_sub, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_261_4 : ∀ a b : ℝ, sin a * sin b = 1/2 * (cos (a - b) - cos (a + b)) := by
  intro a b
  simp [cos_add, cos_sub, sin_add, sin_sub, mul_add, mul_sub, mul_one, mul_comm, sub_eq_add_neg]
  ring
theorem lean_workbook_261_5 : ∀ a b : ℝ, sin a * sin b = 1/2 * (cos (a - b) - cos (a + b)) := by
  intro a b
  simp [cos_sub, cos_add, sin_sub, sin_add]
  ring
theorem lean_workbook_261_6 : ∀ a b : ℝ, sin a * sin b = 1/2 * (cos (a - b) - cos (a + b)) := by
  intro a b
  simp [cos_add, cos_sub, sin_add, sin_sub, mul_add, mul_sub, mul_one, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_261_7 : ∀ a b : ℝ, sin a * sin b = 1/2 * (cos (a - b) - cos (a + b)) := by
  intros a b
  simp [sin, cos_add, cos_sub, mul_sub, mul_add, sub_add, sub_sub]
  ring
theorem lean_workbook_261_8 : ∀ a b : ℝ, sin a * sin b = 1/2 * (cos (a - b) - cos (a + b)) := by
  intro a b
  simp [cos_add, cos_sub, mul_add, mul_sub, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_261_9 : ∀ a b : ℝ, sin a * sin b = 1/2 * (cos (a - b) - cos (a + b)) := by
  refine' fun a b => _
  simp [cos_add, cos_sub, sin_add, sin_sub, mul_add, mul_sub, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_261_10 : ∀ a b : ℝ, sin a * sin b = 1/2 * (cos (a - b) - cos (a + b)) := by
  intro a b
  simp [sub_eq_add_neg, cos_add, cos_neg, cos_two_mul]
  ring
theorem lean_workbook_261_11 : ∀ a b : ℝ, sin a * sin b = 1/2 * (cos (a - b) - cos (a + b)) := by
  intro x y
  simp [cos_sub, cos_add, sin_sub, sin_add]
  ring
theorem lean_workbook_261_12 : ∀ a b : ℝ, sin a * sin b = 1/2 * (cos (a - b) - cos (a + b)) := by
  intro a b
  simp [sin_add, sin_sub, cos_add, cos_sub, mul_sub, mul_add]
  ring
theorem lean_workbook_261_13 : ∀ a b : ℝ, sin a * sin b = 1/2 * (cos (a - b) - cos (a + b)) := by
  simp [sub_eq_add_neg, cos_add, cos_neg, sin_add, sin_neg]
  intros
  ring
theorem lean_workbook_261_14 : ∀ a b : ℝ, sin a * sin b = 1/2 * (cos (a - b) - cos (a + b)) := by
  refine' fun a b => _
  simp [sin_add, cos_add, sin_sub, cos_sub]
  ring
theorem lean_workbook_261_15 : ∀ a b : ℝ, sin a * sin b = 1/2 * (cos (a - b) - cos (a + b)) := by
  simp [cos_add, cos_sub, mul_add, mul_sub, mul_comm, mul_left_comm]
  intros a b
  ring
theorem lean_workbook_261_16 : ∀ a b : ℝ, sin a * sin b = 1/2 * (cos (a - b) - cos (a + b)) := by
  simp [sin_add, cos_add, cos_sub, sin_sub]
  intros a b
  ring
theorem lean_workbook_261_17 : ∀ a b : ℝ, sin a * sin b = 1/2 * (cos (a - b) - cos (a + b)) := by
  intro x y
  simp only [cos_sub, cos_add, sin]
  ring
theorem lean_workbook_261_18 : ∀ a b : ℝ, sin a * sin b = 1/2 * (cos (a - b) - cos (a + b)) := by
  intros a b
  simp [sin_add, cos_add, cos_sub]
  ring
theorem lean_workbook_261_19 : ∀ a b : ℝ, sin a * sin b = 1/2 * (cos (a - b) - cos (a + b)) := by
  intros a b
  simp [sub_eq_add_neg, cos_add, sin_add, cos_neg]
  ring
theorem lean_workbook_261_20 : ∀ a b : ℝ, sin a * sin b = 1/2 * (cos (a - b) - cos (a + b)) := by
  intro a b
  simp [cos_add, cos_sub]
  ring
theorem lean_workbook_261_21 : ∀ a b : ℝ, sin a * sin b = 1/2 * (cos (a - b) - cos (a + b)) := by
  intro a b
  simp [sin_add, sin_sub, cos_sub, cos_add, mul_add, mul_sub, mul_one, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_261_22 : ∀ a b : ℝ, sin a * sin b = 1/2 * (cos (a - b) - cos (a + b)) := by
  intros a b
  simp [sub_eq_add_neg, sin_add, cos_add, cos_neg, sin_neg]
  ring

theorem lean_workbook_273_0 (a : ℝ) (h₀ : 1 ≤ a) : a^4 + a ≥ a^3 + 1 := by
  simp [pow_two]
  nlinarith [sq_nonneg (a^2 - 1), h₀]
theorem lean_workbook_273_1 (a : ℝ) (h₀ : 1 ≤ a) : a^4 + a ≥ a^3 + 1 := by
  have h₁ : 0 ≤ a := by positivity
  nlinarith [sq_nonneg (a - 1)]
theorem lean_workbook_273_2 (a : ℝ) (h₀ : 1 ≤ a) : a^4 + a ≥ a^3 + 1 := by
  nlinarith [pow_two_nonneg (a^2 - 1), pow_two_nonneg (a^2 + a)]
theorem lean_workbook_273_3 (a : ℝ) (h₀ : 1 ≤ a) : a^4 + a ≥ a^3 + 1 := by
  have h1 : 0 ≤ a^2 := sq_nonneg a
  have h2 := sq_nonneg (a - 1)
  have h3 := sq_nonneg (a^2 - 1)
  nlinarith
theorem lean_workbook_273_4 (a : ℝ) (h₀ : 1 ≤ a) : a^4 + a ≥ a^3 + 1 := by
  nlinarith [sq_nonneg (a - 1), sq_nonneg (a^2 - 1)]
theorem lean_workbook_273_5 (a : ℝ) (h₀ : 1 ≤ a) : a^4 + a ≥ a^3 + 1 := by
  simp [sq]
  nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (a - 1)]
theorem lean_workbook_273_6 (a : ℝ) (h₀ : 1 ≤ a) : a^4 + a ≥ a^3 + 1 := by
  nlinarith [sq_nonneg (a^2 - 1), h₀]
theorem lean_workbook_273_7 (a : ℝ) (h₀ : 1 ≤ a) : a^4 + a ≥ a^3 + 1 := by
  nlinarith [sq_nonneg (a - 1), h₀]
theorem lean_workbook_273_8 (a : ℝ) (h₀ : 1 ≤ a) : a^4 + a ≥ a^3 + 1 := by
  have h₁ : 0 ≤ a^3 := by positivity
  nlinarith [sq_nonneg (a^2 - 1), h₀, h₁]
theorem lean_workbook_273_9 (a : ℝ) (h₀ : 1 ≤ a) : a^4 + a ≥ a^3 + 1 := by
  have h₁ : 0 ≤ a^3 := by positivity
  nlinarith [h₀, h₁]
theorem lean_workbook_273_10 (a : ℝ) (h₀ : 1 ≤ a) : a^4 + a ≥ a^3 + 1 := by
  simp [pow_two]
  nlinarith [sq_nonneg (a^2 - 1)]
theorem lean_workbook_273_11 (a : ℝ) (h₀ : 1 ≤ a) : a^4 + a ≥ a^3 + 1 := by
  have h₀' : 0 ≤ a - 1 := by linarith
  nlinarith [sq_nonneg (a - 1)]
theorem lean_workbook_273_12 (a : ℝ) (h₀ : 1 ≤ a) : a^4 + a ≥ a^3 + 1 := by
  have h₁ := sq_nonneg (a^2 - 1)
  have h₂ := sq_nonneg (a - 1)
  nlinarith [h₁, h₂]
theorem lean_workbook_273_13 (a : ℝ) (h₀ : 1 ≤ a) : a^4 + a ≥ a^3 + 1 := by
  nlinarith [sq_nonneg (a^2 - 1)]
theorem lean_workbook_273_14 (a : ℝ) (h₀ : 1 ≤ a) : a^4 + a ≥ a^3 + 1 := by
  have h₁ : 0 ≤ a^3 := by positivity
  nlinarith [sq_nonneg (a^2 - 1)]
theorem lean_workbook_273_15 (a : ℝ) (h₀ : 1 ≤ a) : a^4 + a ≥ a^3 + 1 := by
  simp [pow_two, pow_three]
  nlinarith [sq_nonneg (a^2 - 1), h₀]
theorem lean_workbook_273_16 (a : ℝ) (h₀ : 1 ≤ a) : a^4 + a ≥ a^3 + 1 := by
  simp [sq, pow_two]
  nlinarith [sq_nonneg (a - 1)]
theorem lean_workbook_273_17 (a : ℝ) (h₀ : 1 ≤ a) : a^4 + a ≥ a^3 + 1 := by
  have h₁ : 0 ≤ a^4 := by positivity
  nlinarith [h₀, h₁]

theorem lean_workbook_282_0 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (b * c + c * a + a * b) := by
  have := sq_nonneg (a - b)
  have := sq_nonneg (b - c)
  have := sq_nonneg (a - c)
  linarith
theorem lean_workbook_282_1 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (b * c + c * a + a * b) := by
  have h1 := sq_nonneg (b - c)
  have h2 := sq_nonneg (c - a)
  have h3 := sq_nonneg (a - b)
  linarith
theorem lean_workbook_282_2 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (b * c + c * a + a * b) := by
  simp [sq, add_assoc, add_comm, add_left_comm]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_282_3 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (b * c + c * a + a * b) := by
  simp [sq]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_282_4 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (b * c + c * a + a * b) := by
  have h₀ := sq_nonneg (a - b)
  have h₁ := sq_nonneg (b - c)
  have h₂ := sq_nonneg (c - a)
  linarith
theorem lean_workbook_282_5 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (b * c + c * a + a * b) := by
  linarith [sq_nonneg (a + b + c), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a - b)]
theorem lean_workbook_282_6 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (b * c + c * a + a * b) := by
  have h : 0 ≤ (a - b)^2 + (b - c)^2 + (a - c)^2 := by nlinarith
  linarith
theorem lean_workbook_282_7 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (b * c + c * a + a * b) := by
  ring_nf
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_282_8 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (b * c + c * a + a * b) := by
  simp only [sq, add_mul, add_assoc, add_left_comm]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_282_9 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (b * c + c * a + a * b) := by
  rw [sq]
  nlinarith [sq_nonneg (a + b + c), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a - b)]
theorem lean_workbook_282_10 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (b * c + c * a + a * b) := by
  rw [sq]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_282_11 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (b * c + c * a + a * b) := by
  simp [sq, mul_add, add_mul]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_282_12 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (b * c + c * a + a * b) := by
  simp [add_mul, mul_add, mul_comm, mul_left_comm, sq]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_282_13 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (b * c + c * a + a * b) := by
  simp [add_mul, mul_add]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_282_14 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (b * c + c * a + a * b) := by
  ring_nf
  simp only [sq, add_assoc]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_282_15 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (b * c + c * a + a * b) := by
  ring_nf
  norm_cast
  linarith [sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a - b)]
theorem lean_workbook_282_16 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (b * c + c * a + a * b) := by
  nlinarith [sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a - b)]
theorem lean_workbook_282_17 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (b * c + c * a + a * b) := by
  ring_nf
  ring_nf
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_282_18 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (b * c + c * a + a * b) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_282_19 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (b * c + c * a + a * b) := by
  have h1 := sq_nonneg (a - b)
  have h2 := sq_nonneg (b - c)
  have h3 := sq_nonneg (a - c)
  linarith
theorem lean_workbook_282_20 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (b * c + c * a + a * b) := by
  rw [sq, add_assoc, add_assoc]
  have h1 : 0 ≤ (a - b)^2 := sq_nonneg (a - b)
  have h2 : 0 ≤ (b - c)^2 := sq_nonneg (b - c)
  have h3 : 0 ≤ (c - a)^2 := sq_nonneg (c - a)
  linarith
theorem lean_workbook_282_21 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (b * c + c * a + a * b) := by
  simp [sq, add_assoc, add_left_comm, add_comm]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_282_22 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (b * c + c * a + a * b) := by
  have h1 := sq_nonneg (a - b)
  have h2 := sq_nonneg (b - c)
  have h3 := sq_nonneg (c - a)
  linarith
theorem lean_workbook_282_23 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (b * c + c * a + a * b) := by
  simp [sq, add_mul, mul_add, mul_comm, mul_left_comm]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_282_24 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (b * c + c * a + a * b) := by
  simp [add_sq]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_282_25 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (b * c + c * a + a * b) := by
  rw [sq]
  rw [add_comm]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

theorem lean_workbook_283_0 {a b c : ℤ} (habc : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0) (hab : a.gcd b = 1) (hbc : b.gcd c = 1) (hca : c.gcd a = 1) : ∃ k : ℤ, a.gcd (b + k * c) = 1 := by
  refine ⟨0,?_⟩
  simp [hab,hbc,hca]
theorem lean_workbook_283_1 {a b c : ℤ} (habc : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0) (hab : a.gcd b = 1) (hbc : b.gcd c = 1) (hca : c.gcd a = 1) : ∃ k : ℤ, a.gcd (b + k * c) = 1 := by
  use 0
  simp [habc.1, hab, hbc, hca]
theorem lean_workbook_283_2 {a b c : ℤ} (habc : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0) (hab : a.gcd b = 1) (hbc : b.gcd c = 1) (hca : c.gcd a = 1) : ∃ k : ℤ, a.gcd (b + k * c) = 1 := by
  refine' ⟨0, _⟩
  simp [habc.1, hab, hbc, hca]
theorem lean_workbook_283_3 {a b c : ℤ} (habc : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0) (hab : a.gcd b = 1) (hbc : b.gcd c = 1) (hca : c.gcd a = 1) : ∃ k : ℤ, a.gcd (b + k * c) = 1 := by
  use 0
  simp [hab, hbc, hca]
theorem lean_workbook_283_4 {a b c : ℤ} (habc : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0) (hab : a.gcd b = 1) (hbc : b.gcd c = 1) (hca : c.gcd a = 1) : ∃ k : ℤ, a.gcd (b + k * c) = 1 := by
  eta_reduce at *
  eta_reduce at habc
  refine' ⟨0, by simp [hab, hbc, hca]⟩
theorem lean_workbook_283_5 {a b c : ℤ} (habc : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0) (hab : a.gcd b = 1) (hbc : b.gcd c = 1) (hca : c.gcd a = 1) : ∃ k : ℤ, a.gcd (b + k * c) = 1 := by
  refine' ⟨0, _⟩
  simpa [hab, hbc, hca] using habc
theorem lean_workbook_283_6 {a b c : ℤ} (habc : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0) (hab : a.gcd b = 1) (hbc : b.gcd c = 1) (hca : c.gcd a = 1) : ∃ k : ℤ, a.gcd (b + k * c) = 1 := by
  refine' ⟨0, _⟩
  simp [hab, habc.1, habc.2.1, hbc, hca]
theorem lean_workbook_283_7 {a b c : ℤ} (habc : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0) (hab : a.gcd b = 1) (hbc : b.gcd c = 1) (hca : c.gcd a = 1) : ∃ k : ℤ, a.gcd (b + k * c) = 1 := by
  use 0
  simp [habc, hab, hbc, hca]
theorem lean_workbook_283_8 {a b c : ℤ} (habc : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0) (hab : a.gcd b = 1) (hbc : b.gcd c = 1) (hca : c.gcd a = 1) : ∃ k : ℤ, a.gcd (b + k * c) = 1 := by
  refine ⟨0,?_⟩
  simp [hab, hbc, hca]
theorem lean_workbook_283_9 {a b c : ℤ} (habc : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0) (hab : a.gcd b = 1) (hbc : b.gcd c = 1) (hca : c.gcd a = 1) : ∃ k : ℤ, a.gcd (b + k * c) = 1 := by
  use 0
  simp [habc.1, habc.2.1, habc.2.2, hab, hbc, hca]
theorem lean_workbook_283_10 {a b c : ℤ} (habc : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0) (hab : a.gcd b = 1) (hbc : b.gcd c = 1) (hca : c.gcd a = 1) : ∃ k : ℤ, a.gcd (b + k * c) = 1 := by
  use 0
  simp [hab, hbc, hca, habc.1, habc.2.1, habc.2.2]
theorem lean_workbook_283_11 {a b c : ℤ} (habc : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0) (hab : a.gcd b = 1) (hbc : b.gcd c = 1) (hca : c.gcd a = 1) : ∃ k : ℤ, a.gcd (b + k * c) = 1 := by
  refine' ⟨0, _⟩
  rw [zero_mul, add_zero]
  simp [hab, hbc, hca, gcd_add_mul_right_right]

theorem lean_workbook_302_0 : cos θ = cos θ := by
  congr <;> simp [cos]
theorem lean_workbook_302_1 : cos θ = cos θ := by
  eta_reduce at * <;> rfl
theorem lean_workbook_302_2 : cos θ = cos θ := by
  simp [cos, exp_neg, (neg_div _ _).symm, add_mul]
theorem lean_workbook_302_3 : cos θ = cos θ := by
  simp [Subtype.ext_iff, cos_antiperiodic]
theorem lean_workbook_302_4 : cos θ = cos θ := by
  simp only [← cos_sq_add_sin_sq θ, add_comm]
theorem lean_workbook_302_5 : cos θ = cos θ := by
  simp only [cos, sin]
theorem lean_workbook_302_6 : cos θ = cos θ := by
  simp [cos, exp_neg, exp_eq_one_iff, cos, exp_neg, exp_eq_one_iff]
theorem lean_workbook_302_7 : cos θ = cos θ := by
  simp [Real.cos]
theorem lean_workbook_302_8 : cos θ = cos θ := by
  simp [cos, ← sub_eq_zero]
theorem lean_workbook_302_9 : cos θ = cos θ := by
  simp only [cos, cos]
theorem lean_workbook_302_10 : cos θ = cos θ := by
  simp [cos, Real.cos]
theorem lean_workbook_302_11 : cos θ = cos θ := by
  simp [cos, Real.cos_arccos]
theorem lean_workbook_302_12 : cos θ = cos θ := by
  simp [Complex.cos, exp_ne_zero]
theorem lean_workbook_302_13 : cos θ = cos θ := by
  simp [Complex.cos, exp_add]
theorem lean_workbook_302_14 : cos θ = cos θ := by
  simp [cos, exp_neg, (neg_div _ _).symm, add_mul, mul_assoc, mul_comm, mul_left_comm]
theorem lean_workbook_302_15 : cos θ = cos θ := by
  simp [Complex.cos, Complex.exp_eq_exp_re_mul_sin_add_cos]

theorem lean_workbook_314_0 (n : ℕ) : ∑ i in Finset.range (n+1), choose n i = 2 ^ n := by
  simp [Nat.sum_range_choose]
theorem lean_workbook_314_1 (n : ℕ) : ∑ i in Finset.range (n+1), choose n i = 2 ^ n := by
  simp [pow_two, Nat.sum_range_choose]
theorem lean_workbook_314_2 (n : ℕ) : ∑ i in Finset.range (n+1), choose n i = 2 ^ n := by
  rw [← Nat.sum_range_choose n, Finset.sum_range_succ]
theorem lean_workbook_314_3 (n : ℕ) : ∑ i in Finset.range (n+1), choose n i = 2 ^ n := by
  have := (add_pow 1 1 n).symm
  simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]

theorem lean_workbook_350_0 (n k : ℕ) (h₀ : 0 < k ∧ 0 < n) (h₁ : n ≥ k) : Nat.choose n (k - 1) = Nat.choose n (n - k + 1) := by
  rw [Nat.choose_symm_of_eq_add]
  omega
theorem lean_workbook_350_1 (n k : ℕ) (h₀ : 0 < k ∧ 0 < n) (h₁ : n ≥ k) : Nat.choose n (k - 1) = Nat.choose n (n - k + 1) := by
  apply choose_symm_of_eq_add
  rw [add_comm]
  omega
theorem lean_workbook_350_2 (n k : ℕ) (h₀ : 0 < k ∧ 0 < n) (h₁ : n ≥ k) : Nat.choose n (k - 1) = Nat.choose n (n - k + 1) := by
  rw [← Nat.choose_symm_of_eq_add]
  rw [add_comm]
  omega
theorem lean_workbook_350_3 (n k : ℕ) (h₀ : 0 < k ∧ 0 < n) (h₁ : n ≥ k) : Nat.choose n (k - 1) = Nat.choose n (n - k + 1) := by
  rw [← Nat.choose_symm_of_eq_add]
  omega
theorem lean_workbook_350_4 (n k : ℕ) (h₀ : 0 < k ∧ 0 < n) (h₁ : n ≥ k) : Nat.choose n (k - 1) = Nat.choose n (n - k + 1) := by
  rw [← choose_symm_of_eq_add]
  rw [add_comm]
  omega
theorem lean_workbook_350_5 (n k : ℕ) (h₀ : 0 < k ∧ 0 < n) (h₁ : n ≥ k) : Nat.choose n (k - 1) = Nat.choose n (n - k + 1) := by
  rw [← choose_symm_of_eq_add]
  omega

theorem lean_workbook_381_0 (y z : ℝ) : (y - z) ^ 2 * (2 * y - z) ^ 2 * (3 * y - z) ^ 2 ≥ 0 := by
  apply mul_nonneg
  nlinarith [sq_nonneg (y - z)]
  nlinarith [sq_nonneg (2 * y - z)]
theorem lean_workbook_381_1 (y z : ℝ) : (y - z) ^ 2 * (2 * y - z) ^ 2 * (3 * y - z) ^ 2 ≥ 0 := by
  apply mul_nonneg
  apply mul_nonneg
  all_goals nlinarith [sq_nonneg (y - z), sq_nonneg (2 * y - z), sq_nonneg (3 * y - z)]
theorem lean_workbook_381_2 (y z : ℝ) : (y - z) ^ 2 * (2 * y - z) ^ 2 * (3 * y - z) ^ 2 ≥ 0 := by
  refine' mul_nonneg (mul_nonneg (sq_nonneg (y - z)) (sq_nonneg _)) (sq_nonneg _)
theorem lean_workbook_381_3 (y z : ℝ) : (y - z) ^ 2 * (2 * y - z) ^ 2 * (3 * y - z) ^ 2 ≥ 0 := by
  simp [mul_assoc, mul_comm, mul_left_comm]
  apply_rules [sq_nonneg, mul_nonneg]
theorem lean_workbook_381_4 (y z : ℝ) : (y - z) ^ 2 * (2 * y - z) ^ 2 * (3 * y - z) ^ 2 ≥ 0 := by
  apply mul_nonneg
  apply mul_nonneg
  apply sq_nonneg
  apply sq_nonneg
  apply sq_nonneg
theorem lean_workbook_381_5 (y z : ℝ) : (y - z) ^ 2 * (2 * y - z) ^ 2 * (3 * y - z) ^ 2 ≥ 0 := by
  simp [sub_nonneg]
  positivity
theorem lean_workbook_381_6 (y z : ℝ) : (y - z) ^ 2 * (2 * y - z) ^ 2 * (3 * y - z) ^ 2 ≥ 0 := by
  apply mul_nonneg
  apply mul_nonneg
  apply pow_two_nonneg
  apply pow_two_nonneg
  apply pow_two_nonneg
theorem lean_workbook_381_7 (y z : ℝ) : (y - z) ^ 2 * (2 * y - z) ^ 2 * (3 * y - z) ^ 2 ≥ 0 := by
  apply mul_nonneg
  apply mul_nonneg
  all_goals apply pow_two_nonneg
theorem lean_workbook_381_8 (y z : ℝ) : (y - z) ^ 2 * (2 * y - z) ^ 2 * (3 * y - z) ^ 2 ≥ 0 := by
  apply mul_nonneg
  repeat nlinarith [sq_nonneg (y - z)]
theorem lean_workbook_381_9 (y z : ℝ) : (y - z) ^ 2 * (2 * y - z) ^ 2 * (3 * y - z) ^ 2 ≥ 0 := by
  apply mul_nonneg
  apply mul_nonneg
  all_goals nlinarith [sq_nonneg (y - z)]
theorem lean_workbook_381_10 (y z : ℝ) : (y - z) ^ 2 * (2 * y - z) ^ 2 * (3 * y - z) ^ 2 ≥ 0 := by
  apply mul_nonneg
  apply mul_nonneg
  repeat' nlinarith [sq_nonneg (y - z)]
theorem lean_workbook_381_11 (y z : ℝ) : (y - z) ^ 2 * (2 * y - z) ^ 2 * (3 * y - z) ^ 2 ≥ 0 := by
  apply mul_nonneg <;> nlinarith [sq_nonneg (y - z), sq_nonneg (2 * y - z)]
theorem lean_workbook_381_12 (y z : ℝ) : (y - z) ^ 2 * (2 * y - z) ^ 2 * (3 * y - z) ^ 2 ≥ 0 := by
  apply_rules [sq_nonneg, mul_nonneg]
theorem lean_workbook_381_13 (y z : ℝ) : (y - z) ^ 2 * (2 * y - z) ^ 2 * (3 * y - z) ^ 2 ≥ 0 := by
  apply mul_nonneg
  repeat' nlinarith [sq_nonneg (y - z)]
theorem lean_workbook_381_14 (y z : ℝ) : (y - z) ^ 2 * (2 * y - z) ^ 2 * (3 * y - z) ^ 2 ≥ 0 := by
  apply mul_nonneg
  apply mul_nonneg <;> apply pow_two_nonneg
  apply pow_two_nonneg
theorem lean_workbook_381_15 (y z : ℝ) : (y - z) ^ 2 * (2 * y - z) ^ 2 * (3 * y - z) ^ 2 ≥ 0 := by
  apply mul_nonneg
  apply mul_nonneg <;> nlinarith [sq_nonneg (y - z), sq_nonneg (2 * y - z)]
  nlinarith [sq_nonneg (y - z), sq_nonneg (2 * y - z), sq_nonneg (3 * y - z)]
theorem lean_workbook_381_16 (y z : ℝ) : (y - z) ^ 2 * (2 * y - z) ^ 2 * (3 * y - z) ^ 2 ≥ 0 := by
  refine' mul_nonneg (mul_nonneg _ _) _ <;> positivity
theorem lean_workbook_381_17 (y z : ℝ) : (y - z) ^ 2 * (2 * y - z) ^ 2 * (3 * y - z) ^ 2 ≥ 0 := by
  apply mul_nonneg
  apply mul_nonneg
  exact sq_nonneg (y - z)
  exact sq_nonneg (2 * y - z)
  exact sq_nonneg (3 * y - z)

theorem lean_workbook_407_0 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  induction' n with n ih
  simp [Nat.dvd_zero]
  rw [Nat.pow_succ]
  omega
theorem lean_workbook_407_1 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  induction' n with n IH
  rw [Nat.pow_zero]
  decide
  rw [Nat.pow_succ]
  omega
theorem lean_workbook_407_2 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  induction' n with n hn
  simp [Nat.pow_zero, Nat.mod_self]
  omega
theorem lean_workbook_407_3 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  induction' n with n hn
  simp [Nat.dvd_zero]
  omega
theorem lean_workbook_407_4 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  induction' n with n ih
  case zero => simp [Nat.pow_zero]
  rw [Nat.pow_succ]
  omega
theorem lean_workbook_407_5 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  induction' n with n IH
  case zero => simp [Nat.dvd_one]
  omega
theorem lean_workbook_407_6 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  induction' n with n IH
  simp [Nat.zero_eq]
  rw [Nat.pow_succ]
  omega
theorem lean_workbook_407_7 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  induction' n with d hd
  rw [pow_zero]
  decide
  rw[pow_succ]
  omega
theorem lean_workbook_407_8 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  induction' n with n ih
  simp only [Nat.zero_eq, pow_zero, Nat.sub_self, dvd_zero]
  rw [pow_succ]
  omega
theorem lean_workbook_407_9 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  induction' n with n ih
  simp [Nat.pow_zero]
  rw [Nat.pow_succ]
  omega
theorem lean_workbook_407_10 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  induction' n with n ih
  simp [Nat.pow_zero, Nat.dvd_one]
  simp [Nat.pow_succ]
  omega
theorem lean_workbook_407_11 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  induction' n with n hn
  simp [Nat.sub_zero]
  omega
theorem lean_workbook_407_12 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  induction' n with n IH
  simp [Nat.pow_zero, Nat.sub_self]
  omega
theorem lean_workbook_407_13 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  induction' n with n ih
  simp [Nat.pow_succ]
  omega
theorem lean_workbook_407_14 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  induction' n with pn hpn
  simp [Nat.dvd_zero]
  omega
theorem lean_workbook_407_15 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  induction' n with n ih
  simp [Nat.zero_eq]
  simp [pow_succ, Nat.mul_mod, ih, Nat.add_mod]
  omega
theorem lean_workbook_407_16 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  rw [← one_pow n]
  exact nat_sub_dvd_pow_sub_pow _ 1 n
theorem lean_workbook_407_17 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  induction' n with k hk
  simp [Nat.zero_eq, Nat.pow_zero, Nat.sub_self]
  omega
theorem lean_workbook_407_18 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  induction' n with n hn
  simp [Nat.pow_zero, Nat.sub_self]
  rw [Nat.pow_succ]
  omega
theorem lean_workbook_407_19 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  induction' n with n IH
  simp [Nat.zero_eq]
  simp [pow_succ, Nat.mul_mod, Nat.add_mod, IH]
  omega
theorem lean_workbook_407_20 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  induction' n with n IH
  simp [Nat.pow_zero]
  omega
theorem lean_workbook_407_21 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  induction n <;> simp [*, pow_succ, Nat.mul_sub_left_distrib, mul_comm]
  omega
theorem lean_workbook_407_22 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  induction' n with n IH
  simp [Nat.zero_eq]
  simp [Nat.pow_succ]
  omega
theorem lean_workbook_407_23 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  rw [show (10:ℕ) = 9 + 1 by norm_num]
  simpa only [one_pow] using nat_sub_dvd_pow_sub_pow _ 1 n
theorem lean_workbook_407_24 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  induction' n with n ih
  simp [Nat.pow_zero]
  simp [Nat.pow_succ]
  omega
theorem lean_workbook_407_25 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  simpa [one_pow] using nat_sub_dvd_pow_sub_pow _ 1 n
theorem lean_workbook_407_26 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  induction' n with n ih
  simp [Nat.mod_eq_of_lt]
  omega
theorem lean_workbook_407_27 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  induction' n with n IH
  case zero => simp
  rw [Nat.pow_succ]
  omega
theorem lean_workbook_407_28 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  induction' n with n IH
  simp [Nat.pow_zero]
  simp [Nat.pow_succ]
  omega
theorem lean_workbook_407_29 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  induction' n with n IH
  simp [Nat.pow_zero, Nat.mod_self]
  omega
theorem lean_workbook_407_30 : ∀ n:ℕ, 9 ∣ (10^n - 1) := by
  intro n
  induction' n with n IH
  simp [Nat.pow_zero, Nat.mod_self]
  simp [Nat.pow_succ, Nat.mul_mod, IH]
  omega

theorem lean_workbook_436_0 : 7^7 < 2^20 := by
  norm_num [show (2 : ℕ) = 2 from rfl]
theorem lean_workbook_436_1 : 7^7 < 2^20 := by
  norm_num [Nat.pow_succ, Nat.pow_zero]
theorem lean_workbook_436_2 : 7^7 < 2^20 := by
  norm_num [show (7:ℤ) ^ 7 = 823543 by norm_cast, show (2:ℤ) ^ 20 = 1048576 by norm_cast]
theorem lean_workbook_436_3 : 7^7 < 2^20 := by
  norm_num [pow_succ, pow_zero]
theorem lean_workbook_436_4 : 7^7 < 2^20 := by
  repeat' rw [pow_succ]
  norm_num [pow_zero]
theorem lean_workbook_436_5 : 7^7 < 2^20 := by
  norm_num [pow_succ, pow_mul, pow_one, pow_succ]
theorem lean_workbook_436_6 : 7^7 < 2^20 := by
  norm_num [pow_succ, pow_zero, pow_one, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
theorem lean_workbook_436_7 : 7^7 < 2^20 := by
  exact mod_cast (by norm_num : 7^7 < 2^20)
theorem lean_workbook_436_8 : 7^7 < 2^20 := by
  norm_num [pow_succ, pow_zero, pow_one, pow_two, pow_three]
theorem lean_workbook_436_9 : 7^7 < 2^20 := by
  norm_num [show (2: Real) = (2:ℚ) by norm_cast, show (20: Real) = (20:ℚ) by norm_cast]
theorem lean_workbook_436_10 : 7^7 < 2^20 := by
  norm_num [pow_succ, pow_zero, pow_one, Nat.mul, Nat.add]
theorem lean_workbook_436_11 : 7^7 < 2^20 := by
  linarith [pow_succ 7 6]
theorem lean_workbook_436_12 : 7^7 < 2^20 := by
  norm_num [show 7^7 = 823543 from rfl, show 2^20 = 1048576 from rfl]
theorem lean_workbook_436_13 : 7^7 < 2^20 := by
  norm_num [pow_succ, pow_succ]
theorem lean_workbook_436_14 : 7^7 < 2^20 := by
  norm_num [show (7:ℝ)^7 = 823543 by norm_num, show 2^20 = 1048576 by norm_num]
theorem lean_workbook_436_15 : 7^7 < 2^20 := by
  norm_num [show (7:ℝ)^7 = 823543 by norm_num, show (2:ℝ)^20 = 1048576 by norm_num]
theorem lean_workbook_436_16 : 7^7 < 2^20 := by
  norm_num [pow_succ, pow_succ, pow_succ, pow_succ, pow_succ, pow_succ, pow_succ]
theorem lean_workbook_436_17 : 7^7 < 2^20 := by
  norm_num [pow_succ, mul_comm, mul_assoc, mul_left_comm]
theorem lean_workbook_436_18 : 7^7 < 2^20 := by
  norm_num [show (2:Real) = (2:ℕ) by norm_cast, show (20:Real) = (20:ℕ) by norm_cast]
theorem lean_workbook_436_19 : 7^7 < 2^20 := by
  norm_num [pow_succ, pow_succ, pow_succ]
theorem lean_workbook_436_20 : 7^7 < 2^20 := by
  repeat' rw [Nat.pow_succ]
  norm_num
theorem lean_workbook_436_21 : 7^7 < 2^20 := by
  linarith only [pow_one 7, pow_zero 2]
theorem lean_workbook_436_22 : 7^7 < 2^20 := by
  norm_num [pow_succ, pow_succ, pow_one]
theorem lean_workbook_436_23 : 7^7 < 2^20 := by
  norm_num [show (7:ℝ) = 2^3 - 1 by norm_num, show (3:ℝ) = 2 + 1 by norm_num]
theorem lean_workbook_436_24 : 7^7 < 2^20 := by
  norm_num [pow_succ, pow_zero, pow_one]
theorem lean_workbook_436_25 : 7^7 < 2^20 := by
  linarith [pow_succ 2 9, pow_succ 7 6]
theorem lean_workbook_436_26 : 7^7 < 2^20 := by
  norm_num [show 2^3 = 8 by rfl]
theorem lean_workbook_436_27 : 7^7 < 2^20 := by
  norm_num [pow_succ, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
theorem lean_workbook_436_28 : 7^7 < 2^20 := by
  norm_num [pow_succ, pow_zero, mul_one, mul_add, mul_comm, mul_left_comm]
theorem lean_workbook_436_29 : 7^7 < 2^20 := by
  nlinarith [pow_one 7, pow_zero 2]
theorem lean_workbook_436_30 : 7^7 < 2^20 := by
  norm_num [Nat.pow_succ, Nat.pow_zero, Nat.pow_one, Nat.mul_comm]
theorem lean_workbook_436_31 : 7^7 < 2^20 := by
  clear aops_67
  norm_num

theorem lean_workbook_485_0 (x y : ℝ) (h : 0 < x ∧ 0 < y) (h2 : x^3 + y^3 = x - y) : x^2 - y^2 < 1 := by
  nlinarith only [h.1, h.2, h2]
theorem lean_workbook_485_1 (x y : ℝ) (h : 0 < x ∧ 0 < y) (h2 : x^3 + y^3 = x - y) : x^2 - y^2 < 1 := by
  have h3 : x^3 + y^3 = x - y := h2
  field_simp [pow_two]
  nlinarith [h.1, h.2, h3]
theorem lean_workbook_485_2 (x y : ℝ) (h : 0 < x ∧ 0 < y) (h2 : x^3 + y^3 = x - y) : x^2 - y^2 < 1 := by
  nlinarith [pow_pos h.1 3, pow_pos h.2 3, h2]
theorem lean_workbook_485_3 (x y : ℝ) (h : 0 < x ∧ 0 < y) (h2 : x^3 + y^3 = x - y) : x^2 - y^2 < 1 := by
  have h4 : 0 < x + y := by linarith
  nlinarith [h.1, h.2, h2, h4]
theorem lean_workbook_485_4 (x y : ℝ) (h : 0 < x ∧ 0 < y) (h2 : x^3 + y^3 = x - y) : x^2 - y^2 < 1 := by
  have h1 := sq_pos_of_pos h.1
  have h3 := sq_pos_of_pos h.2
  nlinarith
theorem lean_workbook_485_5 (x y : ℝ) (h : 0 < x ∧ 0 < y) (h2 : x^3 + y^3 = x - y) : x^2 - y^2 < 1 := by
  have h1 := sq_pos_of_pos h.1
  have h3 := sq_pos_of_pos h.2
  nlinarith [h2, h1, h3]
theorem lean_workbook_485_6 (x y : ℝ) (h : 0 < x ∧ 0 < y) (h2 : x^3 + y^3 = x - y) : x^2 - y^2 < 1 := by
  have h1 := h2
  nlinarith [h.1, h.2, h1]
theorem lean_workbook_485_7 (x y : ℝ) (h : 0 < x ∧ 0 < y) (h2 : x^3 + y^3 = x - y) : x^2 - y^2 < 1 := by
  field_simp [pow_two]
  nlinarith [h.1, h2]
theorem lean_workbook_485_8 (x y : ℝ) (h : 0 < x ∧ 0 < y) (h2 : x^3 + y^3 = x - y) : x^2 - y^2 < 1 := by
  field_simp [sq, h.1, h.2]
  nlinarith [h.1, h.2, h2]
theorem lean_workbook_485_9 (x y : ℝ) (h : 0 < x ∧ 0 < y) (h2 : x^3 + y^3 = x - y) : x^2 - y^2 < 1 := by
  have h3 : 0 < x^2 := pow_pos h.1 2
  nlinarith [h2]
theorem lean_workbook_485_10 (x y : ℝ) (h : 0 < x ∧ 0 < y) (h2 : x^3 + y^3 = x - y) : x^2 - y^2 < 1 := by
  ring_nf at h2
  nlinarith [h.1, h.2, h2]
theorem lean_workbook_485_11 (x y : ℝ) (h : 0 < x ∧ 0 < y) (h2 : x^3 + y^3 = x - y) : x^2 - y^2 < 1 := by
  nlinarith [h2, h]
theorem lean_workbook_485_12 (x y : ℝ) (h : 0 < x ∧ 0 < y) (h2 : x^3 + y^3 = x - y) : x^2 - y^2 < 1 := by
  have h1 : 0 < y^3 := pow_pos h.2 3
  nlinarith [h.1, h2]
theorem lean_workbook_485_13 (x y : ℝ) (h : 0 < x ∧ 0 < y) (h2 : x^3 + y^3 = x - y) : x^2 - y^2 < 1 := by
  field_simp [pow_two, pow_three] at h2 ⊢
  nlinarith
theorem lean_workbook_485_14 (x y : ℝ) (h : 0 < x ∧ 0 < y) (h2 : x^3 + y^3 = x - y) : x^2 - y^2 < 1 := by
  contrapose! h2
  nlinarith [h]
theorem lean_workbook_485_15 (x y : ℝ) (h : 0 < x ∧ 0 < y) (h2 : x^3 + y^3 = x - y) : x^2 - y^2 < 1 := by
  nlinarith [h, h2]
theorem lean_workbook_485_16 (x y : ℝ) (h : 0 < x ∧ 0 < y) (h2 : x^3 + y^3 = x - y) : x^2 - y^2 < 1 := by
  norm_num at *
  nlinarith
theorem lean_workbook_485_17 (x y : ℝ) (h : 0 < x ∧ 0 < y) (h2 : x^3 + y^3 = x - y) : x^2 - y^2 < 1 := by
  field_simp [sq, lt_one_iff]
  nlinarith [h2]
theorem lean_workbook_485_18 (x y : ℝ) (h : 0 < x ∧ 0 < y) (h2 : x^3 + y^3 = x - y) : x^2 - y^2 < 1 := by
  have h3 := sq_nonneg (x^2 - y^2)
  nlinarith [h.1, h.2, h2, h3]
theorem lean_workbook_485_19 (x y : ℝ) (h : 0 < x ∧ 0 < y) (h2 : x^3 + y^3 = x - y) : x^2 - y^2 < 1 := by
  have h3 : x^3 + y^3 = x - y := h2
  nlinarith [h.1, h.2, h3]
theorem lean_workbook_485_20 (x y : ℝ) (h : 0 < x ∧ 0 < y) (h2 : x^3 + y^3 = x - y) : x^2 - y^2 < 1 := by
  nlinarith [sq_nonneg x, sq_nonneg y, h.1, h2]
theorem lean_workbook_485_21 (x y : ℝ) (h : 0 < x ∧ 0 < y) (h2 : x^3 + y^3 = x - y) : x^2 - y^2 < 1 := by
  contrapose! h2
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
theorem lean_workbook_485_22 (x y : ℝ) (h : 0 < x ∧ 0 < y) (h2 : x^3 + y^3 = x - y) : x^2 - y^2 < 1 := by
  nlinarith [pow_pos h.1 2, pow_pos h.2 2, h2]
theorem lean_workbook_485_23 (x y : ℝ) (h : 0 < x ∧ 0 < y) (h2 : x^3 + y^3 = x - y) : x^2 - y^2 < 1 := by
  have h3 : 0 < x^2 := pow_pos h.1 2
  nlinarith [h.1, h.2, h2]
theorem lean_workbook_485_24 (x y : ℝ) (h : 0 < x ∧ 0 < y) (h2 : x^3 + y^3 = x - y) : x^2 - y^2 < 1 := by
  have h2' : x^3 + y^3 = x - y := h2
  nlinarith

theorem lean_workbook_490_0 : 3 ∣ c → 3^2 ∣ 3*c → 3 ∣ c := by
  simp (config := { contextual := true }) [Nat.pow_succ]
theorem lean_workbook_490_1 : 3 ∣ c → 3^2 ∣ 3*c → 3 ∣ c := by
  rintro h1 h2
  simp [pow_two] at h2
  omega
theorem lean_workbook_490_2 : 3 ∣ c → 3^2 ∣ 3*c → 3 ∣ c := by
  rintro h₁ h₂
  rw [pow_two] at h₂
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h₂
theorem lean_workbook_490_3 : 3 ∣ c → 3^2 ∣ 3*c → 3 ∣ c := by
  intro h3 h3sq
  rw [pow_two] at h3sq
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3sq
theorem lean_workbook_490_4 : 3 ∣ c → 3^2 ∣ 3*c → 3 ∣ c := by
  intro h1 h2
  simp only [sq, Nat.pow_succ] at h2
  omega
theorem lean_workbook_490_5 : 3 ∣ c → 3^2 ∣ 3*c → 3 ∣ c := by
  intro h1 h2
  rw [pow_two] at h2
  simp at h2
  omega
theorem lean_workbook_490_6 : 3 ∣ c → 3^2 ∣ 3*c → 3 ∣ c := by
  intro h1 h2
  simp [sq] at h2
  omega
theorem lean_workbook_490_7 : 3 ∣ c → 3^2 ∣ 3*c → 3 ∣ c := by
  intro h1 h2
  rw [pow_two] at h2
  omega
theorem lean_workbook_490_8 : 3 ∣ c → 3^2 ∣ 3*c → 3 ∣ c := by
  intro h1 h2
  rw [pow_two] at h2
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
theorem lean_workbook_490_9 : 3 ∣ c → 3^2 ∣ 3*c → 3 ∣ c := by
  intro h₁ h₂
  simp [pow_two] at h₂
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h₂
theorem lean_workbook_490_10 : 3 ∣ c → 3^2 ∣ 3*c → 3 ∣ c := by
  intro h1 h2
  simp [pow_two] at h2
  exact h1
theorem lean_workbook_490_11 : 3 ∣ c → 3^2 ∣ 3*c → 3 ∣ c := by
  intro h3 h9
  rw [pow_two] at h9
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h9
theorem lean_workbook_490_12 : 3 ∣ c → 3^2 ∣ 3*c → 3 ∣ c := by
  intro h1
  intro h2
  rw [pow_two] at h2
  simp [h1, h2]
theorem lean_workbook_490_13 : 3 ∣ c → 3^2 ∣ 3*c → 3 ∣ c := by
  intro h1 h2
  rw [show c = 3*(c/3) by rw [Nat.mul_div_cancel' h1]]
  omega
theorem lean_workbook_490_14 : 3 ∣ c → 3^2 ∣ 3*c → 3 ∣ c := by
  intro h3
  intro h3sq
  rw [pow_two] at h3sq
  omega
theorem lean_workbook_490_15 : 3 ∣ c → 3^2 ∣ 3*c → 3 ∣ c := by
  intro h1 h2
  simp only [pow_two] at h2
  simp [dvd_mul_right] at h2
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
theorem lean_workbook_490_16 : 3 ∣ c → 3^2 ∣ 3*c → 3 ∣ c := by
  intro h3c h3sq3c
  rw [pow_two] at h3sq3c
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3sq3c
theorem lean_workbook_490_17 : 3 ∣ c → 3^2 ∣ 3*c → 3 ∣ c := by
  rintro h1 h2
  rw [pow_two] at h2
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
theorem lean_workbook_490_18 : 3 ∣ c → 3^2 ∣ 3*c → 3 ∣ c := by
  rintro h1 h2
  rw [pow_two] at h2
  simp_all
theorem lean_workbook_490_19 : 3 ∣ c → 3^2 ∣ 3*c → 3 ∣ c := by
  rintro ⟨k, rfl⟩ ⟨k', hk'⟩
  use k'
  linarith
theorem lean_workbook_490_20 : 3 ∣ c → 3^2 ∣ 3*c → 3 ∣ c := by
  intro h₁ h₂
  rw [pow_two] at h₂
  simp [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod] at h₂
  simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod] at h₂
  omega
theorem lean_workbook_490_21 : 3 ∣ c → 3^2 ∣ 3*c → 3 ∣ c := by
  intro h
  simp [h]
theorem lean_workbook_490_22 : 3 ∣ c → 3^2 ∣ 3*c → 3 ∣ c := by
  rintro ⟨k, rfl⟩ ⟨k', hk'⟩
  exact ⟨k', by linarith⟩
theorem lean_workbook_490_23 : 3 ∣ c → 3^2 ∣ 3*c → 3 ∣ c := by
  rintro ⟨k, rfl⟩ ⟨l, h⟩
  use l
  linarith
theorem lean_workbook_490_24 : 3 ∣ c → 3^2 ∣ 3*c → 3 ∣ c := by
  simp [Nat.pow_succ]
  intro h₁ h₂
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h₂
theorem lean_workbook_490_25 : 3 ∣ c → 3^2 ∣ 3*c → 3 ∣ c := by
  exact fun h1 h2 ↦ h1

theorem lean_workbook_504_0 : 11 ^ 10 ≡ 1 [ZMOD 100] := by
  apply Int.modEq_of_dvd
  norm_num [Int.ModEq]
theorem lean_workbook_504_1 : 11 ^ 10 ≡ 1 [ZMOD 100] := by
  conv => lhs; rw [← one_mul 11, pow_succ]
theorem lean_workbook_504_2 : 11 ^ 10 ≡ 1 [ZMOD 100] := by
  change 11 ^ 10 % 100 = 1
  norm_num [Nat.mod_eq_of_lt]
theorem lean_workbook_504_3 : 11 ^ 10 ≡ 1 [ZMOD 100] := by
  norm_num [Int.ModEq, Int.modEq_of_dvd]
theorem lean_workbook_504_4 : 11 ^ 10 ≡ 1 [ZMOD 100] := by
  norm_num [Int.ModEq, Int.dvd_iff_emod_eq_zero]
theorem lean_workbook_504_5 : 11 ^ 10 ≡ 1 [ZMOD 100] := by
  simp only [Int.ModEq, pow_mod, Int.ofNat_mod]
  norm_num
theorem lean_workbook_504_6 : 11 ^ 10 ≡ 1 [ZMOD 100] := by
  show 11 ^ 10 % 100 = 1 % 100
  norm_num [pow_succ]
theorem lean_workbook_504_7 : 11 ^ 10 ≡ 1 [ZMOD 100] := by
  exact (show 11 ^ 10 % 100 = 1 from by norm_num)
theorem lean_workbook_504_8 : 11 ^ 10 ≡ 1 [ZMOD 100] := by
  norm_num [Int.ModEq, Int.emod]
theorem lean_workbook_504_9 : 11 ^ 10 ≡ 1 [ZMOD 100] := by
  conv => lhs; rw [← Nat.mod_add_div 10 100]
theorem lean_workbook_504_10 : 11 ^ 10 ≡ 1 [ZMOD 100] := by
  conv => lhs; rw [← pow_one (11 : ℤ)]
theorem lean_workbook_504_11 : 11 ^ 10 ≡ 1 [ZMOD 100] := by
  conv => lhs; rw [← one_mul 11]; congr; norm_num
theorem lean_workbook_504_12 : 11 ^ 10 ≡ 1 [ZMOD 100] := by
  norm_num [Int.ModEq]
theorem lean_workbook_504_13 : 11 ^ 10 ≡ 1 [ZMOD 100] := by
  conv => lhs; rw [← one_mul (11 ^ 10)]
theorem lean_workbook_504_14 : 11 ^ 10 ≡ 1 [ZMOD 100] := by
  show 11 ^ 10 % 100 = 1
  norm_num
theorem lean_workbook_504_15 : 11 ^ 10 ≡ 1 [ZMOD 100] := by
  norm_num [pow_succ, Int.ModEq]
theorem lean_workbook_504_16 : 11 ^ 10 ≡ 1 [ZMOD 100] := by
  change 11 ^ 10 % 100 = 1
  norm_num [pow_succ]
theorem lean_workbook_504_17 : 11 ^ 10 ≡ 1 [ZMOD 100] := by
  conv => lhs; rw [← one_mul (11 ^ 10), pow_succ]
theorem lean_workbook_504_18 : 11 ^ 10 ≡ 1 [ZMOD 100] := by
  simp [Int.ModEq]
theorem lean_workbook_504_19 : 11 ^ 10 ≡ 1 [ZMOD 100] := by
  simp only [Int.ModEq]
  norm_num

theorem lean_workbook_505_0 : ∀ n : ℤ, 2 ∣ n^5 - n := by
  intro n
  obtain ⟨m, rfl⟩ | ⟨m, rfl⟩ := Int.even_or_odd n
  all_goals ring_nf; simp [Int.dvd_iff_emod_eq_zero, Int.add_emod, Int.mul_emod, Int.mod_self]
theorem lean_workbook_505_1 : ∀ n : ℤ, 2 ∣ n^5 - n := by
  intro n
  obtain ⟨b, rfl⟩ | ⟨c, rfl⟩ := Int.even_or_odd n
  all_goals ring_nf; simp [Int.dvd_iff_emod_eq_zero, Int.add_emod, Int.mul_emod, Int.mod_self]

theorem lean_workbook_508_0 (a b d x y : ℤ) (h₁ : d = gcd a b) : d ∣ a * x + b * y := by
  rw [h₁]
  apply dvd_add
  exact dvd_mul_of_dvd_left (gcd_dvd_left a b) _
  exact dvd_mul_of_dvd_left (gcd_dvd_right a b) _
theorem lean_workbook_508_1 (a b d x y : ℤ) (h₁ : d = gcd a b) : d ∣ a * x + b * y := by
  rw [h₁]
  exact dvd_add ((gcd_dvd_left a b).mul_right _) ((gcd_dvd_right a b).mul_right _)
theorem lean_workbook_508_2 (a b d x y : ℤ) (h₁ : d = gcd a b) : d ∣ a * x + b * y := by
  rw [h₁]
  apply dvd_add
  exact dvd_mul_of_dvd_left (gcd_dvd_left a b) _
  exact dvd_mul_of_dvd_left (gcd_dvd_right a b) y
theorem lean_workbook_508_3 (a b d x y : ℤ) (h₁ : d = gcd a b) : d ∣ a * x + b * y := by
  rw [h₁]
  exact dvd_add (dvd_mul_of_dvd_left (gcd_dvd_left a b) x) (dvd_mul_of_dvd_left (gcd_dvd_right a b) y)

theorem lean_workbook_513_0 : a ^ 2 + 1 ≡ 0 [ZMOD 3] → a ^ 2 ≡ -1 [ZMOD 3] := by
  intro h
  rw [Int.modEq_iff_dvd] at *
  simpa using h
theorem lean_workbook_513_1 : a ^ 2 + 1 ≡ 0 [ZMOD 3] → a ^ 2 ≡ -1 [ZMOD 3] := by
  intro h
  rw [Int.modEq_iff_dvd] at *
  simpa [Int.sub_eq_add_neg] using h
theorem lean_workbook_513_2 : a ^ 2 + 1 ≡ 0 [ZMOD 3] → a ^ 2 ≡ -1 [ZMOD 3] := by
  intro h
  have h1 : a ^ 2 + 1 ≡ 0 [ZMOD 3] := h
  rw [Int.ModEq] at h1 ⊢
  omega
theorem lean_workbook_513_3 : a ^ 2 + 1 ≡ 0 [ZMOD 3] → a ^ 2 ≡ -1 [ZMOD 3] := by
  intro h
  rw [Int.ModEq] at *
  omega
theorem lean_workbook_513_4 : a ^ 2 + 1 ≡ 0 [ZMOD 3] → a ^ 2 ≡ -1 [ZMOD 3] := by
  intro h
  rw [Int.ModEq] at h ⊢
  omega
theorem lean_workbook_513_5 : a ^ 2 + 1 ≡ 0 [ZMOD 3] → a ^ 2 ≡ -1 [ZMOD 3] := by
  simp [← sq, Int.ModEq]
  intro h
  omega
theorem lean_workbook_513_6 : a ^ 2 + 1 ≡ 0 [ZMOD 3] → a ^ 2 ≡ -1 [ZMOD 3] := by
  rw [Int.ModEq]
  rw [Int.ModEq]
  simp [sub_eq_add_neg]
  intro h
  omega
theorem lean_workbook_513_7 : a ^ 2 + 1 ≡ 0 [ZMOD 3] → a ^ 2 ≡ -1 [ZMOD 3] := by
  simp only [Int.ModEq, Int.emod_eq_emod_iff_emod_sub_eq_zero]
  intro h
  omega
theorem lean_workbook_513_8 : a ^ 2 + 1 ≡ 0 [ZMOD 3] → a ^ 2 ≡ -1 [ZMOD 3] := by
  rintro h
  rw [Int.ModEq] at h ⊢
  omega
theorem lean_workbook_513_9 : a ^ 2 + 1 ≡ 0 [ZMOD 3] → a ^ 2 ≡ -1 [ZMOD 3] := by
  intro h
  rw [Int.ModEq] at h ⊢
  simp [h]
  omega
theorem lean_workbook_513_10 : a ^ 2 + 1 ≡ 0 [ZMOD 3] → a ^ 2 ≡ -1 [ZMOD 3] := by
  simp only [Int.ModEq, Int.ofNat_add, Int.ofNat_one]
  intro h
  omega

theorem lean_workbook_519_0 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1) (h : a^2 + b^2 + c^2 = 1) : (bc / (a - a^3) + ca / (b - b^3) + ab / (c - c^3)) ≥ 5 / 2 := by
  simp [div_eq_mul_inv]
  nlinarith [ha, hb, hc, hab, h]
theorem lean_workbook_519_1 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1) (h : a^2 + b^2 + c^2 = 1) : (bc / (a - a^3) + ca / (b - b^3) + ab / (c - c^3)) ≥ 5 / 2 := by
  field_simp [h, ha.ne', hb.ne', hc.ne', hab]
  nlinarith
theorem lean_workbook_519_2 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1) (h : a^2 + b^2 + c^2 = 1) : (bc / (a - a^3) + ca / (b - b^3) + ab / (c - c^3)) ≥ 5 / 2 := by
  field_simp [ha.ne', hb.ne', hc.ne']
  nlinarith [hab, h]
theorem lean_workbook_519_3 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1) (h : a^2 + b^2 + c^2 = 1) : (bc / (a - a^3) + ca / (b - b^3) + ab / (c - c^3)) ≥ 5 / 2 := by
  field_simp [le_refl]
  rw [add_comm]
  nlinarith
theorem lean_workbook_519_4 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1) (h : a^2 + b^2 + c^2 = 1) : (bc / (a - a^3) + ca / (b - b^3) + ab / (c - c^3)) ≥ 5 / 2 := by
  field_simp
  nlinarith [ha, hb, hc, hab, h]

theorem lean_workbook_525_0 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b ≤ c) : a * b + b ^ 2 + c ^ 2 ≥ (7 / 9) * (a + 2 * b) * c := by
  ring_nf
  have : 0 ≤ (a - b)^2 := sq_nonneg (a - b)
  nlinarith [ha, hb, hc, hab]
theorem lean_workbook_525_1 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b ≤ c) : a * b + b ^ 2 + c ^ 2 ≥ (7 / 9) * (a + 2 * b) * c := by
  have h1 : 0 ≤ (c - a - b) ^ 2 := sq_nonneg (c - a - b)
  nlinarith [ha, hb, hc, hab, h1]
theorem lean_workbook_525_2 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b ≤ c) : a * b + b ^ 2 + c ^ 2 ≥ (7 / 9) * (a + 2 * b) * c := by
  have : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  nlinarith [sq_nonneg (a - b), ha, hb, hc, hab]
theorem lean_workbook_525_3 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b ≤ c) : a * b + b ^ 2 + c ^ 2 ≥ (7 / 9) * (a + 2 * b) * c := by
  field_simp [ha.ne', hb.ne', hc.ne', hab]
  nlinarith
theorem lean_workbook_525_4 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b ≤ c) : a * b + b ^ 2 + c ^ 2 ≥ (7 / 9) * (a + 2 * b) * c := by
  nlinarith [sq_nonneg (b - c), sq_nonneg (a - b), sq_nonneg (b - a)]
theorem lean_workbook_525_5 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b ≤ c) : a * b + b ^ 2 + c ^ 2 ≥ (7 / 9) * (a + 2 * b) * c := by
  nlinarith [sq_nonneg (c - a - b), ha, hb, hc]
theorem lean_workbook_525_6 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b ≤ c) : a * b + b ^ 2 + c ^ 2 ≥ (7 / 9) * (a + 2 * b) * c := by
  nlinarith only [ha, hb, hc, hab]
theorem lean_workbook_525_7 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b ≤ c) : a * b + b ^ 2 + c ^ 2 ≥ (7 / 9) * (a + 2 * b) * c := by
  field_simp [ha, hb, hc]
  nlinarith
theorem lean_workbook_525_8 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b ≤ c) : a * b + b ^ 2 + c ^ 2 ≥ (7 / 9) * (a + 2 * b) * c := by
  nlinarith [sq_nonneg (c - a - b), ha, hb, hc, hab]

theorem lean_workbook_543_0 : ∀ p : ℕ, p.Prime → ∀ n : ℕ, p - 1 ∣ p ^ n - 1 := by
  rintro p hp n
  eta_reduce at *
  simpa only [one_pow] using nat_sub_dvd_pow_sub_pow p 1 n
theorem lean_workbook_543_1 : ∀ p : ℕ, p.Prime → ∀ n : ℕ, p - 1 ∣ p ^ n - 1 := by
  intro p hp n
  eta_reduce at *
  eta_reduce at hp
  simpa only [one_pow] using nat_sub_dvd_pow_sub_pow _ 1 n
theorem lean_workbook_543_2 : ∀ p : ℕ, p.Prime → ∀ n : ℕ, p - 1 ∣ p ^ n - 1 := by
  intros p hp n
  simpa only [one_pow] using nat_sub_dvd_pow_sub_pow _ 1 n
theorem lean_workbook_543_3 : ∀ p : ℕ, p.Prime → ∀ n : ℕ, p - 1 ∣ p ^ n - 1 := by
  intro p hyp n
  simpa only [one_pow] using nat_sub_dvd_pow_sub_pow p 1 n
theorem lean_workbook_543_4 : ∀ p : ℕ, p.Prime → ∀ n : ℕ, p - 1 ∣ p ^ n - 1 := by
  intro p hp n
  simpa [one_pow] using nat_sub_dvd_pow_sub_pow _ 1 n
theorem lean_workbook_543_5 : ∀ p : ℕ, p.Prime → ∀ n : ℕ, p - 1 ∣ p ^ n - 1 := by
  rintro p hp n
  simpa only [one_pow] using nat_sub_dvd_pow_sub_pow p 1 n
theorem lean_workbook_543_6 : ∀ p : ℕ, p.Prime → ∀ n : ℕ, p - 1 ∣ p ^ n - 1 := by
  intro p hp n
  rw [← one_pow n]
  simpa only [one_pow] using nat_sub_dvd_pow_sub_pow _ 1 n
theorem lean_workbook_543_7 : ∀ p : ℕ, p.Prime → ∀ n : ℕ, p - 1 ∣ p ^ n - 1 := by
  intro p hp n
  simpa only [one_pow] using nat_sub_dvd_pow_sub_pow _ 1 n
theorem lean_workbook_543_8 : ∀ p : ℕ, p.Prime → ∀ n : ℕ, p - 1 ∣ p ^ n - 1 := by
  intro p hp n
  eta_reduce at *
  eta_reduce at *
  eta_reduce at *
  simpa [one_pow] using nat_sub_dvd_pow_sub_pow _ 1 n
theorem lean_workbook_543_9 : ∀ p : ℕ, p.Prime → ∀ n : ℕ, p - 1 ∣ p ^ n - 1 := by
  intro p h n
  simpa only [one_pow] using nat_sub_dvd_pow_sub_pow p 1 n
theorem lean_workbook_543_10 : ∀ p : ℕ, p.Prime → ∀ n : ℕ, p - 1 ∣ p ^ n - 1 := by
  intro p hprime n
  simpa only [one_pow] using nat_sub_dvd_pow_sub_pow p 1 n
theorem lean_workbook_543_11 : ∀ p : ℕ, p.Prime → ∀ n : ℕ, p - 1 ∣ p ^ n - 1 := by
  refine fun p hp n ↦ by simpa only [one_pow] using nat_sub_dvd_pow_sub_pow p 1 n
theorem lean_workbook_543_12 : ∀ p : ℕ, p.Prime → ∀ n : ℕ, p - 1 ∣ p ^ n - 1 := by
  intro p hp n
  simpa [one_pow, pow_one] using nat_sub_dvd_pow_sub_pow _ 1 n
theorem lean_workbook_543_13 : ∀ p : ℕ, p.Prime → ∀ n : ℕ, p - 1 ∣ p ^ n - 1 := by
  intro p h n
  eta_reduce at *
  simpa only [one_pow] using nat_sub_dvd_pow_sub_pow _ 1 n
theorem lean_workbook_543_14 : ∀ p : ℕ, p.Prime → ∀ n : ℕ, p - 1 ∣ p ^ n - 1 := by
  intro p hp n
  simpa only [one_pow] using nat_sub_dvd_pow_sub_pow p 1 n

theorem lean_workbook_559_0 (a b : ℝ) : (1 + a^4) * (1 + b^4) ≥ (1 + a^2 * b^2) * (a^2 + b^2) := by
  have h1 : 0 ≤ (a^2 - 1)^2 := sq_nonneg (a^2 - 1)
  nlinarith [h1, sq_nonneg (b^2 - 1)]
theorem lean_workbook_559_1 (a b : ℝ) : (1 + a^4) * (1 + b^4) ≥ (1 + a^2 * b^2) * (a^2 + b^2) := by
  have := sq_nonneg (a^2 - 1)
  have := sq_nonneg (b^2 - 1)
  nlinarith
theorem lean_workbook_559_2 (a b : ℝ) : (1 + a^4) * (1 + b^4) ≥ (1 + a^2 * b^2) * (a^2 + b^2) := by
  have h1 := sq_nonneg (a^2 - 1)
  have h2 := sq_nonneg (b^2 - 1)
  nlinarith
theorem lean_workbook_559_3 (a b : ℝ) : (1 + a^4) * (1 + b^4) ≥ (1 + a^2 * b^2) * (a^2 + b^2) := by
  nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1)]
theorem lean_workbook_559_4 (a b : ℝ) : (1 + a^4) * (1 + b^4) ≥ (1 + a^2 * b^2) * (a^2 + b^2) := by
  ring_nf
  nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1)]
theorem lean_workbook_559_5 (a b : ℝ) : (1 + a^4) * (1 + b^4) ≥ (1 + a^2 * b^2) * (a^2 + b^2) := by
  simp [mul_add, mul_comm, mul_left_comm]
  nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1)]
theorem lean_workbook_559_6 (a b : ℝ) : (1 + a^4) * (1 + b^4) ≥ (1 + a^2 * b^2) * (a^2 + b^2) := by
  simp [add_comm, add_left_comm]
  nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1)]
theorem lean_workbook_559_7 (a b : ℝ) : (1 + a^4) * (1 + b^4) ≥ (1 + a^2 * b^2) * (a^2 + b^2) := by
  simp only [add_comm, add_left_comm]
  nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1)]
theorem lean_workbook_559_8 (a b : ℝ) : (1 + a^4) * (1 + b^4) ≥ (1 + a^2 * b^2) * (a^2 + b^2) := by
  simp [add_mul, mul_add]
  nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1)]
theorem lean_workbook_559_9 (a b : ℝ) : (1 + a^4) * (1 + b^4) ≥ (1 + a^2 * b^2) * (a^2 + b^2) := by
  simp [add_comm]
  nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1)]
theorem lean_workbook_559_10 (a b : ℝ) : (1 + a^4) * (1 + b^4) ≥ (1 + a^2 * b^2) * (a^2 + b^2) := by
  nlinarith [sq_nonneg (1 - a^2), sq_nonneg (1 - b^2)]
theorem lean_workbook_559_11 (a b : ℝ) : (1 + a^4) * (1 + b^4) ≥ (1 + a^2 * b^2) * (a^2 + b^2) := by
  have h1 : 0 ≤ (a^2 - 1)^2 := sq_nonneg _
  nlinarith [h1, sq_nonneg (b^2 - 1)]

theorem lean_workbook_561_0 (a b c : ℝ) (ha : a ≠ b) (hb : b ≠ c) (hc : c ≠ a) (hab : a > b) (hbc : b > c) (hca : c > a) : (a * b + b * c + c * a) * (1 / (a - b) ^ 2 + 1 / (b - c) ^ 2 + 1 / (c - a) ^ 2) ≥ 4 := by
  field_simp [mul_add, add_mul, mul_comm, mul_assoc, mul_left_comm]
  nlinarith [ha, hb, hc, hab, hbc, hca]
theorem lean_workbook_561_1 (a b c : ℝ) (ha : a ≠ b) (hb : b ≠ c) (hc : c ≠ a) (hab : a > b) (hbc : b > c) (hca : c > a) : (a * b + b * c + c * a) * (1 / (a - b) ^ 2 + 1 / (b - c) ^ 2 + 1 / (c - a) ^ 2) ≥ 4 := by
  ring_nf
  norm_num
  nlinarith [ha, hb, hc, hab, hbc, hca]
theorem lean_workbook_561_2 (a b c : ℝ) (ha : a ≠ b) (hb : b ≠ c) (hc : c ≠ a) (hab : a > b) (hbc : b > c) (hca : c > a) : (a * b + b * c + c * a) * (1 / (a - b) ^ 2 + 1 / (b - c) ^ 2 + 1 / (c - a) ^ 2) ≥ 4 := by
  nlinarith only [ha, hb, hc, hab, hbc, hca]
theorem lean_workbook_561_3 (a b c : ℝ) (ha : a ≠ b) (hb : b ≠ c) (hc : c ≠ a) (hab : a > b) (hbc : b > c) (hca : c > a) : (a * b + b * c + c * a) * (1 / (a - b) ^ 2 + 1 / (b - c) ^ 2 + 1 / (c - a) ^ 2) ≥ 4 := by
  linarith only [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), ha, hb, hc, hab, hbc, hca]
theorem lean_workbook_561_4 (a b c : ℝ) (ha : a ≠ b) (hb : b ≠ c) (hc : c ≠ a) (hab : a > b) (hbc : b > c) (hca : c > a) : (a * b + b * c + c * a) * (1 / (a - b) ^ 2 + 1 / (b - c) ^ 2 + 1 / (c - a) ^ 2) ≥ 4 := by
  field_simp [ha, hb, hc]
  nlinarith
theorem lean_workbook_561_5 (a b c : ℝ) (ha : a ≠ b) (hb : b ≠ c) (hc : c ≠ a) (hab : a > b) (hbc : b > c) (hca : c > a) : (a * b + b * c + c * a) * (1 / (a - b) ^ 2 + 1 / (b - c) ^ 2 + 1 / (c - a) ^ 2) ≥ 4 := by
  ring_nf
  norm_cast
  nlinarith [ha, hb, hc, hab, hbc, hca]
theorem lean_workbook_561_6 (a b c : ℝ) (ha : a ≠ b) (hb : b ≠ c) (hc : c ≠ a) (hab : a > b) (hbc : b > c) (hca : c > a) : (a * b + b * c + c * a) * (1 / (a - b) ^ 2 + 1 / (b - c) ^ 2 + 1 / (c - a) ^ 2) ≥ 4 := by
  field_simp [sub_ne_zero.2 ha, sub_ne_zero.2 hb, sub_ne_zero.2 hc]
  nlinarith

theorem lean_workbook_565_0 (x : ℕ) (h₀ : (4 * x) % 128 = 12) : x % 32 = 3 := by
  rw [mul_comm] at h₀
  omega
theorem lean_workbook_565_1 (x : ℕ) (h₀ : (4 * x) % 128 = 12) : x % 32 = 3 := by
  eta_reduce at *
  eta_reduce at *
  omega
theorem lean_workbook_565_2 (x : ℕ) (h₀ : (4 * x) % 128 = 12) : x % 32 = 3 := by
  revert h₀
  intro h
  omega
theorem lean_workbook_565_3 (x : ℕ) (h₀ : (4 * x) % 128 = 12) : x % 32 = 3 := by
  change 4 * x % 128 = 12 at h₀
  change x % 32 = 3
  omega
theorem lean_workbook_565_4 (x : ℕ) (h₀ : (4 * x) % 128 = 12) : x % 32 = 3 := by
  simp [Nat.mul_mod, Nat.mod_mod] at h₀
  omega
theorem lean_workbook_565_5 (x : ℕ) (h₀ : (4 * x) % 128 = 12) : x % 32 = 3 := by
  rw [← Nat.mod_add_div x 32] at h₀
  simp [Nat.mul_mod, Nat.add_mod, Nat.mod_mod] at h₀
  omega
theorem lean_workbook_565_6 (x : ℕ) (h₀ : (4 * x) % 128 = 12) : x % 32 = 3 := by
  revert h₀
  revert x
  ring_nf
  omega
theorem lean_workbook_565_7 (x : ℕ) (h₀ : (4 * x) % 128 = 12) : x % 32 = 3 := by
  rw [← eq_comm] at h₀
  omega
theorem lean_workbook_565_8 (x : ℕ) (h₀ : (4 * x) % 128 = 12) : x % 32 = 3 := by
  rw [Nat.mul_mod] at h₀
  simp [Nat.mod_eq_of_lt] at h₀
  omega
theorem lean_workbook_565_9 (x : ℕ) (h₀ : (4 * x) % 128 = 12) : x % 32 = 3 := by
  rw [mul_mod] at h₀
  have h₁ : x % 32 = x % 32 := rfl
  rw [h₁]
  omega
theorem lean_workbook_565_10 (x : ℕ) (h₀ : (4 * x) % 128 = 12) : x % 32 = 3 := by
  rw [← mod_add_div x 32]
  omega
theorem lean_workbook_565_11 (x : ℕ) (h₀ : (4 * x) % 128 = 12) : x % 32 = 3 := by
  simp [Nat.mul_mod] at h₀
  simp [Nat.mod_mod] at h₀ ⊢
  omega
theorem lean_workbook_565_12 (x : ℕ) (h₀ : (4 * x) % 128 = 12) : x % 32 = 3 := by
  zify [h₀]
  omega
theorem lean_workbook_565_13 (x : ℕ) (h₀ : (4 * x) % 128 = 12) : x % 32 = 3 := by
  rw [mul_comm] at h₀
  rw [← mod_add_div x 32]
  omega
theorem lean_workbook_565_14 (x : ℕ) (h₀ : (4 * x) % 128 = 12) : x % 32 = 3 := by
  rw [← mod_add_div x 32] at h₀
  omega
theorem lean_workbook_565_15 (x : ℕ) (h₀ : (4 * x) % 128 = 12) : x % 32 = 3 := by
  rw [mul_mod] at h₀
  simp [Nat.mod_eq_of_lt] at h₀
  omega

theorem lean_workbook_570_0 (c : ℝ) (hc : 0 ≤ c) (f : ℝ → ℝ) (hf: ∀ x, f x = 1 / (c * x + 1)) : ∀ x y, (x > 0 ∧ y > 0) → f x * f (y * f x) = f (x + y) := by
  rintro x y ⟨hx : 0 < x, hy : 0 < y⟩
  simp [hf, hx, hy, add_pos, mul_pos, hc]
  field_simp [mul_assoc]
  ring
theorem lean_workbook_570_1 (c : ℝ) (hc : 0 ≤ c) (f : ℝ → ℝ) (hf: ∀ x, f x = 1 / (c * x + 1)) : ∀ x y, (x > 0 ∧ y > 0) → f x * f (y * f x) = f (x + y) := by
  intro x y hy
  cases' hy with hy1 hy2
  simp [hf, hy1, hy2, hc]
  field_simp [hf, hy1, hy2, hc]
  ring
theorem lean_workbook_570_2 (c : ℝ) (hc : 0 ≤ c) (f : ℝ → ℝ) (hf: ∀ x, f x = 1 / (c * x + 1)) : ∀ x y, (x > 0 ∧ y > 0) → f x * f (y * f x) = f (x + y) := by
  intro x y hxy
  rcases hxy with ⟨hx, hy⟩
  simp [hf, hx, hy]
  field_simp
  ring
theorem lean_workbook_570_3 (c : ℝ) (hc : 0 ≤ c) (f : ℝ → ℝ) (hf: ∀ x, f x = 1 / (c * x + 1)) : ∀ x y, (x > 0 ∧ y > 0) → f x * f (y * f x) = f (x + y) := by
  rintro x y ⟨hx, hy⟩
  field_simp [hc, hf]
  ring
theorem lean_workbook_570_4 (c : ℝ) (hc : 0 ≤ c) (f : ℝ → ℝ) (hf: ∀ x, f x = 1 / (c * x + 1)) : ∀ x y, (x > 0 ∧ y > 0) → f x * f (y * f x) = f (x + y) := by
  rintro x y ⟨hx, hy⟩
  simp only [hf]
  field_simp [mul_assoc]
  ring
theorem lean_workbook_570_5 (c : ℝ) (hc : 0 ≤ c) (f : ℝ → ℝ) (hf: ∀ x, f x = 1 / (c * x + 1)) : ∀ x y, (x > 0 ∧ y > 0) → f x * f (y * f x) = f (x + y) := by
  intro x y hxy
  obtain ⟨hx, hy⟩ := hxy
  field_simp [hf, hx, hy]
  ring_nf

theorem lean_workbook_588_0 (x : ℝ) : (x^6 - 1)^2 + (x^5 - x)^2 + (x^4 - x^2)^2 + 1 ≥ 0 := by
  field_simp [sub_eq_add_neg]
  nlinarith [sq_nonneg (x ^ 6 + (-1)), sq_nonneg (x ^ 5 + (-1) * x)]
theorem lean_workbook_588_1 (x : ℝ) : (x^6 - 1)^2 + (x^5 - x)^2 + (x^4 - x^2)^2 + 1 ≥ 0 := by
  field_simp [add_comm]
  nlinarith [sq_nonneg (x ^ 6 - 1), sq_nonneg (x ^ 5 - x), sq_nonneg (x ^ 4 - x ^ 2)]
theorem lean_workbook_588_2 (x : ℝ) : (x^6 - 1)^2 + (x^5 - x)^2 + (x^4 - x^2)^2 + 1 ≥ 0 := by
  norm_cast at *
  field_simp [add_comm]
  positivity
theorem lean_workbook_588_3 (x : ℝ) : (x^6 - 1)^2 + (x^5 - x)^2 + (x^4 - x^2)^2 + 1 ≥ 0 := by
  simp [add_assoc]
  positivity
theorem lean_workbook_588_4 (x : ℝ) : (x^6 - 1)^2 + (x^5 - x)^2 + (x^4 - x^2)^2 + 1 ≥ 0 := by
  rw [add_comm]
  positivity
theorem lean_workbook_588_5 (x : ℝ) : (x^6 - 1)^2 + (x^5 - x)^2 + (x^4 - x^2)^2 + 1 ≥ 0 := by
  have := sq_nonneg (x ^ 6 - 1)
  have := sq_nonneg (x ^ 5 - x)
  have := sq_nonneg (x ^ 4 - x ^ 2)
  linarith
theorem lean_workbook_588_6 (x : ℝ) : (x^6 - 1)^2 + (x^5 - x)^2 + (x^4 - x^2)^2 + 1 ≥ 0 := by
  have h1 : (x^6 - 1)^2 ≥ 0 := by positivity
  have h2 : (x^5 - x)^2 ≥ 0 := by positivity
  have h3 : (x^4 - x^2)^2 ≥ 0 := by positivity
  linarith
theorem lean_workbook_588_7 (x : ℝ) : (x^6 - 1)^2 + (x^5 - x)^2 + (x^4 - x^2)^2 + 1 ≥ 0 := by
  field_simp [sq]
  nlinarith [sq_nonneg (x ^ 6 - 1), sq_nonneg (x ^ 5 - x), sq_nonneg (x ^ 4 - x ^ 2)]
theorem lean_workbook_588_8 (x : ℝ) : (x^6 - 1)^2 + (x^5 - x)^2 + (x^4 - x^2)^2 + 1 ≥ 0 := by
  rw [sq, sq, sq]
  nlinarith
theorem lean_workbook_588_9 (x : ℝ) : (x^6 - 1)^2 + (x^5 - x)^2 + (x^4 - x^2)^2 + 1 ≥ 0 := by
  field_simp [add_assoc]
  nlinarith
theorem lean_workbook_588_10 (x : ℝ) : (x^6 - 1)^2 + (x^5 - x)^2 + (x^4 - x^2)^2 + 1 ≥ 0 := by
  simp only [sq, sub_eq_add_neg, add_assoc]
  nlinarith
theorem lean_workbook_588_11 (x : ℝ) : (x^6 - 1)^2 + (x^5 - x)^2 + (x^4 - x^2)^2 + 1 ≥ 0 := by
  simp [add_assoc, add_comm, add_left_comm]
  nlinarith [pow_two_nonneg (x^6 - 1), pow_two_nonneg (x^5 - x), pow_two_nonneg (x^4 - x^2)]
theorem lean_workbook_588_12 (x : ℝ) : (x^6 - 1)^2 + (x^5 - x)^2 + (x^4 - x^2)^2 + 1 ≥ 0 := by
  nlinarith [mul_self_nonneg (x^4 - x^2)]
theorem lean_workbook_588_13 (x : ℝ) : (x^6 - 1)^2 + (x^5 - x)^2 + (x^4 - x^2)^2 + 1 ≥ 0 := by
  rw [add_comm]
  nlinarith [sq_nonneg (x ^ 6 - 1), sq_nonneg (x ^ 5 - x), sq_nonneg (x ^ 4 - x ^ 2)]
theorem lean_workbook_588_14 (x : ℝ) : (x^6 - 1)^2 + (x^5 - x)^2 + (x^4 - x^2)^2 + 1 ≥ 0 := by
  simp only [add_comm, add_left_comm, add_assoc]
  nlinarith
theorem lean_workbook_588_15 (x : ℝ) : (x^6 - 1)^2 + (x^5 - x)^2 + (x^4 - x^2)^2 + 1 ≥ 0 := by
  apply add_nonneg <;> positivity
theorem lean_workbook_588_16 (x : ℝ) : (x^6 - 1)^2 + (x^5 - x)^2 + (x^4 - x^2)^2 + 1 ≥ 0 := by
  simp only [add_assoc, add_comm, add_left_comm]
  positivity
theorem lean_workbook_588_17 (x : ℝ) : (x^6 - 1)^2 + (x^5 - x)^2 + (x^4 - x^2)^2 + 1 ≥ 0 := by
  simp only [add_comm]
  nlinarith [sq_nonneg (x ^ 6 - 1), sq_nonneg (x ^ 5 - x), sq_nonneg (x ^ 4 - x ^ 2)]
theorem lean_workbook_588_18 (x : ℝ) : (x^6 - 1)^2 + (x^5 - x)^2 + (x^4 - x^2)^2 + 1 ≥ 0 := by
  field_simp [add_comm]
  nlinarith
theorem lean_workbook_588_19 (x : ℝ) : (x^6 - 1)^2 + (x^5 - x)^2 + (x^4 - x^2)^2 + 1 ≥ 0 := by
  simp [add_assoc, add_comm, add_left_comm]
  positivity
theorem lean_workbook_588_20 (x : ℝ) : (x^6 - 1)^2 + (x^5 - x)^2 + (x^4 - x^2)^2 + 1 ≥ 0 := by
  simp [sub_nonneg]
  positivity

theorem lean_workbook_617_0 : 8 / (2 * 2) = 2 := by
  exact by norm_num [div_eq_mul_inv, mul_assoc]
theorem lean_workbook_617_1 : 8 / (2 * 2) = 2 := by
  norm_num [div_eq_mul_inv, inv_eq_one_div]
theorem lean_workbook_617_2 : 8 / (2 * 2) = 2 := by
  norm_num [Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left]
theorem lean_workbook_617_3 : 8 / (2 * 2) = 2 := by
  simp [Nat.div_eq_of_eq_mul_left]
theorem lean_workbook_617_4 : 8 / (2 * 2) = 2 := by
  simp only [div_eq_mul_inv, mul_inv_rev, mul_one, mul_comm]
theorem lean_workbook_617_5 : 8 / (2 * 2) = 2 := by
  norm_num [div_eq_mul_inv, mul_inv_rev, mul_assoc]
theorem lean_workbook_617_6 : 8 / (2 * 2) = 2 := by
  exact (by norm_num : 8 / (2 * 2) = 2)
theorem lean_workbook_617_7 : 8 / (2 * 2) = 2 := by
  exact by norm_num [div_eq_mul_inv, ← mul_assoc]
theorem lean_workbook_617_8 : 8 / (2 * 2) = 2 := by
  norm_num [Nat.div_eq_of_eq_mul_left, Nat.mul_div_cancel_left]
theorem lean_workbook_617_9 : 8 / (2 * 2) = 2 := by
  symm
  simp only [div_eq_mul_inv, mul_inv_rev, mul_one, mul_comm]
theorem lean_workbook_617_10 : 8 / (2 * 2) = 2 := by
  norm_num [div_eq_mul_inv, inv_inv]
theorem lean_workbook_617_11 : 8 / (2 * 2) = 2 := by
  exact by norm_num [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
theorem lean_workbook_617_12 : 8 / (2 * 2) = 2 := by
  simp only [Int.mul_ediv_cancel_left]
theorem lean_workbook_617_13 : 8 / (2 * 2) = 2 := by
  norm_num [Nat.div_eq_of_eq_mul_left]
theorem lean_workbook_617_14 : 8 / (2 * 2) = 2 := by
  simp [div_eq_mul_inv, mul_comm]
theorem lean_workbook_617_15 : 8 / (2 * 2) = 2 := by
  simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]
theorem lean_workbook_617_16 : 8 / (2 * 2) = 2 := by
  norm_num [show (2 : ℚ) = (2 : ℚ) by rfl]
theorem lean_workbook_617_17 : 8 / (2 * 2) = 2 := by
  simp [div_eq_mul_inv, inv_inv]
theorem lean_workbook_617_18 : 8 / (2 * 2) = 2 := by
  norm_num [Nat.gcd]
theorem lean_workbook_617_19 : 8 / (2 * 2) = 2 := by
  simp only [Nat.div_eq_of_eq_mul_left, Nat.mul_comm]
theorem lean_workbook_617_20 : 8 / (2 * 2) = 2 := by
  field_simp [Nat.cast_mul]
theorem lean_workbook_617_21 : 8 / (2 * 2) = 2 := by
  simp only [Nat.mul_comm, Nat.mul_left_comm]
theorem lean_workbook_617_22 : 8 / (2 * 2) = 2 := by
  simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
theorem lean_workbook_617_23 : 8 / (2 * 2) = 2 := by
  ring_nf at *
theorem lean_workbook_617_24 : 8 / (2 * 2) = 2 := by
  norm_num [div_eq_mul_inv, mul_inv_rev]
theorem lean_workbook_617_25 : 8 / (2 * 2) = 2 := by
  simp [show 2 * 2 = 4 from rfl]
theorem lean_workbook_617_26 : 8 / (2 * 2) = 2 := by
  norm_num [show (2 : ℚ) = (2 : ℤ) by norm_cast, show (8 : ℚ) = (8 : ℤ) by norm_cast]
theorem lean_workbook_617_27 : 8 / (2 * 2) = 2 := by
  norm_num [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
theorem lean_workbook_617_28 : 8 / (2 * 2) = 2 := by
  simp [show 8 = 2 * 2 * 2 by norm_num]
theorem lean_workbook_617_29 : 8 / (2 * 2) = 2 := by
  simp only [Nat.mul_div_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_lt]
theorem lean_workbook_617_30 : 8 / (2 * 2) = 2 := by
  norm_num [show (2 : ℤ) = 1 + 1 by norm_num]
theorem lean_workbook_617_31 : 8 / (2 * 2) = 2 := by
  simp only [div_eq_mul_inv, mul_inv_rev]
theorem lean_workbook_617_32 : 8 / (2 * 2) = 2 := by
  simp only [mul_comm]

theorem lean_workbook_618_0 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  simp only [mul_add, mul_sub, mul_one, add_sub_add_left_eq_sub, sub_add_sub_cancel, sub_sub]
  ring
theorem lean_workbook_618_1 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  simp [sq]
  ring
theorem lean_workbook_618_2 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  linarith only [sq_nonneg (a^2 + 2 * b^2 + 2 * a * b), sq_nonneg (a^2 + 2 * b^2 - 2 * a * b)]
theorem lean_workbook_618_3 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  simp [sq, mul_add, mul_sub, add_mul, add_sub]
  ring_nf
theorem lean_workbook_618_4 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  rw [add_comm]
  ring
theorem lean_workbook_618_5 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  simp [sq]
  ring_nf
theorem lean_workbook_618_6 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  simp [mul_add, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_618_7 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  simp [sq, mul_add, mul_sub, add_mul, add_sub, sub_mul, sub_sub]
  ring
theorem lean_workbook_618_8 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  field_simp [mul_add, add_mul, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_618_9 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  simp [sq, mul_add, add_mul]
  ring
theorem lean_workbook_618_10 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  simp [mul_add, add_mul, mul_sub, sub_mul]
  ring
theorem lean_workbook_618_11 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  simp [mul_add, add_mul]
  ring
theorem lean_workbook_618_12 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  field_simp [add_comm, add_left_comm]
  ring
theorem lean_workbook_618_13 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  simp [mul_add, add_mul, mul_comm, mul_assoc, mul_left_comm]
  ring
theorem lean_workbook_618_14 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  simp [pow_two, mul_add, mul_comm, mul_left_comm]
  ring_nf
theorem lean_workbook_618_15 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  simp only [mul_add, mul_sub, add_mul, add_sub, sub_sub_sub_cancel_right, sub_add_sub_cancel, ←
    pow_two]
  ring
theorem lean_workbook_618_16 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  simp only [mul_add, mul_sub, sub_sub]
  ring_nf
theorem lean_workbook_618_17 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  rw [mul_comm]
  ring_nf
theorem lean_workbook_618_18 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  simp [sq, mul_add, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  ring
theorem lean_workbook_618_19 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  simp [mul_add, add_mul, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_618_20 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  rw [add_mul]
  ring
theorem lean_workbook_618_21 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  simp [pow_two, mul_add, add_mul, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_618_22 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  simp only [sq, mul_add, mul_sub, mul_one, add_sub_add_left_eq_sub, add_sub_cancel]
  ring
theorem lean_workbook_618_23 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  simp [add_mul, mul_add, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_618_24 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  simp [add_mul, mul_add]
  ring
theorem lean_workbook_618_25 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  repeat rw [sq]; ring
theorem lean_workbook_618_26 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  simp [add_mul, mul_add, mul_sub, sub_mul]
  ring
theorem lean_workbook_618_27 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  simp only [mul_add, mul_sub, mul_one, add_sub_add_left_eq_sub]
  ring
theorem lean_workbook_618_28 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  field_simp [sq]
  ring
theorem lean_workbook_618_29 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  simp only [add_mul, mul_add]
  ring_nf
theorem lean_workbook_618_30 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  simp only [mul_add, mul_sub, mul_one, add_sub_add_left_eq_sub, sub_sub]
  ring
theorem lean_workbook_618_31 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  simp [sq, mul_add, mul_sub, mul_comm, mul_left_comm, add_assoc, add_sub_assoc]
  ring
theorem lean_workbook_618_32 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  simp only [add_mul, mul_add, mul_sub, sub_mul]
  ring

theorem lean_workbook_673_0 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  ring_nf
  have h1 : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  linarith [h1]
theorem lean_workbook_673_1 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  ring_nf
  have h1 : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  linarith [sq_nonneg (a + b)]
theorem lean_workbook_673_2 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  simp [sq, mul_add, mul_comm, mul_left_comm]
  have : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  linarith
theorem lean_workbook_673_3 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  have h := sq_nonneg (a - b)
  simp [sq, sub_mul, mul_sub, mul_comm, mul_left_comm] at h
  linarith
theorem lean_workbook_673_4 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  have h : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  linarith [sq_nonneg (a + b)]
theorem lean_workbook_673_5 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  have h : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  linarith [h]
theorem lean_workbook_673_6 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  have : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  linarith [sq_nonneg (a + b)]
theorem lean_workbook_673_7 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  simp only [sq]
  have h1 : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  linarith [h1]
theorem lean_workbook_673_8 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  rw [sq]
  linarith only [sq_nonneg (a - b)]
theorem lean_workbook_673_9 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  have : (a - b) ^ 2 ≥ 0 := sq_nonneg (a - b)
  linarith [sq_nonneg (a - b)]
theorem lean_workbook_673_10 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  simp [mul_add, add_mul, mul_comm, mul_left_comm]
  linarith [sq_nonneg (a + b), sq_nonneg (a - b)]
theorem lean_workbook_673_11 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  simp [add_sq]
  linarith [sq_nonneg (a - b)]
theorem lean_workbook_673_12 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  rw [sq, sq]
  linarith [sq_nonneg (a - b)]
theorem lean_workbook_673_13 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  simp [sq]
  nlinarith [sq_nonneg (a - b)]
theorem lean_workbook_673_14 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  simp [sq, mul_add, mul_comm, mul_left_comm]
  nlinarith [sq_nonneg (a - b)]
theorem lean_workbook_673_15 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  linarith [sq_nonneg (a - b)]
theorem lean_workbook_673_16 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  field_simp [sq]
  linarith [sq_nonneg (a + b), sq_nonneg (a - b)]
theorem lean_workbook_673_17 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  simp [mul_add, add_mul, mul_comm, mul_left_comm]
  have : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  linarith
theorem lean_workbook_673_18 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  ring_nf
  rw [sq]
  nlinarith [sq_nonneg (a - b)]
theorem lean_workbook_673_19 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  ring_nf
  simp [add_comm]
  nlinarith [sq_nonneg (a - b)]
theorem lean_workbook_673_20 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  have h1 : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  ring_nf at h1
  linarith
theorem lean_workbook_673_21 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  nlinarith [sq_nonneg (a - b)]
theorem lean_workbook_673_22 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  apply le_of_sub_nonneg
  field_simp [mul_comm]
  nlinarith [sq_nonneg (a - b)]
theorem lean_workbook_673_23 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  simp [mul_add, add_mul, mul_comm, mul_assoc, mul_left_comm]
  linarith [sq_nonneg (a + b), sq_nonneg (a - b)]
theorem lean_workbook_673_24 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  simp [sq]
  linarith only [sq_nonneg (a - b)]
theorem lean_workbook_673_25 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  have h1 : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  linarith
theorem lean_workbook_673_26 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  rw [sq, sq]
  have : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  linarith
theorem lean_workbook_673_27 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  simp [pow_two]
  linarith [mul_self_nonneg (a - b)]
theorem lean_workbook_673_28 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  have h2 : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  linarith
theorem lean_workbook_673_29 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  ring_nf
  nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
theorem lean_workbook_673_30 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  simp only [two_mul, sq]
  linarith [sq_nonneg (a - b)]
theorem lean_workbook_673_31 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  rw [mul_add]
  linarith [mul_self_nonneg (a - b)]
theorem lean_workbook_673_32 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  simp [pow_two, add_mul_self_eq, mul_add, mul_comm, mul_left_comm]
  linarith [sq_nonneg (a + b), sq_nonneg (a - b)]
theorem lean_workbook_673_33 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  have := sq_nonneg (a - b)
  linarith [sq_nonneg (a + b)]
theorem lean_workbook_673_34 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  rw [sq, sq]
  linarith [mul_self_nonneg (a - b)]
theorem lean_workbook_673_35 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  rw [sq, sq]
  have h : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  linarith
theorem lean_workbook_673_36 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  simp [sq]
  linarith [sq_nonneg (a - b)]
theorem lean_workbook_673_37 (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  ring_nf
  nlinarith [sq_nonneg (a - b)]

theorem lean_workbook_676_0 (a : ℝ) (ha : 0 < a) : (a * (3 * a + 1)) / (a + 1) ^ 2 ≤ (3 / 4 : ℝ) * a + 1 / 4 := by
  field_simp [sq]
  rw [div_le_iff (by positivity)]
  ring_nf
  nlinarith [sq_nonneg (a - 1)]
theorem lean_workbook_676_1 (a : ℝ) (ha : 0 < a) : (a * (3 * a + 1)) / (a + 1) ^ 2 ≤ (3 / 4 : ℝ) * a + 1 / 4 := by
  have h1 : 0 ≤ (a - 1) ^ 2 := sq_nonneg (a - 1)
  rw [div_le_iff]
  nlinarith
  nlinarith [h1]

theorem lean_workbook_680_0 (a b c : ℝ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 3) : a^4 + b^4 + c^4 ≥ a^3 + b^3 + c^3 := by
  nlinarith [pow_two_nonneg (a - 1), pow_two_nonneg (b - 1), pow_two_nonneg (c - 1)]
theorem lean_workbook_680_1 (a b c : ℝ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 3) : a^4 + b^4 + c^4 ≥ a^3 + b^3 + c^3 := by
  simp [ha.2.2.2]
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]

theorem lean_workbook_689_0 (x : ℝ) (h : x > 0) : (x + 1) ^ 2 ≥ 4 * x := by
  have h₁ : (x - 1) ^ 2 ≥ 0 := sq_nonneg (x - 1)
  linarith [h]
theorem lean_workbook_689_1 (x : ℝ) (h : x > 0) : (x + 1) ^ 2 ≥ 4 * x := by
  have h2 : x ≥ 0 := le_of_lt h
  nlinarith [sq_nonneg (x - 1)]
theorem lean_workbook_689_2 (x : ℝ) (h : x > 0) : (x + 1) ^ 2 ≥ 4 * x := by
  conv_lhs => rw [add_comm]
  nlinarith [sq_nonneg (x - 1)]
theorem lean_workbook_689_3 (x : ℝ) (h : x > 0) : (x + 1) ^ 2 ≥ 4 * x := by
  field_simp [sq]
  nlinarith [sq_nonneg (x - 1)]
theorem lean_workbook_689_4 (x : ℝ) (h : x > 0) : (x + 1) ^ 2 ≥ 4 * x := by
  ring_nf
  nlinarith [sq_nonneg (x - 1)]
theorem lean_workbook_689_5 (x : ℝ) (h : x > 0) : (x + 1) ^ 2 ≥ 4 * x := by
  field_simp [pow_two]
  nlinarith [sq_nonneg (x - 1)]
theorem lean_workbook_689_6 (x : ℝ) (h : x > 0) : (x + 1) ^ 2 ≥ 4 * x := by
  ring_nf
  have := sq_nonneg (x - 1)
  nlinarith
theorem lean_workbook_689_7 (x : ℝ) (h : x > 0) : (x + 1) ^ 2 ≥ 4 * x := by
  simp [sq, add_mul_self_eq]
  nlinarith [sq_nonneg (x - 1)]
theorem lean_workbook_689_8 (x : ℝ) (h : x > 0) : (x + 1) ^ 2 ≥ 4 * x := by
  rw [sq]
  nlinarith [sq_nonneg (x - 1)]
theorem lean_workbook_689_9 (x : ℝ) (h : x > 0) : (x + 1) ^ 2 ≥ 4 * x := by
  have h1 : (x - 1) ^ 2 ≥ 0 := sq_nonneg (x - 1)
  linarith [h, h1]
theorem lean_workbook_689_10 (x : ℝ) (h : x > 0) : (x + 1) ^ 2 ≥ 4 * x := by
  simp [sq, mul_add, add_mul, mul_comm, mul_left_comm]
  nlinarith [sq_nonneg (x - 1)]
theorem lean_workbook_689_11 (x : ℝ) (h : x > 0) : (x + 1) ^ 2 ≥ 4 * x := by
  simp [sq, mul_add, mul_comm, mul_left_comm]
  nlinarith [sq_nonneg (x - 1)]
theorem lean_workbook_689_12 (x : ℝ) (h : x > 0) : (x + 1) ^ 2 ≥ 4 * x := by
  rw [sq, add_comm]
  nlinarith [sq_nonneg (x - 1)]
theorem lean_workbook_689_13 (x : ℝ) (h : x > 0) : (x + 1) ^ 2 ≥ 4 * x := by
  simp [add_sq, mul_add, add_mul, mul_comm, mul_left_comm]
  nlinarith [sq_nonneg (x - 1)]
theorem lean_workbook_689_14 (x : ℝ) (h : x > 0) : (x + 1) ^ 2 ≥ 4 * x := by
  simp [h, sq, mul_add, add_mul, mul_comm, mul_left_comm]
  nlinarith [sq_nonneg (x - 1)]
theorem lean_workbook_689_15 (x : ℝ) (h : x > 0) : (x + 1) ^ 2 ≥ 4 * x := by
  have := sq_nonneg (x - 1)
  linarith [h]
theorem lean_workbook_689_16 (x : ℝ) (h : x > 0) : (x + 1) ^ 2 ≥ 4 * x := by
  nlinarith [sq_nonneg (x - 1), h]
theorem lean_workbook_689_17 (x : ℝ) (h : x > 0) : (x + 1) ^ 2 ≥ 4 * x := by
  have : (x - 1) ^ 2 ≥ 0 := sq_nonneg (x - 1)
  linarith only [h, this]
theorem lean_workbook_689_18 (x : ℝ) (h : x > 0) : (x + 1) ^ 2 ≥ 4 * x := by
  rw [sq]
  nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1)]
theorem lean_workbook_689_19 (x : ℝ) (h : x > 0) : (x + 1) ^ 2 ≥ 4 * x := by
  have h₁ : (x - 1) ^ 2 ≥ 0 := sq_nonneg (x - 1)
  linarith only [h₁, h]
theorem lean_workbook_689_20 (x : ℝ) (h : x > 0) : (x + 1) ^ 2 ≥ 4 * x := by
  have h1 : 0 ≤ (x - 1) ^ 2 := sq_nonneg (x - 1)
  nlinarith
theorem lean_workbook_689_21 (x : ℝ) (h : x > 0) : (x + 1) ^ 2 ≥ 4 * x := by
  have h1 : (x - 1) ^ 2 ≥ 0 := sq_nonneg (x - 1)
  linarith only [h, h1]
theorem lean_workbook_689_22 (x : ℝ) (h : x > 0) : (x + 1) ^ 2 ≥ 4 * x := by
  apply le_of_sub_nonneg
  ring_nf
  rw [add_comm]
  nlinarith [sq_nonneg (x - 1)]
theorem lean_workbook_689_23 (x : ℝ) (h : x > 0) : (x + 1) ^ 2 ≥ 4 * x := by
  simp [pow_two]
  rw [add_comm]
  nlinarith [sq_nonneg (x - 1)]
theorem lean_workbook_689_24 (x : ℝ) (h : x > 0) : (x + 1) ^ 2 ≥ 4 * x := by
  simp [sq]
  nlinarith [sq_nonneg (x - 1)]
theorem lean_workbook_689_25 (x : ℝ) (h : x > 0) : (x + 1) ^ 2 ≥ 4 * x := by
  simp only [sq, add_mul_self_eq, mul_add, mul_one, add_comm]
  nlinarith [sq_nonneg (x - 1)]
theorem lean_workbook_689_26 (x : ℝ) (h : x > 0) : (x + 1) ^ 2 ≥ 4 * x := by
  simp [pow_two]
  nlinarith [sq_nonneg (x - 1)]

theorem lean_workbook_694_0 (x : ℝ) (h : x + 600 = 1700) : x = 1100 := by
  simp only [← eq_sub_iff_add_eq] at h
  linarith
theorem lean_workbook_694_1 (x : ℝ) (h : x + 600 = 1700) : x = 1100 := by
  exact by linarith [h]
theorem lean_workbook_694_2 (x : ℝ) (h : x + 600 = 1700) : x = 1100 := by
  apply eq_of_sub_eq_zero
  linarith only [h]
theorem lean_workbook_694_3 (x : ℝ) (h : x + 600 = 1700) : x = 1100 := by
  rw [← sub_eq_zero]
  linarith only [h]
theorem lean_workbook_694_4 (x : ℝ) (h : x + 600 = 1700) : x = 1100 := by
  rw [← sub_eq_zero] at h ⊢
  linarith
theorem lean_workbook_694_5 (x : ℝ) (h : x + 600 = 1700) : x = 1100 := by
  linarith [h]
theorem lean_workbook_694_6 (x : ℝ) (h : x + 600 = 1700) : x = 1100 := by
  linarith only [h]
theorem lean_workbook_694_7 (x : ℝ) (h : x + 600 = 1700) : x = 1100 := by
  rw [← add_right_inj (100 : ℝ)]
  linarith [h]
theorem lean_workbook_694_8 (x : ℝ) (h : x + 600 = 1700) : x = 1100 := by
  exact by linarith only [h]
theorem lean_workbook_694_9 (x : ℝ) (h : x + 600 = 1700) : x = 1100 := by
  rw [← sub_eq_zero]
  linarith [h]
theorem lean_workbook_694_10 (x : ℝ) (h : x + 600 = 1700) : x = 1100 := by
  rw [← sub_eq_zero] at h ⊢
  nlinarith [h]
theorem lean_workbook_694_11 (x : ℝ) (h : x + 600 = 1700) : x = 1100 := by
  rw [eq_comm] at h
  linarith only [h]
theorem lean_workbook_694_12 (x : ℝ) (h : x + 600 = 1700) : x = 1100 := by
  rw [← eq_sub_iff_add_eq] at h
  linarith [h]
theorem lean_workbook_694_13 (x : ℝ) (h : x + 600 = 1700) : x = 1100 := by
  rw [← sub_eq_zero]
  nlinarith
theorem lean_workbook_694_14 (x : ℝ) (h : x + 600 = 1700) : x = 1100 := by
  ring_nf at h
  linarith only [h]
theorem lean_workbook_694_15 (x : ℝ) (h : x + 600 = 1700) : x = 1100 := by
  rw [← add_right_inj 600] at h
  linarith
theorem lean_workbook_694_16 (x : ℝ) (h : x + 600 = 1700) : x = 1100 := by
  rw [add_comm] at h
  linarith
theorem lean_workbook_694_17 (x : ℝ) (h : x + 600 = 1700) : x = 1100 := by
  rw [eq_comm] at h
  linarith [h]
theorem lean_workbook_694_18 (x : ℝ) (h : x + 600 = 1700) : x = 1100 := by
  rw [eq_comm] at h
  linarith

theorem lean_workbook_695_0 (D : Set ℝ) (f : ℝ → ℝ) (hD : IsCompact D) (hf : ContinuousOn f D) : IsCompact (Set.image f D) := by
  simpa only [Set.image_id] using hD.image_of_continuousOn hf
theorem lean_workbook_695_1 (D : Set ℝ) (f : ℝ → ℝ) (hD : IsCompact D) (hf : ContinuousOn f D) : IsCompact (Set.image f D) := by
  refine' IsCompact.image_of_continuousOn hD hf

theorem lean_workbook_698_0 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [add_assoc, add_comm, add_left_comm]
theorem lean_workbook_698_1 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [mul_add, add_mul, mul_comm, mul_assoc, mul_left_comm]
theorem lean_workbook_698_2 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  field_simp [Nat.add_comm]
theorem lean_workbook_698_3 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [Nat.gcd]
theorem lean_workbook_698_4 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [add_comm, add_left_comm, add_assoc]
theorem lean_workbook_698_5 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [add_mul, mul_add, mul_comm, mul_left_comm, mul_assoc]
theorem lean_workbook_698_6 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
theorem lean_workbook_698_7 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [div_eq_mul_inv]
theorem lean_workbook_698_8 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
theorem lean_workbook_698_9 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [Nat.add_comm, Nat.add_left_comm]
theorem lean_workbook_698_10 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [Int.mul_comm, Int.mul_assoc, Int.mul_left_comm]
theorem lean_workbook_698_11 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [add_comm, mul_assoc]
theorem lean_workbook_698_12 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  all_goals norm_num
theorem lean_workbook_698_13 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [mul_add, add_mul, div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]
theorem lean_workbook_698_14 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [mul_assoc]
theorem lean_workbook_698_15 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [Nat.add_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
theorem lean_workbook_698_16 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Nat.add_sub_add_right, Nat.add_sub_cancel_left, Nat.add_sub_cancel, Nat.mul_div_cancel_left]
theorem lean_workbook_698_17 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num at *
theorem lean_workbook_698_18 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [mul_add, add_mul, mul_comm, mul_assoc, mul_left_comm]
theorem lean_workbook_698_19 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
theorem lean_workbook_698_20 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]
theorem lean_workbook_698_21 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [Nat.div_eq_of_eq_mul_left]
theorem lean_workbook_698_22 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [mul_assoc, mul_comm, mul_left_comm]
theorem lean_workbook_698_23 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
theorem lean_workbook_698_24 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [add_comm, add_left_comm, mul_comm, mul_left_comm, mul_assoc]
theorem lean_workbook_698_25 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [Nat.add_zero, Nat.add_succ, Nat.mul_one, Nat.mul_zero, Nat.zero_add, Nat.zero_sub]
theorem lean_workbook_698_26 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [Nat.div_eq]
theorem lean_workbook_698_27 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [mul_comm, mul_assoc, mul_left_comm]
theorem lean_workbook_698_28 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [add_mul, mul_add, mul_comm, mul_left_comm, div_eq_mul_inv]
theorem lean_workbook_698_29 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [Nat.mul]
theorem lean_workbook_698_30 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [mul_add, mul_comm, mul_left_comm]
theorem lean_workbook_698_31 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [Nat.div_eq_of_lt]
theorem lean_workbook_698_32 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [Nat.add_comm]
theorem lean_workbook_698_33 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [Nat.add_comm, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
theorem lean_workbook_698_34 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [Nat.gcd_eq_gcd_ab]
theorem lean_workbook_698_35 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [show (1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000 by ring]
theorem lean_workbook_698_36 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
theorem lean_workbook_698_37 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  exact (by norm_num : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000))
theorem lean_workbook_698_38 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [mul_add, mul_comm, mul_left_comm, add_mul, add_comm, add_left_comm, div_eq_mul_inv]
theorem lean_workbook_698_39 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  field_simp [add_comm, add_left_comm, add_assoc]
theorem lean_workbook_698_40 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [div_eq_mul_inv, ← mul_assoc, ← add_assoc]
theorem lean_workbook_698_41 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [mul_comm, mul_assoc, mul_left_comm, div_eq_mul_inv]
theorem lean_workbook_698_42 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
theorem lean_workbook_698_43 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [div_eq_mul_inv, mul_inv_rev]
theorem lean_workbook_698_44 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [div_eq_mul_inv, ← pow_two]
theorem lean_workbook_698_45 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [Nat.add_comm, Nat.add_left_comm]
theorem lean_workbook_698_46 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  rw [show (1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000 by norm_num]
theorem lean_workbook_698_47 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
theorem lean_workbook_698_48 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [Nat.mul_div_cancel_left]
theorem lean_workbook_698_49 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [div_eq_mul_inv, ← mul_assoc]
theorem lean_workbook_698_50 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]
theorem lean_workbook_698_51 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [Int.negSucc_ne_zero]
theorem lean_workbook_698_52 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [Nat.add_zero]
theorem lean_workbook_698_53 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [add_comm] at *
theorem lean_workbook_698_54 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  field_simp [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]
theorem lean_workbook_698_55 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  field_simp [show (3 + 4) / 7 ≠ 0 by norm_num]
theorem lean_workbook_698_56 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [Int.add_comm]
theorem lean_workbook_698_57 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [Nat.add_comm, Nat.add_left_comm, Nat.mul_comm, Nat.mul_left_comm]
theorem lean_workbook_698_58 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [add_comm, add_left_comm, add_assoc, mul_comm, mul_assoc, mul_left_comm]
theorem lean_workbook_698_59 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [add_comm, add_left_comm, mul_comm, mul_left_comm]
theorem lean_workbook_698_60 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
theorem lean_workbook_698_61 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [add_comm, add_left_comm, add_assoc]
theorem lean_workbook_698_62 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [add_comm]
theorem lean_workbook_698_63 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  congr 1

theorem lean_workbook_704_0 : ∑ k in Finset.range 3, (Nat.choose 5 (2 * k + 1)) = 16 := by
  conv => lhs; rw [← Nat.mod_add_div 5 3]
theorem lean_workbook_704_1 : ∑ k in Finset.range 3, (Nat.choose 5 (2 * k + 1)) = 16 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_zero]
  norm_num [Nat.choose]
theorem lean_workbook_704_2 : ∑ k in Finset.range 3, (Nat.choose 5 (2 * k + 1)) = 16 := by
  congr 1 <;> simp [Finset.sum_range_succ]
theorem lean_workbook_704_3 : ∑ k in Finset.range 3, (Nat.choose 5 (2 * k + 1)) = 16 := by
  unfold Finset.range
  simp [Nat.choose]
theorem lean_workbook_704_4 : ∑ k in Finset.range 3, (Nat.choose 5 (2 * k + 1)) = 16 := by
  unfold Finset.range
  rfl
theorem lean_workbook_704_5 : ∑ k in Finset.range 3, (Nat.choose 5 (2 * k + 1)) = 16 := by
  simp [Finset.sum_range_succ, choose]
theorem lean_workbook_704_6 : ∑ k in Finset.range 3, (Nat.choose 5 (2 * k + 1)) = 16 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero, choose_one_right]
  rfl
theorem lean_workbook_704_7 : ∑ k in Finset.range 3, (Nat.choose 5 (2 * k + 1)) = 16 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_zero]
  rfl
theorem lean_workbook_704_8 : ∑ k in Finset.range 3, (Nat.choose 5 (2 * k + 1)) = 16 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  decide
theorem lean_workbook_704_9 : ∑ k in Finset.range 3, (Nat.choose 5 (2 * k + 1)) = 16 := by
  simp only [Finset.sum, Finset.range]
  rfl
theorem lean_workbook_704_10 : ∑ k in Finset.range 3, (Nat.choose 5 (2 * k + 1)) = 16 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right]
  rfl
theorem lean_workbook_704_11 : ∑ k in Finset.range 3, (Nat.choose 5 (2 * k + 1)) = 16 := by
  suffices 16 = ∑ k in Finset.range 3, (Nat.choose 5 (2 * k + 1)) by exact this.symm
  trivial
theorem lean_workbook_704_12 : ∑ k in Finset.range 3, (Nat.choose 5 (2 * k + 1)) = 16 := by
  conv_lhs => rw [← Nat.mod_add_div 5 3]
theorem lean_workbook_704_13 : ∑ k in Finset.range 3, (Nat.choose 5 (2 * k + 1)) = 16 := by
  simp [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose]

theorem lean_workbook_722_0 : ∀ x y z : ℝ, 16 * x ^ 2 + 25 * y ^ 2 + 36 * z ^ 2 ≥ 45 * y * z + 27 * z * x + 5 * x * y := by
  intro x y z
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]
theorem lean_workbook_722_1 : ∀ x y z : ℝ, 16 * x ^ 2 + 25 * y ^ 2 + 36 * z ^ 2 ≥ 45 * y * z + 27 * z * x + 5 * x * y := by
  intro x y z
  simp [sq]
  linarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]

theorem lean_workbook_742_0 : (-10:ℤ) + (-4:ℤ) + (2:ℤ) + (8:ℤ) + (14:ℤ) + (20:ℤ) + (26:ℤ) + (32:ℤ) + (38:ℤ) + (44:ℤ) = 170 := by
  simp [add_assoc, add_comm, add_left_comm, sub_eq_add_neg]
theorem lean_workbook_742_1 : (-10:ℤ) + (-4:ℤ) + (2:ℤ) + (8:ℤ) + (14:ℤ) + (20:ℤ) + (26:ℤ) + (32:ℤ) + (38:ℤ) + (44:ℤ) = 170 := by
  simp only [Int.neg_add, Int.add_assoc, Int.add_left_neg, Int.add_zero]
  norm_num
theorem lean_workbook_742_2 : (-10:ℤ) + (-4:ℤ) + (2:ℤ) + (8:ℤ) + (14:ℤ) + (20:ℤ) + (26:ℤ) + (32:ℤ) + (38:ℤ) + (44:ℤ) = 170 := by
  norm_num [Int.add_comm, Int.add_assoc, Int.add_left_comm]
theorem lean_workbook_742_3 : (-10:ℤ) + (-4:ℤ) + (2:ℤ) + (8:ℤ) + (14:ℤ) + (20:ℤ) + (26:ℤ) + (32:ℤ) + (38:ℤ) + (44:ℤ) = 170 := by
  rw [add_assoc]
  norm_num [add_assoc, add_comm, add_left_comm]
theorem lean_workbook_742_4 : (-10:ℤ) + (-4:ℤ) + (2:ℤ) + (8:ℤ) + (14:ℤ) + (20:ℤ) + (26:ℤ) + (32:ℤ) + (38:ℤ) + (44:ℤ) = 170 := by
  simp only [add_comm, add_left_comm, add_assoc]
  norm_num [Int.add_comm, Int.add_left_comm, Int.add_assoc]
theorem lean_workbook_742_5 : (-10:ℤ) + (-4:ℤ) + (2:ℤ) + (8:ℤ) + (14:ℤ) + (20:ℤ) + (26:ℤ) + (32:ℤ) + (38:ℤ) + (44:ℤ) = 170 := by
  norm_num [Nat.gcd]
theorem lean_workbook_742_6 : (-10:ℤ) + (-4:ℤ) + (2:ℤ) + (8:ℤ) + (14:ℤ) + (20:ℤ) + (26:ℤ) + (32:ℤ) + (38:ℤ) + (44:ℤ) = 170 := by
  simp only [Int.add_assoc, Int.add_left_comm, Int.add_comm]
  norm_num
theorem lean_workbook_742_7 : (-10:ℤ) + (-4:ℤ) + (2:ℤ) + (8:ℤ) + (14:ℤ) + (20:ℤ) + (26:ℤ) + (32:ℤ) + (38:ℤ) + (44:ℤ) = 170 := by
  congr 1
theorem lean_workbook_742_8 : (-10:ℤ) + (-4:ℤ) + (2:ℤ) + (8:ℤ) + (14:ℤ) + (20:ℤ) + (26:ℤ) + (32:ℤ) + (38:ℤ) + (44:ℤ) = 170 := by
  simp only [add_assoc, add_comm, add_left_comm]
  norm_num
theorem lean_workbook_742_9 : (-10:ℤ) + (-4:ℤ) + (2:ℤ) + (8:ℤ) + (14:ℤ) + (20:ℤ) + (26:ℤ) + (32:ℤ) + (38:ℤ) + (44:ℤ) = 170 := by
  simp [add_assoc]
theorem lean_workbook_742_10 : (-10:ℤ) + (-4:ℤ) + (2:ℤ) + (8:ℤ) + (14:ℤ) + (20:ℤ) + (26:ℤ) + (32:ℤ) + (38:ℤ) + (44:ℤ) = 170 := by
  simp [Int.add_assoc, Int.add_comm, Int.add_left_comm]
theorem lean_workbook_742_11 : (-10:ℤ) + (-4:ℤ) + (2:ℤ) + (8:ℤ) + (14:ℤ) + (20:ℤ) + (26:ℤ) + (32:ℤ) + (38:ℤ) + (44:ℤ) = 170 := by
  norm_num [Int.add_comm, Int.add_assoc]
theorem lean_workbook_742_12 : (-10:ℤ) + (-4:ℤ) + (2:ℤ) + (8:ℤ) + (14:ℤ) + (20:ℤ) + (26:ℤ) + (32:ℤ) + (38:ℤ) + (44:ℤ) = 170 := by
  simp [add_assoc, add_comm, add_left_comm]
theorem lean_workbook_742_13 : (-10:ℤ) + (-4:ℤ) + (2:ℤ) + (8:ℤ) + (14:ℤ) + (20:ℤ) + (26:ℤ) + (32:ℤ) + (38:ℤ) + (44:ℤ) = 170 := by
  norm_num [Nat.succ_eq_add_one]
theorem lean_workbook_742_14 : (-10:ℤ) + (-4:ℤ) + (2:ℤ) + (8:ℤ) + (14:ℤ) + (20:ℤ) + (26:ℤ) + (32:ℤ) + (38:ℤ) + (44:ℤ) = 170 := by
  simp [Int.add_comm, Int.add_assoc, Int.add_left_comm]
theorem lean_workbook_742_15 : (-10:ℤ) + (-4:ℤ) + (2:ℤ) + (8:ℤ) + (14:ℤ) + (20:ℤ) + (26:ℤ) + (32:ℤ) + (38:ℤ) + (44:ℤ) = 170 := by
  norm_num [Int.add_comm, Int.add_assoc, Int.add_left_comm, Int.add_assoc]
theorem lean_workbook_742_16 : (-10:ℤ) + (-4:ℤ) + (2:ℤ) + (8:ℤ) + (14:ℤ) + (20:ℤ) + (26:ℤ) + (32:ℤ) + (38:ℤ) + (44:ℤ) = 170 := by
  simp only [Int.add_assoc, Int.add_comm, Int.add_left_comm]
  norm_num [Int.add_assoc, Int.add_comm, Int.add_left_comm]
theorem lean_workbook_742_17 : (-10:ℤ) + (-4:ℤ) + (2:ℤ) + (8:ℤ) + (14:ℤ) + (20:ℤ) + (26:ℤ) + (32:ℤ) + (38:ℤ) + (44:ℤ) = 170 := by
  norm_num [Int.negSucc]
theorem lean_workbook_742_18 : (-10:ℤ) + (-4:ℤ) + (2:ℤ) + (8:ℤ) + (14:ℤ) + (20:ℤ) + (26:ℤ) + (32:ℤ) + (38:ℤ) + (44:ℤ) = 170 := by
  simp only [Int.add_assoc, Int.add_comm, Int.add_left_comm]
  norm_num
theorem lean_workbook_742_19 : (-10:ℤ) + (-4:ℤ) + (2:ℤ) + (8:ℤ) + (14:ℤ) + (20:ℤ) + (26:ℤ) + (32:ℤ) + (38:ℤ) + (44:ℤ) = 170 := by
  simp [Int.add_assoc, Int.add_comm]

theorem lean_workbook_743_0 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  repeat' rw [sq]; ring
theorem lean_workbook_743_1 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp only [add_mul, mul_add, mul_comm, mul_left_comm, sq]
  ring
theorem lean_workbook_743_2 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp only [sq, mul_add, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_743_3 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp [add_mul, mul_add, mul_comm, mul_left_comm, sq, sub_eq_add_neg, add_assoc]
  ring
theorem lean_workbook_743_4 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp only [add_mul, mul_add, mul_pow, sub_eq_add_neg]
  ring
theorem lean_workbook_743_5 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp only [add_mul, mul_add, mul_sub, sub_mul, mul_pow, add_assoc, add_sub_assoc]
  ring
theorem lean_workbook_743_6 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  linear_combination (a^2 + b^2) * (c^2 + d^2)
theorem lean_workbook_743_7 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp only [sq, add_mul, mul_add, mul_comm, mul_left_comm, mul_assoc]
  ring
theorem lean_workbook_743_8 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp only [sq, mul_add, mul_comm, mul_left_comm, add_assoc, add_sub_assoc]
  ring
theorem lean_workbook_743_9 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp only [add_mul, mul_add, mul_comm, mul_left_comm, sq, add_assoc, add_sub_assoc]
  ring
theorem lean_workbook_743_10 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp [sq, add_mul, mul_add, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_743_11 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp only [sq, mul_add, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  ring
theorem lean_workbook_743_12 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp only [mul_add, mul_sub, mul_pow, add_sq, sub_sq, mul_zero]
  ring
theorem lean_workbook_743_13 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp only [sq]
  ring
theorem lean_workbook_743_14 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp only [sq, add_mul, mul_add, mul_sub, sub_mul]
  ring
theorem lean_workbook_743_15 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp only [mul_add, mul_comm, mul_left_comm, pow_two, add_comm, add_left_comm]
  ring
theorem lean_workbook_743_16 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  linear_combination (a^2 + b^2) * (c^2 + d^2)
theorem lean_workbook_743_17 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp only [sq, mul_add, mul_comm, mul_left_comm, add_mul, add_comm, add_left_comm]
  ring
theorem lean_workbook_743_18 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  repeat' rw [sq]
  ring
theorem lean_workbook_743_19 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp only [sq, add_mul, mul_add, mul_comm, mul_left_comm, add_assoc, add_sub_assoc]
  ring
theorem lean_workbook_743_20 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp only [mul_add, add_mul, mul_pow, sub_mul, mul_sub, add_sub_assoc]
  ring
theorem lean_workbook_743_21 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp only [sq, add_mul, mul_add, mul_sub, sub_mul, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_743_22 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  rw [add_mul, mul_add]
  ring
theorem lean_workbook_743_23 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp [sq, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc]
  ring
theorem lean_workbook_743_24 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp [mul_add, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_743_25 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp only [sq, add_mul, mul_add, mul_sub, sub_mul, mul_comm, mul_assoc, mul_left_comm]
  ring
theorem lean_workbook_743_26 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp only [sq, mul_add, mul_sub, mul_comm, mul_left_comm, mul_assoc]
  ring
theorem lean_workbook_743_27 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp [add_mul, mul_add, mul_comm, mul_left_comm, sq, add_assoc, add_comm, add_left_comm]
  ring
theorem lean_workbook_743_28 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp only [sq, mul_add, mul_sub, mul_comm, mul_left_comm, add_mul, sub_mul]
  ring
theorem lean_workbook_743_29 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp [sq, mul_add, add_mul, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_743_30 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp [mul_add, mul_comm, mul_left_comm, sq, add_assoc, add_comm, add_left_comm]
  ring
theorem lean_workbook_743_31 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp [sq, mul_add, add_mul, mul_comm, mul_assoc, mul_left_comm]
  ring
theorem lean_workbook_743_32 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp only [mul_add, mul_sub, mul_comm, mul_left_comm, sq]
  ring
theorem lean_workbook_743_33 (a b c d : ℤ) : (a^2 + b^2) * (c^2 + d^2) = (a * d + b * c)^2 + (a * c - b * d)^2 := by
  simp [add_mul, mul_add, mul_comm, sub_mul, mul_sub, mul_assoc, mul_comm, ← sq]
  ring

theorem lean_workbook_749_0 (m : ℕ) (hm : 0 < m) : ∃ n, m ∣ fib n := by
  use 0
  simp [fib_zero]
theorem lean_workbook_749_1 (m : ℕ) (hm : 0 < m) : ∃ n, m ∣ fib n := by
  refine' ⟨0, by simp⟩

theorem lean_workbook_773_0 (a b c : ℝ) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a * b * c - 1)^2 := by
  field_simp [add_comm]
  nlinarith [sq_nonneg (a * b * c - 1), sq_nonneg (a * b + c)]
theorem lean_workbook_773_1 (a b c : ℝ) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a * b * c - 1)^2 := by
  field_simp [mul_add, add_mul]
  nlinarith [sq_nonneg (a * b * c), sq_nonneg (a * b + c)]
theorem lean_workbook_773_2 (a b c : ℝ) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a * b * c - 1)^2 := by
  nth_rewrite 1 [← one_mul (a^2 + 1)]
  nth_rewrite 1 [← one_mul (b^2 + 1)]
  nth_rewrite 1 [← one_mul (c^2 + 1)]
  nlinarith [sq_nonneg (a * b * c - 1), sq_nonneg (a * b + c)]
theorem lean_workbook_773_3 (a b c : ℝ) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a * b * c - 1)^2 := by
  simp [sub_eq_add_neg, add_comm, add_left_comm]
  nlinarith [sq_nonneg (a * b * c), sq_nonneg (a * b + c)]
theorem lean_workbook_773_4 (a b c : ℝ) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a * b * c - 1)^2 := by
  simp [mul_add, add_mul]
  nlinarith [sq_nonneg (a * b * c - 1), sq_nonneg (a * b + c)]
theorem lean_workbook_773_5 (a b c : ℝ) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a * b * c - 1)^2 := by
  simp [add_mul, mul_add, mul_comm, mul_assoc, mul_left_comm]
  nlinarith [sq_nonneg (a * b * c - 1), sq_nonneg (a * b + c)]
theorem lean_workbook_773_6 (a b c : ℝ) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a * b * c - 1)^2 := by
  ring_nf
  field_simp [add_comm]
  nlinarith [sq_nonneg (a * b * c - 1), sq_nonneg (a * b + c)]
theorem lean_workbook_773_7 (a b c : ℝ) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a * b * c - 1)^2 := by
  simp [sq, sub_mul, mul_sub, mul_assoc, mul_comm, mul_left_comm]
  nlinarith [sq_nonneg (a * b * c), sq_nonneg (a * b + c)]
theorem lean_workbook_773_8 (a b c : ℝ) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a * b * c - 1)^2 := by
  field_simp [sq]
  ring_nf
  nlinarith [sq_nonneg (a * b * c), sq_nonneg (a * b + c)]
theorem lean_workbook_773_9 (a b c : ℝ) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a * b * c - 1)^2 := by
  rw [sq, sq, sq]
  nlinarith [sq_nonneg (a * b * c - 1), sq_nonneg (a * b + c)]
theorem lean_workbook_773_10 (a b c : ℝ) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a * b * c - 1)^2 := by
  simp [sq, mul_add, mul_comm, mul_left_comm]
  nlinarith [sq_nonneg (a * b * c), sq_nonneg (a * b + c)]
theorem lean_workbook_773_11 (a b c : ℝ) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a * b * c - 1)^2 := by
  simp [add_mul, mul_add, mul_comm, mul_assoc, mul_left_comm]
  nlinarith [sq_nonneg (a * b * c), sq_nonneg (a * b + c)]
theorem lean_workbook_773_12 (a b c : ℝ) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a * b * c - 1)^2 := by
  simp [sq, mul_add, add_mul, mul_comm, mul_left_comm]
  nlinarith [sq_nonneg (a * b * c), sq_nonneg (a * b + c)]
theorem lean_workbook_773_13 (a b c : ℝ) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a * b * c - 1)^2 := by
  have h₁ := sq_nonneg (a * b * c - 1)
  have h₂ := sq_nonneg (a * b + c)
  have h₃ := sq_nonneg (a + b * c)
  nlinarith
theorem lean_workbook_773_14 (a b c : ℝ) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a * b * c - 1)^2 := by
  simp [sq]
  ring_nf
  nlinarith [sq_nonneg (a * b * c), sq_nonneg (a * b + c)]
theorem lean_workbook_773_15 (a b c : ℝ) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a * b * c - 1)^2 := by
  ring_nf
  field_simp [sq]
  nlinarith [sq_nonneg (a * b * c), sq_nonneg (a * b + c), sq_nonneg (a + b * c)]

theorem lean_workbook_785_0 (x y : ℝ) (r : ℝ) (hr : r = Real.sqrt (x ^ 2 + y ^ 2)) (hp : -Real.pi < θ ∧ θ ≤ Real.pi) (htr : (x, y) = (r * Real.cos θ, r * Real.sin θ)) : (x, y) = (r * Real.cos θ, r * Real.sin θ) ∧ -Real.pi < θ ∧ θ ≤ Real.pi := by
  refine' ⟨‹_›, hp⟩
theorem lean_workbook_785_1 (x y : ℝ) (r : ℝ) (hr : r = Real.sqrt (x ^ 2 + y ^ 2)) (hp : -Real.pi < θ ∧ θ ≤ Real.pi) (htr : (x, y) = (r * Real.cos θ, r * Real.sin θ)) : (x, y) = (r * Real.cos θ, r * Real.sin θ) ∧ -Real.pi < θ ∧ θ ≤ Real.pi := by
  eta_reduce at *
  refine ⟨htr, hp⟩
theorem lean_workbook_785_2 (x y : ℝ) (r : ℝ) (hr : r = Real.sqrt (x ^ 2 + y ^ 2)) (hp : -Real.pi < θ ∧ θ ≤ Real.pi) (htr : (x, y) = (r * Real.cos θ, r * Real.sin θ)) : (x, y) = (r * Real.cos θ, r * Real.sin θ) ∧ -Real.pi < θ ∧ θ ≤ Real.pi := by
  refine ⟨htr,?_⟩
  simp [hp, hr]
theorem lean_workbook_785_3 (x y : ℝ) (r : ℝ) (hr : r = Real.sqrt (x ^ 2 + y ^ 2)) (hp : -Real.pi < θ ∧ θ ≤ Real.pi) (htr : (x, y) = (r * Real.cos θ, r * Real.sin θ)) : (x, y) = (r * Real.cos θ, r * Real.sin θ) ∧ -Real.pi < θ ∧ θ ≤ Real.pi := by
  refine' ⟨htr, _⟩
  simp [hr, hp]
theorem lean_workbook_785_4 (x y : ℝ) (r : ℝ) (hr : r = Real.sqrt (x ^ 2 + y ^ 2)) (hp : -Real.pi < θ ∧ θ ≤ Real.pi) (htr : (x, y) = (r * Real.cos θ, r * Real.sin θ)) : (x, y) = (r * Real.cos θ, r * Real.sin θ) ∧ -Real.pi < θ ∧ θ ≤ Real.pi := by
  refine ⟨htr,?_⟩
  exact hp
theorem lean_workbook_785_5 (x y : ℝ) (r : ℝ) (hr : r = Real.sqrt (x ^ 2 + y ^ 2)) (hp : -Real.pi < θ ∧ θ ≤ Real.pi) (htr : (x, y) = (r * Real.cos θ, r * Real.sin θ)) : (x, y) = (r * Real.cos θ, r * Real.sin θ) ∧ -Real.pi < θ ∧ θ ≤ Real.pi := by
  constructor <;> simp [hr, hp, htr]
theorem lean_workbook_785_6 (x y : ℝ) (r : ℝ) (hr : r = Real.sqrt (x ^ 2 + y ^ 2)) (hp : -Real.pi < θ ∧ θ ≤ Real.pi) (htr : (x, y) = (r * Real.cos θ, r * Real.sin θ)) : (x, y) = (r * Real.cos θ, r * Real.sin θ) ∧ -Real.pi < θ ∧ θ ≤ Real.pi := by
  convert And.intro htr (And.intro hp.1 hp.2)
theorem lean_workbook_785_7 (x y : ℝ) (r : ℝ) (hr : r = Real.sqrt (x ^ 2 + y ^ 2)) (hp : -Real.pi < θ ∧ θ ≤ Real.pi) (htr : (x, y) = (r * Real.cos θ, r * Real.sin θ)) : (x, y) = (r * Real.cos θ, r * Real.sin θ) ∧ -Real.pi < θ ∧ θ ≤ Real.pi := by
  refine ⟨?_, hp⟩
  rw [htr]
theorem lean_workbook_785_8 (x y : ℝ) (r : ℝ) (hr : r = Real.sqrt (x ^ 2 + y ^ 2)) (hp : -Real.pi < θ ∧ θ ≤ Real.pi) (htr : (x, y) = (r * Real.cos θ, r * Real.sin θ)) : (x, y) = (r * Real.cos θ, r * Real.sin θ) ∧ -Real.pi < θ ∧ θ ≤ Real.pi := by
  simp [htr, hp]
theorem lean_workbook_785_9 (x y : ℝ) (r : ℝ) (hr : r = Real.sqrt (x ^ 2 + y ^ 2)) (hp : -Real.pi < θ ∧ θ ≤ Real.pi) (htr : (x, y) = (r * Real.cos θ, r * Real.sin θ)) : (x, y) = (r * Real.cos θ, r * Real.sin θ) ∧ -Real.pi < θ ∧ θ ≤ Real.pi := by
  refine ⟨?_, hp⟩
  simp [htr]
theorem lean_workbook_785_10 (x y : ℝ) (r : ℝ) (hr : r = Real.sqrt (x ^ 2 + y ^ 2)) (hp : -Real.pi < θ ∧ θ ≤ Real.pi) (htr : (x, y) = (r * Real.cos θ, r * Real.sin θ)) : (x, y) = (r * Real.cos θ, r * Real.sin θ) ∧ -Real.pi < θ ∧ θ ≤ Real.pi := by
  simp [hr, hp, htr]
theorem lean_workbook_785_11 (x y : ℝ) (r : ℝ) (hr : r = Real.sqrt (x ^ 2 + y ^ 2)) (hp : -Real.pi < θ ∧ θ ≤ Real.pi) (htr : (x, y) = (r * Real.cos θ, r * Real.sin θ)) : (x, y) = (r * Real.cos θ, r * Real.sin θ) ∧ -Real.pi < θ ∧ θ ≤ Real.pi := by
  obtain ⟨h, h'⟩ := hp
  exact ⟨htr, ⟨h, h'⟩⟩
theorem lean_workbook_785_12 (x y : ℝ) (r : ℝ) (hr : r = Real.sqrt (x ^ 2 + y ^ 2)) (hp : -Real.pi < θ ∧ θ ≤ Real.pi) (htr : (x, y) = (r * Real.cos θ, r * Real.sin θ)) : (x, y) = (r * Real.cos θ, r * Real.sin θ) ∧ -Real.pi < θ ∧ θ ≤ Real.pi := by
  exact ⟨htr, hp⟩
theorem lean_workbook_785_13 (x y : ℝ) (r : ℝ) (hr : r = Real.sqrt (x ^ 2 + y ^ 2)) (hp : -Real.pi < θ ∧ θ ≤ Real.pi) (htr : (x, y) = (r * Real.cos θ, r * Real.sin θ)) : (x, y) = (r * Real.cos θ, r * Real.sin θ) ∧ -Real.pi < θ ∧ θ ≤ Real.pi := by
  refine ⟨?_,?_,?_⟩
  exacts [htr, hp.1, hp.2]
theorem lean_workbook_785_14 (x y : ℝ) (r : ℝ) (hr : r = Real.sqrt (x ^ 2 + y ^ 2)) (hp : -Real.pi < θ ∧ θ ≤ Real.pi) (htr : (x, y) = (r * Real.cos θ, r * Real.sin θ)) : (x, y) = (r * Real.cos θ, r * Real.sin θ) ∧ -Real.pi < θ ∧ θ ≤ Real.pi := by
  refine ⟨htr,?_⟩
  refine ⟨?_,?_⟩
  exacts [hp.1, hp.2]
theorem lean_workbook_785_15 (x y : ℝ) (r : ℝ) (hr : r = Real.sqrt (x ^ 2 + y ^ 2)) (hp : -Real.pi < θ ∧ θ ≤ Real.pi) (htr : (x, y) = (r * Real.cos θ, r * Real.sin θ)) : (x, y) = (r * Real.cos θ, r * Real.sin θ) ∧ -Real.pi < θ ∧ θ ≤ Real.pi := by
  refine' ⟨htr, ⟨hp.1, hp.2⟩⟩
theorem lean_workbook_785_16 (x y : ℝ) (r : ℝ) (hr : r = Real.sqrt (x ^ 2 + y ^ 2)) (hp : -Real.pi < θ ∧ θ ≤ Real.pi) (htr : (x, y) = (r * Real.cos θ, r * Real.sin θ)) : (x, y) = (r * Real.cos θ, r * Real.sin θ) ∧ -Real.pi < θ ∧ θ ≤ Real.pi := by
  constructor <;> [exact htr; constructor <;> [exact hp.1; exact hp.2]]
theorem lean_workbook_785_17 (x y : ℝ) (r : ℝ) (hr : r = Real.sqrt (x ^ 2 + y ^ 2)) (hp : -Real.pi < θ ∧ θ ≤ Real.pi) (htr : (x, y) = (r * Real.cos θ, r * Real.sin θ)) : (x, y) = (r * Real.cos θ, r * Real.sin θ) ∧ -Real.pi < θ ∧ θ ≤ Real.pi := by
  refine ⟨htr, ⟨hp.1, hp.2⟩⟩
theorem lean_workbook_785_18 (x y : ℝ) (r : ℝ) (hr : r = Real.sqrt (x ^ 2 + y ^ 2)) (hp : -Real.pi < θ ∧ θ ≤ Real.pi) (htr : (x, y) = (r * Real.cos θ, r * Real.sin θ)) : (x, y) = (r * Real.cos θ, r * Real.sin θ) ∧ -Real.pi < θ ∧ θ ≤ Real.pi := by
  simp [hr, htr, hp]
theorem lean_workbook_785_19 (x y : ℝ) (r : ℝ) (hr : r = Real.sqrt (x ^ 2 + y ^ 2)) (hp : -Real.pi < θ ∧ θ ≤ Real.pi) (htr : (x, y) = (r * Real.cos θ, r * Real.sin θ)) : (x, y) = (r * Real.cos θ, r * Real.sin θ) ∧ -Real.pi < θ ∧ θ ≤ Real.pi := by
  refine' ⟨by simp [htr], hp⟩
theorem lean_workbook_785_20 (x y : ℝ) (r : ℝ) (hr : r = Real.sqrt (x ^ 2 + y ^ 2)) (hp : -Real.pi < θ ∧ θ ≤ Real.pi) (htr : (x, y) = (r * Real.cos θ, r * Real.sin θ)) : (x, y) = (r * Real.cos θ, r * Real.sin θ) ∧ -Real.pi < θ ∧ θ ≤ Real.pi := by
  constructor
  exact htr
  exact hp
theorem lean_workbook_785_21 (x y : ℝ) (r : ℝ) (hr : r = Real.sqrt (x ^ 2 + y ^ 2)) (hp : -Real.pi < θ ∧ θ ≤ Real.pi) (htr : (x, y) = (r * Real.cos θ, r * Real.sin θ)) : (x, y) = (r * Real.cos θ, r * Real.sin θ) ∧ -Real.pi < θ ∧ θ ≤ Real.pi := by
  refine ⟨htr, hp.left, hp.right⟩
theorem lean_workbook_785_22 (x y : ℝ) (r : ℝ) (hr : r = Real.sqrt (x ^ 2 + y ^ 2)) (hp : -Real.pi < θ ∧ θ ≤ Real.pi) (htr : (x, y) = (r * Real.cos θ, r * Real.sin θ)) : (x, y) = (r * Real.cos θ, r * Real.sin θ) ∧ -Real.pi < θ ∧ θ ≤ Real.pi := by
  refine' ⟨_, hp⟩
  exact htr

theorem lean_workbook_790_0 (n : ℕ) (u : ℕ → ℕ) (h₀ : 1 ≤ n) (h₁ : ∀ n, u n ≠ 0) (h₂ : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) = n / (u 1 * u (n + 1))) : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) = n / (u 1 * u (n + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) := by
  simp only [h₀, h₁, h₂]
theorem lean_workbook_790_1 (n : ℕ) (u : ℕ → ℕ) (h₀ : 1 ≤ n) (h₁ : ∀ n, u n ≠ 0) (h₂ : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) = n / (u 1 * u (n + 1))) : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) = n / (u 1 * u (n + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) := by
  simp only [h₂, h₁, h₀, Nat.add_succ_sub_one, add_zero, Finset.sum_add_distrib, Finset.sum_singleton]
theorem lean_workbook_790_2 (n : ℕ) (u : ℕ → ℕ) (h₀ : 1 ≤ n) (h₁ : ∀ n, u n ≠ 0) (h₂ : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) = n / (u 1 * u (n + 1))) : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) = n / (u 1 * u (n + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) := by
  simp only [h₀, h₁, h₂, le_refl, Finset.Icc_self, Finset.sum_singleton]
theorem lean_workbook_790_3 (n : ℕ) (u : ℕ → ℕ) (h₀ : 1 ≤ n) (h₁ : ∀ n, u n ≠ 0) (h₂ : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) = n / (u 1 * u (n + 1))) : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) = n / (u 1 * u (n + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) := by
  simp only [Finset.sum_range_succ, h₂, Nat.succ_eq_add_one]
theorem lean_workbook_790_4 (n : ℕ) (u : ℕ → ℕ) (h₀ : 1 ≤ n) (h₁ : ∀ n, u n ≠ 0) (h₂ : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) = n / (u 1 * u (n + 1))) : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) = n / (u 1 * u (n + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) := by
  simp only [h₂, Finset.sum_add_distrib, add_assoc]
theorem lean_workbook_790_5 (n : ℕ) (u : ℕ → ℕ) (h₀ : 1 ≤ n) (h₁ : ∀ n, u n ≠ 0) (h₂ : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) = n / (u 1 * u (n + 1))) : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) = n / (u 1 * u (n + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) := by
  simp only [h₂, Finset.sum_add_distrib, add_left_inj]
theorem lean_workbook_790_6 (n : ℕ) (u : ℕ → ℕ) (h₀ : 1 ≤ n) (h₁ : ∀ n, u n ≠ 0) (h₂ : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) = n / (u 1 * u (n + 1))) : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) = n / (u 1 * u (n + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) := by
  simp only [h₂, Finset.sum_congr]
theorem lean_workbook_790_7 (n : ℕ) (u : ℕ → ℕ) (h₀ : 1 ≤ n) (h₁ : ∀ n, u n ≠ 0) (h₂ : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) = n / (u 1 * u (n + 1))) : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) = n / (u 1 * u (n + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) := by
  simp only [h₂, Finset.sum_add_distrib, add_right_inj]
theorem lean_workbook_790_8 (n : ℕ) (u : ℕ → ℕ) (h₀ : 1 ≤ n) (h₁ : ∀ n, u n ≠ 0) (h₂ : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) = n / (u 1 * u (n + 1))) : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) = n / (u 1 * u (n + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) := by
  simp only [h₀, h₁, h₂, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
theorem lean_workbook_790_9 (n : ℕ) (u : ℕ → ℕ) (h₀ : 1 ≤ n) (h₁ : ∀ n, u n ≠ 0) (h₂ : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) = n / (u 1 * u (n + 1))) : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) = n / (u 1 * u (n + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) := by
  simp only [h₀, h₁, h₂, Finset.sum_add_distrib, add_comm, add_left_comm]
theorem lean_workbook_790_10 (n : ℕ) (u : ℕ → ℕ) (h₀ : 1 ≤ n) (h₁ : ∀ n, u n ≠ 0) (h₂ : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) = n / (u 1 * u (n + 1))) : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) = n / (u 1 * u (n + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) := by
  simp only [h₂, add_right_inj]
theorem lean_workbook_790_11 (n : ℕ) (u : ℕ → ℕ) (h₀ : 1 ≤ n) (h₁ : ∀ n, u n ≠ 0) (h₂ : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) = n / (u 1 * u (n + 1))) : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) = n / (u 1 * u (n + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) := by
  nth_rw 1 [h₂]
theorem lean_workbook_790_12 (n : ℕ) (u : ℕ → ℕ) (h₀ : 1 ≤ n) (h₁ : ∀ n, u n ≠ 0) (h₂ : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) = n / (u 1 * u (n + 1))) : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) = n / (u 1 * u (n + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) := by
  simp only [h₁, h₂, Finset.sum_add_sum_compl, Finset.sum_singleton, Finset.Icc_self]
theorem lean_workbook_790_13 (n : ℕ) (u : ℕ → ℕ) (h₀ : 1 ≤ n) (h₁ : ∀ n, u n ≠ 0) (h₂ : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) = n / (u 1 * u (n + 1))) : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) = n / (u 1 * u (n + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) := by
  simp only [h₂]
theorem lean_workbook_790_14 (n : ℕ) (u : ℕ → ℕ) (h₀ : 1 ≤ n) (h₁ : ∀ n, u n ≠ 0) (h₂ : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) = n / (u 1 * u (n + 1))) : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) = n / (u 1 * u (n + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) := by
  simp only [h₀, h₁, h₂, add_left_inj]
theorem lean_workbook_790_15 (n : ℕ) (u : ℕ → ℕ) (h₀ : 1 ≤ n) (h₁ : ∀ n, u n ≠ 0) (h₂ : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) = n / (u 1 * u (n + 1))) : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) = n / (u 1 * u (n + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) := by
  simp only [h₂, Nat.cast_add, Nat.cast_one]
theorem lean_workbook_790_16 (n : ℕ) (u : ℕ → ℕ) (h₀ : 1 ≤ n) (h₁ : ∀ n, u n ≠ 0) (h₂ : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) = n / (u 1 * u (n + 1))) : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) = n / (u 1 * u (n + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) := by
  simp only [h₂, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
theorem lean_workbook_790_17 (n : ℕ) (u : ℕ → ℕ) (h₀ : 1 ≤ n) (h₁ : ∀ n, u n ≠ 0) (h₂ : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) = n / (u 1 * u (n + 1))) : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) = n / (u 1 * u (n + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) := by
  simp only [h₂, Finset.sum_add_distrib, Finset.sum_singleton]
theorem lean_workbook_790_18 (n : ℕ) (u : ℕ → ℕ) (h₀ : 1 ≤ n) (h₁ : ∀ n, u n ≠ 0) (h₂ : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) = n / (u 1 * u (n + 1))) : ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / (u k * u (k + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) = n / (u 1 * u (n + 1)) + (1 : ℝ) / (u (n + 1) * u (n + 2)) := by
  simp only [h₂, Finset.sum_add_distrib, add_assoc, add_left_comm]

theorem lean_workbook_795_0 (a b c : ℝ) : (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  simp [mul_add, mul_left_comm, mul_comm]
  ring
theorem lean_workbook_795_1 (a b c : ℝ) : (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  simp only [add_assoc]
  simp only [add_comm, add_left_comm]
  ring
theorem lean_workbook_795_2 (a b c : ℝ) : (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  field_simp [add_comm, add_left_comm, add_assoc]
  ring
theorem lean_workbook_795_3 (a b c : ℝ) : (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  simp [sub_eq_add_neg]
  ring
theorem lean_workbook_795_4 (a b c : ℝ) : (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  field_simp [add_comm, add_left_comm]
  ring
theorem lean_workbook_795_5 (a b c : ℝ) : (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  repeat' rw [pow_three]
  ring_nf
theorem lean_workbook_795_6 (a b c : ℝ) : (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  simp [add_mul, mul_add, mul_comm, mul_left_comm]
  ring_nf
theorem lean_workbook_795_7 (a b c : ℝ) : (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  field_simp [mul_add, mul_comm, mul_left_comm]
  ring_nf
theorem lean_workbook_795_8 (a b c : ℝ) : (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  rw [add_comm a b, add_assoc, add_comm _ c, add_comm b c]
  ring
theorem lean_workbook_795_9 (a b c : ℝ) : (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  simp [add_comm, add_left_comm, add_assoc]
  ring_nf
theorem lean_workbook_795_10 (a b c : ℝ) : (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  simp [mul_add, add_mul, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_795_11 (a b c : ℝ) : (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  field_simp [pow_three]
  ring
theorem lean_workbook_795_12 (a b c : ℝ) : (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  simp [add_comm]
  ring
theorem lean_workbook_795_13 (a b c : ℝ) : (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  simp [mul_add, add_mul, sq]
  ring
theorem lean_workbook_795_14 (a b c : ℝ) : (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  field_simp [add_comm]
  ring
theorem lean_workbook_795_15 (a b c : ℝ) : (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  field_simp [mul_comm, mul_assoc, mul_left_comm]
  ring_nf
theorem lean_workbook_795_16 (a b c : ℝ) : (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  rw [← sub_eq_zero]
  field_simp [add_assoc, add_comm, add_left_comm]
  ring
theorem lean_workbook_795_17 (a b c : ℝ) : (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  simp [mul_add, mul_comm, mul_left_comm]
  ring_nf
theorem lean_workbook_795_18 (a b c : ℝ) : (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  field_simp [add_assoc, add_comm, add_left_comm]
  ring_nf
theorem lean_workbook_795_19 (a b c : ℝ) : (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  ring
theorem lean_workbook_795_20 (a b c : ℝ) : (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  simp only [add_comm]
  ring_nf
theorem lean_workbook_795_21 (a b c : ℝ) : (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  simp [sq, mul_add, add_mul]
  ring
theorem lean_workbook_795_22 (a b c : ℝ) : (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  simp only [add_sq, add_assoc, add_left_comm]
  ring_nf
theorem lean_workbook_795_23 (a b c : ℝ) : (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  simp [add_mul, mul_add]
  ring
theorem lean_workbook_795_24 (a b c : ℝ) : (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  simp [add_mul, mul_add, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_795_25 (a b c : ℝ) : (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  simp only [add_comm, add_left_comm]
  ring
theorem lean_workbook_795_26 (a b c : ℝ) : (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  field_simp [mul_assoc]
  ring
theorem lean_workbook_795_27 (a b c : ℝ) : (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  simp only [sq, add_assoc, add_sub_assoc]
  ring

theorem lean_workbook_811_0 : ∀ x : ℝ, x^4 + x^2 + 1 = (x^2 - x + 1) * (x^2 + x + 1) := by
  simp [sub_eq_add_neg]
  intro x
  ring
theorem lean_workbook_811_1 : ∀ x : ℝ, x^4 + x^2 + 1 = (x^2 - x + 1) * (x^2 + x + 1) := by
  intros x
  simp [sq]
  ring
theorem lean_workbook_811_2 : ∀ x : ℝ, x^4 + x^2 + 1 = (x^2 - x + 1) * (x^2 + x + 1) := by
  intro x
  rw [add_assoc]
  ring
theorem lean_workbook_811_3 : ∀ x : ℝ, x^4 + x^2 + 1 = (x^2 - x + 1) * (x^2 + x + 1) := by
  rintro x
  ring_nf
theorem lean_workbook_811_4 : ∀ x : ℝ, x^4 + x^2 + 1 = (x^2 - x + 1) * (x^2 + x + 1) := by
  refine' fun x => by ring
theorem lean_workbook_811_5 : ∀ x : ℝ, x^4 + x^2 + 1 = (x^2 - x + 1) * (x^2 + x + 1) := by
  intro x; ring
theorem lean_workbook_811_6 : ∀ x : ℝ, x^4 + x^2 + 1 = (x^2 - x + 1) * (x^2 + x + 1) := by
  rintro x
  linear_combination x^4 + x^2 + 1 - (x^2 - x + 1) * (x^2 + x + 1)
theorem lean_workbook_811_7 : ∀ x : ℝ, x^4 + x^2 + 1 = (x^2 - x + 1) * (x^2 + x + 1) := by
  intro x
  simp [sub_mul, mul_add, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_811_8 : ∀ x : ℝ, x^4 + x^2 + 1 = (x^2 - x + 1) * (x^2 + x + 1) := by
  simp [add_mul, mul_add, mul_comm, mul_left_comm, sq]
  intro x
  ring
theorem lean_workbook_811_9 : ∀ x : ℝ, x^4 + x^2 + 1 = (x^2 - x + 1) * (x^2 + x + 1) := by
  intro x
  simp [add_mul, mul_add, mul_comm, mul_left_comm, sq]
  ring
theorem lean_workbook_811_10 : ∀ x : ℝ, x^4 + x^2 + 1 = (x^2 - x + 1) * (x^2 + x + 1) := by
  intro x
  simp [add_mul, mul_add, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_811_11 : ∀ x : ℝ, x^4 + x^2 + 1 = (x^2 - x + 1) * (x^2 + x + 1) := by
  intro x
  simp [mul_add, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_811_12 : ∀ x : ℝ, x^4 + x^2 + 1 = (x^2 - x + 1) * (x^2 + x + 1) := by
  repeat' intro x; ring
theorem lean_workbook_811_13 : ∀ x : ℝ, x^4 + x^2 + 1 = (x^2 - x + 1) * (x^2 + x + 1) := by
  intro x
  nlinarith [x^4 + x^2 + 1]
theorem lean_workbook_811_14 : ∀ x : ℝ, x^4 + x^2 + 1 = (x^2 - x + 1) * (x^2 + x + 1) := by
  intro x
  simp [mul_add, add_mul, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_811_15 : ∀ x : ℝ, x^4 + x^2 + 1 = (x^2 - x + 1) * (x^2 + x + 1) := by
  intro x
  simp [sq, mul_add, add_mul, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_811_16 : ∀ x : ℝ, x^4 + x^2 + 1 = (x^2 - x + 1) * (x^2 + x + 1) := by
  simp [mul_add, add_mul, mul_comm, mul_left_comm]
  intro x
  ring
theorem lean_workbook_811_17 : ∀ x : ℝ, x^4 + x^2 + 1 = (x^2 - x + 1) * (x^2 + x + 1) := by
  simp [sq, mul_add, mul_comm, mul_left_comm]
  intro x
  ring
theorem lean_workbook_811_18 : ∀ x : ℝ, x^4 + x^2 + 1 = (x^2 - x + 1) * (x^2 + x + 1) := by
  intro x
  ring_nf
theorem lean_workbook_811_19 : ∀ x : ℝ, x^4 + x^2 + 1 = (x^2 - x + 1) * (x^2 + x + 1) := by
  intro x
  linarith [x^4 + x^2 + 1]
theorem lean_workbook_811_20 : ∀ x : ℝ, x^4 + x^2 + 1 = (x^2 - x + 1) * (x^2 + x + 1) := by
  intros x
  field_simp [sq, mul_add, add_mul]
  ring
theorem lean_workbook_811_21 : ∀ x : ℝ, x^4 + x^2 + 1 = (x^2 - x + 1) * (x^2 + x + 1) := by
  intro x
  field_simp [pow_two]
  ring
theorem lean_workbook_811_22 : ∀ x : ℝ, x^4 + x^2 + 1 = (x^2 - x + 1) * (x^2 + x + 1) := by
  simp [sq, mul_add, add_mul, mul_comm, mul_left_comm]
  intro x
  ring
theorem lean_workbook_811_23 : ∀ x : ℝ, x^4 + x^2 + 1 = (x^2 - x + 1) * (x^2 + x + 1) := by
  refine' fun x => eq_of_sub_eq_zero _
  field_simp [mul_add, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_811_24 : ∀ x : ℝ, x^4 + x^2 + 1 = (x^2 - x + 1) * (x^2 + x + 1) := by
  intro x
  simp [sq, mul_add, add_mul]
  ring
theorem lean_workbook_811_25 : ∀ x : ℝ, x^4 + x^2 + 1 = (x^2 - x + 1) * (x^2 + x + 1) := by
  refine' fun x => eq_of_sub_eq_zero _
  field_simp [mul_add, add_mul, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_811_26 : ∀ x : ℝ, x^4 + x^2 + 1 = (x^2 - x + 1) * (x^2 + x + 1) := by
  simp [sub_mul, mul_add, mul_sub, add_mul, add_sub, sub_sub_sub_cancel_right]
  intro x; ring

theorem lean_workbook_837_0 :∀ a b c x y z p q r : ℝ, p = a^2 + b^2 + c^2 ∧ q = a * b + b * c + c * a ∧ r = (b - a) * (b - c) ∧ x = a^2 + 2 * b * c ∧ y = b^2 + 2 * c * a ∧ z = c^2 + 2 * a * b → x * z = p * (q - r) + r^2 := by
  intros a b c x y z p q r h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  ring
theorem lean_workbook_837_1 :∀ a b c x y z p q r : ℝ, p = a^2 + b^2 + c^2 ∧ q = a * b + b * c + c * a ∧ r = (b - a) * (b - c) ∧ x = a^2 + 2 * b * c ∧ y = b^2 + 2 * c * a ∧ z = c^2 + 2 * a * b → x * z = p * (q - r) + r^2 := by
  intro a b c x y z p q r h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  repeat rw [sq]; ring
theorem lean_workbook_837_2 :∀ a b c x y z p q r : ℝ, p = a^2 + b^2 + c^2 ∧ q = a * b + b * c + c * a ∧ r = (b - a) * (b - c) ∧ x = a^2 + 2 * b * c ∧ y = b^2 + 2 * c * a ∧ z = c^2 + 2 * a * b → x * z = p * (q - r) + r^2 := by
  intro a b c x y z p q r h
  simp [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2]
  ring_nf
theorem lean_workbook_837_3 :∀ a b c x y z p q r : ℝ, p = a^2 + b^2 + c^2 ∧ q = a * b + b * c + c * a ∧ r = (b - a) * (b - c) ∧ x = a^2 + 2 * b * c ∧ y = b^2 + 2 * c * a ∧ z = c^2 + 2 * a * b → x * z = p * (q - r) + r^2 := by
  intro a b c x y z p q r h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  ring_nf
theorem lean_workbook_837_4 :∀ a b c x y z p q r : ℝ, p = a^2 + b^2 + c^2 ∧ q = a * b + b * c + c * a ∧ r = (b - a) * (b - c) ∧ x = a^2 + 2 * b * c ∧ y = b^2 + 2 * c * a ∧ z = c^2 + 2 * a * b → x * z = p * (q - r) + r^2 := by
  intro a b c x y z p q r h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  repeat' rw [sq]; ring
theorem lean_workbook_837_5 :∀ a b c x y z p q r : ℝ, p = a^2 + b^2 + c^2 ∧ q = a * b + b * c + c * a ∧ r = (b - a) * (b - c) ∧ x = a^2 + 2 * b * c ∧ y = b^2 + 2 * c * a ∧ z = c^2 + 2 * a * b → x * z = p * (q - r) + r^2 := by
  intro a b c x y z p q r h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  simp [add_mul, mul_add, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_837_6 :∀ a b c x y z p q r : ℝ, p = a^2 + b^2 + c^2 ∧ q = a * b + b * c + c * a ∧ r = (b - a) * (b - c) ∧ x = a^2 + 2 * b * c ∧ y = b^2 + 2 * c * a ∧ z = c^2 + 2 * a * b → x * z = p * (q - r) + r^2 := by
  rintro a b c x y z p q r ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  repeat' rw [sq]; ring
theorem lean_workbook_837_7 :∀ a b c x y z p q r : ℝ, p = a^2 + b^2 + c^2 ∧ q = a * b + b * c + c * a ∧ r = (b - a) * (b - c) ∧ x = a^2 + 2 * b * c ∧ y = b^2 + 2 * c * a ∧ z = c^2 + 2 * a * b → x * z = p * (q - r) + r^2 := by
  intro a b c x y z p q r
  rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  ring
theorem lean_workbook_837_8 :∀ a b c x y z p q r : ℝ, p = a^2 + b^2 + c^2 ∧ q = a * b + b * c + c * a ∧ r = (b - a) * (b - c) ∧ x = a^2 + 2 * b * c ∧ y = b^2 + 2 * c * a ∧ z = c^2 + 2 * a * b → x * z = p * (q - r) + r^2 := by
  rintro a b c x y z p q r ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp [mul_comm, mul_assoc, mul_left_comm]
  ring
theorem lean_workbook_837_9 :∀ a b c x y z p q r : ℝ, p = a^2 + b^2 + c^2 ∧ q = a * b + b * c + c * a ∧ r = (b - a) * (b - c) ∧ x = a^2 + 2 * b * c ∧ y = b^2 + 2 * c * a ∧ z = c^2 + 2 * a * b → x * z = p * (q - r) + r^2 := by
  rintro a b c x y z p q r ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  ring

theorem lean_workbook_847_0 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  ring_nf
  have h1 : 0 ≤ (x - y)^2 := sq_nonneg (x - y)
  linarith [sq_nonneg (x + y)]
theorem lean_workbook_847_1 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  rw [add_sq]
  linarith [mul_self_nonneg (x - y)]
theorem lean_workbook_847_2 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  have h1: 0 ≤ (x - y)^2 := sq_nonneg (x - y)
  linarith
theorem lean_workbook_847_3 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  have : 0 ≤ (x - y)^2 := sq_nonneg (x - y)
  linarith
theorem lean_workbook_847_4 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  rw [two_mul]
  have := sq_nonneg (x - y)
  linarith
theorem lean_workbook_847_5 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  have := sq_nonneg (x - y)
  linarith [sq_nonneg (x + y)]
theorem lean_workbook_847_6 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  linarith [sq_nonneg (x - y), sq_nonneg (x + y)]
theorem lean_workbook_847_7 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  simp [sq, mul_add, add_mul, mul_comm, mul_left_comm]
  nlinarith [sq_nonneg (x - y)]
theorem lean_workbook_847_8 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  have h1 : 0 ≤ (x - y)^2 := sq_nonneg (x - y)
  linarith only [h1]
theorem lean_workbook_847_9 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  ring_nf
  nlinarith [sq_nonneg (x - y)]
theorem lean_workbook_847_10 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  rw [pow_two, pow_two]
  have h1 : 0 ≤ (x - y)^2 := sq_nonneg (x - y)
  linarith
theorem lean_workbook_847_11 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  have h0 : 0 ≤ (x - y)^2 := sq_nonneg (x - y)
  linarith
theorem lean_workbook_847_12 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  have h1 : 0 ≤ (x - y)^2 := sq_nonneg (x - y)
  linarith [sq_nonneg (x + y)]
theorem lean_workbook_847_13 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  have h1 : 0 ≤ (x - y)^2 := sq_nonneg (x - y)
  rw [sq] at h1
  linarith
theorem lean_workbook_847_14 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  rw [pow_two]
  have h1 : 0 ≤ (x - y)^2 := sq_nonneg (x - y)
  linarith [sq_nonneg (x + y)]
theorem lean_workbook_847_15 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  have h1 : (x - y)^2 ≥ 0 := sq_nonneg (x - y)
  simp [sub_sq, add_comm] at h1
  linarith
theorem lean_workbook_847_16 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  have : (x - y)^2 ≥ 0 := sq_nonneg (x - y)
  linarith
theorem lean_workbook_847_17 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  rw [sq, sq]
  have h1 : 0 ≤ (x - y)^2 := sq_nonneg (x - y)
  linarith
theorem lean_workbook_847_18 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  simp [sq, mul_add, mul_comm, mul_left_comm]
  linarith [sq_nonneg (x - y)]
theorem lean_workbook_847_19 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  have h : 0 ≤ (x - y)^2 := sq_nonneg (x - y)
  linarith [sq_nonneg (x + y)]
theorem lean_workbook_847_20 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  rw [pow_two]
  ring_nf
  linarith [sq_nonneg (x + y), sq_nonneg (x - y)]
theorem lean_workbook_847_21 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  simp [sq, mul_add, mul_two]
  linarith [sq_nonneg (x - y)]
theorem lean_workbook_847_22 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  ring_nf
  linarith [sq_nonneg (x - y)]
theorem lean_workbook_847_23 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  have : 0 ≤ (x - y)^2 := sq_nonneg (x - y)
  linarith [sq_nonneg (x - y)]
theorem lean_workbook_847_24 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  have h1: 0 ≤ (x - y)^2 := sq_nonneg (x - y)
  linarith [sq_nonneg (x + y)]
theorem lean_workbook_847_25 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  rw [sq]
  have h1 : 0 ≤ (x - y)^2 := sq_nonneg (x - y)
  linarith
theorem lean_workbook_847_26 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  have h0 : 0 ≤ (x - y)^2 := sq_nonneg (x - y)
  linarith [sq_nonneg (x + y)]
theorem lean_workbook_847_27 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  rw [add_sq]
  linarith [sq_nonneg (x - y)]
theorem lean_workbook_847_28 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  have h2 : (x - y)^2 ≥ 0 := sq_nonneg (x - y)
  linarith [sq_nonneg (x + y)]
theorem lean_workbook_847_29 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  have h : 0 ≤ (x - y)^2 := sq_nonneg (x - y)
  linarith
theorem lean_workbook_847_30 (x y : ℝ) : 2 * (x^2 + y^2) ≥ (x + y)^2 := by
  ring_nf
  norm_num
  nlinarith [sq_nonneg (x - y)]

theorem lean_workbook_849_0 : Real.cos (π / 2) = 0 := by
  have h1 : (π / 2 : ℝ) = (π / 2 : ℝ) - 0 := by ring
  rw [h1]
  rw [Real.cos_sub]
  simp
theorem lean_workbook_849_1 : Real.cos (π / 2) = 0 := by
  simp [ Real.cos, exp_neg, add_comm, sub_eq_add_neg]
theorem lean_workbook_849_2 : Real.cos (π / 2) = 0 := by
  simp [Real.cos_pi_div_two]
theorem lean_workbook_849_3 : Real.cos (π / 2) = 0 := by
  simp [Real.pi_pos.le]
theorem lean_workbook_849_4 : Real.cos (π / 2) = 0 := by
  simp [add_comm, cos_add]
theorem lean_workbook_849_5 : Real.cos (π / 2) = 0 := by
  simp [Real.cos_pi]
theorem lean_workbook_849_6 : Real.cos (π / 2) = 0 := by
  simp [cos_antiperiodic, sub_self]
theorem lean_workbook_849_7 : Real.cos (π / 2) = 0 := by
  exact Real.cos_pi_div_two
theorem lean_workbook_849_8 : Real.cos (π / 2) = 0 := by
  simp [Real.cos_sub_pi]
theorem lean_workbook_849_9 : Real.cos (π / 2) = 0 := by
  simp [cos, exp_neg, add_comm]
theorem lean_workbook_849_10 : Real.cos (π / 2) = 0 := by
  simp [Real.pi_div_two_pos.le]
theorem lean_workbook_849_11 : Real.cos (π / 2) = 0 := by
  simp [cos, ← mul_assoc]

theorem lean_workbook_874_0 (a b : ℝ) (hab : a > -1 ∧ b > -1)(h : a^3 + b^3 >= a^2 + b^2) : a^5 + b^5 >= a^2 + b^2 := by
  have h1 := sq_nonneg (a^2 - a)
  have h2 := sq_nonneg (b^2 - b)
  nlinarith [hab.1, hab.2, h, h1, h2]
theorem lean_workbook_874_1 (a b : ℝ) (hab : a > -1 ∧ b > -1)(h : a^3 + b^3 >= a^2 + b^2) : a^5 + b^5 >= a^2 + b^2 := by
  have h₁ := sq_nonneg (a^2 - a)
  have h₂ := sq_nonneg (b^2 - b)
  nlinarith [h₁, h₂, h]

theorem lean_workbook_942_0 : 1 - (25 : ℝ) / 64 = 39 / 64 := by
  field_simp [show (64 : ℝ) ≠ 0 by norm_num, show (25 : ℝ) ≠ 0 by norm_num]
  ring
theorem lean_workbook_942_1 : 1 - (25 : ℝ) / 64 = 39 / 64 := by
  norm_num [Nat.div_eq_of_eq_mul_left zero_lt_two]
theorem lean_workbook_942_2 : 1 - (25 : ℝ) / 64 = 39 / 64 := by
  norm_num [div_eq_mul_inv, inv_eq_one_div]
theorem lean_workbook_942_3 : 1 - (25 : ℝ) / 64 = 39 / 64 := by
  rw [sub_eq_add_neg]
  norm_num [add_comm]
theorem lean_workbook_942_4 : 1 - (25 : ℝ) / 64 = 39 / 64 := by
  linarith  [25 / 64]
theorem lean_workbook_942_5 : 1 - (25 : ℝ) / 64 = 39 / 64 := by
  field_simp; ring
theorem lean_workbook_942_6 : 1 - (25 : ℝ) / 64 = 39 / 64 := by
  simp only [sub_eq_add_neg, neg_div]
  norm_num [div_eq_mul_inv, div_eq_mul_inv]
theorem lean_workbook_942_7 : 1 - (25 : ℝ) / 64 = 39 / 64 := by
  norm_num [show (1:ℝ) = 64 / 64 by norm_num]
theorem lean_workbook_942_8 : 1 - (25 : ℝ) / 64 = 39 / 64 := by
  norm_num [Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_right]
theorem lean_workbook_942_9 : 1 - (25 : ℝ) / 64 = 39 / 64 := by
  norm_num at *
theorem lean_workbook_942_10 : 1 - (25 : ℝ) / 64 = 39 / 64 := by
  norm_num [div_eq_mul_one_div, inv_eq_one_div]
theorem lean_workbook_942_11 : 1 - (25 : ℝ) / 64 = 39 / 64 := by
  norm_num [Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left]
theorem lean_workbook_942_12 : 1 - (25 : ℝ) / 64 = 39 / 64 := by
  norm_num [div_eq_mul_inv, ← mul_sub]
theorem lean_workbook_942_13 : 1 - (25 : ℝ) / 64 = 39 / 64 := by
  norm_num [Nat.gcd]
theorem lean_workbook_942_14 : 1 - (25 : ℝ) / 64 = 39 / 64 := by
  simp only [sub_eq_add_neg, add_comm]
  norm_num [Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left]
theorem lean_workbook_942_15 : 1 - (25 : ℝ) / 64 = 39 / 64 := by
  norm_num [Nat.div_eq_of_lt]
theorem lean_workbook_942_16 : 1 - (25 : ℝ) / 64 = 39 / 64 := by
  norm_num [Int.cast_ofNat]
theorem lean_workbook_942_17 : 1 - (25 : ℝ) / 64 = 39 / 64 := by
  norm_num [Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left]
theorem lean_workbook_942_18 : 1 - (25 : ℝ) / 64 = 39 / 64 := by
  norm_num [div_eq_inv_mul]
theorem lean_workbook_942_19 : 1 - (25 : ℝ) / 64 = 39 / 64 := by
  norm_num [show (1 : ℝ) - 25 / 64 = 39 / 64 by norm_num]
theorem lean_workbook_942_20 : 1 - (25 : ℝ) / 64 = 39 / 64 := by
  norm_num [Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left]
theorem lean_workbook_942_21 : 1 - (25 : ℝ) / 64 = 39 / 64 := by
  exact by norm_num [div_eq_mul_inv, ← mul_sub]
theorem lean_workbook_942_22 : 1 - (25 : ℝ) / 64 = 39 / 64 := by
  field_simp <;> norm_num
theorem lean_workbook_942_23 : 1 - (25 : ℝ) / 64 = 39 / 64 := by
  norm_num [div_eq_mul_inv, ← mul_assoc]
theorem lean_workbook_942_24 : 1 - (25 : ℝ) / 64 = 39 / 64 := by
  rw [show (1 : ℝ) - 25 / 64 = 39 / 64 by norm_num]

theorem lean_workbook_943_0 : (1 ^ 251 * 1 * 3) % 8 = 3 := by
  norm_num [Nat.pow_zero]
theorem lean_workbook_943_1 : (1 ^ 251 * 1 * 3) % 8 = 3 := by
  congr 1
theorem lean_workbook_943_2 : (1 ^ 251 * 1 * 3) % 8 = 3 := by
  simp [Nat.ModEq]
theorem lean_workbook_943_3 : (1 ^ 251 * 1 * 3) % 8 = 3 := by
  norm_num [Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt]
theorem lean_workbook_943_4 : (1 ^ 251 * 1 * 3) % 8 = 3 := by
  simp only [one_pow, one_mul, Nat.mod_eq_of_lt]
theorem lean_workbook_943_5 : (1 ^ 251 * 1 * 3) % 8 = 3 := by
  rw [one_pow, one_mul, mul_comm]
theorem lean_workbook_943_6 : (1 ^ 251 * 1 * 3) % 8 = 3 := by
  conv => lhs; rw [← Nat.mod_add_div (1 ^ 251 * 1 * 3) 8]
theorem lean_workbook_943_7 : (1 ^ 251 * 1 * 3) % 8 = 3 := by
  norm_num [pow_one, mul_one, mul_comm]
theorem lean_workbook_943_8 : (1 ^ 251 * 1 * 3) % 8 = 3 := by
  simp [Nat.one_pow]
theorem lean_workbook_943_9 : (1 ^ 251 * 1 * 3) % 8 = 3 := by
  simp only [Nat.one_pow, Nat.mod_self]
theorem lean_workbook_943_10 : (1 ^ 251 * 1 * 3) % 8 = 3 := by
  norm_num [pow_succ, pow_mul, pow_one]
theorem lean_workbook_943_11 : (1 ^ 251 * 1 * 3) % 8 = 3 := by
  simp [ModEq]
theorem lean_workbook_943_12 : (1 ^ 251 * 1 * 3) % 8 = 3 := by
  norm_num [pow_succ, Nat.mul_mod]
theorem lean_workbook_943_13 : (1 ^ 251 * 1 * 3) % 8 = 3 := by
  simp only [Nat.mul_mod, Nat.pow_mod, Nat.mod_mod]
theorem lean_workbook_943_14 : (1 ^ 251 * 1 * 3) % 8 = 3 := by
  simp only [Nat.one_pow, Nat.mod_self, Nat.mod_eq_of_lt]
theorem lean_workbook_943_15 : (1 ^ 251 * 1 * 3) % 8 = 3 := by
  simp [Nat.pow_succ, Nat.mul_mod, Nat.add_mod]
theorem lean_workbook_943_16 : (1 ^ 251 * 1 * 3) % 8 = 3 := by
  simp [Nat.pow_mod, Nat.mul_mod, Nat.mod_mod]
theorem lean_workbook_943_17 : (1 ^ 251 * 1 * 3) % 8 = 3 := by
  norm_num [Nat.gcd_eq_gcd_ab]
theorem lean_workbook_943_18 : (1 ^ 251 * 1 * 3) % 8 = 3 := by
  norm_num [pow_succ, pow_zero]
theorem lean_workbook_943_19 : (1 ^ 251 * 1 * 3) % 8 = 3 := by
  norm_num [Nat.pow_mod]
theorem lean_workbook_943_20 : (1 ^ 251 * 1 * 3) % 8 = 3 := by
  norm_num [pow_succ, pow_zero, pow_one]

theorem lean_workbook_944_0 ∑ k in (Finset.range 10), (2^k) = 2^10 - 1 := by
  simp [Finset.sum_eq_multiset_sum]
theorem lean_workbook_944_1 ∑ k in (Finset.range 10), (2^k) = 2^10 - 1 := by
  simp [Finset.sum_range_succ]
theorem lean_workbook_944_2 ∑ k in (Finset.range 10), (2^k) = 2^10 - 1 := by
  rw [Finset.sum_eq_multiset_sum]
  congr
theorem lean_workbook_944_3 ∑ k in (Finset.range 10), (2^k) = 2^10 - 1 := by
  rw [Finset.sum_range_succ]
  simp [Finset.sum_range_succ]
theorem lean_workbook_944_4 ∑ k in (Finset.range 10), (2^k) = 2^10 - 1 := by
  rw [Finset.sum_range_succ]
  norm_num [Finset.sum_range_succ]
theorem lean_workbook_944_5 ∑ k in (Finset.range 10), (2^k) = 2^10 - 1 := by
  simp [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]
theorem lean_workbook_944_6 ∑ k in (Finset.range 10), (2^k) = 2^10 - 1 := by
  norm_num [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
theorem lean_workbook_944_7 ∑ k in (Finset.range 10), (2^k) = 2^10 - 1 := by
  aesop (add norm [Finset.sum_range_succ])
theorem lean_workbook_944_8 ∑ k in (Finset.range 10), (2^k) = 2^10 - 1 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one]
theorem lean_workbook_944_9 ∑ k in (Finset.range 10), (2^k) = 2^10 - 1 := by
  conv_lhs => rw [← Nat.mod_add_div 10 4]
theorem lean_workbook_944_10 ∑ k in (Finset.range 10), (2^k) = 2^10 - 1 := by
  refine' Eq.symm _
  simp [Finset.sum_range_succ]
theorem lean_workbook_944_11 ∑ k in (Finset.range 10), (2^k) = 2^10 - 1 := by
  norm_num [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
theorem lean_workbook_944_12 ∑ k in (Finset.range 10), (2^k) = 2^10 - 1 := by
  simp [Finset.sum_range_succ']
theorem lean_workbook_944_13 ∑ k in (Finset.range 10), (2^k) = 2^10 - 1 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_zero]
  norm_num

theorem lean_workbook_946_0 (c d : ℝ) (h₁ : c + d = 7) (h₂ : c * d = 9) : c^3 + d^3 = 154 := by
  field_simp [pow_succ]
  nlinarith [h₁, h₂]
theorem lean_workbook_946_1 (c d : ℝ) (h₁ : c + d = 7) (h₂ : c * d = 9) : c^3 + d^3 = 154 := by
  simp [h₂, h₁, pow_three]
  nlinarith
theorem lean_workbook_946_2 (c d : ℝ) (h₁ : c + d = 7) (h₂ : c * d = 9) : c^3 + d^3 = 154 := by
  simp [pow_three, h₁, h₂, sub_eq_add_neg]
  nlinarith
theorem lean_workbook_946_3 (c d : ℝ) (h₁ : c + d = 7) (h₂ : c * d = 9) : c^3 + d^3 = 154 := by
  apply Eq.symm
  simp [pow_three, h₁, h₂]
  nlinarith
theorem lean_workbook_946_4 (c d : ℝ) (h₁ : c + d = 7) (h₂ : c * d = 9) : c^3 + d^3 = 154 := by
  rw [← sub_eq_zero]
  simp [pow_three]
  nlinarith [h₁, h₂]
theorem lean_workbook_946_5 (c d : ℝ) (h₁ : c + d = 7) (h₂ : c * d = 9) : c^3 + d^3 = 154 := by
  simp [pow_three, h₁, h₂, mul_add, mul_comm, mul_left_comm]
  nlinarith
theorem lean_workbook_946_6 (c d : ℝ) (h₁ : c + d = 7) (h₂ : c * d = 9) : c^3 + d^3 = 154 := by
  simp [pow_three, h₁, h₂, sub_eq_add_neg, add_comm]
  nlinarith
theorem lean_workbook_946_7 (c d : ℝ) (h₁ : c + d = 7) (h₂ : c * d = 9) : c^3 + d^3 = 154 := by
  rw [← add_comm]
  simp [pow_three, h₁, h₂, mul_comm, mul_assoc, mul_left_comm]
  nlinarith
theorem lean_workbook_946_8 (c d : ℝ) (h₁ : c + d = 7) (h₂ : c * d = 9) : c^3 + d^3 = 154 := by
  simp [pow_three, h₁, h₂]
  nlinarith
theorem lean_workbook_946_9 (c d : ℝ) (h₁ : c + d = 7) (h₂ : c * d = 9) : c^3 + d^3 = 154 := by
  field_simp [pow_three, h₁, h₂, add_comm]
  nlinarith [h₁, h₂]
theorem lean_workbook_946_10 (c d : ℝ) (h₁ : c + d = 7) (h₂ : c * d = 9) : c^3 + d^3 = 154 := by
  rw [pow_three, pow_three]
  nlinarith [h₁, h₂]
theorem lean_workbook_946_11 (c d : ℝ) (h₁ : c + d = 7) (h₂ : c * d = 9) : c^3 + d^3 = 154 := by
  simp [pow_three]
  nlinarith [h₁, h₂]
theorem lean_workbook_946_12 (c d : ℝ) (h₁ : c + d = 7) (h₂ : c * d = 9) : c^3 + d^3 = 154 := by
  simp only [pow_three, h₁, h₂]
  nlinarith
theorem lean_workbook_946_13 (c d : ℝ) (h₁ : c + d = 7) (h₂ : c * d = 9) : c^3 + d^3 = 154 := by
  simp [pow_three, h₁, h₂, sub_mul, mul_sub, add_mul, mul_add, add_comm, add_left_comm, add_assoc]
  nlinarith
theorem lean_workbook_946_14 (c d : ℝ) (h₁ : c + d = 7) (h₂ : c * d = 9) : c^3 + d^3 = 154 := by
  simp [pow_three, h₁, h₂, sub_mul, mul_sub, sub_add, add_sub, sub_sub, sub_eq_add_neg]
  nlinarith [h₁, h₂]
theorem lean_workbook_946_15 (c d : ℝ) (h₁ : c + d = 7) (h₂ : c * d = 9) : c^3 + d^3 = 154 := by
  field_simp [pow_succ]
  nlinarith
theorem lean_workbook_946_16 (c d : ℝ) (h₁ : c + d = 7) (h₂ : c * d = 9) : c^3 + d^3 = 154 := by
  simp only [pow_three]
  nlinarith [h₁, h₂]
theorem lean_workbook_946_17 (c d : ℝ) (h₁ : c + d = 7) (h₂ : c * d = 9) : c^3 + d^3 = 154 := by
  simp [pow_three, h₁, h₂, mul_comm, mul_assoc, mul_left_comm]
  nlinarith
theorem lean_workbook_946_18 (c d : ℝ) (h₁ : c + d = 7) (h₂ : c * d = 9) : c^3 + d^3 = 154 := by
  simp [h₁, h₂, pow_three]
  nlinarith

theorem lean_workbook_952_0 (a : ℝ) : sin (a / 2) * (sin (a / 2) - 1) ≥ -1 / 4 := by
  rw [mul_comm]
  have := sq_nonneg (sin (a / 2) - 1 / 2)
  nlinarith [sq_nonneg (sin (a / 2) - 1 / 2)]
theorem lean_workbook_952_1 (a : ℝ) : sin (a / 2) * (sin (a / 2) - 1) ≥ -1 / 4 := by
  have := sq_nonneg (sin (a / 2) - 1 / 2)
  have := sq_nonneg (sin (a / 2))
  nlinarith
theorem lean_workbook_952_2 (a : ℝ) : sin (a / 2) * (sin (a / 2) - 1) ≥ -1 / 4 := by
  have h : 0 ≤ (sin (a / 2) - 1 / 2) ^ 2 := sq_nonneg _
  linarith [h]
theorem lean_workbook_952_3 (a : ℝ) : sin (a / 2) * (sin (a / 2) - 1) ≥ -1 / 4 := by
  have := sq_nonneg (2 * sin (a / 2) - 1)
  linarith [sin_sq_add_cos_sq (a / 2)]
theorem lean_workbook_952_4 (a : ℝ) : sin (a / 2) * (sin (a / 2) - 1) ≥ -1 / 4 := by
  rw [mul_comm]
  have := sq_nonneg (sin (a / 2) - 1 / 2)
  linarith [sin_sq_add_cos_sq (a / 2)]
theorem lean_workbook_952_5 (a : ℝ) : sin (a / 2) * (sin (a / 2) - 1) ≥ -1 / 4 := by
  have := sq_nonneg (sin (a / 2) - 1 / 2)
  have := sq_nonneg (sin (a / 2))
  linarith

theorem lean_workbook_953_0 : ∀ x y : ℝ, Real.sqrt ((x + 2) ^ 2 + (y + 2) ^ 2) ≥ (x + 2 + y + 2) / Real.sqrt 2 := by
  refine' fun x y => _
  rw [add_comm]
  have h1 : 0 ≤ (x + 2 - (y + 2)) ^ 2 := sq_nonneg _
  apply le_sqrt_of_sq_le
  field_simp
  linarith [h1]
theorem lean_workbook_953_1 : ∀ x y : ℝ, Real.sqrt ((x + 2) ^ 2 + (y + 2) ^ 2) ≥ (x + 2 + y + 2) / Real.sqrt 2 := by
  intro x y
  have h : 0 ≤ (x + 2 - y - 2) ^ 2 := sq_nonneg (x + 2 - y - 2)
  apply le_sqrt_of_sq_le
  field_simp [add_comm]
  ring_nf
  nlinarith
theorem lean_workbook_953_2 : ∀ x y : ℝ, Real.sqrt ((x + 2) ^ 2 + (y + 2) ^ 2) ≥ (x + 2 + y + 2) / Real.sqrt 2 := by
  refine' fun x y => _
  rw [add_comm]
  have h1 : 0 ≤ (x + 2 - y - 2) ^ 2 := sq_nonneg _
  apply le_sqrt_of_sq_le
  field_simp [add_comm]
  linarith
theorem lean_workbook_953_3 : ∀ x y : ℝ, Real.sqrt ((x + 2) ^ 2 + (y + 2) ^ 2) ≥ (x + 2 + y + 2) / Real.sqrt 2 := by
  rintro x y
  have h : 0 ≤ (x + 2 - y - 2) ^ 2 := sq_nonneg _
  apply le_sqrt_of_sq_le
  field_simp [add_comm]
  ring_nf
  nlinarith
theorem lean_workbook_953_4 : ∀ x y : ℝ, Real.sqrt ((x + 2) ^ 2 + (y + 2) ^ 2) ≥ (x + 2 + y + 2) / Real.sqrt 2 := by
  intro x y
  have h1 : 0 ≤ (x + 2 - y - 2) ^ 2 := sq_nonneg (x + 2 - y - 2)
  apply le_sqrt_of_sq_le
  field_simp [add_comm]
  ring_nf
  nlinarith
theorem lean_workbook_953_5 : ∀ x y : ℝ, Real.sqrt ((x + 2) ^ 2 + (y + 2) ^ 2) ≥ (x + 2 + y + 2) / Real.sqrt 2 := by
  intros x y
  have h1 : 0 ≤ (x + 2 - y - 2) ^ 2 := sq_nonneg _
  apply le_sqrt_of_sq_le
  field_simp [add_comm]
  linarith
theorem lean_workbook_953_6 : ∀ x y : ℝ, Real.sqrt ((x + 2) ^ 2 + (y + 2) ^ 2) ≥ (x + 2 + y + 2) / Real.sqrt 2 := by
  rintro a b
  have h1 : 0 ≤ (a + 2 - (b + 2)) ^ 2 := sq_nonneg _
  apply le_sqrt_of_sq_le
  field_simp
  linarith
theorem lean_workbook_953_7 : ∀ x y : ℝ, Real.sqrt ((x + 2) ^ 2 + (y + 2) ^ 2) ≥ (x + 2 + y + 2) / Real.sqrt 2 := by
  intro x y
  have h2 : 0 ≤ (x + 2 - (y + 2)) ^ 2 := sq_nonneg _
  apply le_sqrt_of_sq_le
  field_simp
  linarith
theorem lean_workbook_953_8 : ∀ x y : ℝ, Real.sqrt ((x + 2) ^ 2 + (y + 2) ^ 2) ≥ (x + 2 + y + 2) / Real.sqrt 2 := by
  intro X Y
  have h1 : 0 ≤ (X + 2 - (Y + 2)) ^ 2 := sq_nonneg _
  apply le_sqrt_of_sq_le
  field_simp
  linarith
theorem lean_workbook_953_9 : ∀ x y : ℝ, Real.sqrt ((x + 2) ^ 2 + (y + 2) ^ 2) ≥ (x + 2 + y + 2) / Real.sqrt 2 := by
  intro x y
  have := sq_nonneg (x + 2 - (y + 2))
  apply le_sqrt_of_sq_le
  field_simp
  linarith
theorem lean_workbook_953_10 : ∀ x y : ℝ, Real.sqrt ((x + 2) ^ 2 + (y + 2) ^ 2) ≥ (x + 2 + y + 2) / Real.sqrt 2 := by
  intros x y
  have h1 : 0 ≤ (x + 2 - y - 2) ^ 2 := sq_nonneg _
  apply le_sqrt_of_sq_le
  field_simp [add_comm]
  ring_nf
  nlinarith
theorem lean_workbook_953_11 : ∀ x y : ℝ, Real.sqrt ((x + 2) ^ 2 + (y + 2) ^ 2) ≥ (x + 2 + y + 2) / Real.sqrt 2 := by
  rintro x y
  have h1 : 0 ≤ (x + 2 - (y + 2)) ^ 2 := sq_nonneg _
  apply le_sqrt_of_sq_le
  field_simp
  linarith

theorem lean_workbook_954_0 (x y z : ℝ) (h : x*y^2 + y*z^2 + z*x^2 = 3) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + 7)^(1/3) + (y + 7)^(1/3) + (z + 7)^(1/3) ≤ 6 := by
  ring_nf
  norm_num [hx, hy, hz, h]
theorem lean_workbook_954_1 (x y z : ℝ) (h : x*y^2 + y*z^2 + z*x^2 = 3) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + 7)^(1/3) + (y + 7)^(1/3) + (z + 7)^(1/3) ≤ 6 := by
  simp [hx, hy, hz]
  nlinarith [h, hx, hy, hz]
theorem lean_workbook_954_2 (x y z : ℝ) (h : x*y^2 + y*z^2 + z*x^2 = 3) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + 7)^(1/3) + (y + 7)^(1/3) + (z + 7)^(1/3) ≤ 6 := by
  norm_num at h hx hy hz ⊢
theorem lean_workbook_954_3 (x y z : ℝ) (h : x*y^2 + y*z^2 + z*x^2 = 3) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + 7)^(1/3) + (y + 7)^(1/3) + (z + 7)^(1/3) ≤ 6 := by
  simp [← le_sub_iff_add_le]
  norm_num [h, hx, hy, hz]
theorem lean_workbook_954_4 (x y z : ℝ) (h : x*y^2 + y*z^2 + z*x^2 = 3) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + 7)^(1/3) + (y + 7)^(1/3) + (z + 7)^(1/3) ≤ 6 := by
  simp [add_comm] at *
  nlinarith [h, hx, hy, hz]
theorem lean_workbook_954_5 (x y z : ℝ) (h : x*y^2 + y*z^2 + z*x^2 = 3) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + 7)^(1/3) + (y + 7)^(1/3) + (z + 7)^(1/3) ≤ 6 := by
  eta_reduce at *
  eta_reduce at h hx hy hz ⊢
  contrapose! h
  contrapose! h
  ring_nf
  nlinarith
theorem lean_workbook_954_6 (x y z : ℝ) (h : x*y^2 + y*z^2 + z*x^2 = 3) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + 7)^(1/3) + (y + 7)^(1/3) + (z + 7)^(1/3) ≤ 6 := by
  simp [← h] at *
  nlinarith
theorem lean_workbook_954_7 (x y z : ℝ) (h : x*y^2 + y*z^2 + z*x^2 = 3) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + 7)^(1/3) + (y + 7)^(1/3) + (z + 7)^(1/3) ≤ 6 := by
  simp [add_comm]
  nlinarith [hx, hy, hz, h]
theorem lean_workbook_954_8 (x y z : ℝ) (h : x*y^2 + y*z^2 + z*x^2 = 3) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + 7)^(1/3) + (y + 7)^(1/3) + (z + 7)^(1/3) ≤ 6 := by
  norm_num [pow_nonneg, hx.le, hy.le, hz.le, h]
theorem lean_workbook_954_9 (x y z : ℝ) (h : x*y^2 + y*z^2 + z*x^2 = 3) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + 7)^(1/3) + (y + 7)^(1/3) + (z + 7)^(1/3) ≤ 6 := by
  ring_nf
  nlinarith [h, hx, hy, hz]
theorem lean_workbook_954_10 (x y z : ℝ) (h : x*y^2 + y*z^2 + z*x^2 = 3) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + 7)^(1/3) + (y + 7)^(1/3) + (z + 7)^(1/3) ≤ 6 := by
  ring_nf at h
  norm_num [h, hx, hy, hz]
theorem lean_workbook_954_11 (x y z : ℝ) (h : x*y^2 + y*z^2 + z*x^2 = 3) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + 7)^(1/3) + (y + 7)^(1/3) + (z + 7)^(1/3) ≤ 6 := by
  norm_num [pow_one, hx, hy, hz, h]
theorem lean_workbook_954_12 (x y z : ℝ) (h : x*y^2 + y*z^2 + z*x^2 = 3) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + 7)^(1/3) + (y + 7)^(1/3) + (z + 7)^(1/3) ≤ 6 := by
  refine' le_of_sub_nonneg _
  simp only [sub_nonneg]
  norm_num1
  nlinarith [h, hx, hy, hz]
theorem lean_workbook_954_13 (x y z : ℝ) (h : x*y^2 + y*z^2 + z*x^2 = 3) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + 7)^(1/3) + (y + 7)^(1/3) + (z + 7)^(1/3) ≤ 6 := by
  simp [pow_one] at *
  linarith [h, hx, hy, hz]
theorem lean_workbook_954_14 (x y z : ℝ) (h : x*y^2 + y*z^2 + z*x^2 = 3) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + 7)^(1/3) + (y + 7)^(1/3) + (z + 7)^(1/3) ≤ 6 := by
  norm_num at hx hy hz h ⊢

theorem lean_workbook_978_0 (x y z : ℝ) (h : x + y + z = 3) : x * y + x * z + y * z ≤ 3 := by
  have := sq_nonneg (x - y)
  have := sq_nonneg (x - z)
  have := sq_nonneg (y - z)
  nlinarith [h]
theorem lean_workbook_978_1 (x y z : ℝ) (h : x + y + z = 3) : x * y + x * z + y * z ≤ 3 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]
theorem lean_workbook_978_2 (x y z : ℝ) (h : x + y + z = 3) : x * y + x * z + y * z ≤ 3 := by
  have h2 : 0 ≤ (x - y)^2 + (x - z)^2 + (y - z)^2 := by positivity
  nlinarith [h, h2]
theorem lean_workbook_978_3 (x y z : ℝ) (h : x + y + z = 3) : x * y + x * z + y * z ≤ 3 := by
  apply le_of_sub_nonneg
  ring_nf
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
theorem lean_workbook_978_4 (x y z : ℝ) (h : x + y + z = 3) : x * y + x * z + y * z ≤ 3 := by
  rw [← h]
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
theorem lean_workbook_978_5 (x y z : ℝ) (h : x + y + z = 3) : x * y + x * z + y * z ≤ 3 := by
  apply le_of_sub_nonneg
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
theorem lean_workbook_978_6 (x y z : ℝ) (h : x + y + z = 3) : x * y + x * z + y * z ≤ 3 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
theorem lean_workbook_978_7 (x y z : ℝ) (h : x + y + z = 3) : x * y + x * z + y * z ≤ 3 := by
  have t := sq_nonneg (x - y)
  have u := sq_nonneg (y - z)
  have v := sq_nonneg (z - x)
  nlinarith
theorem lean_workbook_978_8 (x y z : ℝ) (h : x + y + z = 3) : x * y + x * z + y * z ≤ 3 := by
  have h2 := sq_nonneg (x - y)
  have h3 := sq_nonneg (y - z)
  have h4 := sq_nonneg (z - x)
  nlinarith
theorem lean_workbook_978_9 (x y z : ℝ) (h : x + y + z = 3) : x * y + x * z + y * z ≤ 3 := by
  have : 0 ≤ (x - y)^2 + (x - z)^2 + (y - z)^2 := by positivity
  nlinarith [h]
theorem lean_workbook_978_10 (x y z : ℝ) (h : x + y + z = 3) : x * y + x * z + y * z ≤ 3 := by
  have h2 := sq_nonneg (x - y)
  have h3 := sq_nonneg (x - z)
  have h4 := sq_nonneg (y - z)
  nlinarith
theorem lean_workbook_978_11 (x y z : ℝ) (h : x + y + z = 3) : x * y + x * z + y * z ≤ 3 := by
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
theorem lean_workbook_978_12 (x y z : ℝ) (h : x + y + z = 3) : x * y + x * z + y * z ≤ 3 := by
  nlinarith [h, sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
theorem lean_workbook_978_13 (x y z : ℝ) (h : x + y + z = 3) : x * y + x * z + y * z ≤ 3 := by
  have h1 := sq_nonneg (x - y)
  have h2 := sq_nonneg (x - z)
  have h3 := sq_nonneg (y - z)
  nlinarith

theorem lean_workbook_982_0 (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z := by
  have := sq_nonneg (x - y + z)
  linarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
theorem lean_workbook_982_1 (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z := by
  simp only [sq, sub_nonneg]
  linarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
theorem lean_workbook_982_2 (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z := by
  simp [sq, mul_comm, mul_assoc, mul_left_comm]
  linarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
theorem lean_workbook_982_3 (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z := by
  ring_nf
  have h1 := sq_nonneg (x - y)
  have h2 := sq_nonneg (x - z)
  have h3 := sq_nonneg (y - z)
  linarith
theorem lean_workbook_982_4 (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z := by
  ring_nf
  have h1 : 0 ≤ (x - y) ^ 2 + (x - z) ^ 2 + (y - z) ^ 2 := by positivity
  linarith
theorem lean_workbook_982_5 (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z := by
  ring_nf
  ring_nf
  linarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
theorem lean_workbook_982_6 (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z := by
  have h0 := sq_nonneg (x - y)
  have h1 := sq_nonneg (y - z)
  have h2 := sq_nonneg (z - x)
  linarith
theorem lean_workbook_982_7 (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z := by
  have h1 : 0 ≤ (x - y)^2 + (x - z)^2 + (y - z)^2 := by nlinarith
  simp at h1
  linarith
theorem lean_workbook_982_8 (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z := by
  simp [sq]
  linarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
theorem lean_workbook_982_9 (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z := by
  simp [sq, sub_eq_add_neg, add_assoc]
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
theorem lean_workbook_982_10 (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z := by
  simp [sq, mul_comm, mul_assoc, mul_left_comm]
  linarith only [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
theorem lean_workbook_982_11 (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z := by
  have h1 := sq_nonneg (x - y)
  have h2 := sq_nonneg (y - z)
  have h3 := sq_nonneg (z - x)
  linarith
theorem lean_workbook_982_12 (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z := by
  have t := mul_self_nonneg (x - y)
  have t2 := mul_self_nonneg (x - z)
  have t3 := mul_self_nonneg (y - z)
  linarith
theorem lean_workbook_982_13 (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z := by
  simp only [sq]
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
theorem lean_workbook_982_14 (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z := by
  linarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
theorem lean_workbook_982_15 (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z := by
  rw [sq]
  rw [sq]
  rw [sq]
  linarith [mul_self_nonneg (x - y), mul_self_nonneg (x - z), mul_self_nonneg (y - z)]
theorem lean_workbook_982_16 (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z := by
  ring_nf
  have := sq_nonneg (x - y)
  have := sq_nonneg (x - z)
  have := sq_nonneg (y - z)
  linarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
theorem lean_workbook_982_17 (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z := by
  have h1 : 0 ≤ (x - y)^2 + (x - z)^2 + (y - z)^2 := by positivity
  linarith
theorem lean_workbook_982_18 (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z := by
  simp [sq]
  linarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_982_19 (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z := by
  have := sq_nonneg (x - y + z)
  linarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_982_20 (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z := by
  rw [sq, sq, sq]
  have := sq_nonneg (x - y)
  have := sq_nonneg (x - z)
  have := sq_nonneg (y - z)
  linarith
theorem lean_workbook_982_21 (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z := by
  simp [sq]
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
theorem lean_workbook_982_22 (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z := by
  simp [sq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_comm, mul_assoc, mul_left_comm]
  linarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
theorem lean_workbook_982_23 (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z := by
  linarith only [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]

theorem lean_workbook_987_0 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  constructor
  linarith [h1.1, h1.2.2.2, h2.2.2.2]
  constructor
  linarith [h1.1, h1.2.2.1, h2.2.2.1]
  constructor
  linarith [h1.1, h1.2.1, h2.2.1]
  constructor
  linarith [h1.1, h1.2.1, h2.1]
  linarith [h1.1, h2.1]
theorem lean_workbook_987_1 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  constructor
  linarith [h1.2.2.1, h1.2.2.2, h2.2.1]
  constructor
  linarith [h1.2.2.1, h1.2.2.2, h2.2.1]
  constructor
  linarith [h1.2.2.1, h1.2.2.2, h2.2.1]
  constructor
  linarith [h1.2.2.1, h1.2.2.2, h2.2.1]
  linarith [h1.2.2.1, h1.2.2.2, h2.2.1]
theorem lean_workbook_987_2 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  exact ⟨by linarith [h1.2.2.1, h2.2.2.2], by linarith [h1.2.1, h2.2.1], by linarith [h1.1, h2.1], by linarith [h1.1, h2.1], by linarith [h1.1, h2.1]⟩
theorem lean_workbook_987_3 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  constructor
  linarith [h1.2.2.1, h1.2.2.2, h2.2.1]
  constructor
  linarith [h1.2.2.1, h1.2.2.2, h2.2.1]
  constructor
  linarith [h1.2.2.1, h1.2.2.2, h2.2.1]
  constructor
  linarith [h1.2.2.1, h1.2.2.2, h2.2.1]
  linarith [h1.1, h1.2.1, h2.1]
theorem lean_workbook_987_4 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  refine' ⟨_, _, _, _, _⟩
  linarith [h1.2.2.1, h2.2.1]
  linarith [h1.2.2.1, h2.1]
  linarith [h1.1, h1.2.2.1, h2.2.2]
  linarith [h1.1, h1.2.1, h2.1]
  linarith [h1.1, h1.2.1, h2.2.2]
theorem lean_workbook_987_5 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  apply And.intro
  linarith [h2.2.2]
  apply And.intro
  linarith [h2.2.1]
  apply And.intro
  linarith [h2.1]
  apply And.intro
  linarith [h2.1, h1.2.2]
  linarith [h1.2.2]
theorem lean_workbook_987_6 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  exact ⟨by linarith [h2.2.2.1], by linarith [h2.2.1], by linarith [h2.1], by linarith [h1.2.2.1], by linarith [h1.2.1]⟩
theorem lean_workbook_987_7 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  refine' ⟨by linarith [h1.2.2.1], by linarith [h1.2.2.2], by linarith [h1.2.1], by linarith [h1.1], by linarith [h1.2.1]⟩
theorem lean_workbook_987_8 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  constructor
  linarith [h2.2.2.1]
  constructor
  linarith [h2.2.2.1]
  constructor
  linarith [h2.2.1]
  constructor
  linarith [h2.1]
  linarith [h1.1, h1.2.1, h1.2.2.1]
theorem lean_workbook_987_9 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  constructor
  linarith [h2.2.2]
  constructor
  linarith [h2.2.2]
  constructor
  linarith [h2.2.2]
  constructor
  linarith [h2.2.2]
  linarith [h2.2.2]
theorem lean_workbook_987_10 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  linarith
  linarith
  linarith
  linarith
  linarith
theorem lean_workbook_987_11 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  repeat' apply And.intro
  all_goals linarith [h1, h2]
theorem lean_workbook_987_12 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  rw [add_comm a b]
  constructor
  linarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2]
  constructor
  linarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2]
  constructor
  linarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2]
  constructor
  linarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2]
  linarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2]
theorem lean_workbook_987_13 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  refine' ⟨_, _, _, _, _⟩
  linarith [h1.2.2.1, h2.2.1]
  linarith [h1.2.2.1, h2.1]
  linarith [h1.1, h1.2.2.1, h2.2.2.1]
  linarith [h1.1, h1.2.1, h2.2.2.1]
  linarith [h1.1, h1.2.1, h2.1]
theorem lean_workbook_987_14 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  refine' ⟨_, _, _, _, _⟩
  linarith [h1.2.2.1, h1.2.2.2]
  linarith [h1.2.2.1, h2.2.1]
  linarith [h1.2.1, h2.1]
  linarith [h1.1, h2.1]
  linarith [h1.1, h1.2.1]
theorem lean_workbook_987_15 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  constructor
  linarith
  constructor
  linarith
  constructor
  linarith
  constructor
  linarith
  linarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2]
theorem lean_workbook_987_16 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  refine' ⟨by linarith [h1.2.2.1, h2.2.1], by linarith [h1.2.2.1, h2.1], by linarith [h1.1, h1.2.2.1, h2.1], by linarith [h1.1, h1.2.1, h2.1], by linarith [h1.1, h1.2.1, h2.2.2.1]⟩
theorem lean_workbook_987_17 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  constructor
  linarith [h1.1, h1.2.2.1, h2.2.1]
  constructor
  linarith [h1.1, h1.2.2.1, h2.2.1]
  constructor
  linarith [h1.1, h1.2.2.1, h2.2.1]
  constructor
  linarith [h1.1, h1.2.2.1, h2.2.1]
  linarith [h1.1, h1.2.2.1, h2.2.1]
theorem lean_workbook_987_18 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  refine' ⟨by linarith [h1.1, h1.2.2.2], by linarith [h1.1, h1.2.2.1], by linarith [h1.1, h1.2.1], by linarith [h1.1, h1.2.2.2], by linarith [h1.1, h1.2.1]⟩
theorem lean_workbook_987_19 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  refine' ⟨_, _, _, _, _⟩
  linarith
  linarith
  linarith
  linarith
  linarith
theorem lean_workbook_987_20 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  refine' ⟨_, _, _, _, _⟩
  linarith [h1.2.1, h2.2.1]
  linarith [h1.2.1, h2.2.2]
  linarith [h1.1, h1.2.1, h2.1, h2.2.1]
  linarith [h1.1, h1.2.1, h2.1, h2.2.2]
  linarith [h1.1, h1.2.1, h2.1, h2.2.1]
theorem lean_workbook_987_21 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  rw [add_comm d e, add_comm c e, add_comm d b, add_comm a c, add_comm a b]
  constructor
  linarith [h2.2.2.2]
  constructor
  linarith [h2.2.2.1]
  constructor
  linarith [h2.1]
  constructor
  linarith [h2.1]
  linarith [h1.1]
theorem lean_workbook_987_22 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  refine' ⟨_, _, _, _, _⟩ <;> linarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2]
theorem lean_workbook_987_23 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  refine ⟨by linarith [h2.2.2], by linarith [h2.2.1], by linarith [h2.1], by linarith [h1.1], by linarith [h1.1]⟩
theorem lean_workbook_987_24 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  refine' ⟨_, _, _, _, _⟩
  all_goals linarith [h1, h2]
theorem lean_workbook_987_25 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  refine' ⟨by linarith [h1.2.2.1, h2.2.1], by linarith [h1.2.2.1, h2.1], by linarith [h1.1, h2.1], by linarith [h1.1, h2.2.2.1], by linarith [h1.1, h2.2.2.2]⟩
theorem lean_workbook_987_26 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  refine' ⟨_, _, _, _, _⟩
  linarith [h1.2.2.1, h1.2.2.2, h2.2.1]
  linarith [h1.2.2.1, h1.2.2.2, h2.1, h2.2.1]
  linarith [h1.1, h1.2.1, h2.1, h2.2.1]
  linarith [h1.1, h1.2.1, h2.1]
  linarith [h1.1, h1.2.1, h2.2.2.1, h2.2.2.2]
theorem lean_workbook_987_27 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  refine ⟨by linarith [h1.2.2.1, h1.2.2.2], by linarith [h1.2.1, h1.2.2.2], by linarith [h1.1, h1.2.2.1, h2.1], by linarith [h1.1, h2.2.1], by linarith [h1.1, h1.2.1, h2.1]⟩
theorem lean_workbook_987_28 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  constructor
  linarith [h2.2.2.1]
  constructor
  linarith [h2.2.1]
  constructor
  linarith [h2.1]
  constructor
  linarith [h1.1, h1.2.1]
  linarith [h1.1, h1.2.2.2]
theorem lean_workbook_987_29 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  constructor
  linarith [h1.1, h1.2.2.2]
  constructor
  linarith [h1.1, h1.2.2.2]
  constructor
  linarith [h1.1, h1.2.2.2]
  constructor
  linarith [h1.1, h1.2.2.2]
  linarith [h1.1, h1.2.2.2]
theorem lean_workbook_987_30 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  constructor
  linarith [h2.2.2]
  constructor
  linarith [h2.2.1]
  constructor
  linarith [h2.1]
  constructor
  linarith [h2.1, h1.1]
  linarith [h1.1, h1.2.1]
theorem lean_workbook_987_31 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  constructor
  linarith [h1.2.2.2]
  constructor
  linarith [h1.2.2.2]
  constructor
  linarith [h1.2.2.2]
  constructor
  linarith [h1.1, h2.1]
  linarith [h1.1, h2.2.1]
theorem lean_workbook_987_32 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  refine' ⟨_, _, _, _, _⟩
  linarith [h1.2.2.1, h1.2.2.2, h2.2.1, h2.2.2]
  linarith [h1.2.2.1, h1.2.2.2, h2.1, h2.2.1]
  linarith [h1.2.2.1, h1.2.2.2, h2.1, h2.2.2]
  linarith [h1.1, h1.2.2.1, h2.1, h2.2.1]
  linarith [h1.1, h1.2.2.1, h2.1, h2.2.2]
theorem lean_workbook_987_33 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  exact ⟨by linarith [h1.2.2.2], by linarith [h1.2.2.2], by linarith [h1.2.2.2], by linarith [h1.2.2.2], by linarith [h1.2.2.2]⟩
theorem lean_workbook_987_34 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  constructor
  linarith [h1.2.2.2, h2.2.2]
  constructor
  linarith [h1.2.2.2, h2.2.1]
  constructor
  linarith [h1.2.2.1, h2.1]
  constructor
  linarith [h1.2.1, h2.1]
  linarith [h1.1, h2.1]
theorem lean_workbook_987_35 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  constructor
  linarith [h1.2.2.1, h1.2.2.2, h2.2.1, h2.2.2]
  constructor
  linarith [h1.2.2.1, h1.2.2.2, h2.1, h2.2.1]
  constructor
  linarith [h1.1, h1.2.2.1, h2.1, h2.2.2]
  constructor
  linarith [h1.1, h1.2.1, h2.1]
  linarith [h1.1, h1.2.1, h2.2.2]
theorem lean_workbook_987_36 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  constructor
  linarith [h2.2.1, h2.2.2]
  constructor
  linarith [h2.2.1, h2.2.2]
  constructor
  linarith [h2.1, h2.2.1]
  constructor
  linarith [h2.1, h2.2.1]
  linarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1]
theorem lean_workbook_987_37 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  constructor
  linarith [h1.2.2.1, h1.2.2.2]
  constructor
  linarith [h1.2.2.1, h1.2.2.2]
  constructor
  linarith [h1.2.2.1, h1.2.2.2]
  constructor
  linarith [h1.2.2.1, h1.2.2.2]
  linarith [h1.2.2.1, h1.2.2.2]
theorem lean_workbook_987_38 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  refine' ⟨by linarith [h2.2.2], by linarith [h2.2.1], by linarith [h2.1], by linarith [h1.1, h2.1], by linarith [h1.1, h2.2.1]⟩
theorem lean_workbook_987_39 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  constructor
  linarith [h1.2.2.1, h2.2.1]
  constructor
  linarith [h1.2.2.1, h2.2.1]
  constructor
  linarith [h1.1, h2.1]
  constructor
  linarith [h1.1, h2.1]
  linarith [h1.1, h2.1]
theorem lean_workbook_987_40 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  constructor
  linarith [h1.2.2.1]
  constructor
  linarith [h1.2.2.1, h2.2.1]
  constructor
  linarith [h1.1, h1.2.2.1, h2.1, h2.2.1]
  constructor
  linarith [h1.1, h1.2.1]
  linarith [h1.1, h1.2.1, h2.1]
theorem lean_workbook_987_41 {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  constructor
  linarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2]
  constructor
  linarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2]
  constructor
  linarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2]
  constructor
  linarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2]
  linarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2]

theorem lean_workbook_1001_0 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  linear_combination (a^2 + b^2) * (c^2 + d^2) - (a * d - b * c)^2 - (a * c + b * d)^2
theorem lean_workbook_1001_1 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  simp only [mul_add, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_1001_2 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  field_simp [pow_two, mul_add, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_1001_3 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  rw [mul_add, add_mul, add_mul]
  ring_nf
theorem lean_workbook_1001_4 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  simp [sq, mul_add, mul_comm, mul_left_comm, add_mul, add_comm, add_left_comm]
  ring
theorem lean_workbook_1001_5 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  rw [sq, sq]
  ring_nf
theorem lean_workbook_1001_6 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  norm_num [sq, add_mul, mul_add]
  ring
theorem lean_workbook_1001_7 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  linear_combination (a^2 + b^2) * (c^2 + d^2) - ((a * d - b * c)^2 + (a * c + b * d)^2)
theorem lean_workbook_1001_8 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  simp [add_mul, mul_add, mul_pow, sub_mul, mul_sub]
  ring
theorem lean_workbook_1001_9 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  simp [pow_two, add_mul, mul_add]
  ring
theorem lean_workbook_1001_10 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  simp [mul_add, add_mul, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_1001_11 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  repeat rw [sq, mul_add, mul_comm, mul_left_comm, add_mul, add_comm, add_left_comm]
  ring
theorem lean_workbook_1001_12 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  simp [mul_add, mul_comm, mul_left_comm, pow_two]
  ring
theorem lean_workbook_1001_13 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  simp only [sq, add_mul, mul_add, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_1001_14 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  field_simp [pow_two]
  ring_nf
theorem lean_workbook_1001_15 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  simp only [sq]
  ring_nf
theorem lean_workbook_1001_16 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  simp [mul_add, mul_comm, mul_left_comm, sq, add_assoc, add_comm, add_left_comm]
  ring
theorem lean_workbook_1001_17 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  field_simp [mul_add, add_mul]
  ring
theorem lean_workbook_1001_18 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  simp [pow_two, mul_add, mul_comm, mul_left_comm, add_mul, add_comm, add_left_comm]
  ring
theorem lean_workbook_1001_19 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  rw [pow_two, pow_two]
  ring
theorem lean_workbook_1001_20 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  simp only [sq, mul_add, add_mul, mul_sub, sub_mul]
  ring
theorem lean_workbook_1001_21 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  simp [sq, mul_add, add_mul, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_1001_22 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  simp [sq, add_mul, mul_add, add_assoc, add_left_comm, mul_comm, mul_assoc]
  ring
theorem lean_workbook_1001_23 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  simp [sub_sq, add_sq, mul_add, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_1001_24 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  simp only [sq, add_mul, mul_add, mul_comm, mul_left_comm, add_assoc, add_left_comm]
  ring
theorem lean_workbook_1001_25 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  simp [mul_add, add_mul, mul_comm, mul_left_comm, sq]
  ring
theorem lean_workbook_1001_26 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  simp [sq]
  ring
theorem lean_workbook_1001_27 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  simp [mul_add, mul_comm, mul_left_comm, pow_two, add_assoc, add_comm, add_left_comm]
  ring
theorem lean_workbook_1001_28 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  simp [sq, add_mul, mul_add, mul_comm, mul_assoc, mul_left_comm]
  ring
theorem lean_workbook_1001_29 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  rw [add_mul, mul_add, mul_add, add_comm]
  ring
theorem lean_workbook_1001_30 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  simp [sq, ← sub_eq_add_neg, ← add_assoc]
  ring
theorem lean_workbook_1001_31 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  repeat' rw [sq, add_mul, mul_add, add_assoc, mul_comm, mul_assoc, mul_comm d]
  ring
theorem lean_workbook_1001_32 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  repeat rw [sq]; ring
theorem lean_workbook_1001_33 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  simp [add_mul, mul_add, mul_comm, mul_left_comm]
  ring_nf
theorem lean_workbook_1001_34 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  field_simp [pow_two]
  ring

theorem lean_workbook_1002_0 (y : ℝ) (hy : -1 / 2 < y ∧ y < 0) : |y| > |2*y^2| := by
  simp [abs_of_neg hy.2, abs_of_pos (mul_pos two_pos (sq_pos_of_neg hy.2))]
  nlinarith
theorem lean_workbook_1002_1 (y : ℝ) (hy : -1 / 2 < y ∧ y < 0) : |y| > |2*y^2| := by
  simp only [abs_of_neg hy.2, abs_of_pos (mul_pos two_pos (sq_pos_of_neg hy.2))]
  nlinarith
theorem lean_workbook_1002_2 (y : ℝ) (hy : -1 / 2 < y ∧ y < 0) : |y| > |2*y^2| := by
  rw [abs_of_neg hy.2, abs_of_pos (mul_pos zero_lt_two (sq_pos_of_neg hy.2))]
  nlinarith
theorem lean_workbook_1002_3 (y : ℝ) (hy : -1 / 2 < y ∧ y < 0) : |y| > |2*y^2| := by
  rw [abs_of_neg hy.2, abs_of_pos (mul_pos two_pos (sq_pos_of_neg hy.2))]
  nlinarith only [hy]
theorem lean_workbook_1002_4 (y : ℝ) (hy : -1 / 2 < y ∧ y < 0) : |y| > |2*y^2| := by
  rw [abs_of_neg hy.2, abs_of_pos (by nlinarith : 0 < 2 * y ^ 2)]
  nlinarith [hy.1, hy.2]
theorem lean_workbook_1002_5 (y : ℝ) (hy : -1 / 2 < y ∧ y < 0) : |y| > |2*y^2| := by
  rw [abs_of_neg hy.2, abs_of_pos (mul_pos (by norm_num) (sq_pos_of_neg hy.2))]
  nlinarith
theorem lean_workbook_1002_6 (y : ℝ) (hy : -1 / 2 < y ∧ y < 0) : |y| > |2*y^2| := by
  simp [abs_of_neg hy.2, abs_of_pos (mul_pos (zero_lt_two' ℝ) (sq_pos_of_neg hy.2))]
  nlinarith [hy.1, hy.2]
theorem lean_workbook_1002_7 (y : ℝ) (hy : -1 / 2 < y ∧ y < 0) : |y| > |2*y^2| := by
  rw [abs_of_neg hy.2, abs_of_pos (by nlinarith : 0 < 2 * y ^ 2)]
  nlinarith
theorem lean_workbook_1002_8 (y : ℝ) (hy : -1 / 2 < y ∧ y < 0) : |y| > |2*y^2| := by
  rw [abs_of_neg hy.2, abs_of_pos (by nlinarith : 0 < 2*y^2)]
  nlinarith
theorem lean_workbook_1002_9 (y : ℝ) (hy : -1 / 2 < y ∧ y < 0) : |y| > |2*y^2| := by
  obtain ⟨h1, h2⟩ := hy
  rw [abs_of_neg h2, abs_of_pos (by nlinarith : 0 < 2 * y ^ 2)]
  nlinarith
theorem lean_workbook_1002_10 (y : ℝ) (hy : -1 / 2 < y ∧ y < 0) : |y| > |2*y^2| := by
  rw [abs_of_neg hy.2, abs_of_pos (mul_pos two_pos (sq_pos_of_neg hy.2))]
  nlinarith [hy.1]
theorem lean_workbook_1002_11 (y : ℝ) (hy : -1 / 2 < y ∧ y < 0) : |y| > |2*y^2| := by
  rw [abs_of_neg hy.2, abs_of_pos (mul_pos (by norm_num) (sq_pos_of_neg hy.2))]
  nlinarith [hy.1, hy.2]
theorem lean_workbook_1002_12 (y : ℝ) (hy : -1 / 2 < y ∧ y < 0) : |y| > |2*y^2| := by
  rw [abs_of_neg hy.2, abs_of_pos (mul_pos zero_lt_two (sq_pos_of_neg hy.2))]
  nlinarith only [hy]
theorem lean_workbook_1002_13 (y : ℝ) (hy : -1 / 2 < y ∧ y < 0) : |y| > |2*y^2| := by
  rw [abs_of_neg hy.2, abs_of_pos (mul_pos two_pos (sq_pos_of_neg hy.2))]
  nlinarith
theorem lean_workbook_1002_14 (y : ℝ) (hy : -1 / 2 < y ∧ y < 0) : |y| > |2*y^2| := by
  simp [abs_of_neg hy.2, abs_of_pos (mul_pos zero_lt_two (sq_pos_of_neg hy.2))]
  nlinarith [hy.1, hy.2]

theorem lean_workbook_1003_0 (x y: ℝ): x ^ 2 + x + y ^ 2 + y + 1 ≥ x * y := by
  nth_rewrite 1 [← zero_add (x ^ 2)]
  nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 1)]
theorem lean_workbook_1003_1 (x y: ℝ): x ^ 2 + x + y ^ 2 + y + 1 ≥ x * y := by
  rw [add_comm]
  field_simp [sq]
  nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 1)]
theorem lean_workbook_1003_2 (x y: ℝ): x ^ 2 + x + y ^ 2 + y + 1 ≥ x * y := by
  field_simp [add_comm]
  rw [add_comm]
  nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 1)]
theorem lean_workbook_1003_3 (x y: ℝ): x ^ 2 + x + y ^ 2 + y + 1 ≥ x * y := by
  rw [add_comm]
  nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 1)]
theorem lean_workbook_1003_4 (x y: ℝ): x ^ 2 + x + y ^ 2 + y + 1 ≥ x * y := by
  ring_nf
  nlinarith [sq_nonneg (y + 1), sq_nonneg (x + 1)]
theorem lean_workbook_1003_5 (x y: ℝ): x ^ 2 + x + y ^ 2 + y + 1 ≥ x * y := by
  simp [sq]
  nlinarith only [sq_nonneg (x + 1), sq_nonneg (y + 1)]
theorem lean_workbook_1003_6 (x y: ℝ): x ^ 2 + x + y ^ 2 + y + 1 ≥ x * y := by
  simp [sq]
  nlinarith [sq_nonneg (y + 1), sq_nonneg (x + 1)]
theorem lean_workbook_1003_7 (x y: ℝ): x ^ 2 + x + y ^ 2 + y + 1 ≥ x * y := by
  simp [sq]
  ring_nf
  nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 1)]
theorem lean_workbook_1003_8 (x y: ℝ): x ^ 2 + x + y ^ 2 + y + 1 ≥ x * y := by
  field_simp [sq]
  rw [add_comm]
  nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 1)]
theorem lean_workbook_1003_9 (x y: ℝ): x ^ 2 + x + y ^ 2 + y + 1 ≥ x * y := by
  nlinarith [pow_two_nonneg (x + 1), pow_two_nonneg (y + 1)]

theorem lean_workbook_1008_0 : ∀ x y : ℝ, Real.cos x - Real.cos y = -2 * Real.sin ((x + y) / 2) * Real.sin ((x - y) / 2) := by
  intros x y
  rw [← Complex.ofReal_inj]
  simp [Complex.cos_sub_cos, Complex.sin_sub_sin]
theorem lean_workbook_1008_1 : ∀ x y : ℝ, Real.cos x - Real.cos y = -2 * Real.sin ((x + y) / 2) * Real.sin ((x - y) / 2) := by
  intro x y
  rw [← Complex.ofReal_inj]
  simp [Complex.cos_sub_cos, Complex.sin_sub_sin]

theorem lean_workbook_1018_0 (a b c d : ℝ) : 3 * (a^2 + b^2 + c^2 + d^2) - 4 * (a * b + b * c + c * d + d * a) + 2 * (a * c + b * d) ≥ 0 := by
  have := sq_nonneg (a - b + c - d)
  have := sq_nonneg (a - c)
  have := sq_nonneg (b - d)
  linarith
theorem lean_workbook_1018_1 (a b c d : ℝ) : 3 * (a^2 + b^2 + c^2 + d^2) - 4 * (a * b + b * c + c * d + d * a) + 2 * (a * c + b * d) ≥ 0 := by
  simp [sq]
  linarith [sq_nonneg (a - b + c - d), sq_nonneg (a - c + d - b), sq_nonneg (b - d + a - c)]
theorem lean_workbook_1018_2 (a b c d : ℝ) : 3 * (a^2 + b^2 + c^2 + d^2) - 4 * (a * b + b * c + c * d + d * a) + 2 * (a * c + b * d) ≥ 0 := by
  linarith [sq_nonneg (a - b + c - d), sq_nonneg (a - c), sq_nonneg (b - d)]

theorem lean_workbook_1021_0 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1 := by
  use fun k ↦ (2:ℝ) ^ (k - 1) * r
  aesop
theorem lean_workbook_1021_1 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1 := by
  use fun (k : ℕ) ↦ (2 : ℝ)^(k-1) * r
  aesop
theorem lean_workbook_1021_2 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1 := by
  use λ k => (2:ℝ)^(k-1) * r
  aesop
theorem lean_workbook_1021_3 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1 := by
  refine ⟨fun k ↦ (2 : ℝ)^(k-1) * r, by simp,?_⟩
  intro k
  simp [pow_add, mul_assoc]
theorem lean_workbook_1021_4 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1 := by
  use fun k => (2 : ℝ)^(k-1) * r
  simp [Nat.zero_sub]
theorem lean_workbook_1021_5 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1 := by
  use (fun k ↦ (2 : ℝ)^(k-1) * r)
  simp
theorem lean_workbook_1021_6 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1 := by
  refine' ⟨fun k => (2:ℝ) ^ (k - 1) * r, by simp, _⟩
  intro k
  simp
theorem lean_workbook_1021_7 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1 := by
  use fun k ↦ (2 : ℝ)^(k-1) * r
  simp
theorem lean_workbook_1021_8 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1 := by
  refine' ⟨fun k => (2 : ℝ)^(k-1) * r, _, _⟩ <;> simp [pow_succ]
theorem lean_workbook_1021_9 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1 := by
  use λ k ↦ (2 : ℝ)^(k-1) * r
  simp [Nat.one_ne_zero]
theorem lean_workbook_1021_10 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1 := by
  use fun k ↦ (2:ℝ) ^ (k-1) * r
  simp [Nat.succ_eq_add_one]
theorem lean_workbook_1021_11 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1 := by
  refine ⟨fun k => (2:ℝ)^(k-1) * r, by simp,?_⟩
  simp [pow_add, mul_assoc, mul_comm, mul_left_comm]
theorem lean_workbook_1021_12 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1 := by
  use λ k ↦ (2 : ℝ)^(k-1) * r
  simp
theorem lean_workbook_1021_13 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1 := by
  use fun (k : ℕ) => (2 : ℝ)^(k-1) * r
  simp [Nat.zero_sub, pow_zero, mul_one]
theorem lean_workbook_1021_14 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1 := by
  refine' ⟨fun k ↦ (2 : ℝ)^(k-1) * r, by simp, fun k ↦ by simp⟩
theorem lean_workbook_1021_15 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1 := by
  use fun (k : ℕ) ↦ (2 : ℝ)^(k-1) * r
  constructor <;> simp
theorem lean_workbook_1021_16 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1 := by
  refine' ⟨fun k => (2:ℝ)^(k-1) * r, by simp, fun k => by simp⟩
theorem lean_workbook_1021_17 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1 := by
  use fun k => (2 : ℝ)^(k-1) * r
  aesop
theorem lean_workbook_1021_18 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1 := by
  use fun (k : ℕ) => (2:ℝ) ^ (k-1) * r
  aesop
theorem lean_workbook_1021_19 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1 := by
  use fun k ↦ (2 : ℝ)^(k-1) * r
  simp [Nat.one_ne_zero]
theorem lean_workbook_1021_20 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1 := by
  use fun k => (2 : ℝ)^(k-1) * r
  constructor
  simp
  intro k
  simp [pow_add, mul_assoc]
theorem lean_workbook_1021_21 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1 := by
  use fun k ↦ (2:ℝ)^(k-1) * r
  simp
theorem lean_workbook_1021_22 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1 := by
  use fun k => (2 : ℝ)^(k-1) * r
  simp
theorem lean_workbook_1021_23 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1 := by
  use fun k => r * (2:ℝ) ^ (k - 1)
  constructor
  simp
  intro k
  rw [mul_comm]
  ring_nf
theorem lean_workbook_1021_24 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1 := by
  refine' ⟨fun k => (2 : ℝ)^(k-1) * r, by simp, fun k => _⟩
  simp [mul_comm]
theorem lean_workbook_1021_25 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1 := by
  use (fun (k : ℕ) ↦ (2 : ℝ)^(k-1) * r)
  simp
theorem lean_workbook_1021_26 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1 := by
  let f : ℕ → ℝ := fun k ↦ (2 : ℝ)^(k-1) * r
  refine ⟨f, by simp [f], fun k ↦?_⟩
  simp [f]

theorem lean_workbook_1024_0 (x : ℝ) (hx : ∃ z : ℤ, x = z) : (Int.floor x)^3 + 2 * x^2 = x^3 + 2 * (Int.floor x)^2 := by
  cases' hx with z hx
  rw [hx]
  simp [Int.floor_intCast]
theorem lean_workbook_1024_1 (x : ℝ) (hx : ∃ z : ℤ, x = z) : (Int.floor x)^3 + 2 * x^2 = x^3 + 2 * (Int.floor x)^2 := by
  rcases hx with ⟨z, rfl⟩
  simp [Int.floor_intCast, add_comm]
theorem lean_workbook_1024_2 (x : ℝ) (hx : ∃ z : ℤ, x = z) : (Int.floor x)^3 + 2 * x^2 = x^3 + 2 * (Int.floor x)^2 := by
  rcases hx with ⟨z, rfl⟩
  simp [Int.floor_intCast, Int.cast_pow, Int.cast_add, Int.cast_mul]
theorem lean_workbook_1024_3 (x : ℝ) (hx : ∃ z : ℤ, x = z) : (Int.floor x)^3 + 2 * x^2 = x^3 + 2 * (Int.floor x)^2 := by
  rcases hx with ⟨z, hz⟩
  rw [hz]
  simp
theorem lean_workbook_1024_4 (x : ℝ) (hx : ∃ z : ℤ, x = z) : (Int.floor x)^3 + 2 * x^2 = x^3 + 2 * (Int.floor x)^2 := by
  obtain ⟨z, hz⟩ := hx
  simp [hz]
theorem lean_workbook_1024_5 (x : ℝ) (hx : ∃ z : ℤ, x = z) : (Int.floor x)^3 + 2 * x^2 = x^3 + 2 * (Int.floor x)^2 := by
  obtain ⟨z, hz⟩ := hx
  simp [hz, Int.floor_intCast]
theorem lean_workbook_1024_6 (x : ℝ) (hx : ∃ z : ℤ, x = z) : (Int.floor x)^3 + 2 * x^2 = x^3 + 2 * (Int.floor x)^2 := by
  obtain ⟨z, hx⟩ := hx
  simp [hx, Int.floor_eq_iff]
theorem lean_workbook_1024_7 (x : ℝ) (hx : ∃ z : ℤ, x = z) : (Int.floor x)^3 + 2 * x^2 = x^3 + 2 * (Int.floor x)^2 := by
  obtain ⟨z, hx⟩ := hx
  simp [hx, Int.floor_eq_iff, Int.cast_pow, Int.cast_add, Int.cast_mul, pow_add, pow_mul, mul_pow]
theorem lean_workbook_1024_8 (x : ℝ) (hx : ∃ z : ℤ, x = z) : (Int.floor x)^3 + 2 * x^2 = x^3 + 2 * (Int.floor x)^2 := by
  rw [hx.choose_spec]
  obtain ⟨z, rfl⟩ := hx
  simp [Int.floor_intCast]
theorem lean_workbook_1024_9 (x : ℝ) (hx : ∃ z : ℤ, x = z) : (Int.floor x)^3 + 2 * x^2 = x^3 + 2 * (Int.floor x)^2 := by
  obtain ⟨z, hz⟩ := hx
  rw [hz]
  simp [Int.floor_intCast, hz]
theorem lean_workbook_1024_10 (x : ℝ) (hx : ∃ z : ℤ, x = z) : (Int.floor x)^3 + 2 * x^2 = x^3 + 2 * (Int.floor x)^2 := by
  obtain ⟨z, rfl⟩ := hx
  simp [Int.floor_intCast, Int.cast_pow]

theorem lean_workbook_1032_0 (a b c : ℝ) : (5 / 3) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 2 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + 3 * (a * b ^ 3 + b * c ^ 3 + c * a ^ 3) := by
  simp [add_mul]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1032_1 (a b c : ℝ) : (5 / 3) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 2 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + 3 * (a * b ^ 3 + b * c ^ 3 + c * a ^ 3) := by
  simp [add_assoc, add_comm, add_left_comm]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1032_2 (a b c : ℝ) : (5 / 3) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 2 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + 3 * (a * b ^ 3 + b * c ^ 3 + c * a ^ 3) := by
  simp [mul_assoc, mul_comm, mul_left_comm]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

theorem lean_workbook_1039_0 (x : ℝ) (hx : x = (4 - 2 * Real.sqrt 3) / 2) : x = 2 - Real.sqrt 3 := by
  linarith [Real.sqrt_nonneg 3]
theorem lean_workbook_1039_1 (x : ℝ) (hx : x = (4 - 2 * Real.sqrt 3) / 2) : x = 2 - Real.sqrt 3 := by
  nlinarith [show (4 : ℝ) = 2 * 2 by norm_num]
theorem lean_workbook_1039_2 (x : ℝ) (hx : x = (4 - 2 * Real.sqrt 3) / 2) : x = 2 - Real.sqrt 3 := by
  simp [hx]
  ring
theorem lean_workbook_1039_3 (x : ℝ) (hx : x = (4 - 2 * Real.sqrt 3) / 2) : x = 2 - Real.sqrt 3 := by
  rw [hx, div_eq_iff (by norm_num : (2 : ℝ) ≠ 0)]
  ring
theorem lean_workbook_1039_4 (x : ℝ) (hx : x = (4 - 2 * Real.sqrt 3) / 2) : x = 2 - Real.sqrt 3 := by
  simp [hx, mul_sub, mul_div_cancel_left]
  ring
theorem lean_workbook_1039_5 (x : ℝ) (hx : x = (4 - 2 * Real.sqrt 3) / 2) : x = 2 - Real.sqrt 3 := by
  rw [hx, ← sub_eq_zero]
  ring
theorem lean_workbook_1039_6 (x : ℝ) (hx : x = (4 - 2 * Real.sqrt 3) / 2) : x = 2 - Real.sqrt 3 := by
  rw [hx]
  field_simp
  ring_nf
theorem lean_workbook_1039_7 (x : ℝ) (hx : x = (4 - 2 * Real.sqrt 3) / 2) : x = 2 - Real.sqrt 3 := by
  field_simp [hx]
  ring
theorem lean_workbook_1039_8 (x : ℝ) (hx : x = (4 - 2 * Real.sqrt 3) / 2) : x = 2 - Real.sqrt 3 := by
  rw [hx]
  ring_nf at hx ⊢
theorem lean_workbook_1039_9 (x : ℝ) (hx : x = (4 - 2 * Real.sqrt 3) / 2) : x = 2 - Real.sqrt 3 := by
  rw [hx, div_eq_iff (two_ne_zero' ℝ)]
  ring
theorem lean_workbook_1039_10 (x : ℝ) (hx : x = (4 - 2 * Real.sqrt 3) / 2) : x = 2 - Real.sqrt 3 := by
  field_simp [hx, mul_comm]
  ring
theorem lean_workbook_1039_11 (x : ℝ) (hx : x = (4 - 2 * Real.sqrt 3) / 2) : x = 2 - Real.sqrt 3 := by
  rw [hx]
  field_simp
  ring
theorem lean_workbook_1039_12 (x : ℝ) (hx : x = (4 - 2 * Real.sqrt 3) / 2) : x = 2 - Real.sqrt 3 := by
  field_simp at hx ⊢
  linarith
theorem lean_workbook_1039_13 (x : ℝ) (hx : x = (4 - 2 * Real.sqrt 3) / 2) : x = 2 - Real.sqrt 3 := by
  simp [hx, sub_eq_add_neg]
  ring_nf
theorem lean_workbook_1039_14 (x : ℝ) (hx : x = (4 - 2 * Real.sqrt 3) / 2) : x = 2 - Real.sqrt 3 := by
  rw [hx, div_eq_iff (two_ne_zero' ℝ)]
  linarith
theorem lean_workbook_1039_15 (x : ℝ) (hx : x = (4 - 2 * Real.sqrt 3) / 2) : x = 2 - Real.sqrt 3 := by
  norm_num at hx
  field_simp at hx ⊢
  linarith [Real.sqrt_nonneg 3]
theorem lean_workbook_1039_16 (x : ℝ) (hx : x = (4 - 2 * Real.sqrt 3) / 2) : x = 2 - Real.sqrt 3 := by
  simp [hx, mul_comm, mul_assoc, mul_left_comm]
  ring
theorem lean_workbook_1039_17 (x : ℝ) (hx : x = (4 - 2 * Real.sqrt 3) / 2) : x = 2 - Real.sqrt 3 := by
  field_simp [hx]
  ring_nf
theorem lean_workbook_1039_18 (x : ℝ) (hx : x = (4 - 2 * Real.sqrt 3) / 2) : x = 2 - Real.sqrt 3 := by
  field_simp [hx]
  linarith [Real.sqrt_nonneg 3]

theorem lean_workbook_1041_0 : 13 ∣ 2^30 + 3^60 := by
  norm_num [Nat.dvd_add, Nat.pow_succ]
theorem lean_workbook_1041_1 : 13 ∣ 2^30 + 3^60 := by
  norm_num [Nat.gcd_eq_gcd_ab 13 12]
theorem lean_workbook_1041_2 : 13 ∣ 2^30 + 3^60 := by
  norm_num [Nat.div_mod_unique]
theorem lean_workbook_1041_3 : 13 ∣ 2^30 + 3^60 := by
  norm_num [Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_zero_of_dvd]
theorem lean_workbook_1041_4 : 13 ∣ 2^30 + 3^60 := by
  norm_num [Nat.pow_succ, Nat.pow_zero, Nat.pow_one, Nat.succ_eq_add_one]
theorem lean_workbook_1041_5 : 13 ∣ 2^30 + 3^60 := by
  norm_num [pow_succ, pow_zero, pow_one, add_assoc]
theorem lean_workbook_1041_6 : 13 ∣ 2^30 + 3^60 := by
  rw [← Nat.mod_add_div 13 4]
  norm_num [Nat.pow_mod]
theorem lean_workbook_1041_7 : 13 ∣ 2^30 + 3^60 := by
  norm_num [Nat.dvd_add_iff_left, Nat.pow_succ]
theorem lean_workbook_1041_8 : 13 ∣ 2^30 + 3^60 := by
  rw [← Nat.mod_add_div (2 ^ 30) 13, ← Nat.mod_add_div (3 ^ 60) 13]
  norm_num
theorem lean_workbook_1041_9 : 13 ∣ 2^30 + 3^60 := by
  simp only [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod, Nat.mod_mod]
  norm_num
theorem lean_workbook_1041_10 : 13 ∣ 2^30 + 3^60 := by
  rw [← Nat.mod_add_div 13 4]
  norm_num [Nat.pow_succ]
theorem lean_workbook_1041_11 : 13 ∣ 2^30 + 3^60 := by
  norm_num [Nat.pow_succ, Nat.pow_zero]
theorem lean_workbook_1041_12 : 13 ∣ 2^30 + 3^60 := by
  norm_num [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod]
theorem lean_workbook_1041_13 : 13 ∣ 2^30 + 3^60 := by
  norm_num [Nat.dvd_add]
theorem lean_workbook_1041_14 : 13 ∣ 2^30 + 3^60 := by
  simp [Nat.pow_succ, Nat.pow_zero]
  norm_num
theorem lean_workbook_1041_15 : 13 ∣ 2^30 + 3^60 := by
  rw [← Nat.mod_add_div (2^30) 13, ← Nat.mod_add_div (3^60) 13]
  norm_num
theorem lean_workbook_1041_16 : 13 ∣ 2^30 + 3^60 := by
  norm_num [pow_one]
theorem lean_workbook_1041_17 : 13 ∣ 2^30 + 3^60 := by
  norm_num [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, Nat.mod_mod]
theorem lean_workbook_1041_18 : 13 ∣ 2^30 + 3^60 := by
  norm_num [pow_succ, add_mul]
theorem lean_workbook_1041_19 : 13 ∣ 2^30 + 3^60 := by
  norm_num [Nat.pow_succ, Nat.pow_zero, Nat.pow_one, Nat.pow_zero, Nat.pow_one]
theorem lean_workbook_1041_20 : 13 ∣ 2^30 + 3^60 := by
  norm_num [pow_succ, pow_zero, pow_one, mul_comm, mul_assoc, mul_left_comm]
theorem lean_workbook_1041_21 : 13 ∣ 2^30 + 3^60 := by
  norm_num [Nat.pow_succ, Nat.pow_zero, mul_one, Nat.pow_one, Nat.add_comm]
theorem lean_workbook_1041_22 : 13 ∣ 2^30 + 3^60 := by
  norm_num [Nat.ModEq]
theorem lean_workbook_1041_23 : 13 ∣ 2^30 + 3^60 := by
  norm_num [Nat.pow_succ, Nat.pow_zero, Nat.pow_one, Nat.add_zero, Nat.add_one]
theorem lean_workbook_1041_24 : 13 ∣ 2^30 + 3^60 := by
  norm_num [Nat.gcd_eq_gcd_ab, Nat.gcd_rec]
theorem lean_workbook_1041_25 : 13 ∣ 2^30 + 3^60 := by
  norm_num [Nat.gcd_eq_gcd_ab 13 27]
theorem lean_workbook_1041_26 : 13 ∣ 2^30 + 3^60 := by
  exact Nat.dvd_of_mod_eq_zero (by norm_num)
theorem lean_workbook_1041_27 : 13 ∣ 2^30 + 3^60 := by
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.pow_one]
  norm_num
theorem lean_workbook_1041_28 : 13 ∣ 2^30 + 3^60 := by
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one]
  norm_num
theorem lean_workbook_1041_29 : 13 ∣ 2^30 + 3^60 := by
  norm_num [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
theorem lean_workbook_1041_30 : 13 ∣ 2^30 + 3^60 := by
  norm_num [Nat.pow_succ, Nat.pow_zero, Nat.pow_one]

theorem lean_workbook_1043_0 : 2 / 5 * (x + 1) ^ (5 / 2) - 2 / 3 * (x + 1) ^ (3 / 2) = 2 / 3 * x * (x + 1) ^ (3 / 2) - 4 / 15 * (x + 1) ^ (5 / 2) := by
  norm_cast at *
  ring
theorem lean_workbook_1043_1 : 2 / 5 * (x + 1) ^ (5 / 2) - 2 / 3 * (x + 1) ^ (3 / 2) = 2 / 3 * x * (x + 1) ^ (3 / 2) - 4 / 15 * (x + 1) ^ (5 / 2) := by
  rw [add_comm]
  ring_nf
theorem lean_workbook_1043_2 : 2 / 5 * (x + 1) ^ (5 / 2) - 2 / 3 * (x + 1) ^ (3 / 2) = 2 / 3 * x * (x + 1) ^ (3 / 2) - 4 / 15 * (x + 1) ^ (5 / 2) := by
  ring_nf at *

theorem lean_workbook_1046_0 : ∀ a b c : ℝ, (2 * a ^ 2 - c ^ 2) ^ 2 + (2 * b ^ 2 - c ^ 2) ^ 2 ≥ 0 := by
  intros a b c
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]
theorem lean_workbook_1046_1 : ∀ a b c : ℝ, (2 * a ^ 2 - c ^ 2) ^ 2 + (2 * b ^ 2 - c ^ 2) ^ 2 ≥ 0 := by
  intros a b c
  nlinarith only [c]
theorem lean_workbook_1046_2 : ∀ a b c : ℝ, (2 * a ^ 2 - c ^ 2) ^ 2 + (2 * b ^ 2 - c ^ 2) ^ 2 ≥ 0 := by
  intro a b c
  simp only [sq_nonneg, add_nonneg]
theorem lean_workbook_1046_3 : ∀ a b c : ℝ, (2 * a ^ 2 - c ^ 2) ^ 2 + (2 * b ^ 2 - c ^ 2) ^ 2 ≥ 0 := by
  simp [add_nonneg, mul_nonneg, sq_nonneg]
theorem lean_workbook_1046_4 : ∀ a b c : ℝ, (2 * a ^ 2 - c ^ 2) ^ 2 + (2 * b ^ 2 - c ^ 2) ^ 2 ≥ 0 := by
  intro a b c
  nlinarith [mul_self_nonneg a, mul_self_nonneg b, mul_self_nonneg c]
theorem lean_workbook_1046_5 : ∀ a b c : ℝ, (2 * a ^ 2 - c ^ 2) ^ 2 + (2 * b ^ 2 - c ^ 2) ^ 2 ≥ 0 := by
  refine' fun a b c => add_nonneg (sq_nonneg _) (sq_nonneg _)
theorem lean_workbook_1046_6 : ∀ a b c : ℝ, (2 * a ^ 2 - c ^ 2) ^ 2 + (2 * b ^ 2 - c ^ 2) ^ 2 ≥ 0 := by
  intro a b c
  exact add_nonneg (pow_two_nonneg _) (pow_two_nonneg _)
theorem lean_workbook_1046_7 : ∀ a b c : ℝ, (2 * a ^ 2 - c ^ 2) ^ 2 + (2 * b ^ 2 - c ^ 2) ^ 2 ≥ 0 := by
  simp [add_comm, add_left_comm, add_assoc]
  intro a b c
  nlinarith
theorem lean_workbook_1046_8 : ∀ a b c : ℝ, (2 * a ^ 2 - c ^ 2) ^ 2 + (2 * b ^ 2 - c ^ 2) ^ 2 ≥ 0 := by
  intro a b c
  nlinarith
theorem lean_workbook_1046_9 : ∀ a b c : ℝ, (2 * a ^ 2 - c ^ 2) ^ 2 + (2 * b ^ 2 - c ^ 2) ^ 2 ≥ 0 := by
  intro a b c
  nlinarith [mul_self_nonneg (2 * a ^ 2 - c ^ 2), mul_self_nonneg (2 * b ^ 2 - c ^ 2)]
theorem lean_workbook_1046_10 : ∀ a b c : ℝ, (2 * a ^ 2 - c ^ 2) ^ 2 + (2 * b ^ 2 - c ^ 2) ^ 2 ≥ 0 := by
  intro a b c
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)
theorem lean_workbook_1046_11 : ∀ a b c : ℝ, (2 * a ^ 2 - c ^ 2) ^ 2 + (2 * b ^ 2 - c ^ 2) ^ 2 ≥ 0 := by
  intros a b c
  apply add_nonneg <;> simp [sq_nonneg]
theorem lean_workbook_1046_12 : ∀ a b c : ℝ, (2 * a ^ 2 - c ^ 2) ^ 2 + (2 * b ^ 2 - c ^ 2) ^ 2 ≥ 0 := by
  exact fun a b c ↦ by nlinarith [sq_nonneg (2 * a ^ 2 - c ^ 2), sq_nonneg (2 * b ^ 2 - c ^ 2)]
theorem lean_workbook_1046_13 : ∀ a b c : ℝ, (2 * a ^ 2 - c ^ 2) ^ 2 + (2 * b ^ 2 - c ^ 2) ^ 2 ≥ 0 := by
  rintro a b c
  nlinarith [pow_two_nonneg a, pow_two_nonneg b, pow_two_nonneg c]
theorem lean_workbook_1046_14 : ∀ a b c : ℝ, (2 * a ^ 2 - c ^ 2) ^ 2 + (2 * b ^ 2 - c ^ 2) ^ 2 ≥ 0 := by
  intro a b c
  nlinarith only [sq_nonneg c]
theorem lean_workbook_1046_15 : ∀ a b c : ℝ, (2 * a ^ 2 - c ^ 2) ^ 2 + (2 * b ^ 2 - c ^ 2) ^ 2 ≥ 0 := by
  intro a b c
  apply add_nonneg
  apply sq_nonneg
  apply sq_nonneg
theorem lean_workbook_1046_16 : ∀ a b c : ℝ, (2 * a ^ 2 - c ^ 2) ^ 2 + (2 * b ^ 2 - c ^ 2) ^ 2 ≥ 0 := by
  intros
  apply_rules [sq_nonneg, add_nonneg]
theorem lean_workbook_1046_17 : ∀ a b c : ℝ, (2 * a ^ 2 - c ^ 2) ^ 2 + (2 * b ^ 2 - c ^ 2) ^ 2 ≥ 0 := by
  intro a b c
  apply_rules [sq_nonneg, add_nonneg]
theorem lean_workbook_1046_18 : ∀ a b c : ℝ, (2 * a ^ 2 - c ^ 2) ^ 2 + (2 * b ^ 2 - c ^ 2) ^ 2 ≥ 0 := by
  intro a b c
  apply_rules [add_nonneg, sq_nonneg, sub_nonneg]
theorem lean_workbook_1046_19 : ∀ a b c : ℝ, (2 * a ^ 2 - c ^ 2) ^ 2 + (2 * b ^ 2 - c ^ 2) ^ 2 ≥ 0 := by
  intros a b c
  apply_rules [sq_nonneg, add_nonneg]
theorem lean_workbook_1046_20 : ∀ a b c : ℝ, (2 * a ^ 2 - c ^ 2) ^ 2 + (2 * b ^ 2 - c ^ 2) ^ 2 ≥ 0 := by
  intro a b c
  apply_rules [add_nonneg, sq_nonneg]
theorem lean_workbook_1046_21 : ∀ a b c : ℝ, (2 * a ^ 2 - c ^ 2) ^ 2 + (2 * b ^ 2 - c ^ 2) ^ 2 ≥ 0 := by
  simp [sub_nonneg, sq_nonneg]
  intros
  nlinarith

theorem lean_workbook_1048_0 (p : ℕ) (hp : p.Prime) (a : ZMod p) (ha : a ≠ 0) : ∃ b : ZMod p, a * b = 1 := by
  have hp' : Fact p.Prime := ⟨hp⟩
  have : (a : ZMod p) * (a⁻¹ : ZMod p) = 1 := mul_inv_cancel ha
  exact ⟨a⁻¹, this⟩
theorem lean_workbook_1048_1 (p : ℕ) (hp : p.Prime) (a : ZMod p) (ha : a ≠ 0) : ∃ b : ZMod p, a * b = 1 := by
  haveI := Fact.mk hp
  have : a * a⁻¹ = 1 := mul_inv_cancel ha
  exact ⟨a⁻¹, this⟩
theorem lean_workbook_1048_2 (p : ℕ) (hp : p.Prime) (a : ZMod p) (ha : a ≠ 0) : ∃ b : ZMod p, a * b = 1 := by
  have hp' : Fact p.Prime := ⟨hp⟩
  refine' ⟨a⁻¹, _⟩
  rw [mul_inv_cancel ha]
theorem lean_workbook_1048_3 (p : ℕ) (hp : p.Prime) (a : ZMod p) (ha : a ≠ 0) : ∃ b : ZMod p, a * b = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have : a * a⁻¹ = 1 := mul_inv_cancel ha
  exact ⟨a⁻¹, this⟩

theorem lean_workbook_1062_0 (R r : ℝ) : 9 * R ^ 2 - 20 * R * r + 31 * r ^ 2 ≥ 16 * R * r - 5 * r ^ 2 := by
  ring_nf
  nlinarith [sq_nonneg (R - 2 * r)]
theorem lean_workbook_1062_1 (R r : ℝ) : 9 * R ^ 2 - 20 * R * r + 31 * r ^ 2 ≥ 16 * R * r - 5 * r ^ 2 := by
  simp [sub_eq_add_neg, add_comm]
  nlinarith [sq_nonneg (R - 2 * r)]
theorem lean_workbook_1062_2 (R r : ℝ) : 9 * R ^ 2 - 20 * R * r + 31 * r ^ 2 ≥ 16 * R * r - 5 * r ^ 2 := by
  ring_nf
  field_simp [sq]
  nlinarith [sq_nonneg (R - r), sq_nonneg (R - 2 * r)]
theorem lean_workbook_1062_3 (R r : ℝ) : 9 * R ^ 2 - 20 * R * r + 31 * r ^ 2 ≥ 16 * R * r - 5 * r ^ 2 := by
  simp [sq]
  ring_nf
  nlinarith [sq_nonneg (R - 2 * r), sq_nonneg (R - r)]
theorem lean_workbook_1062_4 (R r : ℝ) : 9 * R ^ 2 - 20 * R * r + 31 * r ^ 2 ≥ 16 * R * r - 5 * r ^ 2 := by
  field_simp [sq]
  ring_nf
  nlinarith [sq_nonneg (R - 2 * r), sq_nonneg (R - r)]
theorem lean_workbook_1062_5 (R r : ℝ) : 9 * R ^ 2 - 20 * R * r + 31 * r ^ 2 ≥ 16 * R * r - 5 * r ^ 2 := by
  have h1 := sq_nonneg (R - 2 * r)
  linarith

theorem lean_workbook_1071_0 (n : ℕ) : 1998 = 2 * 3^3 * 37 := by
  simp [Nat.factorization]
theorem lean_workbook_1071_1 (n : ℕ) : 1998 = 2 * 3^3 * 37 := by
  simp [show 1998 = 2 * 3^3 * 37 by norm_num]
theorem lean_workbook_1071_2 (n : ℕ) : 1998 = 2 * 3^3 * 37 := by
  congr 1
theorem lean_workbook_1071_3 (n : ℕ) : 1998 = 2 * 3^3 * 37 := by
  simp [mul_comm]
theorem lean_workbook_1071_4 (n : ℕ) : 1998 = 2 * 3^3 * 37 := by
  norm_num [Nat.factorization, show 1998 = 2 * 3^3 * 37 by norm_num]
theorem lean_workbook_1071_5 (n : ℕ) : 1998 = 2 * 3^3 * 37 := by
  simp [mul_assoc, Nat.pow_succ]
theorem lean_workbook_1071_6 (n : ℕ) : 1998 = 2 * 3^3 * 37 := by
  repeat' rw [Nat.succ_eq_add_one]
  ring
theorem lean_workbook_1071_7 (n : ℕ) : 1998 = 2 * 3^3 * 37 := by
  simp only [show 1998 = 2 * 3 ^ 3 * 37 by norm_num]
theorem lean_workbook_1071_8 (n : ℕ) : 1998 = 2 * 3^3 * 37 := by
  simp [show 1998 = 2 * 3^3 * 37 from rfl]
theorem lean_workbook_1071_9 (n : ℕ) : 1998 = 2 * 3^3 * 37 := by
  norm_num [pow_succ, pow_zero]
theorem lean_workbook_1071_10 (n : ℕ) : 1998 = 2 * 3^3 * 37 := by
  norm_num [Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right, Nat.coprime_iff_gcd_eq_one]
theorem lean_workbook_1071_11 (n : ℕ) : 1998 = 2 * 3^3 * 37 := by
  norm_num [Nat.factorization, show 1998 = 2 * 3^3 * 37 from rfl]
theorem lean_workbook_1071_12 (n : ℕ) : 1998 = 2 * 3^3 * 37 := by
  norm_num [pow_succ, pow_succ, pow_succ, mul_comm, mul_assoc, mul_left_comm]
theorem lean_workbook_1071_13 (n : ℕ) : 1998 = 2 * 3^3 * 37 := by
  simp [mul_comm, mul_assoc, mul_left_comm]
theorem lean_workbook_1071_14 (n : ℕ) : 1998 = 2 * 3^3 * 37 := by
  norm_num [show (2:ℤ) * 3 ^ 3 * 37 = 1998 by norm_num]
theorem lean_workbook_1071_15 (n : ℕ) : 1998 = 2 * 3^3 * 37 := by
  rw [show 1998 = 2 * 3^3 * 37 by norm_num]
theorem lean_workbook_1071_16 (n : ℕ) : 1998 = 2 * 3^3 * 37 := by
  norm_num [show (2 : ℤ) * 3 ^ 3 * 37 = 1998 by norm_num]
theorem lean_workbook_1071_17 (n : ℕ) : 1998 = 2 * 3^3 * 37 := by
  norm_num [Nat.gcd_eq_gcd_ab 1998 n]
theorem lean_workbook_1071_18 (n : ℕ) : 1998 = 2 * 3^3 * 37 := by
  norm_num [Nat.coprime_mul_iff_right]
theorem lean_workbook_1071_19 (n : ℕ) : 1998 = 2 * 3^3 * 37 := by
  norm_num [Nat.gcd_eq_gcd_ab]
theorem lean_workbook_1071_20 (n : ℕ) : 1998 = 2 * 3^3 * 37 := by
  norm_num [Nat.factorization, Nat.pow_succ]
theorem lean_workbook_1071_21 (n : ℕ) : 1998 = 2 * 3^3 * 37 := by
  norm_num [show 37 = 37 by norm_num]
theorem lean_workbook_1071_22 (n : ℕ) : 1998 = 2 * 3^3 * 37 := by
  norm_num [show (3 : ℕ) = 1 + 2 by norm_num]
theorem lean_workbook_1071_23 (n : ℕ) : 1998 = 2 * 3^3 * 37 := by
  norm_num [Nat.gcd_eq_right (by norm_num : 37 ∣ 1998)]
theorem lean_workbook_1071_24 (n : ℕ) : 1998 = 2 * 3^3 * 37 := by
  norm_num [Nat.gcd_eq_gcd_ab 1998 37]
theorem lean_workbook_1071_25 (n : ℕ) : 1998 = 2 * 3^3 * 37 := by
  norm_num [show (2 : ℤ) = (2 : ℕ) by norm_cast, show (3 : ℤ) = (3 : ℕ) by norm_cast]
theorem lean_workbook_1071_26 (n : ℕ) : 1998 = 2 * 3^3 * 37 := by
  norm_num [Nat.factorization]

theorem lean_workbook_1082_0 : 2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  have s1 := sin_add a b
  have s2 := sin_sub a b
  rw [s1, s2]
  ring
theorem lean_workbook_1082_1 : 2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  simp [add_mul, sub_mul, sin_add, sin_sub]
  ring
theorem lean_workbook_1082_2 : 2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  rw [sin_add, sin_sub, two_mul, add_comm]
  ring
theorem lean_workbook_1082_3 : 2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  simp [Real.sin_add, Real.sin_sub, mul_add, mul_sub, mul_comm, sub_eq_add_neg]
  ring
theorem lean_workbook_1082_4 : 2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  simp only [sin_add, sin_sub, mul_add, mul_sub]
  ring
theorem lean_workbook_1082_5 : 2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  rw [← mul_right_inj' (two_ne_zero' ℝ)]
  rw [sin_add, sin_sub]
  rw [two_mul, add_sub_left_comm]
  ring
theorem lean_workbook_1082_6 : 2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  simp [sin_add, sin_sub, mul_add, mul_sub]
  ring
theorem lean_workbook_1082_7 : 2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  rw [Real.sin_add, Real.sin_sub]
  rw [← mul_right_inj' (two_ne_zero' ℝ)]
  ring
theorem lean_workbook_1082_8 : 2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  rw [sin_add, sin_sub]
  ring
theorem lean_workbook_1082_9 : 2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  simp [sub_eq_add_neg, sin_add, cos_add, sin_neg, cos_neg]
  ring
theorem lean_workbook_1082_10 : 2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  simp [Real.sin_add, sin_sub, mul_add, mul_sub, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_1082_11 : 2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  simp [sin_add, sin_sub, mul_add, mul_sub, mul_comm]
  ring
theorem lean_workbook_1082_12 : 2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  simp [sin_add, sin_sub, mul_add, mul_sub, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_1082_13 : 2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  simp [sin_add, sin_sub, sin_two_mul, cos_two_mul]
  ring
theorem lean_workbook_1082_14 : 2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  simp [sin_add, sin_sub, mul_add, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_1082_15 : 2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  simp only [sin_add, sin_sub, mul_add, mul_sub, mul_one, mul_zero]
  ring
theorem lean_workbook_1082_16 : 2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  simp [cos_add, cos_sub, sin_add, sin_sub, mul_add, mul_sub, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_1082_17 : 2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  simp [cos_add, cos_sub, sin_add, sin_sub]
  ring
theorem lean_workbook_1082_18 : 2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  simp [sin_add, sin_sub, mul_add, mul_sub, mul_two, mul_comm, sub_eq_add_neg]
  ring
theorem lean_workbook_1082_19 : 2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  eta_reduce at *
  simp [sin_add, sin_sub, two_mul]
  ring
theorem lean_workbook_1082_20 : 2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  simp [sin_add, sin_sub]
  ring
theorem lean_workbook_1082_21 : 2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  simp [Real.sin_add, Real.sin_sub, mul_add, mul_sub]
  ring
theorem lean_workbook_1082_22 : 2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  simp [sub_eq_add_neg, sin_add, sin_neg, cos_neg, sub_eq_add_neg]
  ring
theorem lean_workbook_1082_23 : 2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  simp [sub_eq_add_neg, sin_add, cos_add, mul_add]
  ring
theorem lean_workbook_1082_24 : 2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  have s1 := sin_add a b
  have s2 := sin_sub a b
  rw [s1, s2, add_comm]
  ring
theorem lean_workbook_1082_25 : 2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  rw [← Complex.ofReal_inj]
  simp [sin_add, sin_sub, Complex.sin_ofReal_re, Complex.cos_ofReal_re]
  ring
theorem lean_workbook_1082_26 : 2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  simp [sin_add, sin_sub, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_1082_27 : 2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  simp [sin_add, sin_sub, mul_comm, mul_assoc, mul_left_comm]
  ring

theorem lean_workbook_1096_0 (a b c : ℝ) : a * b + b * c + c * a - a * b * c ≤ (c^2 + 1) / 2 + (a^2 + b^2) / 2 ↔ a^2 + b^2 + c^2 + 2 * a * b * c + 1 ≥ 2 * (a * b + b * c + c * a) := by
  field_simp [sq]
  refine' ⟨fun h => _, fun h => _⟩
  linarith
  linarith
theorem lean_workbook_1096_1 (a b c : ℝ) : a * b + b * c + c * a - a * b * c ≤ (c^2 + 1) / 2 + (a^2 + b^2) / 2 ↔ a^2 + b^2 + c^2 + 2 * a * b * c + 1 ≥ 2 * (a * b + b * c + c * a) := by
  refine' ⟨fun h => _, fun h => _⟩
  linarith [h]
  linarith
theorem lean_workbook_1096_2 (a b c : ℝ) : a * b + b * c + c * a - a * b * c ≤ (c^2 + 1) / 2 + (a^2 + b^2) / 2 ↔ a^2 + b^2 + c^2 + 2 * a * b * c + 1 ≥ 2 * (a * b + b * c + c * a) := by
  field_simp [add_comm]
  ring_nf
  refine' ⟨fun h => _, fun h => _⟩
  linarith
  linarith
theorem lean_workbook_1096_3 (a b c : ℝ) : a * b + b * c + c * a - a * b * c ≤ (c^2 + 1) / 2 + (a^2 + b^2) / 2 ↔ a^2 + b^2 + c^2 + 2 * a * b * c + 1 ≥ 2 * (a * b + b * c + c * a) := by
  constructor <;> intro h <;> linarith [h]
theorem lean_workbook_1096_4 (a b c : ℝ) : a * b + b * c + c * a - a * b * c ≤ (c^2 + 1) / 2 + (a^2 + b^2) / 2 ↔ a^2 + b^2 + c^2 + 2 * a * b * c + 1 ≥ 2 * (a * b + b * c + c * a) := by
  field_simp [mul_add, add_mul]
  ring_nf
  constructor <;> intro h
  linarith
  linarith [h]
theorem lean_workbook_1096_5 (a b c : ℝ) : a * b + b * c + c * a - a * b * c ≤ (c^2 + 1) / 2 + (a^2 + b^2) / 2 ↔ a^2 + b^2 + c^2 + 2 * a * b * c + 1 ≥ 2 * (a * b + b * c + c * a) := by
  refine ⟨fun h ↦?_, fun h ↦?_⟩
  linarith [h]
  linarith [h]
theorem lean_workbook_1096_6 (a b c : ℝ) : a * b + b * c + c * a - a * b * c ≤ (c^2 + 1) / 2 + (a^2 + b^2) / 2 ↔ a^2 + b^2 + c^2 + 2 * a * b * c + 1 ≥ 2 * (a * b + b * c + c * a) := by
  constructor <;> intro h
  linarith
  linarith
theorem lean_workbook_1096_7 (a b c : ℝ) : a * b + b * c + c * a - a * b * c ≤ (c^2 + 1) / 2 + (a^2 + b^2) / 2 ↔ a^2 + b^2 + c^2 + 2 * a * b * c + 1 ≥ 2 * (a * b + b * c + c * a) := by
  field_simp [sub_eq_add_neg]
  ring_nf
  constructor <;> intro h <;> linarith
theorem lean_workbook_1096_8 (a b c : ℝ) : a * b + b * c + c * a - a * b * c ≤ (c^2 + 1) / 2 + (a^2 + b^2) / 2 ↔ a^2 + b^2 + c^2 + 2 * a * b * c + 1 ≥ 2 * (a * b + b * c + c * a) := by
  ring_nf
  refine ⟨fun h ↦?_, fun h ↦?_⟩
  linarith
  linarith
theorem lean_workbook_1096_9 (a b c : ℝ) : a * b + b * c + c * a - a * b * c ≤ (c^2 + 1) / 2 + (a^2 + b^2) / 2 ↔ a^2 + b^2 + c^2 + 2 * a * b * c + 1 ≥ 2 * (a * b + b * c + c * a) := by
  field_simp [sub_le_iff_le_add]
  ring_nf
  constructor <;> intro h
  linarith
  linarith
theorem lean_workbook_1096_10 (a b c : ℝ) : a * b + b * c + c * a - a * b * c ≤ (c^2 + 1) / 2 + (a^2 + b^2) / 2 ↔ a^2 + b^2 + c^2 + 2 * a * b * c + 1 ≥ 2 * (a * b + b * c + c * a) := by
  refine' ⟨fun h => _, fun h => _⟩
  linarith
  linarith
theorem lean_workbook_1096_11 (a b c : ℝ) : a * b + b * c + c * a - a * b * c ≤ (c^2 + 1) / 2 + (a^2 + b^2) / 2 ↔ a^2 + b^2 + c^2 + 2 * a * b * c + 1 ≥ 2 * (a * b + b * c + c * a) := by
  constructor <;> intro h <;> linarith
theorem lean_workbook_1096_12 (a b c : ℝ) : a * b + b * c + c * a - a * b * c ≤ (c^2 + 1) / 2 + (a^2 + b^2) / 2 ↔ a^2 + b^2 + c^2 + 2 * a * b * c + 1 ≥ 2 * (a * b + b * c + c * a) := by
  field_simp [mul_add, add_mul, add_assoc, add_comm, mul_comm, mul_assoc, mul_left_comm]
  ring_nf
  refine ⟨λ h ↦?_, λ h ↦?_⟩ <;> linarith
theorem lean_workbook_1096_13 (a b c : ℝ) : a * b + b * c + c * a - a * b * c ≤ (c^2 + 1) / 2 + (a^2 + b^2) / 2 ↔ a^2 + b^2 + c^2 + 2 * a * b * c + 1 ≥ 2 * (a * b + b * c + c * a) := by
  refine ⟨fun h ↦?_, fun h ↦?_⟩
  linarith
  linarith
theorem lean_workbook_1096_14 (a b c : ℝ) : a * b + b * c + c * a - a * b * c ≤ (c^2 + 1) / 2 + (a^2 + b^2) / 2 ↔ a^2 + b^2 + c^2 + 2 * a * b * c + 1 ≥ 2 * (a * b + b * c + c * a) := by
  rw [ge_iff_le]
  field_simp [mul_add, add_mul, mul_comm, mul_assoc, mul_left_comm]
  ring_nf
  constructor <;> intro h <;> linarith
theorem lean_workbook_1096_15 (a b c : ℝ) : a * b + b * c + c * a - a * b * c ≤ (c^2 + 1) / 2 + (a^2 + b^2) / 2 ↔ a^2 + b^2 + c^2 + 2 * a * b * c + 1 ≥ 2 * (a * b + b * c + c * a) := by
  constructor <;> intro h
  linarith
  ring_nf at h ⊢
  nlinarith
theorem lean_workbook_1096_16 (a b c : ℝ) : a * b + b * c + c * a - a * b * c ≤ (c^2 + 1) / 2 + (a^2 + b^2) / 2 ↔ a^2 + b^2 + c^2 + 2 * a * b * c + 1 ≥ 2 * (a * b + b * c + c * a) := by
  rw [ge_iff_le]
  constructor <;> intro h <;> linarith
theorem lean_workbook_1096_17 (a b c : ℝ) : a * b + b * c + c * a - a * b * c ≤ (c^2 + 1) / 2 + (a^2 + b^2) / 2 ↔ a^2 + b^2 + c^2 + 2 * a * b * c + 1 ≥ 2 * (a * b + b * c + c * a) := by
  field_simp [sq]
  constructor <;> intro h
  linarith
  linarith [h]
theorem lean_workbook_1096_18 (a b c : ℝ) : a * b + b * c + c * a - a * b * c ≤ (c^2 + 1) / 2 + (a^2 + b^2) / 2 ↔ a^2 + b^2 + c^2 + 2 * a * b * c + 1 ≥ 2 * (a * b + b * c + c * a) := by
  field_simp [add_comm]
  ring_nf
  constructor <;> intro h <;> linarith
theorem lean_workbook_1096_19 (a b c : ℝ) : a * b + b * c + c * a - a * b * c ≤ (c^2 + 1) / 2 + (a^2 + b^2) / 2 ↔ a^2 + b^2 + c^2 + 2 * a * b * c + 1 ≥ 2 * (a * b + b * c + c * a) := by
  field_simp [mul_add, add_mul]
  ring_nf
  constructor <;> intro h
  linarith
  nlinarith

theorem lean_workbook_1105_0 (n : ℕ) (hn : 0 < n) (x_n : ℝ) (hx_n : x_n = (3 + Real.sqrt 5)^n + (3 - Real.sqrt 5)^n) : 2^n ∣ x_n := by
  rw [hx_n]
  simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, Nat.mod_mod]
theorem lean_workbook_1105_1 (n : ℕ) (hn : 0 < n) (x_n : ℝ) (hx_n : x_n = (3 + Real.sqrt 5)^n + (3 - Real.sqrt 5)^n) : 2^n ∣ x_n := by
  rcases even_or_odd' n with ⟨m, rfl | rfl⟩ <;> simp [hx_n]
  all_goals ring_nf; norm_cast
theorem lean_workbook_1105_2 (n : ℕ) (hn : 0 < n) (x_n : ℝ) (hx_n : x_n = (3 + Real.sqrt 5)^n + (3 - Real.sqrt 5)^n) : 2^n ∣ x_n := by
  rcases even_or_odd n with ⟨m, rfl | rfl⟩ <;> simp [hx_n]
  all_goals ring_nf; simp [Nat.pow_succ]
theorem lean_workbook_1105_3 (n : ℕ) (hn : 0 < n) (x_n : ℝ) (hx_n : x_n = (3 + Real.sqrt 5)^n + (3 - Real.sqrt 5)^n) : 2^n ∣ x_n := by
  simp_rw [hx_n]
  simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, Nat.mod_mod]
theorem lean_workbook_1105_4 (n : ℕ) (hn : 0 < n) (x_n : ℝ) (hx_n : x_n = (3 + Real.sqrt 5)^n + (3 - Real.sqrt 5)^n) : 2^n ∣ x_n := by
  rw [hx_n]
  simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod]

theorem lean_workbook_1116_0 (a b c : ℝ) : a^4 + b^4 + c^4 ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 := by
  -- we can prove this by contradiction
  apply le_of_not_lt
  intro h
  -- The proof is by contradiction. Assume that the sum of the squares is greater than the sum of the fourth powers.
  let h1 := sq_nonneg (a^2 - b^2)
  let h2 := sq_nonneg (b^2 - c^2)
  let h3 := sq_nonneg (c^2 - a^2)
  linarith
theorem lean_workbook_1116_1 (a b c : ℝ) : a^4 + b^4 + c^4 ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 := by
  have h1 : 0 ≤ (a^2 - b^2)^2 := sq_nonneg (a^2 - b^2)
  have h2 : 0 ≤ (b^2 - c^2)^2 := sq_nonneg (b^2 - c^2)
  have h3 : 0 ≤ (c^2 - a^2)^2 := sq_nonneg (c^2 - a^2)
  linarith
theorem lean_workbook_1116_2 (a b c : ℝ) : a^4 + b^4 + c^4 ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 := by
  linarith only [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2)]
theorem lean_workbook_1116_3 (a b c : ℝ) : a^4 + b^4 + c^4 ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 := by
  have := sq_nonneg (a^2 - b^2)
  have := sq_nonneg (b^2 - c^2)
  have := sq_nonneg (c^2 - a^2)
  linarith
theorem lean_workbook_1116_4 (a b c : ℝ) : a^4 + b^4 + c^4 ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 := by
  have h1 : 0 ≤ (a^2 - b^2)^2 + (b^2 - c^2)^2 + (c^2 - a^2)^2 := by positivity
  linarith
theorem lean_workbook_1116_5 (a b c : ℝ) : a^4 + b^4 + c^4 ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 := by
  simp only [sq]
  linarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2)]
theorem lean_workbook_1116_6 (a b c : ℝ) : a^4 + b^4 + c^4 ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 := by
  have h₁ := sq_nonneg (a^2 - b^2)
  have h₂ := sq_nonneg (b^2 - c^2)
  have h₃ := sq_nonneg (c^2 - a^2)
  linarith
theorem lean_workbook_1116_7 (a b c : ℝ) : a^4 + b^4 + c^4 ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 := by
  nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2)]
theorem lean_workbook_1116_8 (a b c : ℝ) : a^4 + b^4 + c^4 ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 := by
  have le1 := sq_nonneg (a^2 - b^2)
  have le2 := sq_nonneg (b^2 - c^2)
  have le3 := sq_nonneg (c^2 - a^2)
  linarith
theorem lean_workbook_1116_9 (a b c : ℝ) : a^4 + b^4 + c^4 ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 := by
  simp [sq]
  have := sq_nonneg (a^2 - b^2)
  have := sq_nonneg (b^2 - c^2)
  have := sq_nonneg (c^2 - a^2)
  linarith
theorem lean_workbook_1116_10 (a b c : ℝ) : a^4 + b^4 + c^4 ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 := by
  have h₁ : 0 ≤ (a^2 - b^2)^2 := sq_nonneg _
  have h₂ : 0 ≤ (b^2 - c^2)^2 := sq_nonneg _
  have h₃ : 0 ≤ (c^2 - a^2)^2 := sq_nonneg _
  linarith
theorem lean_workbook_1116_11 (a b c : ℝ) : a^4 + b^4 + c^4 ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 := by
  have : 0 ≤ (a^2 - b^2)^2 + (b^2 - c^2)^2 + (c^2 - a^2)^2 := by positivity
  linarith
theorem lean_workbook_1116_12 (a b c : ℝ) : a^4 + b^4 + c^4 ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 := by
  have h1 := sq_nonneg (a^2 - b^2)
  have h2 := sq_nonneg (b^2 - c^2)
  have h3 := sq_nonneg (c^2 - a^2)
  linarith [h1, h2, h3]
theorem lean_workbook_1116_13 (a b c : ℝ) : a^4 + b^4 + c^4 ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 := by
  have h1: 0 ≤ (a^2 - b^2)^2 := sq_nonneg (a^2 - b^2)
  have h2: 0 ≤ (b^2 - c^2)^2 := sq_nonneg (b^2 - c^2)
  have h3: 0 ≤ (c^2 - a^2)^2 := sq_nonneg (c^2 - a^2)
  linarith
theorem lean_workbook_1116_14 (a b c : ℝ) : a^4 + b^4 + c^4 ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 := by
  linarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2)]
theorem lean_workbook_1116_15 (a b c : ℝ) : a^4 + b^4 + c^4 ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 := by
  have h0 := sq_nonneg (a^2 - b^2)
  have h1 := sq_nonneg (b^2 - c^2)
  have h2 := sq_nonneg (c^2 - a^2)
  linarith

theorem lean_workbook_1122_0 (n : ℕ) : choose (n + 1) 2 + n + 1 = choose (n + 2) 2 := by
  simp [choose_succ_succ, add_comm, add_left_comm, add_assoc, choose_symm_of_eq_add]
theorem lean_workbook_1122_1 (n : ℕ) : choose (n + 1) 2 + n + 1 = choose (n + 2) 2 := by
  simp [add_comm, add_assoc, add_left_comm, choose_succ_succ, add_choose]
theorem lean_workbook_1122_2 (n : ℕ) : choose (n + 1) 2 + n + 1 = choose (n + 2) 2 := by
  rw [add_comm]
  simp [add_assoc, choose_succ_succ, add_comm]
  ring_nf
theorem lean_workbook_1122_3 (n : ℕ) : choose (n + 1) 2 + n + 1 = choose (n + 2) 2 := by
  simp [Nat.choose_succ_succ, Nat.succ_eq_add_one, Nat.choose_symm_add]
  ring
theorem lean_workbook_1122_4 (n : ℕ) : choose (n + 1) 2 + n + 1 = choose (n + 2) 2 := by
  rw [add_comm]
  simp [Nat.choose_succ_succ, add_comm, add_left_comm, add_assoc]
theorem lean_workbook_1122_5 (n : ℕ) : choose (n + 1) 2 + n + 1 = choose (n + 2) 2 := by
  field_simp [choose_succ_succ, add_comm, add_left_comm, add_assoc]
theorem lean_workbook_1122_6 (n : ℕ) : choose (n + 1) 2 + n + 1 = choose (n + 2) 2 := by
  simp [choose_succ_succ, add_comm, add_left_comm, add_assoc, choose_symm_add]
theorem lean_workbook_1122_7 (n : ℕ) : choose (n + 1) 2 + n + 1 = choose (n + 2) 2 := by
  field_simp [add_comm]
  simp [choose_succ_succ, add_comm, add_left_comm, add_assoc]
theorem lean_workbook_1122_8 (n : ℕ) : choose (n + 1) 2 + n + 1 = choose (n + 2) 2 := by
  simp [choose_succ_succ, add_assoc, add_comm, add_left_comm]
theorem lean_workbook_1122_9 (n : ℕ) : choose (n + 1) 2 + n + 1 = choose (n + 2) 2 := by
  simp [choose_succ_succ, choose_two_right, add_comm, add_left_comm, add_assoc]
theorem lean_workbook_1122_10 (n : ℕ) : choose (n + 1) 2 + n + 1 = choose (n + 2) 2 := by
  field_simp [Nat.choose_succ_succ, Nat.choose_symm_add]
  ring
theorem lean_workbook_1122_11 (n : ℕ) : choose (n + 1) 2 + n + 1 = choose (n + 2) 2 := by
  rw [← add_comm]
  simp [choose_succ_succ, add_comm, add_left_comm, add_assoc]
theorem lean_workbook_1122_12 (n : ℕ) : choose (n + 1) 2 + n + 1 = choose (n + 2) 2 := by
  simp [choose_two_right, choose_succ_succ, add_comm, add_left_comm, add_assoc]
theorem lean_workbook_1122_13 (n : ℕ) : choose (n + 1) 2 + n + 1 = choose (n + 2) 2 := by
  rw [add_comm]
  simp [choose_succ_succ, add_comm, add_left_comm]
  ring
theorem lean_workbook_1122_14 (n : ℕ) : choose (n + 1) 2 + n + 1 = choose (n + 2) 2 := by
  rw [add_comm]
  simp [add_assoc, choose_succ_succ]
  ring
theorem lean_workbook_1122_15 (n : ℕ) : choose (n + 1) 2 + n + 1 = choose (n + 2) 2 := by
  rw [choose_succ_succ, add_comm]
  simp [add_assoc, choose_succ_succ, add_comm, add_left_comm]
theorem lean_workbook_1122_16 (n : ℕ) : choose (n + 1) 2 + n + 1 = choose (n + 2) 2 := by
  simp [Nat.choose_succ_succ, add_comm, add_left_comm, add_assoc]
theorem lean_workbook_1122_17 (n : ℕ) : choose (n + 1) 2 + n + 1 = choose (n + 2) 2 := by
  simp [Nat.choose_succ_succ, Nat.succ_eq_add_one, Nat.choose_succ_succ', add_comm, add_left_comm,
    add_assoc]
theorem lean_workbook_1122_18 (n : ℕ) : choose (n + 1) 2 + n + 1 = choose (n + 2) 2 := by
  simp [add_assoc, choose_succ_succ, add_comm, add_left_comm, add_assoc]

theorem lean_workbook_1130_0 : √((-1 : ℝ) ^ 2) = 1 := by
  simp [abs_of_nonneg]
theorem lean_workbook_1130_1 : √((-1 : ℝ) ^ 2) = 1 := by
  simp [pow_two, Real.sqrt_one]
theorem lean_workbook_1130_2 : √((-1 : ℝ) ^ 2) = 1 := by
  rw [neg_one_sq]
  norm_num [Real.sqrt_one]
theorem lean_workbook_1130_3 : √((-1 : ℝ) ^ 2) = 1 := by
  rw [Real.sqrt_eq_iff_sq_eq] <;> simp [pow_two]
theorem lean_workbook_1130_4 : √((-1 : ℝ) ^ 2) = 1 := by
  simp [abs_of_pos]
theorem lean_workbook_1130_5 : √((-1 : ℝ) ^ 2) = 1 := by
  rw [Real.sqrt_eq_iff_sq_eq]
  ring_nf
  norm_num
  exact le_of_lt zero_lt_one
theorem lean_workbook_1130_6 : √((-1 : ℝ) ^ 2) = 1 := by
  norm_num [sqrt_eq_iff_mul_self_eq_of_pos (by norm_num : (0 : ℝ) < 1)]
theorem lean_workbook_1130_7 : √((-1 : ℝ) ^ 2) = 1 := by
  rw [Real.sqrt_eq_iff_sq_eq]
  all_goals { norm_num }
theorem lean_workbook_1130_8 : √((-1 : ℝ) ^ 2) = 1 := by
  simp [sqrt_sq_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1)]
theorem lean_workbook_1130_9 : √((-1 : ℝ) ^ 2) = 1 := by
  simp [sqrt_eq_iff_mul_self_eq_of_pos]
theorem lean_workbook_1130_10 : √((-1 : ℝ) ^ 2) = 1 := by
  simp only [neg_one_sq, Real.sqrt_one]
theorem lean_workbook_1130_11 : √((-1 : ℝ) ^ 2) = 1 := by
  norm_num [Real.sqrt_sq_eq_abs, abs_of_nonneg]
theorem lean_workbook_1130_12 : √((-1 : ℝ) ^ 2) = 1 := by
  simp [sq, abs_of_nonneg]
theorem lean_workbook_1130_13 : √((-1 : ℝ) ^ 2) = 1 := by
  simp [sq, abs_of_pos]
theorem lean_workbook_1130_14 : √((-1 : ℝ) ^ 2) = 1 := by
  field_simp [sqrt_eq_iff_sq_eq]
theorem lean_workbook_1130_15 : √((-1 : ℝ) ^ 2) = 1 := by
  norm_num [sqrt_eq_iff_sq_eq]
theorem lean_workbook_1130_16 : √((-1 : ℝ) ^ 2) = 1 := by
  simp only [neg_sq, one_pow, Real.sqrt_one]
theorem lean_workbook_1130_17 : √((-1 : ℝ) ^ 2) = 1 := by
  simp [sq, pow_two]
theorem lean_workbook_1130_18 : √((-1 : ℝ) ^ 2) = 1 := by
  simp [sq, neg_mul_neg]
theorem lean_workbook_1130_19 : √((-1 : ℝ) ^ 2) = 1 := by
  rw[Real.sqrt_eq_iff_sq_eq] <;> norm_num
theorem lean_workbook_1130_20 : √((-1 : ℝ) ^ 2) = 1 := by
  simp [Real.sqrt_eq_iff_sq_eq]
theorem lean_workbook_1130_21 : √((-1 : ℝ) ^ 2) = 1 := by
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num

theorem lean_workbook_1155_0 {a b : ℕ} : Nat.lcm a b = a * b / Nat.gcd a b := by
  rw [← Int.natAbs_ofNat a, ← Int.natAbs_ofNat b]
  apply Int.lcm_def
theorem lean_workbook_1155_1 {a b : ℕ} : Nat.lcm a b = a * b / Nat.gcd a b := by
  simp [Nat.lcm]
theorem lean_workbook_1155_2 {a b : ℕ} : Nat.lcm a b = a * b / Nat.gcd a b := by
  cases a <;>  cases b <;> rfl
theorem lean_workbook_1155_3 {a b : ℕ} : Nat.lcm a b = a * b / Nat.gcd a b := by
  rw [← Int.natAbs_ofNat a, ← Int.natAbs_ofNat b]
  rfl

theorem lean_workbook_1160_0 (a b c d : ℝ) (ha : a + 4 * b + 9 * c + 16 * d = 25) (hb : 4 * a + 9 * b + 16 * c + 25 * d = 36) (hc : 9 * a + 16 * b + 25 * c + 36 * d = 49) : 16 * a + 25 * b + 36 * c + 49 * d = 64 := by
  simp only [add_comm, add_left_comm, add_assoc] at *
  linarith
theorem lean_workbook_1160_1 (a b c d : ℝ) (ha : a + 4 * b + 9 * c + 16 * d = 25) (hb : 4 * a + 9 * b + 16 * c + 25 * d = 36) (hc : 9 * a + 16 * b + 25 * c + 36 * d = 49) : 16 * a + 25 * b + 36 * c + 49 * d = 64 := by
  simp only [mul_comm] at *
  linarith
theorem lean_workbook_1160_2 (a b c d : ℝ) (ha : a + 4 * b + 9 * c + 16 * d = 25) (hb : 4 * a + 9 * b + 16 * c + 25 * d = 36) (hc : 9 * a + 16 * b + 25 * c + 36 * d = 49) : 16 * a + 25 * b + 36 * c + 49 * d = 64 := by
  repeat' linarith only [ha, hb, hc]
theorem lean_workbook_1160_3 (a b c d : ℝ) (ha : a + 4 * b + 9 * c + 16 * d = 25) (hb : 4 * a + 9 * b + 16 * c + 25 * d = 36) (hc : 9 * a + 16 * b + 25 * c + 36 * d = 49) : 16 * a + 25 * b + 36 * c + 49 * d = 64 := by
  simp only [add_assoc] at *
  linarith
theorem lean_workbook_1160_4 (a b c d : ℝ) (ha : a + 4 * b + 9 * c + 16 * d = 25) (hb : 4 * a + 9 * b + 16 * c + 25 * d = 36) (hc : 9 * a + 16 * b + 25 * c + 36 * d = 49) : 16 * a + 25 * b + 36 * c + 49 * d = 64 := by
  norm_num at *
  linarith
theorem lean_workbook_1160_5 (a b c d : ℝ) (ha : a + 4 * b + 9 * c + 16 * d = 25) (hb : 4 * a + 9 * b + 16 * c + 25 * d = 36) (hc : 9 * a + 16 * b + 25 * c + 36 * d = 49) : 16 * a + 25 * b + 36 * c + 49 * d = 64 := by
  norm_num at *
  linarith only [ha, hb, hc]
theorem lean_workbook_1160_6 (a b c d : ℝ) (ha : a + 4 * b + 9 * c + 16 * d = 25) (hb : 4 * a + 9 * b + 16 * c + 25 * d = 36) (hc : 9 * a + 16 * b + 25 * c + 36 * d = 49) : 16 * a + 25 * b + 36 * c + 49 * d = 64 := by
  linarith [ha.symm, hb.symm, hc.symm]
theorem lean_workbook_1160_7 (a b c d : ℝ) (ha : a + 4 * b + 9 * c + 16 * d = 25) (hb : 4 * a + 9 * b + 16 * c + 25 * d = 36) (hc : 9 * a + 16 * b + 25 * c + 36 * d = 49) : 16 * a + 25 * b + 36 * c + 49 * d = 64 := by
  simp [mul_comm] at *
  linarith
theorem lean_workbook_1160_8 (a b c d : ℝ) (ha : a + 4 * b + 9 * c + 16 * d = 25) (hb : 4 * a + 9 * b + 16 * c + 25 * d = 36) (hc : 9 * a + 16 * b + 25 * c + 36 * d = 49) : 16 * a + 25 * b + 36 * c + 49 * d = 64 := by
  linarith [ha, hb, hc, ha, hb, hc]
theorem lean_workbook_1160_9 (a b c d : ℝ) (ha : a + 4 * b + 9 * c + 16 * d = 25) (hb : 4 * a + 9 * b + 16 * c + 25 * d = 36) (hc : 9 * a + 16 * b + 25 * c + 36 * d = 49) : 16 * a + 25 * b + 36 * c + 49 * d = 64 := by
  simp [mul_add, add_mul, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm] at *
  linarith
theorem lean_workbook_1160_10 (a b c d : ℝ) (ha : a + 4 * b + 9 * c + 16 * d = 25) (hb : 4 * a + 9 * b + 16 * c + 25 * d = 36) (hc : 9 * a + 16 * b + 25 * c + 36 * d = 49) : 16 * a + 25 * b + 36 * c + 49 * d = 64 := by
  ring_nf at ha hb hc
  linarith
theorem lean_workbook_1160_11 (a b c d : ℝ) (ha : a + 4 * b + 9 * c + 16 * d = 25) (hb : 4 * a + 9 * b + 16 * c + 25 * d = 36) (hc : 9 * a + 16 * b + 25 * c + 36 * d = 49) : 16 * a + 25 * b + 36 * c + 49 * d = 64 := by
  linarith [ha, hb, hc]

theorem lean_workbook_1168_0 (a b c : ℝ) : (3 * (a + b) + (a + b) * (b + c) * (c + a) / (a + b + c) - 2 * (a + b + c)) ^ 2 ≥ 0 := by
  apply pow_two_nonneg
theorem lean_workbook_1168_1 (a b c : ℝ) : (3 * (a + b) + (a + b) * (b + c) * (c + a) / (a + b + c) - 2 * (a + b + c)) ^ 2 ≥ 0 := by
  simp only [sq_nonneg]
theorem lean_workbook_1168_2 (a b c : ℝ) : (3 * (a + b) + (a + b) * (b + c) * (c + a) / (a + b + c) - 2 * (a + b + c)) ^ 2 ≥ 0 := by
  simp [sub_nonneg, sq_nonneg]
theorem lean_workbook_1168_3 (a b c : ℝ) : (3 * (a + b) + (a + b) * (b + c) * (c + a) / (a + b + c) - 2 * (a + b + c)) ^ 2 ≥ 0 := by
  exact pow_two_nonneg _
theorem lean_workbook_1168_4 (a b c : ℝ) : (3 * (a + b) + (a + b) * (b + c) * (c + a) / (a + b + c) - 2 * (a + b + c)) ^ 2 ≥ 0 := by
  simp only [ge_iff_le, sq_nonneg]
theorem lean_workbook_1168_5 (a b c : ℝ) : (3 * (a + b) + (a + b) * (b + c) * (c + a) / (a + b + c) - 2 * (a + b + c)) ^ 2 ≥ 0 := by
  exact sq_nonneg _
theorem lean_workbook_1168_6 (a b c : ℝ) : (3 * (a + b) + (a + b) * (b + c) * (c + a) / (a + b + c) - 2 * (a + b + c)) ^ 2 ≥ 0 := by
  simp [sq_nonneg]
theorem lean_workbook_1168_7 (a b c : ℝ) : (3 * (a + b) + (a + b) * (b + c) * (c + a) / (a + b + c) - 2 * (a + b + c)) ^ 2 ≥ 0 := by
  norm_num
  apply pow_two_nonneg

theorem lean_workbook_1184_0 (f : ℕ → ℕ) (hf : ∀ x y : ℕ, f (x + y) = f x + f y + 1002) : f 2004 = 1002 → f 5555 = 4553 := by
  intro h
  linarith [hf 2004 5555, hf 2004 0, h]
theorem lean_workbook_1184_1 (f : ℕ → ℕ) (hf : ∀ x y : ℕ, f (x + y) = f x + f y + 1002) : f 2004 = 1002 → f 5555 = 4553 := by
  intro h1
  linarith [hf 2004 5555, hf 2004 0, hf 0 5555]
theorem lean_workbook_1184_2 (f : ℕ → ℕ) (hf : ∀ x y : ℕ, f (x + y) = f x + f y + 1002) : f 2004 = 1002 → f 5555 = 4553 := by
  intro h1
  have h2 := hf 2004 5555
  simp [h1] at h2
  linarith [hf 0 2004, hf 0 5555]

theorem lean_workbook_1230_0 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  apply And.intro
  all_goals norm_num
theorem lean_workbook_1230_1 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  refine ⟨?_,?_⟩
  exact (by norm_num : 3^16 % 17 = 1)
  exact (by norm_num : 9^30 % 31 = 1)
theorem lean_workbook_1230_2 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  norm_num [Nat.pow_succ]
theorem lean_workbook_1230_3 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  apply And.intro <;> ring
theorem lean_workbook_1230_4 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  norm_num [pow_succ, pow_zero, pow_one]
theorem lean_workbook_1230_5 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  refine' ⟨by norm_num [Nat.pow_mod], by norm_num [Nat.pow_mod]⟩
theorem lean_workbook_1230_6 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  simp [Nat.mod_eq_of_lt]
theorem lean_workbook_1230_7 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  norm_num [pow_succ, Nat.gcd]
theorem lean_workbook_1230_8 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  refine' ⟨_, _⟩
  all_goals norm_num
theorem lean_workbook_1230_9 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  simp [pow_succ]
theorem lean_workbook_1230_10 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  exact ⟨by rfl, by rfl⟩
theorem lean_workbook_1230_11 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  refine' ⟨by norm_num, by norm_num⟩
theorem lean_workbook_1230_12 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  norm_num [Nat.gcd_eq_gcd_ab]
theorem lean_workbook_1230_13 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  exact ⟨by norm_num, by norm_num⟩
theorem lean_workbook_1230_14 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  norm_num [Nat.modEq_zero_iff_dvd]
theorem lean_workbook_1230_15 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  norm_num [pow_succ, pow_mul, pow_one]
theorem lean_workbook_1230_16 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  simp [Nat.ModEq]
theorem lean_workbook_1230_17 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  simp (config := {decide := true}) [Nat.pow_succ]
theorem lean_workbook_1230_18 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  refine ⟨rfl,?_⟩
  norm_num
theorem lean_workbook_1230_19 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  refine' ⟨by decide, by decide⟩
theorem lean_workbook_1230_20 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  norm_num [Nat.pow_succ, Nat.pow_zero, Nat.pow_one]
theorem lean_workbook_1230_21 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  apply And.intro
  ring
  ring
theorem lean_workbook_1230_22 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  simp [Nat.modEq_iff_dvd]
theorem lean_workbook_1230_23 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  norm_num [pow_succ]
theorem lean_workbook_1230_24 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  exact ⟨by decide, by decide⟩
theorem lean_workbook_1230_25 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  norm_num [pow_succ, Nat.mul_mod, Nat.pow_mod]
theorem lean_workbook_1230_26 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  simp [Nat.gcd_eq_gcd_ab]
theorem lean_workbook_1230_27 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  norm_num [pow_succ, pow_zero, pow_one, mul_comm, mul_assoc, mul_left_comm]
theorem lean_workbook_1230_28 : (3^16) % 17 = 1 ∧ (9^30) % 31 = 1 := by
  simp only [Nat.pow_succ]
  norm_num

theorem lean_workbook_1232_0 : 11 * b ≡ 0 [ZMOD 7] → b ≡ 0 [ZMOD 7] := by
  simp only [Int.ModEq, Int.ofNat_mul, Int.ofNat_mod]
  omega
theorem lean_workbook_1232_1 : 11 * b ≡ 0 [ZMOD 7] → b ≡ 0 [ZMOD 7] := by
  intro h
  have h₁ := h
  rw [Int.ModEq] at h₁ ⊢
  omega
theorem lean_workbook_1232_2 : 11 * b ≡ 0 [ZMOD 7] → b ≡ 0 [ZMOD 7] := by
  simp [Int.modEq_iff_dvd, mul_comm]
  intro h
  omega
theorem lean_workbook_1232_3 : 11 * b ≡ 0 [ZMOD 7] → b ≡ 0 [ZMOD 7] := by
  simp [Int.ModEq]
  intro h
  omega

theorem lean_workbook_1244_0 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y) * (y + z) * (z + x) ≥ (8 / 9) * (x + y + z) * (x * y + y * z + z * x) := by
  simp [add_comm, add_left_comm]
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_1244_1 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y) * (y + z) * (z + x) ≥ (8 / 9) * (x + y + z) * (x * y + y * z + z * x) := by
  simp [add_mul]
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
theorem lean_workbook_1244_2 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y) * (y + z) * (z + x) ≥ (8 / 9) * (x + y + z) * (x * y + y * z + z * x) := by
  ring_nf
  nlinarith [sq_nonneg (x + y + z), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_1244_3 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y) * (y + z) * (z + x) ≥ (8 / 9) * (x + y + z) * (x * y + y * z + z * x) := by
  nlinarith [sq_nonneg (x + y + z), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x - y)]
theorem lean_workbook_1244_4 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y) * (y + z) * (z + x) ≥ (8 / 9) * (x + y + z) * (x * y + y * z + z * x) := by
  simp [add_mul, mul_add]
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]

theorem lean_workbook_1257_0 (a b c : ℝ) (ha : a ^ 2 + b ^ 2 + c ^ 2 = 3) : (b + 1) * (a + b + 1) + (c + 1) * (b + c + 1) + (a + 1) * (c + a + 1) = (1 / 2) * (a + b + c + 3) ^ 2 := by
  simp [add_mul, mul_add]
  field_simp [ha]
  linarith
theorem lean_workbook_1257_1 (a b c : ℝ) (ha : a ^ 2 + b ^ 2 + c ^ 2 = 3) : (b + 1) * (a + b + 1) + (c + 1) * (b + c + 1) + (a + 1) * (c + a + 1) = (1 / 2) * (a + b + c + 3) ^ 2 := by
  rw [add_assoc] at ha ⊢
  field_simp [ha]
  linarith
theorem lean_workbook_1257_2 (a b c : ℝ) (ha : a ^ 2 + b ^ 2 + c ^ 2 = 3) : (b + 1) * (a + b + 1) + (c + 1) * (b + c + 1) + (a + 1) * (c + a + 1) = (1 / 2) * (a + b + c + 3) ^ 2 := by
  field_simp [pow_two] at ha ⊢
  linarith
theorem lean_workbook_1257_3 (a b c : ℝ) (ha : a ^ 2 + b ^ 2 + c ^ 2 = 3) : (b + 1) * (a + b + 1) + (c + 1) * (b + c + 1) + (a + 1) * (c + a + 1) = (1 / 2) * (a + b + c + 3) ^ 2 := by
  linarith only [ha]
theorem lean_workbook_1257_4 (a b c : ℝ) (ha : a ^ 2 + b ^ 2 + c ^ 2 = 3) : (b + 1) * (a + b + 1) + (c + 1) * (b + c + 1) + (a + 1) * (c + a + 1) = (1 / 2) * (a + b + c + 3) ^ 2 := by
  field_simp [add_assoc]
  linarith [ha]
theorem lean_workbook_1257_5 (a b c : ℝ) (ha : a ^ 2 + b ^ 2 + c ^ 2 = 3) : (b + 1) * (a + b + 1) + (c + 1) * (b + c + 1) + (a + 1) * (c + a + 1) = (1 / 2) * (a + b + c + 3) ^ 2 := by
  field_simp [add_assoc, add_comm, add_left_comm]
  linarith [ha]
theorem lean_workbook_1257_6 (a b c : ℝ) (ha : a ^ 2 + b ^ 2 + c ^ 2 = 3) : (b + 1) * (a + b + 1) + (c + 1) * (b + c + 1) + (a + 1) * (c + a + 1) = (1 / 2) * (a + b + c + 3) ^ 2 := by
  field_simp [sq]
  linarith [ha, ha, ha]
theorem lean_workbook_1257_7 (a b c : ℝ) (ha : a ^ 2 + b ^ 2 + c ^ 2 = 3) : (b + 1) * (a + b + 1) + (c + 1) * (b + c + 1) + (a + 1) * (c + a + 1) = (1 / 2) * (a + b + c + 3) ^ 2 := by
  field_simp [pow_two]
  ring_nf at *
  linarith [ha]
theorem lean_workbook_1257_8 (a b c : ℝ) (ha : a ^ 2 + b ^ 2 + c ^ 2 = 3) : (b + 1) * (a + b + 1) + (c + 1) * (b + c + 1) + (a + 1) * (c + a + 1) = (1 / 2) * (a + b + c + 3) ^ 2 := by
  field_simp [sq]
  linarith only [ha]
theorem lean_workbook_1257_9 (a b c : ℝ) (ha : a ^ 2 + b ^ 2 + c ^ 2 = 3) : (b + 1) * (a + b + 1) + (c + 1) * (b + c + 1) + (a + 1) * (c + a + 1) = (1 / 2) * (a + b + c + 3) ^ 2 := by
  field_simp [mul_add, add_mul, mul_comm, mul_assoc, mul_left_comm]
  linarith [ha]
theorem lean_workbook_1257_10 (a b c : ℝ) (ha : a ^ 2 + b ^ 2 + c ^ 2 = 3) : (b + 1) * (a + b + 1) + (c + 1) * (b + c + 1) + (a + 1) * (c + a + 1) = (1 / 2) * (a + b + c + 3) ^ 2 := by
  field_simp [sq]
  linarith [ha]
theorem lean_workbook_1257_11 (a b c : ℝ) (ha : a ^ 2 + b ^ 2 + c ^ 2 = 3) : (b + 1) * (a + b + 1) + (c + 1) * (b + c + 1) + (a + 1) * (c + a + 1) = (1 / 2) * (a + b + c + 3) ^ 2 := by
  field_simp [add_assoc]
  ring_nf
  linarith
theorem lean_workbook_1257_12 (a b c : ℝ) (ha : a ^ 2 + b ^ 2 + c ^ 2 = 3) : (b + 1) * (a + b + 1) + (c + 1) * (b + c + 1) + (a + 1) * (c + a + 1) = (1 / 2) * (a + b + c + 3) ^ 2 := by
  field_simp [sq]
  linarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, ha]
theorem lean_workbook_1257_13 (a b c : ℝ) (ha : a ^ 2 + b ^ 2 + c ^ 2 = 3) : (b + 1) * (a + b + 1) + (c + 1) * (b + c + 1) + (a + 1) * (c + a + 1) = (1 / 2) * (a + b + c + 3) ^ 2 := by
  nlinarith [ha, show (1:ℝ) = 1/2 + 1/2 by norm_num]
theorem lean_workbook_1257_14 (a b c : ℝ) (ha : a ^ 2 + b ^ 2 + c ^ 2 = 3) : (b + 1) * (a + b + 1) + (c + 1) * (b + c + 1) + (a + 1) * (c + a + 1) = (1 / 2) * (a + b + c + 3) ^ 2 := by
  field_simp [add_mul, mul_add, mul_comm, mul_left_comm]
  ring_nf at ha ⊢
  linarith [ha]
theorem lean_workbook_1257_15 (a b c : ℝ) (ha : a ^ 2 + b ^ 2 + c ^ 2 = 3) : (b + 1) * (a + b + 1) + (c + 1) * (b + c + 1) + (a + 1) * (c + a + 1) = (1 / 2) * (a + b + c + 3) ^ 2 := by
  field_simp [add_comm]
  ring_nf
  norm_num
  linarith [ha]
theorem lean_workbook_1257_16 (a b c : ℝ) (ha : a ^ 2 + b ^ 2 + c ^ 2 = 3) : (b + 1) * (a + b + 1) + (c + 1) * (b + c + 1) + (a + 1) * (c + a + 1) = (1 / 2) * (a + b + c + 3) ^ 2 := by
  linarith [ha]

theorem lean_workbook_1260_0 (a b c : ℝ) : a^4 + b^4 + c^4 ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 := by
  ring_nf
  nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2)]
theorem lean_workbook_1260_1 (a b c : ℝ) : a^4 + b^4 + c^4 ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 := by
  linarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2)]
theorem lean_workbook_1260_2 (a b c : ℝ) : a^4 + b^4 + c^4 ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 := by
  have := sq_nonneg (a^2 - b^2)
  linarith [sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2)]
theorem lean_workbook_1260_3 (a b c : ℝ) : a^4 + b^4 + c^4 ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 := by
  have h₁ := sq_nonneg (a^2 - b^2)
  have h₂ := sq_nonneg (b^2 - c^2)
  have h₃ := sq_nonneg (c^2 - a^2)
  linarith
theorem lean_workbook_1260_4 (a b c : ℝ) : a^4 + b^4 + c^4 ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 := by
  have h1 := sq_nonneg (a^2 - b^2)
  have h2 := sq_nonneg (b^2 - c^2)
  have h3 := sq_nonneg (a^2 - c^2)
  linarith
theorem lean_workbook_1260_5 (a b c : ℝ) : a^4 + b^4 + c^4 ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 := by
  have h₁ : 0 ≤ (a^2 - b^2)^2 := sq_nonneg (a^2 - b^2)
  have h₂ : 0 ≤ (b^2 - c^2)^2 := sq_nonneg (b^2 - c^2)
  have h₃ : 0 ≤ (c^2 - a^2)^2 := sq_nonneg (c^2 - a^2)
  linarith
theorem lean_workbook_1260_6 (a b c : ℝ) : a^4 + b^4 + c^4 ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 := by
  have := sq_nonneg (a^2 - b^2)
  have := sq_nonneg (b^2 - c^2)
  have := sq_nonneg (c^2 - a^2)
  linarith
theorem lean_workbook_1260_7 (a b c : ℝ) : a^4 + b^4 + c^4 ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 := by
  have := sq_nonneg (a^2 - b^2)
  have := sq_nonneg (b^2 - c^2)
  have := sq_nonneg (a^2 - c^2)
  linarith
theorem lean_workbook_1260_8 (a b c : ℝ) : a^4 + b^4 + c^4 ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 := by
  linarith only [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2)]
theorem lean_workbook_1260_9 (a b c : ℝ) : a^4 + b^4 + c^4 ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 := by
  have h0 := sq_nonneg (a^2 - b^2)
  have h1 := sq_nonneg (b^2 - c^2)
  have h2 := sq_nonneg (a^2 - c^2)
  linarith
theorem lean_workbook_1260_10 (a b c : ℝ) : a^4 + b^4 + c^4 ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 := by
  have : 0 ≤ (a^2 - b^2)^2 + (b^2 - c^2)^2 + (c^2 - a^2)^2 := by positivity
  linarith

theorem lean_workbook_1264_0 : 2 + A + B + 8 ≡ 1 + A + B [ZMOD 3] := by
  simp (config := { contextual := true }) [Int.modEq_iff_dvd, Int.sub_emod]
  ring_nf
  norm_num
theorem lean_workbook_1264_1 : 2 + A + B + 8 ≡ 1 + A + B [ZMOD 3] := by
  simp only [Int.ModEq, Int.ofNat_add]
  ring_nf
  simp [Int.add_emod, Int.mul_emod, Int.modEq_iff_dvd]
theorem lean_workbook_1264_2 : 2 + A + B + 8 ≡ 1 + A + B [ZMOD 3] := by
  simp only [Int.modEq_iff_dvd, sub_sub]
  ring_nf
  simp [Int.dvd_iff_emod_eq_zero]
theorem lean_workbook_1264_3 : 2 + A + B + 8 ≡ 1 + A + B [ZMOD 3] := by
  simp only [Int.ModEq]
  ring_nf
  omega
theorem lean_workbook_1264_4 : 2 + A + B + 8 ≡ 1 + A + B [ZMOD 3] := by
  simp only [Int.modEq_iff_dvd]
  ring_nf
  simp [Int.dvd_iff_emod_eq_zero]
theorem lean_workbook_1264_5 : 2 + A + B + 8 ≡ 1 + A + B [ZMOD 3] := by
  simp only [Int.modEq_iff_dvd, Int.ofNat_add]
  ring_nf
  norm_num
theorem lean_workbook_1264_6 : 2 + A + B + 8 ≡ 1 + A + B [ZMOD 3] := by
  simp [Int.ModEq]
  ring_nf
  simp [Int.add_emod, Int.mul_emod]
theorem lean_workbook_1264_7 : 2 + A + B + 8 ≡ 1 + A + B [ZMOD 3] := by
  simp [Int.ModEq]
  ring_nf
  simp [Int.add_emod]
theorem lean_workbook_1264_8 : 2 + A + B + 8 ≡ 1 + A + B [ZMOD 3] := by
  simp [Int.modEq_iff_dvd]
  ring_nf
  norm_num
theorem lean_workbook_1264_9 : 2 + A + B + 8 ≡ 1 + A + B [ZMOD 3] := by
  simp only [Int.modEq_iff_dvd, Int.ofNat_add]
  ring_nf
  simp [Int.dvd_iff_emod_eq_zero]
theorem lean_workbook_1264_10 : 2 + A + B + 8 ≡ 1 + A + B [ZMOD 3] := by
  simp [Nat.ModEq, Int.ModEq]
  ring_nf
  omega
theorem lean_workbook_1264_11 : 2 + A + B + 8 ≡ 1 + A + B [ZMOD 3] := by
  simp only [Int.ModEq]
  omega
theorem lean_workbook_1264_12 : 2 + A + B + 8 ≡ 1 + A + B [ZMOD 3] := by
  simp only [Int.modEq_iff_dvd, Int.ofNat_add, Int.ofNat_one]
  ring_nf
  norm_num
theorem lean_workbook_1264_13 : 2 + A + B + 8 ≡ 1 + A + B [ZMOD 3] := by
  simp only [Int.ModEq]
  ring_nf
  simp [Int.add_emod]

theorem lean_workbook_1265_0 : (10 : ℝ)⁻¹ = 0.1 := by
  norm_num [div_eq_mul_inv, div_eq_mul_inv]
theorem lean_workbook_1265_1 : (10 : ℝ)⁻¹ = 0.1 := by
  norm_num [show (0.1 : ℝ) = 10⁻¹ by norm_num]
theorem lean_workbook_1265_2 : (10 : ℝ)⁻¹ = 0.1 := by
  norm_num [show (10 : ℝ)⁻¹ = 1 / 10 by rw [inv_eq_one_div]]
theorem lean_workbook_1265_3 : (10 : ℝ)⁻¹ = 0.1 := by
  rw [inv_eq_one_div]
  norm_num
theorem lean_workbook_1265_4 : (10 : ℝ)⁻¹ = 0.1 := by
  norm_num [show (10 : ℝ) = 10 by norm_num]
theorem lean_workbook_1265_5 : (10 : ℝ)⁻¹ = 0.1 := by
  norm_num [show (10 : ℝ) = (10 : ℚ) by norm_num, show (0.1 : ℝ) = (0.1 : ℚ) by norm_num]
theorem lean_workbook_1265_6 : (10 : ℝ)⁻¹ = 0.1 := by
  norm_num [show (10 : ℝ) = (10 : ℚ) by norm_cast]
theorem lean_workbook_1265_7 : (10 : ℝ)⁻¹ = 0.1 := by
  norm_num [inv_eq_one_div]
theorem lean_workbook_1265_8 : (10 : ℝ)⁻¹ = 0.1 := by
  norm_num [show (0.1 : ℝ) = (10 : ℝ)⁻¹ by norm_num]
theorem lean_workbook_1265_9 : (10 : ℝ)⁻¹ = 0.1 := by
  norm_num [show (10 : ℝ) = (10 : ℚ) by norm_num]
theorem lean_workbook_1265_10 : (10 : ℝ)⁻¹ = 0.1 := by
  simp only [one_div, Nat.cast_ofNat, inv_eq_iff_eq_inv]
  norm_num
theorem lean_workbook_1265_11 : (10 : ℝ)⁻¹ = 0.1 := by
  norm_num [show (10 : ℝ)⁻¹ = 0.1  by norm_num]
theorem lean_workbook_1265_12 : (10 : ℝ)⁻¹ = 0.1 := by
  simp [show (10 : ℝ) = 10 by norm_num, show (0.1 : ℝ) = 1 / 10 by norm_num]
theorem lean_workbook_1265_13 : (10 : ℝ)⁻¹ = 0.1 := by
  rw [show (0.1 : ℝ) = 10⁻¹ by norm_num]
theorem lean_workbook_1265_14 : (10 : ℝ)⁻¹ = 0.1 := by
  norm_num [show (10 : ℝ) = (10 : ℚ) by norm_cast, show (0.1 : ℝ) = (0.1 : ℚ) by norm_cast]
theorem lean_workbook_1265_15 : (10 : ℝ)⁻¹ = 0.1 := by
  norm_num [div_eq_mul_inv, mul_comm, mul_assoc]
theorem lean_workbook_1265_16 : (10 : ℝ)⁻¹ = 0.1 := by
  norm_num [div_eq_mul_inv, mul_comm]
theorem lean_workbook_1265_17 : (10 : ℝ)⁻¹ = 0.1 := by
  norm_num [div_eq_inv_mul]
theorem lean_workbook_1265_18 : (10 : ℝ)⁻¹ = 0.1 := by
  norm_num [show (10 : ℝ)⁻¹ = 0.1 by norm_num]

theorem lean_workbook_1267_0 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : a / (a^2 + 8 * b * c)^(1 / 3) + b / (b^2 + 8 * c * a)^(1 / 3) + c / (c^2 + 8 * a * b)^(1 / 3) >= 1 := by
  norm_num
  linarith [ha, hb, hc, habc]
theorem lean_workbook_1267_1 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : a / (a^2 + 8 * b * c)^(1 / 3) + b / (b^2 + 8 * c * a)^(1 / 3) + c / (c^2 + 8 * a * b)^(1 / 3) >= 1 := by
  eta_reduce at *
  eta_reduce at *
  eta_reduce at a b c ha hb hc habc ⊢
  norm_num
  nlinarith
theorem lean_workbook_1267_2 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : a / (a^2 + 8 * b * c)^(1 / 3) + b / (b^2 + 8 * c * a)^(1 / 3) + c / (c^2 + 8 * a * b)^(1 / 3) >= 1 := by
  ring_nf
  linarith [ha, hb, hc, habc]
theorem lean_workbook_1267_3 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : a / (a^2 + 8 * b * c)^(1 / 3) + b / (b^2 + 8 * c * a)^(1 / 3) + c / (c^2 + 8 * a * b)^(1 / 3) >= 1 := by
  simp [div_eq_mul_inv, ← mul_add]
  nlinarith [ha, hb, hc, habc]
theorem lean_workbook_1267_4 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : a / (a^2 + 8 * b * c)^(1 / 3) + b / (b^2 + 8 * c * a)^(1 / 3) + c / (c^2 + 8 * a * b)^(1 / 3) >= 1 := by
  ring_nf at *
  norm_cast at *
  nlinarith [ha, hb, hc, habc]
theorem lean_workbook_1267_5 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : a / (a^2 + 8 * b * c)^(1 / 3) + b / (b^2 + 8 * c * a)^(1 / 3) + c / (c^2 + 8 * a * b)^(1 / 3) >= 1 := by
  ring_nf at ha hb hc habc ⊢
  nlinarith
theorem lean_workbook_1267_6 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : a / (a^2 + 8 * b * c)^(1 / 3) + b / (b^2 + 8 * c * a)^(1 / 3) + c / (c^2 + 8 * a * b)^(1 / 3) >= 1 := by
  ring_nf at *
  field_simp [ha.ne', hb.ne', hc.ne']
  nlinarith [ha, hb, hc, habc]
theorem lean_workbook_1267_7 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : a / (a^2 + 8 * b * c)^(1 / 3) + b / (b^2 + 8 * c * a)^(1 / 3) + c / (c^2 + 8 * a * b)^(1 / 3) >= 1 := by
  ring_nf
  norm_num
  nlinarith [ha, hb, hc, habc]
theorem lean_workbook_1267_8 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : a / (a^2 + 8 * b * c)^(1 / 3) + b / (b^2 + 8 * c * a)^(1 / 3) + c / (c^2 + 8 * a * b)^(1 / 3) >= 1 := by
  simp [ge_iff_le]
  nlinarith [ha, hb, hc, habc]
theorem lean_workbook_1267_9 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : a / (a^2 + 8 * b * c)^(1 / 3) + b / (b^2 + 8 * c * a)^(1 / 3) + c / (c^2 + 8 * a * b)^(1 / 3) >= 1 := by
  ring_nf at habc ⊢
  field_simp [ha.ne', hb.ne', hc.ne']
  nlinarith
theorem lean_workbook_1267_10 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : a / (a^2 + 8 * b * c)^(1 / 3) + b / (b^2 + 8 * c * a)^(1 / 3) + c / (c^2 + 8 * a * b)^(1 / 3) >= 1 := by
  norm_num [ha, hb, hc, habc]

theorem lean_workbook_1299_0 (x y z: ℝ) : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := by
  simp [add_sq, mul_add, add_mul]
  linarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_1299_1 (x y z: ℝ) : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := by
  simp [add_sq]
  linarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]
theorem lean_workbook_1299_2 (x y z: ℝ) : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_1299_3 (x y z: ℝ) : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := by
  have h1 := sq_nonneg (x - y)
  have h2 := sq_nonneg (y - z)
  have h3 := sq_nonneg (z - x)
  linarith
theorem lean_workbook_1299_4 (x y z: ℝ) : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := by
  rw [sq]
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_1299_5 (x y z: ℝ) : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := by
  rw [sq]
  have h1 := sq_nonneg (x - y)
  have h2 := sq_nonneg (y - z)
  have h3 := sq_nonneg (z - x)
  linarith [h1, h2, h3]
theorem lean_workbook_1299_6 (x y z: ℝ) : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := by
  have := sq_nonneg (x - y)
  have := sq_nonneg (y - z)
  have := sq_nonneg (x - z)
  linarith
theorem lean_workbook_1299_7 (x y z: ℝ) : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := by
  have h1 : 0 ≤ (x - y)^2 + (y - z)^2 + (z - x)^2 := by nlinarith
  nlinarith
theorem lean_workbook_1299_8 (x y z: ℝ) : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := by
  have h0 := sq_nonneg (x - y)
  have h1 := sq_nonneg (y - z)
  have h2 := sq_nonneg (z - x)
  linarith
theorem lean_workbook_1299_9 (x y z: ℝ) : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := by
  simp [sq, add_assoc, add_comm, add_left_comm]
  linarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_1299_10 (x y z: ℝ) : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := by
  simp [add_mul, mul_add, mul_comm, mul_left_comm, sq]
  linarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_1299_11 (x y z: ℝ) : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := by
  simp [add_mul, mul_add, mul_comm, mul_assoc, pow_two]
  linarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_1299_12 (x y z: ℝ) : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := by
  simp [sq]
  linarith only [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_1299_13 (x y z: ℝ) : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := by
  have := sq_nonneg (x - y)
  have := sq_nonneg (y - z)
  have := sq_nonneg (z - x)
  linarith
theorem lean_workbook_1299_14 (x y z: ℝ) : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := by
  ring_nf
  norm_cast
  linarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_1299_15 (x y z: ℝ) : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := by
  rw [sq, add_assoc, add_assoc]
  have h1 := sq_nonneg (x - y)
  have h2 := sq_nonneg (y - z)
  have h3 := sq_nonneg (z - x)
  linarith
theorem lean_workbook_1299_16 (x y z: ℝ) : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := by
  eta_reduce at *
  rw [sq]
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_1299_17 (x y z: ℝ) : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := by
  ring_nf
  linarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_1299_18 (x y z: ℝ) : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := by
  ring_nf
  ring_nf
  ring_nf
  linarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]
theorem lean_workbook_1299_19 (x y z: ℝ) : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := by
  nlinarith [sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x - y)]
theorem lean_workbook_1299_20 (x y z: ℝ) : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := by
  simp [sq]
  linarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_1299_21 (x y z: ℝ) : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := by
  nlinarith [sq_nonneg (x + y + z), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_1299_22 (x y z: ℝ) : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := by
  rw [sq, add_mul_self_eq]
  linarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]

theorem lean_workbook_1336_0 (b c : ℝ) : |b - c| = Real.sqrt (2 * (b^2 + c^2) - (b + c)^2) := by
  rw [← Real.sqrt_sq_eq_abs]
  field_simp [sq]
  ring_nf
theorem lean_workbook_1336_1 (b c : ℝ) : |b - c| = Real.sqrt (2 * (b^2 + c^2) - (b + c)^2) := by
  rw [← Real.sqrt_sq_eq_abs]
  congr
  ring
theorem lean_workbook_1336_2 (b c : ℝ) : |b - c| = Real.sqrt (2 * (b^2 + c^2) - (b + c)^2) := by
  rw [← Real.sqrt_sq_eq_abs]
  congr 1
  ring

theorem lean_workbook_1341_0 (b d c : ℝ) : (b * d + c) * (d * c + b) ≤ (1 / 4) * (d + 1)^2 * (b + c)^2 := by
  have h1 := sq_nonneg (b * d + c - (d + 1) * (b + c) / 2)
  linarith
theorem lean_workbook_1341_1 (b d c : ℝ) : (b * d + c) * (d * c + b) ≤ (1 / 4) * (d + 1)^2 * (b + c)^2 := by
  have := sq_nonneg (b - c)
  have := sq_nonneg (d - 1)
  nlinarith
theorem lean_workbook_1341_2 (b d c : ℝ) : (b * d + c) * (d * c + b) ≤ (1 / 4) * (d + 1)^2 * (b + c)^2 := by
  linarith [sq_nonneg (b * d + c - d * c - b)]
theorem lean_workbook_1341_3 (b d c : ℝ) : (b * d + c) * (d * c + b) ≤ (1 / 4) * (d + 1)^2 * (b + c)^2 := by
  have := sq_nonneg (b * d + c - (d * c + b))
  linarith
theorem lean_workbook_1341_4 (b d c : ℝ) : (b * d + c) * (d * c + b) ≤ (1 / 4) * (d + 1)^2 * (b + c)^2 := by
  nlinarith [sq_nonneg (b * d + c - (d * c + b))]
theorem lean_workbook_1341_5 (b d c : ℝ) : (b * d + c) * (d * c + b) ≤ (1 / 4) * (d + 1)^2 * (b + c)^2 := by
  have := sq_nonneg (b * d + c - (d + 1) * (b + c) / 2)
  linarith
theorem lean_workbook_1341_6 (b d c : ℝ) : (b * d + c) * (d * c + b) ≤ (1 / 4) * (d + 1)^2 * (b + c)^2 := by
  have := sq_nonneg (b * d + c - d * c - b)
  linarith
theorem lean_workbook_1341_7 (b d c : ℝ) : (b * d + c) * (d * c + b) ≤ (1 / 4) * (d + 1)^2 * (b + c)^2 := by
  have h1 : 0 ≤ (b - c)^2 + (d - 1)^2 := by nlinarith
  field_simp [h1]
  nlinarith
theorem lean_workbook_1341_8 (b d c : ℝ) : (b * d + c) * (d * c + b) ≤ (1 / 4) * (d + 1)^2 * (b + c)^2 := by
  linarith [sq_nonneg (b * d + c - (1 / 2) * (d + 1) * (b + c))]

theorem lean_workbook_1343_0 (a d : ℝ) : a^4-14*a^2*d^2+49*d^4 ≥ 0 ↔ (a^2-7*d^2)^2 ≥ 0 := by
  constructor <;> intro h
  nlinarith
  nlinarith [h]
theorem lean_workbook_1343_1 (a d : ℝ) : a^4-14*a^2*d^2+49*d^4 ≥ 0 ↔ (a^2-7*d^2)^2 ≥ 0 := by
  simp only [sq, sub_mul, mul_sub, mul_add, add_mul, sub_add, sub_sub, sub_zero, add_sub, mul_one,
    mul_zero, sub_self, zero_add, zero_sub, mul_comm, mul_assoc, mul_left_comm]
  exact ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩
theorem lean_workbook_1343_2 (a d : ℝ) : a^4-14*a^2*d^2+49*d^4 ≥ 0 ↔ (a^2-7*d^2)^2 ≥ 0 := by
  rw [sq, sq]
  ring_nf
theorem lean_workbook_1343_3 (a d : ℝ) : a^4-14*a^2*d^2+49*d^4 ≥ 0 ↔ (a^2-7*d^2)^2 ≥ 0 := by
  exact ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩
theorem lean_workbook_1343_4 (a d : ℝ) : a^4-14*a^2*d^2+49*d^4 ≥ 0 ↔ (a^2-7*d^2)^2 ≥ 0 := by
  refine' ⟨fun h => by nlinarith [h], fun h => by nlinarith [h]⟩
theorem lean_workbook_1343_5 (a d : ℝ) : a^4-14*a^2*d^2+49*d^4 ≥ 0 ↔ (a^2-7*d^2)^2 ≥ 0 := by
  field_simp [sub_sq, add_assoc]
  ring_nf
theorem lean_workbook_1343_6 (a d : ℝ) : a^4-14*a^2*d^2+49*d^4 ≥ 0 ↔ (a^2-7*d^2)^2 ≥ 0 := by
  simp only [sub_nonneg, sq]
  ring_nf
theorem lean_workbook_1343_7 (a d : ℝ) : a^4-14*a^2*d^2+49*d^4 ≥ 0 ↔ (a^2-7*d^2)^2 ≥ 0 := by
  simp [sub_nonneg]
  simp only [pow_two]
  ring_nf
theorem lean_workbook_1343_8 (a d : ℝ) : a^4-14*a^2*d^2+49*d^4 ≥ 0 ↔ (a^2-7*d^2)^2 ≥ 0 := by
  constructor <;> intro h
  linarith [h]
  nlinarith [h]
theorem lean_workbook_1343_9 (a d : ℝ) : a^4-14*a^2*d^2+49*d^4 ≥ 0 ↔ (a^2-7*d^2)^2 ≥ 0 := by
  simp only [sub_sq, sub_add, sub_le_iff_le_add, zero_add, mul_pow, pow_add, pow_one]
  ring_nf
theorem lean_workbook_1343_10 (a d : ℝ) : a^4-14*a^2*d^2+49*d^4 ≥ 0 ↔ (a^2-7*d^2)^2 ≥ 0 := by
  field_simp [sub_eq_add_neg]
  ring_nf
theorem lean_workbook_1343_11 (a d : ℝ) : a^4-14*a^2*d^2+49*d^4 ≥ 0 ↔ (a^2-7*d^2)^2 ≥ 0 := by
  constructor
  intro h
  nlinarith
  intro h
  nlinarith [h]
theorem lean_workbook_1343_12 (a d : ℝ) : a^4-14*a^2*d^2+49*d^4 ≥ 0 ↔ (a^2-7*d^2)^2 ≥ 0 := by
  simp [sub_nonneg]
  ring_nf
theorem lean_workbook_1343_13 (a d : ℝ) : a^4-14*a^2*d^2+49*d^4 ≥ 0 ↔ (a^2-7*d^2)^2 ≥ 0 := by
  refine ⟨fun h ↦?_, fun h ↦?_⟩
  nlinarith
  nlinarith
theorem lean_workbook_1343_14 (a d : ℝ) : a^4-14*a^2*d^2+49*d^4 ≥ 0 ↔ (a^2-7*d^2)^2 ≥ 0 := by
  simp only [sub_nonneg, pow_two]
  ring_nf
theorem lean_workbook_1343_15 (a d : ℝ) : a^4-14*a^2*d^2+49*d^4 ≥ 0 ↔ (a^2-7*d^2)^2 ≥ 0 := by
  constructor
  intro h
  nlinarith
  intro h
  nlinarith
theorem lean_workbook_1343_16 (a d : ℝ) : a^4-14*a^2*d^2+49*d^4 ≥ 0 ↔ (a^2-7*d^2)^2 ≥ 0 := by
  field_simp [sq]
  constructor <;> intro h <;> linarith
theorem lean_workbook_1343_17 (a d : ℝ) : a^4-14*a^2*d^2+49*d^4 ≥ 0 ↔ (a^2-7*d^2)^2 ≥ 0 := by
  constructor <;> intro h <;> nlinarith only [h]
theorem lean_workbook_1343_18 (a d : ℝ) : a^4-14*a^2*d^2+49*d^4 ≥ 0 ↔ (a^2-7*d^2)^2 ≥ 0 := by
  simp only [sub_nonneg, mul_comm]
  ring_nf
theorem lean_workbook_1343_19 (a d : ℝ) : a^4-14*a^2*d^2+49*d^4 ≥ 0 ↔ (a^2-7*d^2)^2 ≥ 0 := by
  constructor <;> intro h <;> linarith
theorem lean_workbook_1343_20 (a d : ℝ) : a^4-14*a^2*d^2+49*d^4 ≥ 0 ↔ (a^2-7*d^2)^2 ≥ 0 := by
  field_simp [sub_sq, add_comm]
  ring_nf

theorem lean_workbook_1346_0 (x : ℝ) : (16*x^4 - 32*x^3 + 28*x^2 - 12*x + 9) * (2*x - 1)^2 ≥ 0 := by
  refine' mul_nonneg _ (sq_nonneg (2*x - 1))
  nlinarith [pow_two_nonneg (2*x - 1)]
theorem lean_workbook_1346_1 (x : ℝ) : (16*x^4 - 32*x^3 + 28*x^2 - 12*x + 9) * (2*x - 1)^2 ≥ 0 := by
  apply mul_nonneg <;> nlinarith [pow_two_nonneg (2*x - 1)]
theorem lean_workbook_1346_2 (x : ℝ) : (16*x^4 - 32*x^3 + 28*x^2 - 12*x + 9) * (2*x - 1)^2 ≥ 0 := by
  apply mul_nonneg
  nlinarith [sq_nonneg (2 * x - 1)]
  nlinarith [sq_nonneg (2 * x - 1)]
theorem lean_workbook_1346_3 (x : ℝ) : (16*x^4 - 32*x^3 + 28*x^2 - 12*x + 9) * (2*x - 1)^2 ≥ 0 := by
  refine' mul_nonneg _ (sq_nonneg _)
  nlinarith [sq_nonneg (2*x - 1)]
theorem lean_workbook_1346_4 (x : ℝ) : (16*x^4 - 32*x^3 + 28*x^2 - 12*x + 9) * (2*x - 1)^2 ≥ 0 := by
  refine' mul_nonneg _ (sq_nonneg _)
  nlinarith [sq_nonneg (2 * x - 1)]
theorem lean_workbook_1346_5 (x : ℝ) : (16*x^4 - 32*x^3 + 28*x^2 - 12*x + 9) * (2*x - 1)^2 ≥ 0 := by
  apply mul_nonneg _ (sq_nonneg _)
  simp [add_comm]
  nlinarith [sq_nonneg (2 * x - 1)]
theorem lean_workbook_1346_6 (x : ℝ) : (16*x^4 - 32*x^3 + 28*x^2 - 12*x + 9) * (2*x - 1)^2 ≥ 0 := by
  apply mul_nonneg
  nlinarith [sq_nonneg (x - 1/2)]
  nlinarith [sq_nonneg (2*x - 1)]
theorem lean_workbook_1346_7 (x : ℝ) : (16*x^4 - 32*x^3 + 28*x^2 - 12*x + 9) * (2*x - 1)^2 ≥ 0 := by
  refine' mul_nonneg _ (sq_nonneg (2 * x - 1))
  nlinarith [sq_nonneg (2 * x - 1)]
theorem lean_workbook_1346_8 (x : ℝ) : (16*x^4 - 32*x^3 + 28*x^2 - 12*x + 9) * (2*x - 1)^2 ≥ 0 := by
  simp only [ge_iff_le]
  apply mul_nonneg <;> nlinarith [sq_nonneg (2 * x - 1)]
theorem lean_workbook_1346_9 (x : ℝ) : (16*x^4 - 32*x^3 + 28*x^2 - 12*x + 9) * (2*x - 1)^2 ≥ 0 := by
  apply mul_nonneg
  nlinarith [sq_nonneg (2*x - 1)]
  nlinarith [sq_nonneg (2*x - 3)]
theorem lean_workbook_1346_10 (x : ℝ) : (16*x^4 - 32*x^3 + 28*x^2 - 12*x + 9) * (2*x - 1)^2 ≥ 0 := by
  apply mul_nonneg
  repeat nlinarith [sq_nonneg (2*x - 1)]

theorem lean_workbook_1347_0 (a b c : ℝ) (h : a + b + c ≥ 3) : a^2 + b^2 + c^2 + a * b + a * c + b * c ≥ 6 := by
  have h1 : 0 ≤ (a - 1)^2 + (b - 1)^2 + (c - 1)^2 := by nlinarith
  nlinarith
theorem lean_workbook_1347_1 (a b c : ℝ) (h : a + b + c ≥ 3) : a^2 + b^2 + c^2 + a * b + a * c + b * c ≥ 6 := by
  ring_nf
  simp [sq]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1347_2 (a b c : ℝ) (h : a + b + c ≥ 3) : a^2 + b^2 + c^2 + a * b + a * c + b * c ≥ 6 := by
  ring_nf at *
  rw [add_comm]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_1347_3 (a b c : ℝ) (h : a + b + c ≥ 3) : a^2 + b^2 + c^2 + a * b + a * c + b * c ≥ 6 := by
  simp [sq, add_assoc, add_left_comm, add_comm]
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]

theorem lean_workbook_1376_0 (n r : ℕ) : choose n r + choose n (r + 1) = choose (n + 1) (r + 1) := by
  simp [choose_succ_succ, add_comm, ← add_assoc, add_comm, add_assoc, choose_succ_right_eq]
theorem lean_workbook_1376_1 (n r : ℕ) : choose n r + choose n (r + 1) = choose (n + 1) (r + 1) := by
  simpa only [one_mul] using Nat.choose_succ_succ n r
theorem lean_workbook_1376_2 (n r : ℕ) : choose n r + choose n (r + 1) = choose (n + 1) (r + 1) := by
  suffices (n + 1).choose r.succ = n.choose r + n.choose r.succ by exact this
  rw [← succ_eq_add_one, choose_succ_succ, add_comm]
theorem lean_workbook_1376_3 (n r : ℕ) : choose n r + choose n (r + 1) = choose (n + 1) (r + 1) := by
  rw [← succ_eq_add_one]
  rw [← succ_eq_add_one]
  rw [choose_succ_succ, add_comm]
theorem lean_workbook_1376_4 (n r : ℕ) : choose n r + choose n (r + 1) = choose (n + 1) (r + 1) := by
  simp [choose_succ_succ, add_comm, ← add_assoc, Nat.add_comm]
theorem lean_workbook_1376_5 (n r : ℕ) : choose n r + choose n (r + 1) = choose (n + 1) (r + 1) := by
  rw [add_comm]
  simp [choose_succ_succ, add_comm, add_left_comm, add_assoc]
theorem lean_workbook_1376_6 (n r : ℕ) : choose n r + choose n (r + 1) = choose (n + 1) (r + 1) := by
  rw [← succ_eq_add_one, ← succ_eq_add_one]
  simp [choose_succ_succ, add_comm, add_left_comm, add_assoc]
theorem lean_workbook_1376_7 (n r : ℕ) : choose n r + choose n (r + 1) = choose (n + 1) (r + 1) := by
  simp [choose_succ_succ, add_comm, ← add_assoc, add_comm]
theorem lean_workbook_1376_8 (n r : ℕ) : choose n r + choose n (r + 1) = choose (n + 1) (r + 1) := by
  simp [add_comm, choose_succ_succ, choose_succ_right_eq]
theorem lean_workbook_1376_9 (n r : ℕ) : choose n r + choose n (r + 1) = choose (n + 1) (r + 1) := by
  rw [← succ_eq_add_one, choose_succ_succ, add_comm]
theorem lean_workbook_1376_10 (n r : ℕ) : choose n r + choose n (r + 1) = choose (n + 1) (r + 1) := by
  simp [Nat.choose_succ_succ, add_comm, ← add_assoc, add_assoc, add_comm]
theorem lean_workbook_1376_11 (n r : ℕ) : choose n r + choose n (r + 1) = choose (n + 1) (r + 1) := by
  simp [choose_succ_succ, add_comm, add_left_comm, add_assoc]
theorem lean_workbook_1376_12 (n r : ℕ) : choose n r + choose n (r + 1) = choose (n + 1) (r + 1) := by
  rw [← succ_eq_add_one]
  simp [choose_succ_succ, add_comm]
theorem lean_workbook_1376_13 (n r : ℕ) : choose n r + choose n (r + 1) = choose (n + 1) (r + 1) := by
  cases n <;> simp [Nat.choose_succ_succ, add_comm, add_left_comm, add_assoc]
theorem lean_workbook_1376_14 (n r : ℕ) : choose n r + choose n (r + 1) = choose (n + 1) (r + 1) := by
  simp [← choose_succ_succ, add_comm, ← Nat.succ_add]
theorem lean_workbook_1376_15 (n r : ℕ) : choose n r + choose n (r + 1) = choose (n + 1) (r + 1) := by
  repeat rw [← succ_eq_add_one]
  rw [choose_succ_succ, add_comm]
theorem lean_workbook_1376_16 (n r : ℕ) : choose n r + choose n (r + 1) = choose (n + 1) (r + 1) := by
  simp [add_comm, Nat.choose_succ_succ, choose]
theorem lean_workbook_1376_17 (n r : ℕ) : choose n r + choose n (r + 1) = choose (n + 1) (r + 1) := by
  apply choose_succ_succ
theorem lean_workbook_1376_18 (n r : ℕ) : choose n r + choose n (r + 1) = choose (n + 1) (r + 1) := by
  simp [choose_succ_succ]
theorem lean_workbook_1376_19 (n r : ℕ) : choose n r + choose n (r + 1) = choose (n + 1) (r + 1) := by
  simp [Nat.choose_succ_succ, add_comm, ← Nat.succ_add]
theorem lean_workbook_1376_20 (n r : ℕ) : choose n r + choose n (r + 1) = choose (n + 1) (r + 1) := by
  suffices (n + 1).choose r.succ = n.choose r + n.choose r.succ by exact this
  rw [← succ_eq_add_one]
  exact choose_succ_succ n r
theorem lean_workbook_1376_21 (n r : ℕ) : choose n r + choose n (r + 1) = choose (n + 1) (r + 1) := by
  simp only [← Nat.succ_eq_add_one, choose_succ_succ, add_comm]
theorem lean_workbook_1376_22 (n r : ℕ) : choose n r + choose n (r + 1) = choose (n + 1) (r + 1) := by
  rw [add_comm, choose_succ_succ, add_comm]
theorem lean_workbook_1376_23 (n r : ℕ) : choose n r + choose n (r + 1) = choose (n + 1) (r + 1) := by
  rw [add_comm]
  simp [choose_succ_succ, add_comm]
theorem lean_workbook_1376_24 (n r : ℕ) : choose n r + choose n (r + 1) = choose (n + 1) (r + 1) := by
  rw [← succ_eq_add_one]
  rw [← succ_eq_add_one]
  simp [choose_succ_succ, add_comm]

theorem lean_workbook_1377_0 : ∑ k in (Nat.divisors 12), k = 28 := by
  rw [divisors]
  simp only [Finset.sum]
  congr
theorem lean_workbook_1377_1 : ∑ k in (Nat.divisors 12), k = 28 := by
  unfold Nat.divisors
  simp only [Finset.sum]
  congr
theorem lean_workbook_1377_2 : ∑ k in (Nat.divisors 12), k = 28 := by
  conv_lhs => rw [← Nat.mod_add_div 12 2]
theorem lean_workbook_1377_3 : ∑ k in (Nat.divisors 12), k = 28 := by
  -- The divisors of 12 are 1, 2, 3, 4, 6, 12
  rw [Finset.sum_eq_multiset_sum]
  congr
theorem lean_workbook_1377_4 : ∑ k in (Nat.divisors 12), k = 28 := by
  congr 1 <;> simp [Nat.divisors]
theorem lean_workbook_1377_5 : ∑ k in (Nat.divisors 12), k = 28 := by
  rw [Finset.sum_eq_multiset_sum]
  congr 1
theorem lean_workbook_1377_6 : ∑ k in (Nat.divisors 12), k = 28 := by
  simp only [Nat.divisors]
  congr
theorem lean_workbook_1377_7 : ∑ k in (Nat.divisors 12), k = 28 := by
  simp only [Nat.divisors, List.map_map, Function.comp_apply]
  congr
theorem lean_workbook_1377_8 : ∑ k in (Nat.divisors 12), k = 28 := by
  simp only [Nat.divisors, Nat.sum]
  rfl
theorem lean_workbook_1377_9 : ∑ k in (Nat.divisors 12), k = 28 := by
  simp only [Finset.sum_eq_multiset_sum]
  trivial
theorem lean_workbook_1377_10 : ∑ k in (Nat.divisors 12), k = 28 := by
  calc ∑ k in (Nat.divisors 12), k
theorem lean_workbook_1377_11 : ∑ k in (Nat.divisors 12), k = 28 := by
  simp only [Nat.divisors]
  rfl
theorem lean_workbook_1377_12 : ∑ k in (Nat.divisors 12), k = 28 := by
  simp only [Nat.divisors, Finset.mem_range, Finset.mem_filter]
  rfl
theorem lean_workbook_1377_13 : ∑ k in (Nat.divisors 12), k = 28 := by
  unfold Nat.divisors
  congr
theorem lean_workbook_1377_14 : ∑ k in (Nat.divisors 12), k = 28 := by
  simp only [Finset.sum, Nat.divisors]
  trivial
theorem lean_workbook_1377_15 : ∑ k in (Nat.divisors 12), k = 28 := by
  conv => lhs; rw [← Nat.mod_add_div 12 10]
theorem lean_workbook_1377_16 : ∑ k in (Nat.divisors 12), k = 28 := by
  unfold Nat.divisors
  trivial
theorem lean_workbook_1377_17 : ∑ k in (Nat.divisors 12), k = 28 := by
  simp only [Nat.divisors, Finset.sum_range_succ]
  congr
theorem lean_workbook_1377_18 : ∑ k in (Nat.divisors 12), k = 28 := by
  conv => lhs; rw [← Nat.mod_add_div 12 2]
theorem lean_workbook_1377_19 : ∑ k in (Nat.divisors 12), k = 28 := by
  simp (config := {decide := true})
theorem lean_workbook_1377_20 : ∑ k in (Nat.divisors 12), k = 28 := by
  rw [Nat.divisors]
  trivial
theorem lean_workbook_1377_21 : ∑ k in (Nat.divisors 12), k = 28 := by
  simp only [Finset.sum]
  rfl
theorem lean_workbook_1377_22 : ∑ k in (Nat.divisors 12), k = 28 := by
  calc ∑ k in Nat.divisors 12, k
theorem lean_workbook_1377_23 : ∑ k in (Nat.divisors 12), k = 28 := by
  simp only [Nat.divisors, List.map, List.foldr, List.sum_cons, List.sum_nil]
  congr
theorem lean_workbook_1377_24 : ∑ k in (Nat.divisors 12), k = 28 := by
  calc ∑ k in divisors 12, k
theorem lean_workbook_1377_25 : ∑ k in (Nat.divisors 12), k = 28 := by
  simp only [Nat.divisors, List.map_map]
  rfl
theorem lean_workbook_1377_26 : ∑ k in (Nat.divisors 12), k = 28 := by
  rw [Finset.sum_eq_multiset_sum]
  rfl

theorem lean_workbook_1403_0 (n a : ℕ) (h₁ : 2 ≤ a) : n % a = 0 ↔ a ∣ n := by
  constructor
  intro h
  rw [← Nat.mod_add_div n a]
  simp [h]
  rintro ⟨k, rfl⟩
  simp [Nat.mul_mod_right]
theorem lean_workbook_1403_1 (n a : ℕ) (h₁ : 2 ≤ a) : n % a = 0 ↔ a ∣ n := by
  refine ⟨fun h =>?_, fun ⟨k, hk⟩ =>?_⟩
  rw [← Nat.mod_add_div n a]
  simp [h]
  rw [hk, Nat.mul_mod_right]
theorem lean_workbook_1403_2 (n a : ℕ) (h₁ : 2 ≤ a) : n % a = 0 ↔ a ∣ n := by
  constructor
  intro h
  exact Nat.dvd_of_mod_eq_zero h
  intro h
  rw [← Nat.mod_add_div n a]
  simp [h, Nat.zero_add, Nat.mod_eq_zero_of_dvd]
theorem lean_workbook_1403_3 (n a : ℕ) (h₁ : 2 ≤ a) : n % a = 0 ↔ a ∣ n := by
  refine' ⟨fun h => _, fun h => _⟩
  rw [dvd_iff_mod_eq_zero]
  exact h
  exact Nat.mod_eq_zero_of_dvd h
theorem lean_workbook_1403_4 (n a : ℕ) (h₁ : 2 ≤ a) : n % a = 0 ↔ a ∣ n := by
  constructor
  intro h
  rw [← Nat.mod_add_div n a]
  simp [h, Nat.dvd_iff_mod_eq_zero]
  rintro ⟨k, rfl⟩
  simp [Nat.mul_mod, Nat.mod_eq_zero_of_dvd]
theorem lean_workbook_1403_5 (n a : ℕ) (h₁ : 2 ≤ a) : n % a = 0 ↔ a ∣ n := by
  constructor
  intro h
  rw [← Nat.mod_add_div n a]
  simp [h]
  rintro ⟨k, rfl⟩
  rw [Nat.mul_mod_right]

theorem lean_workbook_1404_0 (a b c : ℝ) (hab : a + b > c) (hbc : b + c > a) (hca : c + a > b) : a > 0 ∧ b > 0 ∧ c > 0 := by
  refine' ⟨_, _, _⟩
  linarith only [hab, hbc, hca]
  linarith only [hab, hbc, hca]
  linarith only [hab, hbc, hca]
theorem lean_workbook_1404_1 (a b c : ℝ) (hab : a + b > c) (hbc : b + c > a) (hca : c + a > b) : a > 0 ∧ b > 0 ∧ c > 0 := by
  constructor
  linarith [hbc, hca]
  constructor
  linarith [hab, hca]
  linarith [hab, hbc]
theorem lean_workbook_1404_2 (a b c : ℝ) (hab : a + b > c) (hbc : b + c > a) (hca : c + a > b) : a > 0 ∧ b > 0 ∧ c > 0 := by
  refine ⟨by linarith [hab, hbc, hca], by linarith [hab, hbc, hca], by linarith [hab, hbc, hca]⟩
theorem lean_workbook_1404_3 (a b c : ℝ) (hab : a + b > c) (hbc : b + c > a) (hca : c + a > b) : a > 0 ∧ b > 0 ∧ c > 0 := by
  constructor
  linarith [hab, hbc, hca]
  constructor
  linarith [hab, hbc, hca]
  linarith [hab, hbc, hca]
theorem lean_workbook_1404_4 (a b c : ℝ) (hab : a + b > c) (hbc : b + c > a) (hca : c + a > b) : a > 0 ∧ b > 0 ∧ c > 0 := by
  refine' ⟨by linarith [hab, hbc, hca], by linarith [hab, hbc, hca], by linarith [hab, hbc, hca]⟩
theorem lean_workbook_1404_5 (a b c : ℝ) (hab : a + b > c) (hbc : b + c > a) (hca : c + a > b) : a > 0 ∧ b > 0 ∧ c > 0 := by
  constructor
  linarith only [hab, hbc, hca]
  constructor <;> linarith only [hab, hbc, hca]
theorem lean_workbook_1404_6 (a b c : ℝ) (hab : a + b > c) (hbc : b + c > a) (hca : c + a > b) : a > 0 ∧ b > 0 ∧ c > 0 := by
  constructor
  linarith
  constructor
  linarith
  linarith only [hab, hbc, hca]
theorem lean_workbook_1404_7 (a b c : ℝ) (hab : a + b > c) (hbc : b + c > a) (hca : c + a > b) : a > 0 ∧ b > 0 ∧ c > 0 := by
  constructor
  linarith [hab, hbc]
  constructor <;> linarith [hab, hbc, hca]
theorem lean_workbook_1404_8 (a b c : ℝ) (hab : a + b > c) (hbc : b + c > a) (hca : c + a > b) : a > 0 ∧ b > 0 ∧ c > 0 := by
  constructor
  linarith [hbc, hca, hab]
  constructor
  linarith [hab, hbc, hca]
  linarith [hbc, hca, hab]
theorem lean_workbook_1404_9 (a b c : ℝ) (hab : a + b > c) (hbc : b + c > a) (hca : c + a > b) : a > 0 ∧ b > 0 ∧ c > 0 := by
  simp only [add_comm] at *
  constructor
  linarith
  constructor <;> linarith
theorem lean_workbook_1404_10 (a b c : ℝ) (hab : a + b > c) (hbc : b + c > a) (hca : c + a > b) : a > 0 ∧ b > 0 ∧ c > 0 := by
  constructor
  linarith [hab, hbc, hca]
  constructor <;> linarith [hab, hbc, hca]
theorem lean_workbook_1404_11 (a b c : ℝ) (hab : a + b > c) (hbc : b + c > a) (hca : c + a > b) : a > 0 ∧ b > 0 ∧ c > 0 := by
  constructor
  linarith
  constructor
  linarith
  linarith [hab, hbc, hca]
theorem lean_workbook_1404_12 (a b c : ℝ) (hab : a + b > c) (hbc : b + c > a) (hca : c + a > b) : a > 0 ∧ b > 0 ∧ c > 0 := by
  constructor
  linarith [hab]
  constructor
  linarith [hbc]
  linarith [hca]
theorem lean_workbook_1404_13 (a b c : ℝ) (hab : a + b > c) (hbc : b + c > a) (hca : c + a > b) : a > 0 ∧ b > 0 ∧ c > 0 := by
  constructor
  linarith only [hab, hbc, hca]
  constructor
  linarith only [hab, hbc, hca]
  linarith only [hab, hbc, hca]
theorem lean_workbook_1404_14 (a b c : ℝ) (hab : a + b > c) (hbc : b + c > a) (hca : c + a > b) : a > 0 ∧ b > 0 ∧ c > 0 := by
  refine ⟨?_,?_,?_⟩
  linarith only [hab, hbc, hca]
  linarith only [hab, hbc, hca]
  linarith only [hab, hbc, hca]
theorem lean_workbook_1404_15 (a b c : ℝ) (hab : a + b > c) (hbc : b + c > a) (hca : c + a > b) : a > 0 ∧ b > 0 ∧ c > 0 := by
  field_simp [add_comm, add_left_comm, add_assoc] at *
  constructor
  linarith
  constructor <;> linarith
theorem lean_workbook_1404_16 (a b c : ℝ) (hab : a + b > c) (hbc : b + c > a) (hca : c + a > b) : a > 0 ∧ b > 0 ∧ c > 0 := by
  constructor
  linarith [hbc, hca]
  constructor
  linarith [hab, hbc]
  linarith [hbc, hca]
theorem lean_workbook_1404_17 (a b c : ℝ) (hab : a + b > c) (hbc : b + c > a) (hca : c + a > b) : a > 0 ∧ b > 0 ∧ c > 0 := by
  obtain ⟨h₁, h₂, h₃⟩ := add_lt_add_of_lt_of_le hab hbc.le, add_lt_add_of_lt_of_le hbc hca.le, add_lt_add_of_lt_of_le hca hab.le
  exact ⟨by linarith, by linarith, by linarith⟩
theorem lean_workbook_1404_18 (a b c : ℝ) (hab : a + b > c) (hbc : b + c > a) (hca : c + a > b) : a > 0 ∧ b > 0 ∧ c > 0 := by
  refine' ⟨_, _, _⟩
  linarith [hab, hbc, hca]
  linarith [hab, hbc, hca]
  linarith [hab, hbc, hca]
theorem lean_workbook_1404_19 (a b c : ℝ) (hab : a + b > c) (hbc : b + c > a) (hca : c + a > b) : a > 0 ∧ b > 0 ∧ c > 0 := by
  constructor
  contrapose! hab
  linarith
  constructor
  contrapose! hbc
  linarith
  contrapose! hca
  linarith
theorem lean_workbook_1404_20 (a b c : ℝ) (hab : a + b > c) (hbc : b + c > a) (hca : c + a > b) : a > 0 ∧ b > 0 ∧ c > 0 := by
  constructor
  linarith [add_lt_add_right hbc a, add_lt_add_left hca b]
  constructor
  linarith [add_lt_add_right hbc a, add_lt_add_left hca b]
  linarith [add_lt_add_right hbc a, add_lt_add_left hca b]

theorem lean_workbook_1405_0 (x : ℝ) (h₀ : 3 * x^2 = 23) : x = Real.sqrt (23 / 3) ∨ x = -Real.sqrt (23 / 3) := by
  apply eq_or_eq_neg_of_sq_eq_sq
  field_simp [h₀]
  nlinarith
theorem lean_workbook_1405_1 (x : ℝ) (h₀ : 3 * x^2 = 23) : x = Real.sqrt (23 / 3) ∨ x = -Real.sqrt (23 / 3) := by
  simp [pow_two] at h₀
  apply eq_or_eq_neg_of_sq_eq_sq
  field_simp [h₀]
  linarith
theorem lean_workbook_1405_2 (x : ℝ) (h₀ : 3 * x^2 = 23) : x = Real.sqrt (23 / 3) ∨ x = -Real.sqrt (23 / 3) := by
  have h₁ : 3 * x^2 = 23 := h₀
  apply eq_or_eq_neg_of_sq_eq_sq
  field_simp [h₁]
  nlinarith [h₁]

theorem lean_workbook_1458_0 (a b : ℝ) (h1 : 0 < a ∧ 0 < b) (h2 : a^2 + b^2 = 1) : 1 < a + b ∧ a + b ≤ Real.sqrt 2 := by
  constructor
  nlinarith [h1.1, h1.2, h2]
  have h3 : 0 ≤ (a - b)^2 := sq_nonneg (a - b)
  apply le_sqrt_of_sq_le
  nlinarith [h1.1, h1.2, h2, h3]
theorem lean_workbook_1458_1 (a b : ℝ) (h1 : 0 < a ∧ 0 < b) (h2 : a^2 + b^2 = 1) : 1 < a + b ∧ a + b ≤ Real.sqrt 2 := by
  constructor
  nlinarith [h1.1, h1.2, h2]
  have h3 : 0 ≤ (a - b)^2 := sq_nonneg (a - b)
  apply le_sqrt_of_sq_le
  linarith [h1.1, h1.2, h2, h3]
theorem lean_workbook_1458_2 (a b : ℝ) (h1 : 0 < a ∧ 0 < b) (h2 : a^2 + b^2 = 1) : 1 < a + b ∧ a + b ≤ Real.sqrt 2 := by
  refine' ⟨_, _⟩
  nlinarith
  have h3 : 0 ≤ (a - b)^2 := sq_nonneg (a - b)
  apply le_sqrt_of_sq_le
  nlinarith
theorem lean_workbook_1458_3 (a b : ℝ) (h1 : 0 < a ∧ 0 < b) (h2 : a^2 + b^2 = 1) : 1 < a + b ∧ a + b ≤ Real.sqrt 2 := by
  constructor
  nlinarith [h1, h2]
  have h3 : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  apply le_sqrt_of_sq_le
  nlinarith [h1, h2, h3]

theorem lean_workbook_1465_0 (x y z : ℝ) : 3 * (1 - x * y * z) ^ 2 + (3 - x * y - x * z - y * z) ^ 2 ≥ 0 := by
  nlinarith [sq_nonneg (x * y * z), sq_nonneg (x * y + x * z + y * z)]
theorem lean_workbook_1465_1 (x y z : ℝ) : 3 * (1 - x * y * z) ^ 2 + (3 - x * y - x * z - y * z) ^ 2 ≥ 0 := by
  nlinarith [mul_self_nonneg (x * y * z - 1), mul_self_nonneg (x * y + x * z + y * z - 3)]
theorem lean_workbook_1465_2 (x y z : ℝ) : 3 * (1 - x * y * z) ^ 2 + (3 - x * y - x * z - y * z) ^ 2 ≥ 0 := by
  apply_rules [add_nonneg, sq_nonneg, mul_nonneg] <;> norm_num
theorem lean_workbook_1465_3 (x y z : ℝ) : 3 * (1 - x * y * z) ^ 2 + (3 - x * y - x * z - y * z) ^ 2 ≥ 0 := by
  nlinarith [sq_nonneg (x * y + x * z + y * z)]
theorem lean_workbook_1465_4 (x y z : ℝ) : 3 * (1 - x * y * z) ^ 2 + (3 - x * y - x * z - y * z) ^ 2 ≥ 0 := by
  simp [sq]
  nlinarith [sq_nonneg (x * y + x * z + y * z - 3)]
theorem lean_workbook_1465_5 (x y z : ℝ) : 3 * (1 - x * y * z) ^ 2 + (3 - x * y - x * z - y * z) ^ 2 ≥ 0 := by
  nlinarith [mul_nonneg (mul_nonneg zero_le_three (sq_nonneg (1 - x * y * z))) (sq_nonneg (3 - x * y - x * z - y * z))]
theorem lean_workbook_1465_6 (x y z : ℝ) : 3 * (1 - x * y * z) ^ 2 + (3 - x * y - x * z - y * z) ^ 2 ≥ 0 := by
  field_simp [pow_two]
  nlinarith
theorem lean_workbook_1465_7 (x y z : ℝ) : 3 * (1 - x * y * z) ^ 2 + (3 - x * y - x * z - y * z) ^ 2 ≥ 0 := by
  simp [sq]
  nlinarith [sq_nonneg (3 * x * y * z - 3), sq_nonneg (x * y + x * z + y * z - 3)]
theorem lean_workbook_1465_8 (x y z : ℝ) : 3 * (1 - x * y * z) ^ 2 + (3 - x * y - x * z - y * z) ^ 2 ≥ 0 := by
  nlinarith [mul_nonneg (mul_nonneg (sq_nonneg x) (sq_nonneg y)) (sq_nonneg z)]
theorem lean_workbook_1465_9 (x y z : ℝ) : 3 * (1 - x * y * z) ^ 2 + (3 - x * y - x * z - y * z) ^ 2 ≥ 0 := by
  simp [add_assoc]
  nlinarith [mul_self_nonneg x, mul_self_nonneg y, mul_self_nonneg z]
theorem lean_workbook_1465_10 (x y z : ℝ) : 3 * (1 - x * y * z) ^ 2 + (3 - x * y - x * z - y * z) ^ 2 ≥ 0 := by
  simp [add_comm, add_left_comm]
  nlinarith
theorem lean_workbook_1465_11 (x y z : ℝ) : 3 * (1 - x * y * z) ^ 2 + (3 - x * y - x * z - y * z) ^ 2 ≥ 0 := by
  nlinarith [pow_two_nonneg (1 - x * y * z), pow_two_nonneg (3 - x * y - x * z - y * z)]
theorem lean_workbook_1465_12 (x y z : ℝ) : 3 * (1 - x * y * z) ^ 2 + (3 - x * y - x * z - y * z) ^ 2 ≥ 0 := by
  nlinarith [x * y * z, x * y, x * z, y * z]
theorem lean_workbook_1465_13 (x y z : ℝ) : 3 * (1 - x * y * z) ^ 2 + (3 - x * y - x * z - y * z) ^ 2 ≥ 0 := by
  nlinarith [ mul_self_nonneg (1 - x * y * z) ]
theorem lean_workbook_1465_14 (x y z : ℝ) : 3 * (1 - x * y * z) ^ 2 + (3 - x * y - x * z - y * z) ^ 2 ≥ 0 := by
  simp [sq, sub_eq_add_neg, add_assoc]
  nlinarith
theorem lean_workbook_1465_15 (x y z : ℝ) : 3 * (1 - x * y * z) ^ 2 + (3 - x * y - x * z - y * z) ^ 2 ≥ 0 := by
  nlinarith [mul_self_nonneg (x * y * z), mul_self_nonneg (x * y + x * z + y * z)]
theorem lean_workbook_1465_16 (x y z : ℝ) : 3 * (1 - x * y * z) ^ 2 + (3 - x * y - x * z - y * z) ^ 2 ≥ 0 := by
  nlinarith [mul_self_nonneg (x * y + x * z + y * z - 3)]
theorem lean_workbook_1465_17 (x y z : ℝ) : 3 * (1 - x * y * z) ^ 2 + (3 - x * y - x * z - y * z) ^ 2 ≥ 0 := by
  simp [add_assoc]
  nlinarith
theorem lean_workbook_1465_18 (x y z : ℝ) : 3 * (1 - x * y * z) ^ 2 + (3 - x * y - x * z - y * z) ^ 2 ≥ 0 := by
  nlinarith [mul_self_nonneg x, mul_self_nonneg y, mul_self_nonneg z]

theorem lean_workbook_1478_0 (a : ℝ) : a * 0 = 0 := by
  cases' le_total a 0 with h h <;> simp [h, mul_nonpos_of_nonneg_of_nonpos, mul_nonpos_of_nonpos_of_nonneg]
theorem lean_workbook_1478_1 (a : ℝ) : a * 0 = 0 := by
  rw [← zero_add 0]
  simp
theorem lean_workbook_1478_2 (a : ℝ) : a * 0 = 0 := by
  rcases lt_trichotomy a 0 with (h | h | h)
  any_goals linarith [h]
theorem lean_workbook_1478_3 (a : ℝ) : a * 0 = 0 := by
  simp [mul_comm]
theorem lean_workbook_1478_4 (a : ℝ) : a * 0 = 0 := by
  rw [mul_comm, zero_mul a]
theorem lean_workbook_1478_5 (a : ℝ) : a * 0 = 0 := by
  rw [mul_comm]
  simp only [zero_mul, mul_zero]
theorem lean_workbook_1478_6 (a : ℝ) : a * 0 = 0 := by
  rw [← zero_add (a * 0)]
  simp
theorem lean_workbook_1478_7 (a : ℝ) : a * 0 = 0 := by
  rw [mul_comm]
  simp [zero_mul]
theorem lean_workbook_1478_8 (a : ℝ) : a * 0 = 0 := by
  rw [mul_comm, zero_mul]

theorem lean_workbook_1481_0 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  simp [hx, show (4 : ℚ) = 4 from rfl, show (23 : ℚ) = 23 from rfl]
  norm_num [hx, show (4 : ℚ) = 4 from rfl, show (23 : ℚ) = 23 from rfl]
theorem lean_workbook_1481_1 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  simp [hx, show (4 : ℚ) = (4 : ℝ) by norm_cast]
  norm_num
theorem lean_workbook_1481_2 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  simp only [hx]
  norm_num [div_eq_mul_inv, inv_eq_one_div]
theorem lean_workbook_1481_3 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  field_simp [hx]
  norm_num [show (4 : ℚ) ≠ 0 by norm_num]
theorem lean_workbook_1481_4 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  simp [hx, div_eq_mul_inv]
  norm_num
theorem lean_workbook_1481_5 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  rw [hx]
  norm_num [div_eq_mul_inv, ← mul_assoc]
theorem lean_workbook_1481_6 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  rw [hx]
  ring_nf
theorem lean_workbook_1481_7 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  rw [hx, show (23 / 4 : ℚ) = 5.75 by norm_num]
theorem lean_workbook_1481_8 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  rw [hx]
  linear_combination 5.75 - 23/4
theorem lean_workbook_1481_9 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  rw [hx, show (23 : ℚ) / 4 = 5.75 by norm_num]
theorem lean_workbook_1481_10 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  rw [hx]
  norm_num [show (23 : ℚ) / 4 = 23 / 4 by norm_cast]
theorem lean_workbook_1481_11 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  rw [hx]
  norm_num [hx]
theorem lean_workbook_1481_12 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  norm_num [hx, show (5.75 : ℚ) = 23 / 4 by norm_num]
theorem lean_workbook_1481_13 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  rw [hx]
  norm_num [div_eq_mul_inv, inv_eq_one_div]
theorem lean_workbook_1481_14 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  rw [hx]
  norm_num [show (5.75 : ℚ) = 23 / 4 by norm_num]
theorem lean_workbook_1481_15 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  norm_num [hx, show (5.75 : ℚ) = 23 / 4 by norm_num1]
theorem lean_workbook_1481_16 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  simp only [hx, div_eq_mul_inv]
  norm_num [hx, div_eq_mul_inv]
theorem lean_workbook_1481_17 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  simp only [hx]
  norm_num [hx]
theorem lean_workbook_1481_18 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  simp only [hx]
  norm_num [show (23 : ℚ) / 4 = 5.75 by norm_num]
theorem lean_workbook_1481_19 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  simp only [hx, div_eq_mul_inv]
  norm_num [Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left]
theorem lean_workbook_1481_20 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  rw [hx]
  norm_num [hx, ← mul_one (4 : ℚ), ← mul_assoc]
theorem lean_workbook_1481_21 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  rw [hx]
  norm_num [show (23:ℝ) / 4 = 5.75 by norm_num]
theorem lean_workbook_1481_22 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  rw [hx]
  norm_num [div_eq_mul_inv]
theorem lean_workbook_1481_23 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  field_simp [hx]
  norm_num [show (4 : ℚ) = 2^2 by norm_num]
theorem lean_workbook_1481_24 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  linear_combination hx
theorem lean_workbook_1481_25 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  subst hx
  norm_num [show (23 : ℚ) / 4 = 23 / 4 by norm_num]
theorem lean_workbook_1481_26 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  rw [hx]
  norm_num [show (23:ℚ) / 4 = 5.75 by norm_num]
theorem lean_workbook_1481_27 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  simp [hx]
  norm_num [show (4 : ℚ) = 4 / 1 by norm_num]
theorem lean_workbook_1481_28 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  rw [hx]
  norm_num [show (23 : ℚ) / 4 = 5.75 by norm_num]
theorem lean_workbook_1481_29 (x : ℚ) (hx : x = 23/4) : x = 5.75 := by
  rw [hx]
  norm_num [show (23 : ℚ) / 4 = 23 / 4 by norm_num]

theorem lean_workbook_1486_0 (a b c d : ℝ) : Real.sqrt ((a^2 + b^2) * (c^2 + d^2)) ≥ a * d + b * c := by
  have h : 0 ≤ (a * c - b * d)^2 := sq_nonneg _
  apply Real.le_sqrt_of_sq_le
  linarith
theorem lean_workbook_1486_1 (a b c d : ℝ) : Real.sqrt ((a^2 + b^2) * (c^2 + d^2)) ≥ a * d + b * c := by
  apply le_sqrt_of_sq_le
  nlinarith [sq_nonneg (a * d + b * c), sq_nonneg (a * c - b * d)]
theorem lean_workbook_1486_2 (a b c d : ℝ) : Real.sqrt ((a^2 + b^2) * (c^2 + d^2)) ≥ a * d + b * c := by
  apply Real.le_sqrt_of_sq_le
  have := sq_nonneg (a * c - b * d)
  linarith
theorem lean_workbook_1486_3 (a b c d : ℝ) : Real.sqrt ((a^2 + b^2) * (c^2 + d^2)) ≥ a * d + b * c := by
  have h1 : 0 ≤ (a * c - b * d)^2 := sq_nonneg _
  apply le_sqrt_of_sq_le
  linarith
theorem lean_workbook_1486_4 (a b c d : ℝ) : Real.sqrt ((a^2 + b^2) * (c^2 + d^2)) ≥ a * d + b * c := by
  have h1 := sq_nonneg (a * d + b * c)
  have h2 := sq_nonneg (a * c - b * d)
  apply Real.le_sqrt_of_sq_le
  nlinarith
theorem lean_workbook_1486_5 (a b c d : ℝ) : Real.sqrt ((a^2 + b^2) * (c^2 + d^2)) ≥ a * d + b * c := by
  have := sq_nonneg (a * d + b * c)
  have := sq_nonneg (a * c - b * d)
  apply le_sqrt_of_sq_le
  linarith
theorem lean_workbook_1486_6 (a b c d : ℝ) : Real.sqrt ((a^2 + b^2) * (c^2 + d^2)) ≥ a * d + b * c := by
  have h : 0 ≤ (a * c - b * d) ^ 2 := sq_nonneg _
  apply Real.le_sqrt_of_sq_le
  linarith
theorem lean_workbook_1486_7 (a b c d : ℝ) : Real.sqrt ((a^2 + b^2) * (c^2 + d^2)) ≥ a * d + b * c := by
  have h0 : 0 ≤ (a * c - b * d)^2 := sq_nonneg _
  apply le_sqrt_of_sq_le
  linarith
theorem lean_workbook_1486_8 (a b c d : ℝ) : Real.sqrt ((a^2 + b^2) * (c^2 + d^2)) ≥ a * d + b * c := by
  have h1 : 0 ≤ (a * c - b * d)^2 := sq_nonneg _
  apply Real.le_sqrt_of_sq_le
  linarith
theorem lean_workbook_1486_9 (a b c d : ℝ) : Real.sqrt ((a^2 + b^2) * (c^2 + d^2)) ≥ a * d + b * c := by
  have h1 := sq_nonneg (a * d + b * c)
  have h2 := sq_nonneg (a * c - b * d)
  apply Real.le_sqrt_of_sq_le
  linarith
theorem lean_workbook_1486_10 (a b c d : ℝ) : Real.sqrt ((a^2 + b^2) * (c^2 + d^2)) ≥ a * d + b * c := by
  have h1 : 0 ≤ (a * c - b * d) ^ 2 := sq_nonneg _
  apply Real.le_sqrt_of_sq_le
  linarith

theorem lean_workbook_1510_0 (s t : ℂ) : ‖s + t‖ ≤ ‖s‖ + ‖t‖ := by
  exact Complex.norm_eq_abs s ▸ Complex.norm_eq_abs t ▸ Complex.abs.add_le s t
theorem lean_workbook_1510_1 (s t : ℂ) : ‖s + t‖ ≤ ‖s‖ + ‖t‖ := by
  simp only [Complex.norm_eq_abs, Complex.abs.add_le]
theorem lean_workbook_1510_2 (s t : ℂ) : ‖s + t‖ ≤ ‖s‖ + ‖t‖ := by
  simp only [Complex.norm_eq_abs]
  apply Complex.abs.add_le
theorem lean_workbook_1510_3 (s t : ℂ) : ‖s + t‖ ≤ ‖s‖ + ‖t‖ := by
  apply Complex.abs.add_le
theorem lean_workbook_1510_4 (s t : ℂ) : ‖s + t‖ ≤ ‖s‖ + ‖t‖ := by
  simp [Complex.norm_eq_abs, Complex.abs.add_le]
theorem lean_workbook_1510_5 (s t : ℂ) : ‖s + t‖ ≤ ‖s‖ + ‖t‖ := by
  simpa only [← Complex.norm_eq_abs] using Complex.abs.add_le s t
theorem lean_workbook_1510_6 (s t : ℂ) : ‖s + t‖ ≤ ‖s‖ + ‖t‖ := by
  rw [Complex.norm_eq_abs]
  rw [Complex.norm_eq_abs]
  rw [Complex.norm_eq_abs]
  apply Complex.abs.add_le
theorem lean_workbook_1510_7 (s t : ℂ) : ‖s + t‖ ≤ ‖s‖ + ‖t‖ := by
  simpa only [norm_eq_abs] using Complex.abs.add_le s t
theorem lean_workbook_1510_8 (s t : ℂ) : ‖s + t‖ ≤ ‖s‖ + ‖t‖ := by
  simp [norm_eq_abs]
  apply Complex.abs.add_le
theorem lean_workbook_1510_9 (s t : ℂ) : ‖s + t‖ ≤ ‖s‖ + ‖t‖ := by
  simpa only [Complex.norm_eq_abs] using Complex.abs.add_le s t

theorem lean_workbook_1513_0 : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  norm_num [Nat.modEq_iff_dvd, Int.modEq_iff_dvd]
theorem lean_workbook_1513_1 : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  conv_lhs => rw [← pow_one 2]
theorem lean_workbook_1513_2 : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  norm_num [pow_succ, pow_mul, pow_one, Int.ModEq]
theorem lean_workbook_1513_3 : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  rw [Int.ModEq]
  norm_num
theorem lean_workbook_1513_4 : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  conv => lhs; rw [← one_mul (2 ^ 32)]
theorem lean_workbook_1513_5 : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  norm_num [Nat.gcd_eq_gcd_ab, Int.ModEq]
theorem lean_workbook_1513_6 : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  conv => lhs; rw [← one_mul (2 ^ 32 + 1)]
theorem lean_workbook_1513_7 : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  simp [Int.ModEq]
theorem lean_workbook_1513_8 : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  simp [Int.ModEq, Int.emod]
theorem lean_workbook_1513_9 : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  simp only [Int.ModEq]
  norm_num
theorem lean_workbook_1513_10 : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  exact (show 2 ^ 32 + 1 ≡ 0 [ZMOD 641] by rfl)
theorem lean_workbook_1513_11 : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  ring_nf
  norm_num [Nat.ModEq, Int.ModEq]
theorem lean_workbook_1513_12 : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  exact (show 2 ^ 32 + 1 ≡ 0 [ZMOD 641] from rfl)
theorem lean_workbook_1513_13 : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  norm_num [pow_succ, pow_zero, pow_one, Int.ModEq]
theorem lean_workbook_1513_14 : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  conv => lhs; rw [← pow_one 2]; norm_num
theorem lean_workbook_1513_15 : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  norm_num [Nat.ModEq, Int.ModEq]
theorem lean_workbook_1513_16 : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  rw [Int.modEq_zero_iff_dvd]
  norm_num [Nat.pow_succ, Nat.pow_zero]
theorem lean_workbook_1513_17 : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  conv_lhs => norm_num
theorem lean_workbook_1513_18 : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  norm_num [Int.ModEq]
theorem lean_workbook_1513_19 : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  exact (show 2^32 + 1 ≡ 0 [ZMOD 641] from by decide)
theorem lean_workbook_1513_20 : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  conv_lhs => rw [← pow_one 2]; norm_num
theorem lean_workbook_1513_21 : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  conv => lhs; rw [← pow_one (2 : ℤ)]
theorem lean_workbook_1513_22 : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  rw [Int.modEq_zero_iff_dvd]
  norm_num [Nat.pow_succ, Nat.pow_zero, Nat.mod_eq_of_lt]
theorem lean_workbook_1513_23 : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  norm_num [pow_succ, pow_zero]
  rfl
theorem lean_workbook_1513_24 : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  apply Int.modEq_zero_iff_dvd.mpr
  norm_num
theorem lean_workbook_1513_25 : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  norm_num [Int.ModEq, Int.ModEq]
theorem lean_workbook_1513_26 : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  change 2^32 + 1 ≡ 0 [ZMOD 641]
  norm_num [pow_succ, pow_mul, Int.ModEq]
theorem lean_workbook_1513_27 : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  norm_num [Nat.modEq_zero_iff_dvd, Int.ModEq]

theorem lean_workbook_1514_0 (n k : ℕ) : ∑ i in Finset.range (k+1), choose (n+i) n = choose (n+k+1) (n+1) := by
  induction' k with k IH
  simp [Nat.choose_succ_succ]
  rw [Finset.sum_range_succ, Nat.choose_succ_succ, IH]
  simp [add_comm, add_left_comm, add_assoc, choose_succ_succ]
theorem lean_workbook_1514_1 (n k : ℕ) : ∑ i in Finset.range (k+1), choose (n+i) n = choose (n+k+1) (n+1) := by
  induction' k with k IH
  simp [Finset.range_one]
  rw [Finset.sum_range_succ, Nat.choose_succ_succ, IH, add_comm]
  simp [add_assoc, add_comm, add_left_comm]

theorem lean_workbook_1516_0 (a b : ℕ) (hab : a ∣ b) : (2^a - 1) ∣ (2^b - 1) := by
  rcases hab with ⟨c, rfl⟩
  rw [Nat.pow_mul]
  simpa only [one_pow] using nat_sub_dvd_pow_sub_pow _ 1 c
theorem lean_workbook_1516_1 (a b : ℕ) (hab : a ∣ b) : (2^a - 1) ∣ (2^b - 1) := by
  rcases hab with ⟨c, rfl⟩
  rw [pow_mul]
  simpa only [one_pow] using nat_sub_dvd_pow_sub_pow _ 1 c
theorem lean_workbook_1516_2 (a b : ℕ) (hab : a ∣ b) : (2^a - 1) ∣ (2^b - 1) := by
  obtain ⟨c, h⟩ := hab
  rw [h]
  rw [Nat.pow_mul]
  simpa only [one_pow, pow_mul, one_mul] using nat_sub_dvd_pow_sub_pow _ 1 c
theorem lean_workbook_1516_3 (a b : ℕ) (hab : a ∣ b) : (2^a - 1) ∣ (2^b - 1) := by
  obtain ⟨c, rfl⟩ := hab
  rw [Nat.pow_mul]
  simpa only [one_pow, pow_mul, one_mul] using nat_sub_dvd_pow_sub_pow _ 1 c
theorem lean_workbook_1516_4 (a b : ℕ) (hab : a ∣ b) : (2^a - 1) ∣ (2^b - 1) := by
  obtain ⟨d, rfl⟩ := hab
  rw [pow_mul]
  simpa only [one_pow, Nat.sub_self, zero_add] using nat_sub_dvd_pow_sub_pow _ 1 d
theorem lean_workbook_1516_5 (a b : ℕ) (hab : a ∣ b) : (2^a - 1) ∣ (2^b - 1) := by
  obtain ⟨d, rfl⟩ := hab
  rw [Nat.pow_mul]
  simpa only [one_pow, Nat.sub_self, zero_add] using nat_sub_dvd_pow_sub_pow _ 1 d
theorem lean_workbook_1516_6 (a b : ℕ) (hab : a ∣ b) : (2^a - 1) ∣ (2^b - 1) := by
  obtain ⟨r, hr⟩ := hab
  rw [hr]
  rw [pow_mul]
  simpa only [pow_mul, one_pow] using nat_sub_dvd_pow_sub_pow _ 1 r
theorem lean_workbook_1516_7 (a b : ℕ) (hab : a ∣ b) : (2^a - 1) ∣ (2^b - 1) := by
  rcases hab with ⟨c, rfl⟩
  rw [Nat.pow_mul]
  simpa only [one_pow, pow_mul, one_mul] using nat_sub_dvd_pow_sub_pow _ 1 c
theorem lean_workbook_1516_8 (a b : ℕ) (hab : a ∣ b) : (2^a - 1) ∣ (2^b - 1) := by
  obtain ⟨k, rfl⟩ := hab
  rw [Nat.pow_mul]
  simpa only [Nat.pow_mul, one_pow] using nat_sub_dvd_pow_sub_pow _ 1 k
theorem lean_workbook_1516_9 (a b : ℕ) (hab : a ∣ b) : (2^a - 1) ∣ (2^b - 1) := by
  rcases hab with ⟨c, rfl⟩
  rw [Nat.pow_mul]
  simpa only [one_pow, Nat.sub_self, zero_add] using nat_sub_dvd_pow_sub_pow _ 1 c
theorem lean_workbook_1516_10 (a b : ℕ) (hab : a ∣ b) : (2^a - 1) ∣ (2^b - 1) := by
  obtain ⟨c, rfl⟩ := hab
  rw [Nat.pow_mul]
  simpa only [pow_mul, one_pow] using nat_sub_dvd_pow_sub_pow _ 1 c
theorem lean_workbook_1516_11 (a b : ℕ) (hab : a ∣ b) : (2^a - 1) ∣ (2^b - 1) := by
  cases' hab with k hk
  rw [hk]
  rw [pow_mul]
  simpa only [one_pow, Nat.sub_self, zero_add] using nat_sub_dvd_pow_sub_pow _ 1 k
theorem lean_workbook_1516_12 (a b : ℕ) (hab : a ∣ b) : (2^a - 1) ∣ (2^b - 1) := by
  obtain ⟨m, rfl⟩ := hab
  rw [Nat.pow_mul]
  simpa only [one_pow, pow_mul, one_mul] using nat_sub_dvd_pow_sub_pow _ 1 m
theorem lean_workbook_1516_13 (a b : ℕ) (hab : a ∣ b) : (2^a - 1) ∣ (2^b - 1) := by
  obtain ⟨r, hr⟩ := hab
  rw [hr]
  rw [pow_mul]
  simpa only [one_pow, Nat.sub_self, zero_add] using nat_sub_dvd_pow_sub_pow _ 1 r
theorem lean_workbook_1516_14 (a b : ℕ) (hab : a ∣ b) : (2^a - 1) ∣ (2^b - 1) := by
  rcases hab with ⟨d, rfl⟩
  simp only [pow_mul]
  simpa only [one_pow, pow_mul, one_mul] using nat_sub_dvd_pow_sub_pow _ 1 d
theorem lean_workbook_1516_15 (a b : ℕ) (hab : a ∣ b) : (2^a - 1) ∣ (2^b - 1) := by
  obtain ⟨d, rfl⟩ := hab
  rw [Nat.pow_mul]
  simpa only [one_pow] using nat_sub_dvd_pow_sub_pow _ 1 d
theorem lean_workbook_1516_16 (a b : ℕ) (hab : a ∣ b) : (2^a - 1) ∣ (2^b - 1) := by
  obtain ⟨c, rfl⟩ := hab
  rw [Nat.pow_mul]
  simpa only [one_pow] using nat_sub_dvd_pow_sub_pow _ 1 c
theorem lean_workbook_1516_17 (a b : ℕ) (hab : a ∣ b) : (2^a - 1) ∣ (2^b - 1) := by
  rcases hab with ⟨c, rfl⟩
  simp only [pow_mul]
  simpa only [pow_mul, one_pow] using nat_sub_dvd_pow_sub_pow _ 1 c
theorem lean_workbook_1516_18 (a b : ℕ) (hab : a ∣ b) : (2^a - 1) ∣ (2^b - 1) := by
  obtain ⟨d, rfl⟩ := hab
  rw [Nat.pow_mul]
  simpa only [pow_mul, one_pow] using nat_sub_dvd_pow_sub_pow _ 1 d
theorem lean_workbook_1516_19 (a b : ℕ) (hab : a ∣ b) : (2^a - 1) ∣ (2^b - 1) := by
  rcases hab with ⟨k, rfl⟩
  rw [pow_mul]
  simpa only [one_pow] using nat_sub_dvd_pow_sub_pow _ 1 k

theorem lean_workbook_1520_0 {m n : ℕ} (hmn: m ∣ n) : 2^m - 1 ∣ 2^n - 1 := by
  obtain ⟨k, rfl⟩ :=exists_eq_mul_right_of_dvd hmn
  rw [Nat.pow_mul]
  simpa only [one_pow, pow_mul, one_mul] using nat_sub_dvd_pow_sub_pow _ 1 k
theorem lean_workbook_1520_1 {m n : ℕ} (hmn: m ∣ n) : 2^m - 1 ∣ 2^n - 1 := by
  obtain ⟨k, hk⟩ := hmn
  rw [hk, pow_mul]
  simpa only [one_pow, Nat.sub_self, zero_add] using nat_sub_dvd_pow_sub_pow _ 1 k
theorem lean_workbook_1520_2 {m n : ℕ} (hmn: m ∣ n) : 2^m - 1 ∣ 2^n - 1 := by
  obtain ⟨k, hk⟩ := hmn
  rw [hk]
  rw [pow_mul]
  simpa only [one_pow] using nat_sub_dvd_pow_sub_pow _ 1 k
theorem lean_workbook_1520_3 {m n : ℕ} (hmn: m ∣ n) : 2^m - 1 ∣ 2^n - 1 := by
  cases' hmn with p hp
  rw [hp]
  rw [pow_mul]
  simpa only [one_pow] using nat_sub_dvd_pow_sub_pow _ 1 p
theorem lean_workbook_1520_4 {m n : ℕ} (hmn: m ∣ n) : 2^m - 1 ∣ 2^n - 1 := by
  rcases hmn with ⟨k, rfl⟩
  rw [Nat.pow_mul]
  simpa only [pow_mul, one_pow] using nat_sub_dvd_pow_sub_pow _ 1 k
theorem lean_workbook_1520_5 {m n : ℕ} (hmn: m ∣ n) : 2^m - 1 ∣ 2^n - 1 := by
  obtain ⟨k, hk⟩ := hmn
  rw [hk]
  simpa only [pow_mul, one_pow] using nat_sub_dvd_pow_sub_pow _ 1 k
theorem lean_workbook_1520_6 {m n : ℕ} (hmn: m ∣ n) : 2^m - 1 ∣ 2^n - 1 := by
  obtain ⟨k, rfl⟩ := hmn
  rw [Nat.pow_mul]
  simpa only [Nat.pow_mul, one_pow] using nat_sub_dvd_pow_sub_pow _ 1 k
theorem lean_workbook_1520_7 {m n : ℕ} (hmn: m ∣ n) : 2^m - 1 ∣ 2^n - 1 := by
  obtain ⟨r, hr⟩ := hmn
  rw [hr]
  rw [Nat.pow_mul]
  simpa only [Nat.pow_mul, one_pow] using nat_sub_dvd_pow_sub_pow _ 1 r
theorem lean_workbook_1520_8 {m n : ℕ} (hmn: m ∣ n) : 2^m - 1 ∣ 2^n - 1 := by
  rcases hmn with ⟨k, rfl⟩
  rw [Nat.pow_mul]
  simpa only [one_pow, mul_one] using nat_sub_dvd_pow_sub_pow _ 1 k
theorem lean_workbook_1520_9 {m n : ℕ} (hmn: m ∣ n) : 2^m - 1 ∣ 2^n - 1 := by
  obtain ⟨k, rfl⟩ := hmn
  simp only [pow_mul]
  simpa only [one_pow, pow_add, pow_one] using nat_sub_dvd_pow_sub_pow _ 1 k
theorem lean_workbook_1520_10 {m n : ℕ} (hmn: m ∣ n) : 2^m - 1 ∣ 2^n - 1 := by
  obtain ⟨k, rfl⟩ := hmn
  rw [Nat.pow_mul]
  simpa only [one_pow, pow_mul, one_mul] using nat_sub_dvd_pow_sub_pow _ 1 k
theorem lean_workbook_1520_11 {m n : ℕ} (hmn: m ∣ n) : 2^m - 1 ∣ 2^n - 1 := by
  obtain ⟨k, rfl⟩ := hmn
  rw [Nat.pow_mul]
  simpa only [one_pow, Nat.pow_mul, one_mul] using nat_sub_dvd_pow_sub_pow _ 1 k
theorem lean_workbook_1520_12 {m n : ℕ} (hmn: m ∣ n) : 2^m - 1 ∣ 2^n - 1 := by
  rcases hmn with ⟨k, rfl⟩
  rw [Nat.pow_mul]
  simpa only [one_pow, pow_mul, one_mul] using nat_sub_dvd_pow_sub_pow _ 1 k
theorem lean_workbook_1520_13 {m n : ℕ} (hmn: m ∣ n) : 2^m - 1 ∣ 2^n - 1 := by
  rcases hmn with ⟨k, rfl⟩
  rw [pow_mul]
  simpa only [one_pow] using nat_sub_dvd_pow_sub_pow _ 1 k
theorem lean_workbook_1520_14 {m n : ℕ} (hmn: m ∣ n) : 2^m - 1 ∣ 2^n - 1 := by
  obtain ⟨k, rfl⟩ := hmn
  rw[pow_mul]
  simpa only [one_pow] using nat_sub_dvd_pow_sub_pow _ 1 k
theorem lean_workbook_1520_15 {m n : ℕ} (hmn: m ∣ n) : 2^m - 1 ∣ 2^n - 1 := by
  obtain ⟨k, rfl⟩ := hmn
  rw [pow_mul]
  simpa only [one_pow, mul_one] using nat_sub_dvd_pow_sub_pow _ 1 k
theorem lean_workbook_1520_16 {m n : ℕ} (hmn: m ∣ n) : 2^m - 1 ∣ 2^n - 1 := by
  rcases hmn with ⟨k, rfl⟩
  rw [Nat.pow_mul]
  simpa only [one_pow, Nat.pow_mul, one_mul] using nat_sub_dvd_pow_sub_pow _ 1 k
theorem lean_workbook_1520_17 {m n : ℕ} (hmn: m ∣ n) : 2^m - 1 ∣ 2^n - 1 := by
  obtain ⟨k, rfl⟩ := hmn
  rw [Nat.pow_mul]
  simpa only [one_pow, Nat.sub_self, zero_add] using nat_sub_dvd_pow_sub_pow _ 1 k

theorem lean_workbook_1537_0 (k : ℕ) (x : ℝ) (hx : 0 < x) : (x * (k/x) - (x+1) * (k/(x+1))) ≤ 1 := by
  ring_nf
  rw [add_comm]
  field_simp [hx, add_pos hx zero_lt_one]
  ring_nf
  have h₁ : 0 < x + 1 := by linarith
  nlinarith
theorem lean_workbook_1537_1 (k : ℕ) (x : ℝ) (hx : 0 < x) : (x * (k/x) - (x+1) * (k/(x+1))) ≤ 1 := by
  field_simp [hx]
  ring_nf
  rw [← sub_nonneg]
  have h : 0 < x * (x + 1) := by nlinarith
  nlinarith
theorem lean_workbook_1537_2 (k : ℕ) (x : ℝ) (hx : 0 < x) : (x * (k/x) - (x+1) * (k/(x+1))) ≤ 1 := by
  field_simp [hx, hx.ne']
  ring_nf
  rw [← sub_nonneg]
  have h : 0 < x * (x + 1) := by nlinarith
  nlinarith
theorem lean_workbook_1537_3 (k : ℕ) (x : ℝ) (hx : 0 < x) : (x * (k/x) - (x+1) * (k/(x+1))) ≤ 1 := by
  field_simp [hx, add_pos hx zero_lt_one]
  ring_nf
  nlinarith
theorem lean_workbook_1537_4 (k : ℕ) (x : ℝ) (hx : 0 < x) : (x * (k/x) - (x+1) * (k/(x+1))) ≤ 1 := by
  field_simp [add_pos hx hx]
  ring_nf
  rw [← sub_nonneg]
  have h₁ : 0 < x * (x + 1) := mul_pos hx (by linarith)
  nlinarith
theorem lean_workbook_1537_5 (k : ℕ) (x : ℝ) (hx : 0 < x) : (x * (k/x) - (x+1) * (k/(x+1))) ≤ 1 := by
  have h1: 0 < x + 1 := by linarith
  field_simp [hx, h1]
  ring_nf
  rw [← sub_nonneg]
  have h2: 0 < 2 * x + 1 := by linarith
  nlinarith
theorem lean_workbook_1537_6 (k : ℕ) (x : ℝ) (hx : 0 < x) : (x * (k/x) - (x+1) * (k/(x+1))) ≤ 1 := by
  rw [add_mul]
  field_simp [hx, mul_comm]
  ring_nf
  nlinarith

theorem lean_workbook_1590_0 : ∀ a : ℝ, 0 < a ∧ a < 1 → ¬(1 - Real.log a < a) := by
  intro a h
  have h₁ := Real.log_le_sub_one_of_pos h.1
  linarith
theorem lean_workbook_1590_1 : ∀ a : ℝ, 0 < a ∧ a < 1 → ¬(1 - Real.log a < a) := by
  intro a h
  simp [h.1, h.2, sub_lt_iff_lt_add]
  nlinarith [Real.log_le_sub_one_of_pos h.1]
theorem lean_workbook_1590_2 : ∀ a : ℝ, 0 < a ∧ a < 1 → ¬(1 - Real.log a < a) := by
  intro a h
  rw [← not_le]
  intro h'
  nlinarith [Real.log_le_sub_one_of_pos h.1]
theorem lean_workbook_1590_3 : ∀ a : ℝ, 0 < a ∧ a < 1 → ¬(1 - Real.log a < a) := by
  intro x hx hx'
  nlinarith [Real.log_le_sub_one_of_pos hx.1]
theorem lean_workbook_1590_4 : ∀ a : ℝ, 0 < a ∧ a < 1 → ¬(1 - Real.log a < a) := by
  intro x h
  have h₁ := log_le_sub_one_of_pos h.1
  linarith
theorem lean_workbook_1590_5 : ∀ a : ℝ, 0 < a ∧ a < 1 → ¬(1 - Real.log a < a) := by
  rintro a ⟨h₁, h₂⟩ h₃
  nlinarith [Real.log_le_sub_one_of_pos h₁]
theorem lean_workbook_1590_6 : ∀ a : ℝ, 0 < a ∧ a < 1 → ¬(1 - Real.log a < a) := by
  rintro a ⟨h₁, h₂⟩
  contrapose! h₂
  nlinarith [Real.log_le_sub_one_of_pos h₁]
theorem lean_workbook_1590_7 : ∀ a : ℝ, 0 < a ∧ a < 1 → ¬(1 - Real.log a < a) := by
  rintro a ⟨ha0, ha1⟩ h
  linarith [Real.log_le_sub_one_of_pos ha0]
theorem lean_workbook_1590_8 : ∀ a : ℝ, 0 < a ∧ a < 1 → ¬(1 - Real.log a < a) := by
  intro a h
  rw [not_lt]
  nlinarith [log_le_sub_one_of_pos h.1]
theorem lean_workbook_1590_9 : ∀ a : ℝ, 0 < a ∧ a < 1 → ¬(1 - Real.log a < a) := by
  rintro a ⟨ha, ha'⟩ h
  nlinarith [Real.log_le_sub_one_of_pos ha]
theorem lean_workbook_1590_10 : ∀ a : ℝ, 0 < a ∧ a < 1 → ¬(1 - Real.log a < a) := by
  intro a h
  have : 0 < 1 - Real.log a := by linarith [Real.log_le_sub_one_of_pos h.1]
  intro h'
  linarith [Real.log_le_sub_one_of_pos h.1]
theorem lean_workbook_1590_11 : ∀ a : ℝ, 0 < a ∧ a < 1 → ¬(1 - Real.log a < a) := by
  intro a h
  rw [not_lt]
  nlinarith [Real.log_le_sub_one_of_pos h.1]
theorem lean_workbook_1590_12 : ∀ a : ℝ, 0 < a ∧ a < 1 → ¬(1 - Real.log a < a) := by
  refine' fun a h => not_lt.2 _
  have := Real.log_le_sub_one_of_pos h.1
  linarith [h.2]
theorem lean_workbook_1590_13 : ∀ a : ℝ, 0 < a ∧ a < 1 → ¬(1 - Real.log a < a) := by
  intro a
  rintro ⟨h1, h2⟩
  intro h
  have h3 := Real.log_lt_log h1 h2
  have h4 := Real.log_one
  linarith
theorem lean_workbook_1590_14 : ∀ a : ℝ, 0 < a ∧ a < 1 → ¬(1 - Real.log a < a) := by
  intro a h
  have : 0 < 1 - Real.log a := by linarith [Real.log_le_sub_one_of_pos h.1]
  linarith [Real.log_le_sub_one_of_pos h.1]
theorem lean_workbook_1590_15 : ∀ a : ℝ, 0 < a ∧ a < 1 → ¬(1 - Real.log a < a) := by
  intro a h
  have : 0 < a ∧ a < 1 := h
  push_neg
  nlinarith [Real.log_le_sub_one_of_pos this.1]
theorem lean_workbook_1590_16 : ∀ a : ℝ, 0 < a ∧ a < 1 → ¬(1 - Real.log a < a) := by
  exact fun a ha ha' => by linarith [Real.log_le_sub_one_of_pos ha.1]
theorem lean_workbook_1590_17 : ∀ a : ℝ, 0 < a ∧ a < 1 → ¬(1 - Real.log a < a) := by
  intro a h
  simp [h.1, h.2, Real.log_le_sub_one_of_pos]
  nlinarith [Real.log_le_sub_one_of_pos h.1]

theorem lean_workbook_1610_0 (x y z a b c : ℝ) : x > 0 ∧ y > 0 ∧ z > 0 ∧ a + b = z ∧ b + c = x ∧ c + a = y → a = (y + z - x) / 2 ∧ b = (z + x - y) / 2 ∧ c = (x + y - z) / 2 := by
  rintro ⟨x_pos, y_pos, z_pos, a_b_sum, b_c_sum, a_c_sum⟩
  constructor
  linarith only [a_b_sum, b_c_sum, a_c_sum]
  constructor
  linarith only [a_b_sum, b_c_sum, a_c_sum]
  linarith only [a_b_sum, b_c_sum, a_c_sum]
theorem lean_workbook_1610_1 (x y z a b c : ℝ) : x > 0 ∧ y > 0 ∧ z > 0 ∧ a + b = z ∧ b + c = x ∧ c + a = y → a = (y + z - x) / 2 ∧ b = (z + x - y) / 2 ∧ c = (x + y - z) / 2 := by
  rintro ⟨hx, hy, hz, h₁, h₂, h₃⟩
  refine' ⟨_, _, _⟩ <;> linarith [hx, hy, hz, h₁, h₂, h₃]
theorem lean_workbook_1610_2 (x y z a b c : ℝ) : x > 0 ∧ y > 0 ∧ z > 0 ∧ a + b = z ∧ b + c = x ∧ c + a = y → a = (y + z - x) / 2 ∧ b = (z + x - y) / 2 ∧ c = (x + y - z) / 2 := by
  intro h
  rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
  refine' ⟨_, _, _⟩ <;> linarith
theorem lean_workbook_1610_3 (x y z a b c : ℝ) : x > 0 ∧ y > 0 ∧ z > 0 ∧ a + b = z ∧ b + c = x ∧ c + a = y → a = (y + z - x) / 2 ∧ b = (z + x - y) / 2 ∧ c = (x + y - z) / 2 := by
  rintro ⟨x_pos, y_pos, z_pos, a_add_b_eq_z, b_add_c_eq_x, c_add_a_eq_y⟩
  refine' ⟨_, _, _⟩
  linarith [a_add_b_eq_z, b_add_c_eq_x, c_add_a_eq_y]
  linarith [a_add_b_eq_z, b_add_c_eq_x, c_add_a_eq_y]
  linarith [a_add_b_eq_z, b_add_c_eq_x, c_add_a_eq_y]
theorem lean_workbook_1610_4 (x y z a b c : ℝ) : x > 0 ∧ y > 0 ∧ z > 0 ∧ a + b = z ∧ b + c = x ∧ c + a = y → a = (y + z - x) / 2 ∧ b = (z + x - y) / 2 ∧ c = (x + y - z) / 2 := by
  rintro ⟨hx, hy, hz, h1, h2, h3⟩
  refine ⟨?_,?_,?_⟩ <;> linarith only [hx, hy, hz, h1, h2, h3]
theorem lean_workbook_1610_5 (x y z a b c : ℝ) : x > 0 ∧ y > 0 ∧ z > 0 ∧ a + b = z ∧ b + c = x ∧ c + a = y → a = (y + z - x) / 2 ∧ b = (z + x - y) / 2 ∧ c = (x + y - z) / 2 := by
  rintro ⟨hx, hy, hz, hab, hbc, hca⟩
  refine' ⟨_, _, _⟩
  linarith [hab, hbc, hca]
  linarith [hab, hbc, hca]
  linarith [hab, hbc, hca]
theorem lean_workbook_1610_6 (x y z a b c : ℝ) : x > 0 ∧ y > 0 ∧ z > 0 ∧ a + b = z ∧ b + c = x ∧ c + a = y → a = (y + z - x) / 2 ∧ b = (z + x - y) / 2 ∧ c = (x + y - z) / 2 := by
  rintro ⟨hx, hy, hz, ha, hb, hc⟩
  refine' ⟨_, _, _⟩
  linarith [ha, hb, hc]
  linarith [ha, hb, hc]
  linarith [ha, hb, hc]
theorem lean_workbook_1610_7 (x y z a b c : ℝ) : x > 0 ∧ y > 0 ∧ z > 0 ∧ a + b = z ∧ b + c = x ∧ c + a = y → a = (y + z - x) / 2 ∧ b = (z + x - y) / 2 ∧ c = (x + y - z) / 2 := by
  rintro ⟨hx, hy, hz, h₁, h₂, h₃⟩
  refine' ⟨_, _, _⟩
  linarith
  linarith
  linarith
theorem lean_workbook_1610_8 (x y z a b c : ℝ) : x > 0 ∧ y > 0 ∧ z > 0 ∧ a + b = z ∧ b + c = x ∧ c + a = y → a = (y + z - x) / 2 ∧ b = (z + x - y) / 2 ∧ c = (x + y - z) / 2 := by
  rintro ⟨x_pos, y_pos, z_pos, h1, h2, h3⟩
  constructor
  linarith [h1, h2, h3]
  constructor
  linarith [h1, h2, h3]
  linarith [h1, h2, h3]
theorem lean_workbook_1610_9 (x y z a b c : ℝ) : x > 0 ∧ y > 0 ∧ z > 0 ∧ a + b = z ∧ b + c = x ∧ c + a = y → a = (y + z - x) / 2 ∧ b = (z + x - y) / 2 ∧ c = (x + y - z) / 2 := by
  rintro ⟨hx, hy, hz, hz1, hz2, hz3⟩
  exact ⟨by linarith, by linarith, by linarith⟩
theorem lean_workbook_1610_10 (x y z a b c : ℝ) : x > 0 ∧ y > 0 ∧ z > 0 ∧ a + b = z ∧ b + c = x ∧ c + a = y → a = (y + z - x) / 2 ∧ b = (z + x - y) / 2 ∧ c = (x + y - z) / 2 := by
  rintro ⟨h1, h2, h3, h4, h5, h6⟩
  refine' ⟨_, _, _⟩ <;> linarith
theorem lean_workbook_1610_11 (x y z a b c : ℝ) : x > 0 ∧ y > 0 ∧ z > 0 ∧ a + b = z ∧ b + c = x ∧ c + a = y → a = (y + z - x) / 2 ∧ b = (z + x - y) / 2 ∧ c = (x + y - z) / 2 := by
  rintro ⟨hx, hy, hz, hab, hbc, hca⟩
  refine' ⟨_, _, _⟩ <;> linarith
theorem lean_workbook_1610_12 (x y z a b c : ℝ) : x > 0 ∧ y > 0 ∧ z > 0 ∧ a + b = z ∧ b + c = x ∧ c + a = y → a = (y + z - x) / 2 ∧ b = (z + x - y) / 2 ∧ c = (x + y - z) / 2 := by
  intro h
  refine' ⟨_, _, _⟩ <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2]
theorem lean_workbook_1610_13 (x y z a b c : ℝ) : x > 0 ∧ y > 0 ∧ z > 0 ∧ a + b = z ∧ b + c = x ∧ c + a = y → a = (y + z - x) / 2 ∧ b = (z + x - y) / 2 ∧ c = (x + y - z) / 2 := by
  exact fun h => ⟨ by linarith [h.2.2.1], by linarith [h.2.2.1], by linarith [h.2.2.1] ⟩
theorem lean_workbook_1610_14 (x y z a b c : ℝ) : x > 0 ∧ y > 0 ∧ z > 0 ∧ a + b = z ∧ b + c = x ∧ c + a = y → a = (y + z - x) / 2 ∧ b = (z + x - y) / 2 ∧ c = (x + y - z) / 2 := by
  intro h
  obtain ⟨hx, hy, hz, hab, hbc, hca⟩ := h
  refine' ⟨_, _, _⟩
  linarith only [hx, hy, hz, hab, hbc, hca]
  linarith only [hx, hy, hz, hab, hbc, hca]
  linarith only [hx, hy, hz, hab, hbc, hca]
theorem lean_workbook_1610_15 (x y z a b c : ℝ) : x > 0 ∧ y > 0 ∧ z > 0 ∧ a + b = z ∧ b + c = x ∧ c + a = y → a = (y + z - x) / 2 ∧ b = (z + x - y) / 2 ∧ c = (x + y - z) / 2 := by
  rintro ⟨hx, hy, hz, h1, h2, h3⟩
  constructor
  linarith [h1, h2, h3]
  constructor
  linarith [h1, h2, h3]
  linarith [h1, h2, h3]
theorem lean_workbook_1610_16 (x y z a b c : ℝ) : x > 0 ∧ y > 0 ∧ z > 0 ∧ a + b = z ∧ b + c = x ∧ c + a = y → a = (y + z - x) / 2 ∧ b = (z + x - y) / 2 ∧ c = (x + y - z) / 2 := by
  rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
  refine' ⟨_, _, _⟩ <;> linarith

theorem lean_workbook_1627_0 : Real.cos 10 = Real.cos 10 := by
  simp only [cos_zero, mul_zero, add_zero, sub_self, cos_pi]
theorem lean_workbook_1627_1 : Real.cos 10 = Real.cos 10 := by
  simp only [cos_antiperiodic]
theorem lean_workbook_1627_2 : Real.cos 10 = Real.cos 10 := by
  simp only [Real.cos_antiperiodic]
theorem lean_workbook_1627_3 : Real.cos 10 = Real.cos 10 := by
  simp [show (10 : ℝ) = 10 by norm_num]
theorem lean_workbook_1627_4 : Real.cos 10 = Real.cos 10 := by
  exact Eq.refl (Real.cos 10)
theorem lean_workbook_1627_5 : Real.cos 10 = Real.cos 10 := by
  norm_num [cos_add]
theorem lean_workbook_1627_6 : Real.cos 10 = Real.cos 10 := by
  norm_num [cos_three_mul]
theorem lean_workbook_1627_7 : Real.cos 10 = Real.cos 10 := by
  simp [Real.cos_add]
theorem lean_workbook_1627_8 : Real.cos 10 = Real.cos 10 := by
  simp [cos_antiperiodic]
theorem lean_workbook_1627_9 : Real.cos 10 = Real.cos 10 := by
  norm_num [cos_add, cos_antiperiodic]
theorem lean_workbook_1627_10 : Real.cos 10 = Real.cos 10 := by
  simp [Nat.add_zero]
theorem lean_workbook_1627_11 : Real.cos 10 = Real.cos 10 := by
  norm_num [Real.cos, Real.exp]
theorem lean_workbook_1627_12 : Real.cos 10 = Real.cos 10 := by
  simp [cos_10]
theorem lean_workbook_1627_13 : Real.cos 10 = Real.cos 10 := by
  norm_num [cos_add, cos_two_mul, cos_three_mul]
theorem lean_workbook_1627_14 : Real.cos 10 = Real.cos 10 := by
  simp [cos_two_mul, cos_three_mul]
theorem lean_workbook_1627_15 : Real.cos 10 = Real.cos 10 := by
  simp [Real.cos, Real.sin, Real.exp, Real.log, Complex.cos, Complex.sin, Complex.exp, Complex.log]
theorem lean_workbook_1627_16 : Real.cos 10 = Real.cos 10 := by
  simp [← cos_pi_div_two_sub]
theorem lean_workbook_1627_17 : Real.cos 10 = Real.cos 10 := by
  norm_cast at *
theorem lean_workbook_1627_18 : Real.cos 10 = Real.cos 10 := by
  norm_num [Real.cos_antiperiodic]
theorem lean_workbook_1627_19 : Real.cos 10 = Real.cos 10 := by
  simp only [← le_antisymm_iff]
theorem lean_workbook_1627_20 : Real.cos 10 = Real.cos 10 := by
  field_simp [cos_10]
theorem lean_workbook_1627_21 : Real.cos 10 = Real.cos 10 := by
  norm_num [cos_zero]
theorem lean_workbook_1627_22 : Real.cos 10 = Real.cos 10 := by
  simp [cos_add]
theorem lean_workbook_1627_23 : Real.cos 10 = Real.cos 10 := by
  norm_num [cos_sq_add_sin_sq (10 : ℝ)]

theorem lean_workbook_1629_0 (a b c : ℝ) (h : a + b + c = 3) : a * b + b * c + c * a <= 3 := by
  have : 0 ≤ (a - b)^2 + (b - c)^2 + (c - a)^2 := by positivity
  nlinarith
theorem lean_workbook_1629_1 (a b c : ℝ) (h : a + b + c = 3) : a * b + b * c + c * a <= 3 := by
  ring_nf
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1629_2 (a b c : ℝ) (h : a + b + c = 3) : a * b + b * c + c * a <= 3 := by
  have h1 := sq_nonneg (a - 1)
  have h2 := sq_nonneg (b - 1)
  have h3 := sq_nonneg (c - 1)
  nlinarith
theorem lean_workbook_1629_3 (a b c : ℝ) (h : a + b + c = 3) : a * b + b * c + c * a <= 3 := by
  have h1 : 0 ≤ (a - b)^2 + (b - c)^2 + (c - a)^2 := by positivity
  simp at h1
  nlinarith
theorem lean_workbook_1629_4 (a b c : ℝ) (h : a + b + c = 3) : a * b + b * c + c * a <= 3 := by
  have : (a - 1)^2 + (b - 1)^2 + (c - 1)^2 ≥ 0 := by positivity
  nlinarith
theorem lean_workbook_1629_5 (a b c : ℝ) (h : a + b + c = 3) : a * b + b * c + c * a <= 3 := by
  have h1 : 0 ≤ (a - 1)^2 + (b - 1)^2 + (c - 1)^2 := by nlinarith
  nlinarith
theorem lean_workbook_1629_6 (a b c : ℝ) (h : a + b + c = 3) : a * b + b * c + c * a <= 3 := by
  have hv := sq_nonneg (a - b)
  have hw := sq_nonneg (b - c)
  have hy := sq_nonneg (c - a)
  nlinarith
theorem lean_workbook_1629_7 (a b c : ℝ) (h : a + b + c = 3) : a * b + b * c + c * a <= 3 := by
  have h3 : 0 ≤ (a - 1)^2 + (b - 1)^2 + (c - 1)^2 := by nlinarith
  nlinarith
theorem lean_workbook_1629_8 (a b c : ℝ) (h : a + b + c = 3) : a * b + b * c + c * a <= 3 := by
  have : 0 ≤ (a - 1)^2 + (b - 1)^2 + (c - 1)^2 := by positivity
  nlinarith [h]
theorem lean_workbook_1629_9 (a b c : ℝ) (h : a + b + c = 3) : a * b + b * c + c * a <= 3 := by
  have h1 : 0 ≤ (a - b)^2 + (b - c)^2 + (c - a)^2 := by nlinarith
  nlinarith [h1, h]
theorem lean_workbook_1629_10 (a b c : ℝ) (h : a + b + c = 3) : a * b + b * c + c * a <= 3 := by
  have hab := sq_nonneg (a - b)
  have hbc := sq_nonneg (b - c)
  have hac := sq_nonneg (c - a)
  nlinarith
theorem lean_workbook_1629_11 (a b c : ℝ) (h : a + b + c = 3) : a * b + b * c + c * a <= 3 := by
  have h1 : 0 ≤ (a - b)^2 + (b - c)^2 + (c - a)^2 := by positivity
  nlinarith
theorem lean_workbook_1629_12 (a b c : ℝ) (h : a + b + c = 3) : a * b + b * c + c * a <= 3 := by
  have : 0 ≤ (a - 1)^2 + (b - 1)^2 + (c - 1)^2 := by nlinarith
  nlinarith [h, this]
theorem lean_workbook_1629_13 (a b c : ℝ) (h : a + b + c = 3) : a * b + b * c + c * a <= 3 := by
  nlinarith [sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a - b)]
theorem lean_workbook_1629_14 (a b c : ℝ) (h : a + b + c = 3) : a * b + b * c + c * a <= 3 := by
  rw [← sub_nonneg]
  ring_nf
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1629_15 (a b c : ℝ) (h : a + b + c = 3) : a * b + b * c + c * a <= 3 := by
  rw [← h]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1629_16 (a b c : ℝ) (h : a + b + c = 3) : a * b + b * c + c * a <= 3 := by
  have : 0 ≤ (a-1)^2 + (b-1)^2 + (c-1)^2 := by nlinarith
  nlinarith
theorem lean_workbook_1629_17 (a b c : ℝ) (h : a + b + c = 3) : a * b + b * c + c * a <= 3 := by
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]

theorem lean_workbook_1630_0 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  have := sq_nonneg (x / 2 - (y - z))
  linarith
theorem lean_workbook_1630_1 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  ring_nf
  have h1 := sq_nonneg (x / 2 - y + z)
  linarith [sq_nonneg (x / 2 + y - z)]
theorem lean_workbook_1630_2 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  have h2 : 0 ≤ (x / 2 - y + z)^2 := sq_nonneg (_ - _ + _)
  linarith [h2]
theorem lean_workbook_1630_3 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  ring_nf
  norm_cast
  linarith [sq_nonneg (x / 2 - y + z)]
theorem lean_workbook_1630_4 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  linarith only [sq_nonneg (x / 2 - y + z)]
theorem lean_workbook_1630_5 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  have : (x/2 - y + z)^2 ≥ 0 := sq_nonneg (x/2 - y + z)
  linarith [sq_nonneg (x/2 - y + z)]
theorem lean_workbook_1630_6 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  ring_nf
  field_simp
  ring_nf
  nlinarith [sq_nonneg (x / 2 - y + z)]
theorem lean_workbook_1630_7 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  field_simp [add_comm]
  nlinarith [sq_nonneg (x - 2 * y + 2 * z)]
theorem lean_workbook_1630_8 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  have := sq_nonneg (x / 2 - y + z)
  linarith only [this]
theorem lean_workbook_1630_9 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  have : (x / 2 - y + z)^2 ≥ 0 := sq_nonneg (x / 2 - y + z)
  linarith [this]
theorem lean_workbook_1630_10 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  have := sq_nonneg (x / 2 - (y - z))
  linarith [sq_nonneg (y - z)]
theorem lean_workbook_1630_11 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  have := sq_nonneg (x / 2 - y + z)
  linarith [sq_nonneg (x / 2 - y + z)]
theorem lean_workbook_1630_12 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  have h0 : 0 ≤ (x / 2 - y + z)^2 := sq_nonneg (x / 2 - y + z)
  linarith
theorem lean_workbook_1630_13 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  have h1 : 0 ≤ (x / 2 - y + z)^2 := sq_nonneg (x / 2 - y + z)
  linarith
theorem lean_workbook_1630_14 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  ring_nf
  linarith [sq_nonneg (x / 2 - y + z)]
theorem lean_workbook_1630_15 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  have t := sq_nonneg (x / 2 - y + z)
  linarith
theorem lean_workbook_1630_16 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  have := sq_nonneg (x / 2 - y + z)
  linarith [sq_nonneg (x / 2 + y - z)]
theorem lean_workbook_1630_17 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  field_simp [sq]
  ring_nf
  linarith [sq_nonneg (x / 2 - y + z)]
theorem lean_workbook_1630_18 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  have := sq_nonneg (x / 2 - y + z)
  linarith [sq_nonneg (x / 2 - y), sq_nonneg (x / 2 - z)]
theorem lean_workbook_1630_19 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  ring_nf
  have h1 : 0 ≤ (x/2 - y + z)^2 := sq_nonneg (x/2 - y + z)
  linarith
theorem lean_workbook_1630_20 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  have h1 := sq_nonneg (x / 2 - y + z)
  linarith [sq_nonneg (x / 2 - y - z)]
theorem lean_workbook_1630_21 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  have h1 := sq_nonneg (y - z)
  have h2 := sq_nonneg (x - 2 * y + 2 * z)
  field_simp [h1, h2]
  linarith
theorem lean_workbook_1630_22 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  have := sq_nonneg (x / 2 - (y - z))
  linarith [sq_nonneg (x / 2 - (y - z))]
theorem lean_workbook_1630_23 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  have : (x - 2 * y + 2 * z)^2 ≥ 0 := sq_nonneg _
  linarith
theorem lean_workbook_1630_24 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  field_simp
  linarith [sq_nonneg (x / 2 - y + z)]
theorem lean_workbook_1630_25 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  have : (x/2 - y + z)^2 ≥ 0 := sq_nonneg (x/2 - y + z)
  linarith
theorem lean_workbook_1630_26 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  nlinarith [sq_nonneg (x - 2 * y + 2 * z), sq_nonneg (x + 2 * y - 2 * z)]
theorem lean_workbook_1630_27 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  have h1 : 0 ≤ (x/2 - y + z)^2 := sq_nonneg (x/2 - y + z)
  linarith
theorem lean_workbook_1630_28 (x y z : ℝ) : x^2 / 4 + y^2 + z^2 ≥ x * y - x * z + 2 * y * z := by
  have h1 : 0 ≤ (x/2 - y + z)^2 := sq_nonneg _
  linarith

theorem lean_workbook_1646_0 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3*c^2 + a^2*b^3 + a*b^4 + b^2*c^3 + b^3*c^2 ≥ a^2*b^2*c + 2*a*b^3*c + 2*a*b^2*c^2 := by
  nlinarith [sq_nonneg (a*c - b^2), sq_nonneg (a*b - b*c), sq_nonneg (b*c - a*c)]
theorem lean_workbook_1646_1 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3*c^2 + a^2*b^3 + a*b^4 + b^2*c^3 + b^3*c^2 ≥ a^2*b^2*c + 2*a*b^3*c + 2*a*b^2*c^2 := by
  ring_nf
  ring_nf
  nlinarith [sq_nonneg (a*c - b^2), sq_nonneg (b*c - a*b), sq_nonneg (a*b - b*c)]
theorem lean_workbook_1646_2 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3*c^2 + a^2*b^3 + a*b^4 + b^2*c^3 + b^3*c^2 ≥ a^2*b^2*c + 2*a*b^3*c + 2*a*b^2*c^2 := by
  simp [add_comm, add_left_comm]
  nlinarith [sq_nonneg (a*c - b^2), sq_nonneg (b*c - a*b), sq_nonneg (a*b - c^2)]
theorem lean_workbook_1646_3 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3*c^2 + a^2*b^3 + a*b^4 + b^2*c^3 + b^3*c^2 ≥ a^2*b^2*c + 2*a*b^3*c + 2*a*b^2*c^2 := by
  ring_nf
  have h1 := sq_nonneg (a*c - b^2)
  have h2 := sq_nonneg (b*c - a*b)
  nlinarith
theorem lean_workbook_1646_4 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3*c^2 + a^2*b^3 + a*b^4 + b^2*c^3 + b^3*c^2 ≥ a^2*b^2*c + 2*a*b^3*c + 2*a*b^2*c^2 := by
  field_simp [mul_assoc]
  nlinarith [sq_nonneg (a*c - b^2), sq_nonneg (a*b - b*c), sq_nonneg (b*c - a*c)]
theorem lean_workbook_1646_5 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3*c^2 + a^2*b^3 + a*b^4 + b^2*c^3 + b^3*c^2 ≥ a^2*b^2*c + 2*a*b^3*c + 2*a*b^2*c^2 := by
  nlinarith [sq_nonneg (a*c - b^2), sq_nonneg (b*c - a*b), sq_nonneg (a*b - b*c)]

theorem lean_workbook_1702_0 (x : ℝ) : ↑⌊x⌋ ≤ x ∧ x < ↑⌊x⌋ + 1 := by
  refine' ⟨_, _⟩
  exact Int.floor_le x
  exact Int.lt_floor_add_one x
theorem lean_workbook_1702_1 (x : ℝ) : ↑⌊x⌋ ≤ x ∧ x < ↑⌊x⌋ + 1 := by
  refine ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
theorem lean_workbook_1702_2 (x : ℝ) : ↑⌊x⌋ ≤ x ∧ x < ↑⌊x⌋ + 1 := by
  refine' ⟨Int.floor_le _, _⟩
  exact Int.lt_floor_add_one x
theorem lean_workbook_1702_3 (x : ℝ) : ↑⌊x⌋ ≤ x ∧ x < ↑⌊x⌋ + 1 := by
  refine ⟨?_,?_⟩
  exact (Int.floor_le x)
  exact (Int.lt_floor_add_one x)
theorem lean_workbook_1702_4 (x : ℝ) : ↑⌊x⌋ ≤ x ∧ x < ↑⌊x⌋ + 1 := by
  constructor
  exact mod_cast (Int.floor_le x)
  exact mod_cast (Int.lt_floor_add_one x)
theorem lean_workbook_1702_5 (x : ℝ) : ↑⌊x⌋ ≤ x ∧ x < ↑⌊x⌋ + 1 := by
  refine' ⟨_, _⟩
  exact (Int.floor_le x).trans (le_of_eq rfl)
  exact Int.lt_floor_add_one x
theorem lean_workbook_1702_6 (x : ℝ) : ↑⌊x⌋ ≤ x ∧ x < ↑⌊x⌋ + 1 := by
  constructor
  exact Int.floor_le x
  apply Int.lt_floor_add_one
theorem lean_workbook_1702_7 (x : ℝ) : ↑⌊x⌋ ≤ x ∧ x < ↑⌊x⌋ + 1 := by
  constructor
  exact (Int.floor_le x)
  exact (Int.lt_floor_add_one x)
theorem lean_workbook_1702_8 (x : ℝ) : ↑⌊x⌋ ≤ x ∧ x < ↑⌊x⌋ + 1 := by
  constructor
  exact Int.floor_le x
  exact Int.lt_floor_add_one x
theorem lean_workbook_1702_9 (x : ℝ) : ↑⌊x⌋ ≤ x ∧ x < ↑⌊x⌋ + 1 := by
  exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
theorem lean_workbook_1702_10 (x : ℝ) : ↑⌊x⌋ ≤ x ∧ x < ↑⌊x⌋ + 1 := by
  refine ⟨Int.floor_le x,?_⟩
  have h : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have h₁ := Int.lt_floor_add_one x
  exact h₁
theorem lean_workbook_1702_11 (x : ℝ) : ↑⌊x⌋ ≤ x ∧ x < ↑⌊x⌋ + 1 := by
  apply And.intro
  exact mod_cast Int.floor_le x
  exact mod_cast Int.lt_floor_add_one x
theorem lean_workbook_1702_12 (x : ℝ) : ↑⌊x⌋ ≤ x ∧ x < ↑⌊x⌋ + 1 := by
  constructor
  exact mod_cast Int.floor_le x
  exact mod_cast Int.lt_floor_add_one x
theorem lean_workbook_1702_13 (x : ℝ) : ↑⌊x⌋ ≤ x ∧ x < ↑⌊x⌋ + 1 := by
  refine' ⟨_, _⟩
  exact (Int.floor_le x)
  exact (Int.lt_floor_add_one x)
theorem lean_workbook_1702_14 (x : ℝ) : ↑⌊x⌋ ≤ x ∧ x < ↑⌊x⌋ + 1 := by
  use Int.floor_le x
  exact mod_cast Int.lt_floor_add_one x
theorem lean_workbook_1702_15 (x : ℝ) : ↑⌊x⌋ ≤ x ∧ x < ↑⌊x⌋ + 1 := by
  refine' ⟨Int.floor_le x, _⟩
  exact Int.lt_floor_add_one x

theorem lean_workbook_1708_0 (a b c : ℝ) : (a^2 + b^2) * (a^2 + c^2) ≥ (a^2 + b * c)^2 := by
  have h1 : 0 ≤ (a * b - a * c)^2 := sq_nonneg _
  linarith [sq_nonneg (b - c)]
theorem lean_workbook_1708_1 (a b c : ℝ) : (a^2 + b^2) * (a^2 + c^2) ≥ (a^2 + b * c)^2 := by
  have h1 := sq_nonneg (a * b - a * c)
  linarith
theorem lean_workbook_1708_2 (a b c : ℝ) : (a^2 + b^2) * (a^2 + c^2) ≥ (a^2 + b * c)^2 := by
  ring_nf
  norm_cast
  nlinarith [sq_nonneg (b - c)]
theorem lean_workbook_1708_3 (a b c : ℝ) : (a^2 + b^2) * (a^2 + c^2) ≥ (a^2 + b * c)^2 := by
  have h₁ : 0 ≤ (a * b - a * c)^2 := sq_nonneg _
  linarith [sq_nonneg (b - c)]
theorem lean_workbook_1708_4 (a b c : ℝ) : (a^2 + b^2) * (a^2 + c^2) ≥ (a^2 + b * c)^2 := by
  have h1: 0 ≤ (a * b - a * c)^2 := sq_nonneg _
  linarith
theorem lean_workbook_1708_5 (a b c : ℝ) : (a^2 + b^2) * (a^2 + c^2) ≥ (a^2 + b * c)^2 := by
  rw [pow_two, pow_two]
  nlinarith [sq_nonneg (b - c)]
theorem lean_workbook_1708_6 (a b c : ℝ) : (a^2 + b^2) * (a^2 + c^2) ≥ (a^2 + b * c)^2 := by
  have h1 : 0 ≤ (a * b - a * c)^2 := sq_nonneg _
  linarith
theorem lean_workbook_1708_7 (a b c : ℝ) : (a^2 + b^2) * (a^2 + c^2) ≥ (a^2 + b * c)^2 := by
  ring_nf
  nlinarith [sq_nonneg (b - c)]
theorem lean_workbook_1708_8 (a b c : ℝ) : (a^2 + b^2) * (a^2 + c^2) ≥ (a^2 + b * c)^2 := by
  have h0 : 0 ≤ (b - c)^2 := sq_nonneg (b - c)
  nlinarith
theorem lean_workbook_1708_9 (a b c : ℝ) : (a^2 + b^2) * (a^2 + c^2) ≥ (a^2 + b * c)^2 := by
  have h₁ : 0 ≤ (a * b - a * c)^2 := sq_nonneg _
  linarith
theorem lean_workbook_1708_10 (a b c : ℝ) : (a^2 + b^2) * (a^2 + c^2) ≥ (a^2 + b * c)^2 := by
  nlinarith [sq_nonneg (a * b - a * c), sq_nonneg (b - c)]
theorem lean_workbook_1708_11 (a b c : ℝ) : (a^2 + b^2) * (a^2 + c^2) ≥ (a^2 + b * c)^2 := by
  field_simp [sq]
  nlinarith [sq_nonneg (a * b - a * c)]
theorem lean_workbook_1708_12 (a b c : ℝ) : (a^2 + b^2) * (a^2 + c^2) ≥ (a^2 + b * c)^2 := by
  simp [add_mul, mul_add, mul_comm, mul_left_comm]
  nlinarith [sq_nonneg (a * b - a * c)]
theorem lean_workbook_1708_13 (a b c : ℝ) : (a^2 + b^2) * (a^2 + c^2) ≥ (a^2 + b * c)^2 := by
  have h1 : 0 ≤ (a * b - a * c)^2 := sq_nonneg _
  linarith [sq_nonneg (a * b + a * c)]
theorem lean_workbook_1708_14 (a b c : ℝ) : (a^2 + b^2) * (a^2 + c^2) ≥ (a^2 + b * c)^2 := by
  rw [pow_two]
  nlinarith [sq_nonneg (b - c)]
theorem lean_workbook_1708_15 (a b c : ℝ) : (a^2 + b^2) * (a^2 + c^2) ≥ (a^2 + b * c)^2 := by
  have h2 : 0 ≤ (a * b - a * c)^2 := sq_nonneg _
  linarith
theorem lean_workbook_1708_16 (a b c : ℝ) : (a^2 + b^2) * (a^2 + c^2) ≥ (a^2 + b * c)^2 := by
  simp [mul_add, mul_comm, mul_left_comm]
  nlinarith [sq_nonneg (b - c)]
theorem lean_workbook_1708_17 (a b c : ℝ) : (a^2 + b^2) * (a^2 + c^2) ≥ (a^2 + b * c)^2 := by
  rw [sq, sq]
  nlinarith [sq_nonneg (b - c)]
theorem lean_workbook_1708_18 (a b c : ℝ) : (a^2 + b^2) * (a^2 + c^2) ≥ (a^2 + b * c)^2 := by
  linarith [sq_nonneg (a * b - a * c), sq_nonneg (b * c - a^2)]
theorem lean_workbook_1708_19 (a b c : ℝ) : (a^2 + b^2) * (a^2 + c^2) ≥ (a^2 + b * c)^2 := by
  nlinarith [sq_nonneg (b - c), sq_nonneg (a^2 + b * c)]
theorem lean_workbook_1708_20 (a b c : ℝ) : (a^2 + b^2) * (a^2 + c^2) ≥ (a^2 + b * c)^2 := by
  simp [sq]
  have h1 : 0 ≤ (a * b - a * c)^2 := sq_nonneg _
  linarith
theorem lean_workbook_1708_21 (a b c : ℝ) : (a^2 + b^2) * (a^2 + c^2) ≥ (a^2 + b * c)^2 := by
  rw [sq]
  nlinarith [sq_nonneg (b - c)]
theorem lean_workbook_1708_22 (a b c : ℝ) : (a^2 + b^2) * (a^2 + c^2) ≥ (a^2 + b * c)^2 := by
  ring_nf
  nlinarith [sq_nonneg (a * b - a * c)]
theorem lean_workbook_1708_23 (a b c : ℝ) : (a^2 + b^2) * (a^2 + c^2) ≥ (a^2 + b * c)^2 := by
  ring_nf
  ring_nf
  nlinarith [sq_nonneg (b - c)]

theorem lean_workbook_1716_0 (a b c : ℝ) (h₁ : a + b + c = 11) (h₂ : a^2 + b^2 + c^2 = 49) : a * b + b * c + c * a = 36 := by
  simp [← h₁, pow_two] at h₂ ⊢
  nlinarith
theorem lean_workbook_1716_1 (a b c : ℝ) (h₁ : a + b + c = 11) (h₂ : a^2 + b^2 + c^2 = 49) : a * b + b * c + c * a = 36 := by
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, h₁, h₂]
theorem lean_workbook_1716_2 (a b c : ℝ) (h₁ : a + b + c = 11) (h₂ : a^2 + b^2 + c^2 = 49) : a * b + b * c + c * a = 36 := by
  simp [add_comm, add_left_comm] at h₁
  nlinarith
theorem lean_workbook_1716_3 (a b c : ℝ) (h₁ : a + b + c = 11) (h₂ : a^2 + b^2 + c^2 = 49) : a * b + b * c + c * a = 36 := by
  field_simp [sq, add_assoc, add_comm, add_left_comm] at h₂ ⊢
  nlinarith [h₁, h₂]
theorem lean_workbook_1716_4 (a b c : ℝ) (h₁ : a + b + c = 11) (h₂ : a^2 + b^2 + c^2 = 49) : a * b + b * c + c * a = 36 := by
  simp [add_comm, add_left_comm, add_assoc, mul_add, mul_left_comm, mul_comm] at *
  nlinarith
theorem lean_workbook_1716_5 (a b c : ℝ) (h₁ : a + b + c = 11) (h₂ : a^2 + b^2 + c^2 = 49) : a * b + b * c + c * a = 36 := by
  simp [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] at h₁ h₂ ⊢
  nlinarith
theorem lean_workbook_1716_6 (a b c : ℝ) (h₁ : a + b + c = 11) (h₂ : a^2 + b^2 + c^2 = 49) : a * b + b * c + c * a = 36 := by
  ring_nf at *
  nlinarith
theorem lean_workbook_1716_7 (a b c : ℝ) (h₁ : a + b + c = 11) (h₂ : a^2 + b^2 + c^2 = 49) : a * b + b * c + c * a = 36 := by
  norm_num at h₁ h₂ ⊢
  nlinarith [h₁, h₂]
theorem lean_workbook_1716_8 (a b c : ℝ) (h₁ : a + b + c = 11) (h₂ : a^2 + b^2 + c^2 = 49) : a * b + b * c + c * a = 36 := by
  repeat nlinarith [h₁, h₂]
theorem lean_workbook_1716_9 (a b c : ℝ) (h₁ : a + b + c = 11) (h₂ : a^2 + b^2 + c^2 = 49) : a * b + b * c + c * a = 36 := by
  ring_nf at h₁ h₂ ⊢
  nlinarith [h₁, h₂]
theorem lean_workbook_1716_10 (a b c : ℝ) (h₁ : a + b + c = 11) (h₂ : a^2 + b^2 + c^2 = 49) : a * b + b * c + c * a = 36 := by
  repeat nlinarith
theorem lean_workbook_1716_11 (a b c : ℝ) (h₁ : a + b + c = 11) (h₂ : a^2 + b^2 + c^2 = 49) : a * b + b * c + c * a = 36 := by
  ring_nf at h₁ h₂ ⊢
  nlinarith only [h₁, h₂]

theorem lean_workbook_1723_0 {x : ℝ} (hx : 0 < x ∧ x < 1) : (3 * x ^ 2 - 1) ^ 2 * (5 * x ^ 2 - 1) ^ 2 ≥ 0 := by
  apply mul_nonneg
  apply pow_two_nonneg
  apply pow_two_nonneg
theorem lean_workbook_1723_1 {x : ℝ} (hx : 0 < x ∧ x < 1) : (3 * x ^ 2 - 1) ^ 2 * (5 * x ^ 2 - 1) ^ 2 ≥ 0 := by
  nth_rw 1 [← one_mul (0 : ℝ)]
  nlinarith [hx.1, hx.2]
theorem lean_workbook_1723_2 {x : ℝ} (hx : 0 < x ∧ x < 1) : (3 * x ^ 2 - 1) ^ 2 * (5 * x ^ 2 - 1) ^ 2 ≥ 0 := by
  apply mul_nonneg
  exact sq_nonneg _
  exact sq_nonneg _
theorem lean_workbook_1723_3 {x : ℝ} (hx : 0 < x ∧ x < 1) : (3 * x ^ 2 - 1) ^ 2 * (5 * x ^ 2 - 1) ^ 2 ≥ 0 := by
  exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
theorem lean_workbook_1723_4 {x : ℝ} (hx : 0 < x ∧ x < 1) : (3 * x ^ 2 - 1) ^ 2 * (5 * x ^ 2 - 1) ^ 2 ≥ 0 := by
  repeat nlinarith [hx.1, hx.2]
theorem lean_workbook_1723_5 {x : ℝ} (hx : 0 < x ∧ x < 1) : (3 * x ^ 2 - 1) ^ 2 * (5 * x ^ 2 - 1) ^ 2 ≥ 0 := by
  apply mul_nonneg
  exact pow_two_nonneg _
  exact pow_two_nonneg _
theorem lean_workbook_1723_6 {x : ℝ} (hx : 0 < x ∧ x < 1) : (3 * x ^ 2 - 1) ^ 2 * (5 * x ^ 2 - 1) ^ 2 ≥ 0 := by
  simp only [sq_nonneg, mul_nonneg]
theorem lean_workbook_1723_7 {x : ℝ} (hx : 0 < x ∧ x < 1) : (3 * x ^ 2 - 1) ^ 2 * (5 * x ^ 2 - 1) ^ 2 ≥ 0 := by
  apply mul_nonneg
  nlinarith
  nlinarith [hx.1, hx.2]
theorem lean_workbook_1723_8 {x : ℝ} (hx : 0 < x ∧ x < 1) : (3 * x ^ 2 - 1) ^ 2 * (5 * x ^ 2 - 1) ^ 2 ≥ 0 := by
  apply mul_nonneg <;> apply sq_nonneg
theorem lean_workbook_1723_9 {x : ℝ} (hx : 0 < x ∧ x < 1) : (3 * x ^ 2 - 1) ^ 2 * (5 * x ^ 2 - 1) ^ 2 ≥ 0 := by
  apply mul_nonneg
  nlinarith [hx]
  nlinarith [hx]
theorem lean_workbook_1723_10 {x : ℝ} (hx : 0 < x ∧ x < 1) : (3 * x ^ 2 - 1) ^ 2 * (5 * x ^ 2 - 1) ^ 2 ≥ 0 := by
  apply mul_nonneg
  nlinarith only [hx.1, hx.2]
  nlinarith only [hx.1, hx.2]
theorem lean_workbook_1723_11 {x : ℝ} (hx : 0 < x ∧ x < 1) : (3 * x ^ 2 - 1) ^ 2 * (5 * x ^ 2 - 1) ^ 2 ≥ 0 := by
  have : 0 < x ^ 2 := pow_pos hx.1 2
  nlinarith [hx.1, hx.2]
theorem lean_workbook_1723_12 {x : ℝ} (hx : 0 < x ∧ x < 1) : (3 * x ^ 2 - 1) ^ 2 * (5 * x ^ 2 - 1) ^ 2 ≥ 0 := by
  simp only [pow_two]
  nlinarith [hx.1, hx.2]
theorem lean_workbook_1723_13 {x : ℝ} (hx : 0 < x ∧ x < 1) : (3 * x ^ 2 - 1) ^ 2 * (5 * x ^ 2 - 1) ^ 2 ≥ 0 := by
  obtain ⟨left, right⟩ := hx
  nlinarith
theorem lean_workbook_1723_14 {x : ℝ} (hx : 0 < x ∧ x < 1) : (3 * x ^ 2 - 1) ^ 2 * (5 * x ^ 2 - 1) ^ 2 ≥ 0 := by
  have : 0 < x ^ 2 := pow_pos hx.1 2
  nlinarith
theorem lean_workbook_1723_15 {x : ℝ} (hx : 0 < x ∧ x < 1) : (3 * x ^ 2 - 1) ^ 2 * (5 * x ^ 2 - 1) ^ 2 ≥ 0 := by
  apply mul_nonneg <;> apply pow_two_nonneg

theorem lean_workbook_1790_0 (n : ℕ) (b : ℕ → ℕ) : (∑ i in Finset.range n, (b i)^2) - (∑ i in Finset.range n, b i)^2 ≥ 0 := by
  simp [Finset.sum_nonneg]
theorem lean_workbook_1790_1 (n : ℕ) (b : ℕ → ℕ) : (∑ i in Finset.range n, (b i)^2) - (∑ i in Finset.range n, b i)^2 ≥ 0 := by
  simp only [ge_iff_le, sub_nonneg]
  apply Nat.zero_le
theorem lean_workbook_1790_2 (n : ℕ) (b : ℕ → ℕ) : (∑ i in Finset.range n, (b i)^2) - (∑ i in Finset.range n, b i)^2 ≥ 0 := by
  simp only [sq, sub_nonneg]
  nlinarith [sq_nonneg (∑ i in Finset.range n, b i)]
theorem lean_workbook_1790_3 (n : ℕ) (b : ℕ → ℕ) : (∑ i in Finset.range n, (b i)^2) - (∑ i in Finset.range n, b i)^2 ≥ 0 := by
  rw [ge_iff_le]
  simp only [Finset.sum_nonneg, Nat.zero_le, Nat.cast_nonneg]
theorem lean_workbook_1790_4 (n : ℕ) (b : ℕ → ℕ) : (∑ i in Finset.range n, (b i)^2) - (∑ i in Finset.range n, b i)^2 ≥ 0 := by
  simp only [sq, Nat.mul_self_le_mul_self, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_mul]
  nlinarith
theorem lean_workbook_1790_5 (n : ℕ) (b : ℕ → ℕ) : (∑ i in Finset.range n, (b i)^2) - (∑ i in Finset.range n, b i)^2 ≥ 0 := by
  simp [sq_nonneg, Finset.sum_nonneg]
theorem lean_workbook_1790_6 (n : ℕ) (b : ℕ → ℕ) : (∑ i in Finset.range n, (b i)^2) - (∑ i in Finset.range n, b i)^2 ≥ 0 := by
  nlinarith [sq_nonneg (∑ i in Finset.range n, b i)]

theorem lean_workbook_1805_0 : ∀ a b c : ℝ, 100 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 - 192 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 0 := by
  refine' fun a b c => sub_nonneg_of_le _
  ring_nf
  nlinarith [sq_nonneg (a * b + b * c + c * a)]
theorem lean_workbook_1805_1 : ∀ a b c : ℝ, 100 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 - 192 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 0 := by
  intro a b c
  nlinarith [sq_nonneg (a^2 + b^2 + c^2), sq_nonneg (a^2 * b^2 + b^2 * c^2 + c^2 * a^2)]
theorem lean_workbook_1805_2 : ∀ a b c : ℝ, 100 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 - 192 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 0 := by
  intros a b c
  ring_nf
  rw [add_comm]
  nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2)]
theorem lean_workbook_1805_3 : ∀ a b c : ℝ, 100 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 - 192 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 0 := by
  intro a b c
  ring_nf
  nlinarith [sq_nonneg (a * b + b * c + c * a)]
theorem lean_workbook_1805_4 : ∀ a b c : ℝ, 100 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 - 192 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 0 := by
  intro a b c
  simp [sq_nonneg]
  nlinarith [sq_nonneg (a * b + b * c + c * a)]
theorem lean_workbook_1805_5 : ∀ a b c : ℝ, 100 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 - 192 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 0 := by
  intros a b c
  nlinarith [sq_nonneg (a^2 + b^2 + c^2), sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2)]
theorem lean_workbook_1805_6 : ∀ a b c : ℝ, 100 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 - 192 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 0 := by
  simp [sub_nonneg]
  intro a b c
  nlinarith [sq_nonneg (a ^ 2 + b ^ 2 + c ^ 2), sq_nonneg (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2)]
theorem lean_workbook_1805_7 : ∀ a b c : ℝ, 100 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 - 192 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 0 := by
  refine' fun a b c => sub_nonneg_of_le _
  nlinarith [sq_nonneg (a ^ 2 + b ^ 2 + c ^ 2), sq_nonneg (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2)]
theorem lean_workbook_1805_8 : ∀ a b c : ℝ, 100 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 - 192 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 0 := by
  intros a b c
  simp only [sq]
  nlinarith [sq_nonneg (a * b + b * c + c * a)]
theorem lean_workbook_1805_9 : ∀ a b c : ℝ, 100 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 - 192 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 0 := by
  intro a b c
  nlinarith [sq_nonneg (a ^ 2 + b ^ 2 + c ^ 2), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2)]
theorem lean_workbook_1805_10 : ∀ a b c : ℝ, 100 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 - 192 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 0 := by
  intro a b c
  ring_nf
  norm_num
  ring_nf
  nlinarith [sq_nonneg (a * b + b * c + c * a)]
theorem lean_workbook_1805_11 : ∀ a b c : ℝ, 100 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 - 192 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 0 := by
  intro a b c
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

theorem lean_workbook_1806_0 (a b : ℝ) (h₁ : a + b = 2) : b = 2 - a := by
  simp only [sub_eq_add_neg]
  linarith [h₁]
theorem lean_workbook_1806_1 (a b : ℝ) (h₁ : a + b = 2) : b = 2 - a := by
  rw [← h₁]
  simp [add_comm]
theorem lean_workbook_1806_2 (a b : ℝ) (h₁ : a + b = 2) : b = 2 - a := by
  rw [← h₁, add_comm]
  simp [add_comm, add_left_comm, sub_eq_add_neg, add_assoc]
theorem lean_workbook_1806_3 (a b : ℝ) (h₁ : a + b = 2) : b = 2 - a := by
  exact eq_sub_of_add_eq' h₁
theorem lean_workbook_1806_4 (a b : ℝ) (h₁ : a + b = 2) : b = 2 - a := by
  simp only [sub_eq_add_neg]
  linarith
theorem lean_workbook_1806_5 (a b : ℝ) (h₁ : a + b = 2) : b = 2 - a := by
  rw [add_comm] at h₁
  linarith [h₁]
theorem lean_workbook_1806_6 (a b : ℝ) (h₁ : a + b = 2) : b = 2 - a := by
  rw [← h₁, add_comm a b]
  linarith [h₁]
theorem lean_workbook_1806_7 (a b : ℝ) (h₁ : a + b = 2) : b = 2 - a := by
  rw [add_comm] at h₁
  linarith
theorem lean_workbook_1806_8 (a b : ℝ) (h₁ : a + b = 2) : b = 2 - a := by
  rw [← h₁, add_comm]
  simp
theorem lean_workbook_1806_9 (a b : ℝ) (h₁ : a + b = 2) : b = 2 - a := by
  rw [← h₁, add_comm]
  linarith
theorem lean_workbook_1806_10 (a b : ℝ) (h₁ : a + b = 2) : b = 2 - a := by
  rw [← h₁, add_comm]
  linarith [h₁]
theorem lean_workbook_1806_11 (a b : ℝ) (h₁ : a + b = 2) : b = 2 - a := by
  linear_combination h₁
theorem lean_workbook_1806_12 (a b : ℝ) (h₁ : a + b = 2) : b = 2 - a := by
  rw [eq_comm] at h₁
  rw [eq_comm] at h₁
  linarith
theorem lean_workbook_1806_13 (a b : ℝ) (h₁ : a + b = 2) : b = 2 - a := by
  rw [← h₁, eq_comm]
  linarith
theorem lean_workbook_1806_14 (a b : ℝ) (h₁ : a + b = 2) : b = 2 - a := by
  rw [add_comm] at h₁
  rw [eq_comm] at h₁
  linarith only [h₁]
theorem lean_workbook_1806_15 (a b : ℝ) (h₁ : a + b = 2) : b = 2 - a := by
  rw [add_comm] at h₁
  rw [eq_sub_iff_add_eq]
  exact h₁
theorem lean_workbook_1806_16 (a b : ℝ) (h₁ : a + b = 2) : b = 2 - a := by
  nlinarith [h₁]
theorem lean_workbook_1806_17 (a b : ℝ) (h₁ : a + b = 2) : b = 2 - a := by
  rw [← h₁, add_comm a b]
  linarith
theorem lean_workbook_1806_18 (a b : ℝ) (h₁ : a + b = 2) : b = 2 - a := by
  rw [eq_comm] at h₁
  linarith [h₁]
theorem lean_workbook_1806_19 (a b : ℝ) (h₁ : a + b = 2) : b = 2 - a := by
  revert h₁
  intros
  linarith
theorem lean_workbook_1806_20 (a b : ℝ) (h₁ : a + b = 2) : b = 2 - a := by
  rw [← h₁, add_comm]
  simp [add_comm, add_left_comm]
theorem lean_workbook_1806_21 (a b : ℝ) (h₁ : a + b = 2) : b = 2 - a := by
  exact by linarith [h₁]
theorem lean_workbook_1806_22 (a b : ℝ) (h₁ : a + b = 2) : b = 2 - a := by
  linarith [h₁]
theorem lean_workbook_1806_23 (a b : ℝ) (h₁ : a + b = 2) : b = 2 - a := by
  rw [add_comm] at h₁
  rw [eq_comm] at h₁
  linarith [h₁]

theorem lean_workbook_1811_0 (a b c : ℝ) : (a + b + c)^2 ≥ 3 * (a * b + b * c + c * a) := by
  have h0 := sq_nonneg (a - b)
  have h1 := sq_nonneg (b - c)
  have h2 := sq_nonneg (c - a)
  linarith
theorem lean_workbook_1811_1 (a b c : ℝ) : (a + b + c)^2 ≥ 3 * (a * b + b * c + c * a) := by
  ring_nf
  have h1 := sq_nonneg (a - b)
  have h2 := sq_nonneg (b - c)
  have h3 := sq_nonneg (c - a)
  linarith
theorem lean_workbook_1811_2 (a b c : ℝ) : (a + b + c)^2 ≥ 3 * (a * b + b * c + c * a) := by
  simp [mul_add, add_mul, add_assoc, add_left_comm]
  have h1 := sq_nonneg (a - b)
  have h2 := sq_nonneg (b - c)
  have h3 := sq_nonneg (c - a)
  linarith
theorem lean_workbook_1811_3 (a b c : ℝ) : (a + b + c)^2 ≥ 3 * (a * b + b * c + c * a) := by
  have h1 := sq_nonneg (a - b)
  have h2 := sq_nonneg (b - c)
  have h3 := sq_nonneg (a - c)
  linarith
theorem lean_workbook_1811_4 (a b c : ℝ) : (a + b + c)^2 ≥ 3 * (a * b + b * c + c * a) := by
  simp [sq, mul_add, add_mul]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_1811_5 (a b c : ℝ) : (a + b + c)^2 ≥ 3 * (a * b + b * c + c * a) := by
  simp [add_sq]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1811_6 (a b c : ℝ) : (a + b + c)^2 ≥ 3 * (a * b + b * c + c * a) := by
  simp [add_sq]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_1811_7 (a b c : ℝ) : (a + b + c)^2 ≥ 3 * (a * b + b * c + c * a) := by
  have h1 := sq_nonneg (a - b)
  have h2 := sq_nonneg (b - c)
  have h3 := sq_nonneg (c - a)
  linarith
theorem lean_workbook_1811_8 (a b c : ℝ) : (a + b + c)^2 ≥ 3 * (a * b + b * c + c * a) := by
  simp [sq, add_assoc, add_comm, add_left_comm]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_1811_9 (a b c : ℝ) : (a + b + c)^2 ≥ 3 * (a * b + b * c + c * a) := by
  simp only [sq, add_mul, mul_add, mul_assoc, mul_left_comm]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1811_10 (a b c : ℝ) : (a + b + c)^2 ≥ 3 * (a * b + b * c + c * a) := by
  rw [add_assoc]
  nlinarith [sq_nonneg (a + b + c), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a - b)]
theorem lean_workbook_1811_11 (a b c : ℝ) : (a + b + c)^2 ≥ 3 * (a * b + b * c + c * a) := by
  have h1 : 0 ≤ (a - b)^2 + (b - c)^2 + (c - a)^2 := by nlinarith
  simp at h1
  nlinarith
theorem lean_workbook_1811_12 (a b c : ℝ) : (a + b + c)^2 ≥ 3 * (a * b + b * c + c * a) := by
  simp [add_mul, mul_add]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_1811_13 (a b c : ℝ) : (a + b + c)^2 ≥ 3 * (a * b + b * c + c * a) := by
  ring_nf
  ring_nf
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1811_14 (a b c : ℝ) : (a + b + c)^2 ≥ 3 * (a * b + b * c + c * a) := by
  suffices (a - b)^2 + (b - c)^2 + (c - a)^2 ≥ 0 by linarith
  nlinarith
theorem lean_workbook_1811_15 (a b c : ℝ) : (a + b + c)^2 ≥ 3 * (a * b + b * c + c * a) := by
  simp [sq]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_1811_16 (a b c : ℝ) : (a + b + c)^2 ≥ 3 * (a * b + b * c + c * a) := by
  field_simp [sq, mul_add, add_mul]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1811_17 (a b c : ℝ) : (a + b + c)^2 ≥ 3 * (a * b + b * c + c * a) := by
  simp [sq, mul_add, add_mul, mul_comm, mul_left_comm]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1811_18 (a b c : ℝ) : (a + b + c)^2 ≥ 3 * (a * b + b * c + c * a) := by
  simp only [sq, add_mul, mul_add]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1811_19 (a b c : ℝ) : (a + b + c)^2 ≥ 3 * (a * b + b * c + c * a) := by
  have h1 : 0 ≤ (a - b)^2 + (b - c)^2 + (c - a)^2 := by nlinarith
  linarith
theorem lean_workbook_1811_20 (a b c : ℝ) : (a + b + c)^2 ≥ 3 * (a * b + b * c + c * a) := by
  simp [sq, add_assoc, add_left_comm, add_comm]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1811_21 (a b c : ℝ) : (a + b + c)^2 ≥ 3 * (a * b + b * c + c * a) := by
  simp only [sq]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

theorem lean_workbook_1837_0 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 3 ≥ 27 * a * b * c := by
  simp only [pow_three]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_1837_1 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 3 ≥ 27 * a * b * c := by
  simp only [pow_three]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1837_2 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 3 ≥ 27 * a * b * c := by
  simp [add_comm]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1837_3 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 3 ≥ 27 * a * b * c := by
  simp [add_comm]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_1837_4 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 3 ≥ 27 * a * b * c := by
  rw [pow_three]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_1837_5 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 3 ≥ 27 * a * b * c := by
  simp [add_mul]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1837_6 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 3 ≥ 27 * a * b * c := by
  simp [add_assoc]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

theorem lean_workbook_1840_0 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z))^(2/3) + (y / (x + z))^(2/3) + (z / (x + y))^(2/3) ≥ 3 * (1 / 4)^(1/3) := by
  simp [inv_mul_cancel, add_comm, add_left_comm, add_assoc]
  nlinarith [hx, hy, hz]
theorem lean_workbook_1840_1 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z))^(2/3) + (y / (x + z))^(2/3) + (z / (x + y))^(2/3) ≥ 3 * (1 / 4)^(1/3) := by
  norm_num [pow_nonneg, add_pos, add_pos, add_pos, hx, hy, hz]
theorem lean_workbook_1840_2 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z))^(2/3) + (y / (x + z))^(2/3) + (z / (x + y))^(2/3) ≥ 3 * (1 / 4)^(1/3) := by
  simp [mul_comm]
  nlinarith [hx, hy, hz]
theorem lean_workbook_1840_3 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z))^(2/3) + (y / (x + z))^(2/3) + (z / (x + y))^(2/3) ≥ 3 * (1 / 4)^(1/3) := by
  eta_reduce at *
  eta_reduce at *
  eta_reduce at hx hy hz ⊢
  norm_num [hx, hy, hz]
theorem lean_workbook_1840_4 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z))^(2/3) + (y / (x + z))^(2/3) + (z / (x + y))^(2/3) ≥ 3 * (1 / 4)^(1/3) := by
  simp [sq]
  nlinarith [hx, hy, hz]
theorem lean_workbook_1840_5 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z))^(2/3) + (y / (x + z))^(2/3) + (z / (x + y))^(2/3) ≥ 3 * (1 / 4)^(1/3) := by
  simp [one_div]
  nlinarith [hx, hy, hz]
theorem lean_workbook_1840_6 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z))^(2/3) + (y / (x + z))^(2/3) + (z / (x + y))^(2/3) ≥ 3 * (1 / 4)^(1/3) := by
  simp [add_comm, add_left_comm, add_assoc]
  nlinarith [hx, hy, hz]
theorem lean_workbook_1840_7 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z))^(2/3) + (y / (x + z))^(2/3) + (z / (x + y))^(2/3) ≥ 3 * (1 / 4)^(1/3) := by
  simp [hx, hy, hz, zero_lt_one]
  norm_num
theorem lean_workbook_1840_8 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z))^(2/3) + (y / (x + z))^(2/3) + (z / (x + y))^(2/3) ≥ 3 * (1 / 4)^(1/3) := by
  simp [mul_add, add_mul]
  nlinarith [hx, hy, hz]
theorem lean_workbook_1840_9 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z))^(2/3) + (y / (x + z))^(2/3) + (z / (x + y))^(2/3) ≥ 3 * (1 / 4)^(1/3) := by
  simp [div_eq_inv_mul, add_comm, add_left_comm, add_assoc]
  nlinarith [hx, hy, hz]
theorem lean_workbook_1840_10 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z))^(2/3) + (y / (x + z))^(2/3) + (z / (x + y))^(2/3) ≥ 3 * (1 / 4)^(1/3) := by
  simp [add_comm, add_left_comm]
  nlinarith [hx, hy, hz]
theorem lean_workbook_1840_11 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z))^(2/3) + (y / (x + z))^(2/3) + (z / (x + y))^(2/3) ≥ 3 * (1 / 4)^(1/3) := by
  simp [div_pow]
  nlinarith [add_nonneg hx.le hy.le, add_nonneg hy.le hz.le, add_nonneg hz.le hx.le]
theorem lean_workbook_1840_12 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z))^(2/3) + (y / (x + z))^(2/3) + (z / (x + y))^(2/3) ≥ 3 * (1 / 4)^(1/3) := by
  simp [inv_mul_cancel, add_comm, add_left_comm, add_assoc] at *
  nlinarith [hx, hy, hz]
theorem lean_workbook_1840_13 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z))^(2/3) + (y / (x + z))^(2/3) + (z / (x + y))^(2/3) ≥ 3 * (1 / 4)^(1/3) := by
  rw [mul_comm]
  simp [hx, hy, hz]
  norm_num
theorem lean_workbook_1840_14 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z))^(2/3) + (y / (x + z))^(2/3) + (z / (x + y))^(2/3) ≥ 3 * (1 / 4)^(1/3) := by
  ring_nf at *
  nlinarith [hx, hy, hz]
theorem lean_workbook_1840_15 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z))^(2/3) + (y / (x + z))^(2/3) + (z / (x + y))^(2/3) ≥ 3 * (1 / 4)^(1/3) := by
  simp [div_eq_inv_mul, ← inv_add_inv, mul_rpow, ← rpow_mul, ← rpow_add, hx, hy, hz]
  nlinarith
theorem lean_workbook_1840_16 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z))^(2/3) + (y / (x + z))^(2/3) + (z / (x + y))^(2/3) ≥ 3 * (1 / 4)^(1/3) := by
  simp [div_eq_inv_mul, inv_nonneg]
  nlinarith [hx, hy, hz]
theorem lean_workbook_1840_17 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z))^(2/3) + (y / (x + z))^(2/3) + (z / (x + y))^(2/3) ≥ 3 * (1 / 4)^(1/3) := by
  norm_num [hx, hy, hz]

theorem lean_workbook_1843_0 (a b : ℝ) : 3 * a ^ 4 - 4 * a ^ 3 * b + b ^ 4 ≥ 0 := by
  simp [sub_nonneg]
  ring_nf
  nlinarith [sq_nonneg (a - b), sq_nonneg (a^2 - b^2)]
theorem lean_workbook_1843_1 (a b : ℝ) : 3 * a ^ 4 - 4 * a ^ 3 * b + b ^ 4 ≥ 0 := by
  apply le_of_sub_nonneg
  field_simp [sq]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a ^ 2 - b ^ 2)]
theorem lean_workbook_1843_2 (a b : ℝ) : 3 * a ^ 4 - 4 * a ^ 3 * b + b ^ 4 ≥ 0 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a^2 - b^2)]
theorem lean_workbook_1843_3 (a b : ℝ) : 3 * a ^ 4 - 4 * a ^ 3 * b + b ^ 4 ≥ 0 := by
  simp [mul_comm, sub_nonneg]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a ^ 2 - b ^ 2)]
theorem lean_workbook_1843_4 (a b : ℝ) : 3 * a ^ 4 - 4 * a ^ 3 * b + b ^ 4 ≥ 0 := by
  have h1 : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  have h2 := sq_nonneg (a ^ 2 - b ^ 2)
  nlinarith [h1, h2]
theorem lean_workbook_1843_5 (a b : ℝ) : 3 * a ^ 4 - 4 * a ^ 3 * b + b ^ 4 ≥ 0 := by
  nlinarith [pow_two_nonneg (a - b), pow_two_nonneg (a ^ 2 - b ^ 2)]

theorem lean_workbook_1848_0 (n : ℕ) : ∑ i in Finset.range (n+1), choose n i = 2^n := by
  simp [Nat.sum_range_choose]
theorem lean_workbook_1848_1 (n : ℕ) : ∑ i in Finset.range (n+1), choose n i = 2^n := by
  simp only [← Nat.cast_sum, ← Nat.cast_pow, sum_range_choose, Nat.cast_pow]
theorem lean_workbook_1848_2 (n : ℕ) : ∑ i in Finset.range (n+1), choose n i = 2^n := by
  have := (add_pow 1 1 n).symm
  simpa [one_add_one_eq_two] using this

theorem lean_workbook_1853_0 (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 2 ≥ 6 * (a * b + b * c + a * c) := by
  simp [sq]
  linarith [mul_self_nonneg (a - b), mul_self_nonneg (b - c), mul_self_nonneg (c - a)]
theorem lean_workbook_1853_1 (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 2 ≥ 6 * (a * b + b * c + a * c) := by
  simp [add_sq]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1853_2 (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 2 ≥ 6 * (a * b + b * c + a * c) := by
  simp [mul_add, add_mul, mul_comm, mul_left_comm]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1853_3 (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 2 ≥ 6 * (a * b + b * c + a * c) := by
  simp only [sq, add_assoc, add_left_comm]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1853_4 (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 2 ≥ 6 * (a * b + b * c + a * c) := by
  ring_nf
  have h1 := sq_nonneg (a - b)
  have h2 := sq_nonneg (b - c)
  have h3 := sq_nonneg (c - a)
  linarith
theorem lean_workbook_1853_5 (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 2 ≥ 6 * (a * b + b * c + a * c) := by
  have := sq_nonneg (a + b + c)
  have := sq_nonneg (a - b)
  have := sq_nonneg (b - c)
  have := sq_nonneg (c - a)
  linarith
theorem lean_workbook_1853_6 (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 2 ≥ 6 * (a * b + b * c + a * c) := by
  ring_nf
  norm_cast
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_1853_7 (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 2 ≥ 6 * (a * b + b * c + a * c) := by
  have h₀ := sq_nonneg (a - b)
  have h₁ := sq_nonneg (b - c)
  have h₂ := sq_nonneg (a - c)
  linarith
theorem lean_workbook_1853_8 (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 2 ≥ 6 * (a * b + b * c + a * c) := by
  ring_nf
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_1853_9 (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 2 ≥ 6 * (a * b + b * c + a * c) := by
  rw [add_comm]
  linarith [sq_nonneg (a-b), sq_nonneg (b-c), sq_nonneg (a-c)]
theorem lean_workbook_1853_10 (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 2 ≥ 6 * (a * b + b * c + a * c) := by
  simp [add_comm, add_left_comm]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_1853_11 (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 2 ≥ 6 * (a * b + b * c + a * c) := by
  simp [sq, add_assoc, add_comm, add_left_comm]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_1853_12 (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 2 ≥ 6 * (a * b + b * c + a * c) := by
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_1853_13 (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 2 ≥ 6 * (a * b + b * c + a * c) := by
  have h1 : 0 ≤ (a - b)^2 + (b - c)^2 + (c - a)^2 := by nlinarith
  nlinarith
theorem lean_workbook_1853_14 (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 2 ≥ 6 * (a * b + b * c + a * c) := by
  field_simp [mul_add, add_mul]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1853_15 (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 2 ≥ 6 * (a * b + b * c + a * c) := by
  have t := sq_nonneg (a - b)
  have u := sq_nonneg (b - c)
  have v := sq_nonneg (c - a)
  linarith
theorem lean_workbook_1853_16 (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 2 ≥ 6 * (a * b + b * c + a * c) := by
  ring_nf
  ring_nf
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_1853_17 (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 2 ≥ 6 * (a * b + b * c + a * c) := by
  have h₁ := sq_nonneg (a - b)
  have h₂ := sq_nonneg (b - c)
  have h₃ := sq_nonneg (c - a)
  linarith
theorem lean_workbook_1853_18 (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 2 ≥ 6 * (a * b + b * c + a * c) := by
  simp [sq, mul_add, add_mul]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1853_19 (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 2 ≥ 6 * (a * b + b * c + a * c) := by
  have h₁ : 0 ≤ (a - b)^2 := sq_nonneg (a - b)
  have h₂ : 0 ≤ (b - c)^2 := sq_nonneg (b - c)
  have h₃ : 0 ≤ (c - a)^2 := sq_nonneg (c - a)
  linarith
theorem lean_workbook_1853_20 (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 2 ≥ 6 * (a * b + b * c + a * c) := by
  simp [add_mul, mul_add, mul_comm, mul_left_comm]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

theorem lean_workbook_1861_0 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_1861_1 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  simp [mul_add, add_mul, mul_comm, mul_left_comm, sub_nonneg]
  have := sq_nonneg (a - b)
  have := sq_nonneg (b - c)
  have := sq_nonneg (c - a)
  linarith
theorem lean_workbook_1861_2 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1861_3 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  simp [two_mul, add_assoc, add_left_comm]
  have := sq_nonneg (a - b)
  have := sq_nonneg (b - c)
  have := sq_nonneg (c - a)
  linarith
theorem lean_workbook_1861_4 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  ring_nf
  rw [add_comm]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1861_5 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  simp only [mul_add, mul_left_comm, mul_assoc]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1861_6 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  ring_nf
  ring_nf
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_1861_7 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  have h1 : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  have h2 : 0 ≤ (b - c) ^ 2 := sq_nonneg (b - c)
  have h3 : 0 ≤ (c - a) ^ 2 := sq_nonneg (c - a)
  linarith [h1, h2, h3]
theorem lean_workbook_1861_8 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  have h1 : 0 ≤ (a - b) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ (b - c) ^ 2 := sq_nonneg _
  have h3 : 0 ≤ (c - a) ^ 2 := sq_nonneg _
  linarith
theorem lean_workbook_1861_9 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  rw [ge_iff_le]
  simp only [mul_add, mul_left_comm, mul_comm]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1861_10 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  have h₁ : 0 ≤ (a - b) ^ 2 := sq_nonneg _
  have h₂ : 0 ≤ (b - c) ^ 2 := sq_nonneg _
  have h₃ : 0 ≤ (c - a) ^ 2 := sq_nonneg _
  linarith
theorem lean_workbook_1861_11 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  ring_nf
  have h1 := sq_nonneg (a - b)
  have h2 := sq_nonneg (b - c)
  have h3 := sq_nonneg (c - a)
  linarith
theorem lean_workbook_1861_12 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  simp [mul_add, add_mul, mul_comm, mul_assoc, mul_left_comm]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_1861_13 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  ring_nf
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1861_14 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  simp [mul_add, add_mul, mul_comm, mul_assoc, mul_left_comm]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1861_15 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  rw [mul_comm]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1861_16 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  simp [mul_add, add_mul]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1861_17 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  have h1 : 0 ≤ (a - b)^2 + (b - c)^2 + (c - a)^2 := by nlinarith
  linarith
theorem lean_workbook_1861_18 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  simp [mul_add, add_mul, mul_comm, mul_left_comm]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_1861_19 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  have h1 := sq_nonneg (a - b)
  have h2 := sq_nonneg (b - c)
  have h3 := sq_nonneg (a - c)
  linarith
theorem lean_workbook_1861_20 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  have h1 : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  have h2 : 0 ≤ (b - c) ^ 2 := sq_nonneg (b - c)
  have h3 : 0 ≤ (c - a) ^ 2 := sq_nonneg (c - a)
  linarith
theorem lean_workbook_1861_21 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_1861_22 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  have := sq_nonneg (a - b + c)
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1861_23 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  simp [mul_add, add_mul]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1861_24 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  simp [sq]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1861_25 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  have := sq_nonneg (a - b + c)
  have := sq_nonneg (a - b)
  have := sq_nonneg (b - c)
  have := sq_nonneg (c - a)
  linarith
theorem lean_workbook_1861_26 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  simp [mul_sub, mul_add]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1861_27 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  rw [mul_comm]
  ring_nf
  linarith [mul_self_nonneg (a - b), mul_self_nonneg (b - c), mul_self_nonneg (c - a)]
theorem lean_workbook_1861_28 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  simp [mul_add, add_mul, mul_comm, mul_left_comm]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_1861_29 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  simp [sq, mul_add, mul_comm, mul_left_comm]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

theorem lean_workbook_1903_0 (a c : ℤ) (h1 : Odd a) (h2 : Odd c) : Even (a + c) := by
  rcases h1 with ⟨b, rfl⟩
  rcases h2 with ⟨d, rfl⟩
  simp [Int.add_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.even_add]
theorem lean_workbook_1903_1 (a c : ℤ) (h1 : Odd a) (h2 : Odd c) : Even (a + c) := by
  obtain ⟨b, rfl⟩ := h1
  obtain ⟨d, rfl⟩ := h2
  simp [Int.even_add]
theorem lean_workbook_1903_2 (a c : ℤ) (h1 : Odd a) (h2 : Odd c) : Even (a + c) := by
  obtain ⟨k, rfl⟩ := h1
  obtain ⟨l, rfl⟩ := h2
  simp [Int.even_add]

theorem lean_workbook_1905_0 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [add_assoc, add_comm, add_left_comm]
theorem lean_workbook_1905_1 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [mul_add, add_mul, mul_comm, mul_assoc, mul_left_comm]
theorem lean_workbook_1905_2 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  field_simp [Nat.add_comm]
theorem lean_workbook_1905_3 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [Nat.gcd]
theorem lean_workbook_1905_4 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [add_comm, add_left_comm, add_assoc]
theorem lean_workbook_1905_5 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [add_mul, mul_add, mul_comm, mul_left_comm, mul_assoc]
theorem lean_workbook_1905_6 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
theorem lean_workbook_1905_7 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [div_eq_mul_inv]
theorem lean_workbook_1905_8 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
theorem lean_workbook_1905_9 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [Nat.add_comm, Nat.add_left_comm]
theorem lean_workbook_1905_10 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [Int.mul_comm, Int.mul_assoc, Int.mul_left_comm]
theorem lean_workbook_1905_11 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [add_comm, mul_assoc]
theorem lean_workbook_1905_12 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  all_goals norm_num
theorem lean_workbook_1905_13 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [mul_add, add_mul, div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]
theorem lean_workbook_1905_14 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [mul_assoc]
theorem lean_workbook_1905_15 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [Nat.add_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
theorem lean_workbook_1905_16 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Nat.add_sub_add_right, Nat.add_sub_cancel_left, Nat.add_sub_cancel, Nat.mul_div_cancel_left]
theorem lean_workbook_1905_17 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num at *
theorem lean_workbook_1905_18 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [mul_add, add_mul, mul_comm, mul_assoc, mul_left_comm]
theorem lean_workbook_1905_19 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
theorem lean_workbook_1905_20 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]
theorem lean_workbook_1905_21 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [Nat.div_eq_of_eq_mul_left]
theorem lean_workbook_1905_22 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [mul_assoc, mul_comm, mul_left_comm]
theorem lean_workbook_1905_23 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
theorem lean_workbook_1905_24 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [add_comm, add_left_comm, mul_comm, mul_left_comm, mul_assoc]
theorem lean_workbook_1905_25 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [Nat.add_zero, Nat.add_succ, Nat.mul_one, Nat.mul_zero, Nat.zero_add, Nat.zero_sub]
theorem lean_workbook_1905_26 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [Nat.div_eq]
theorem lean_workbook_1905_27 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [mul_comm, mul_assoc, mul_left_comm]
theorem lean_workbook_1905_28 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [add_mul, mul_add, mul_comm, mul_left_comm, div_eq_mul_inv]
theorem lean_workbook_1905_29 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [Nat.mul]
theorem lean_workbook_1905_30 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [mul_add, mul_comm, mul_left_comm]
theorem lean_workbook_1905_31 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [Nat.div_eq_of_lt]
theorem lean_workbook_1905_32 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [Nat.add_comm]
theorem lean_workbook_1905_33 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [Nat.add_comm, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
theorem lean_workbook_1905_34 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [Nat.gcd_eq_gcd_ab]
theorem lean_workbook_1905_35 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [show (1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000 by ring]
theorem lean_workbook_1905_36 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
theorem lean_workbook_1905_37 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  exact (by norm_num : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000))
theorem lean_workbook_1905_38 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [mul_add, mul_comm, mul_left_comm, add_mul, add_comm, add_left_comm, div_eq_mul_inv]
theorem lean_workbook_1905_39 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  field_simp [add_comm, add_left_comm, add_assoc]
theorem lean_workbook_1905_40 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [div_eq_mul_inv, ← mul_assoc, ← add_assoc]
theorem lean_workbook_1905_41 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [mul_comm, mul_assoc, mul_left_comm, div_eq_mul_inv]
theorem lean_workbook_1905_42 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
theorem lean_workbook_1905_43 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [div_eq_mul_inv, mul_inv_rev]
theorem lean_workbook_1905_44 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [div_eq_mul_inv, ← pow_two]
theorem lean_workbook_1905_45 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [Nat.add_comm, Nat.add_left_comm]
theorem lean_workbook_1905_46 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  rw [show (1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000 by norm_num]
theorem lean_workbook_1905_47 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
theorem lean_workbook_1905_48 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [Nat.mul_div_cancel_left]
theorem lean_workbook_1905_49 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [div_eq_mul_inv, ← mul_assoc]
theorem lean_workbook_1905_50 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]
theorem lean_workbook_1905_51 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [Int.negSucc_ne_zero]
theorem lean_workbook_1905_52 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [Nat.add_zero]
theorem lean_workbook_1905_53 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [add_comm] at *
theorem lean_workbook_1905_54 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  field_simp [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]
theorem lean_workbook_1905_55 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  field_simp [show (3 + 4) / 7 ≠ 0 by norm_num]
theorem lean_workbook_1905_56 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [Int.add_comm]
theorem lean_workbook_1905_57 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [Nat.add_comm, Nat.add_left_comm, Nat.mul_comm, Nat.mul_left_comm]
theorem lean_workbook_1905_58 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [add_comm, add_left_comm, add_assoc, mul_comm, mul_assoc, mul_left_comm]
theorem lean_workbook_1905_59 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [add_comm, add_left_comm, mul_comm, mul_left_comm]
theorem lean_workbook_1905_60 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  norm_num [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
theorem lean_workbook_1905_61 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp [add_comm, add_left_comm, add_assoc]
theorem lean_workbook_1905_62 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  simp only [add_comm]
theorem lean_workbook_1905_63 : ((1 + 6) * (2 + 9) * (5 + 8) - (3 + 4) / 7 = 1000) := by
  congr 1

theorem lean_workbook_1932_0 : 77 ^ 10 ≥ 2 ^ 10 * (10!) ^ 2 := by
  norm_num [Nat.pow_succ, Nat.factorial_succ, mul_assoc]
theorem lean_workbook_1932_1 : 77 ^ 10 ≥ 2 ^ 10 * (10!) ^ 2 := by
  norm_cast at *

theorem lean_workbook_1948_0 (x y : ℝ) (h₁ : x + y = 3) (h₂ : x^2 + y^2 - x*y = 4) : x^4 + y^4 + x^3*y + x*y^3 = 36 := by
  simp [add_comm, add_left_comm, mul_comm, mul_left_comm, mul_assoc, h₁, h₂, sq, ← sub_eq_zero]
  nlinarith
theorem lean_workbook_1948_1 (x y : ℝ) (h₁ : x + y = 3) (h₂ : x^2 + y^2 - x*y = 4) : x^4 + y^4 + x^3*y + x*y^3 = 36 := by
  simp [mul_add, mul_comm, mul_left_comm, pow_two, pow_three, h₁, h₂]
  nlinarith
theorem lean_workbook_1948_2 (x y : ℝ) (h₁ : x + y = 3) (h₂ : x^2 + y^2 - x*y = 4) : x^4 + y^4 + x^3*y + x*y^3 = 36 := by
  simp [pow_two, h₁, h₂, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  nlinarith
theorem lean_workbook_1948_3 (x y : ℝ) (h₁ : x + y = 3) (h₂ : x^2 + y^2 - x*y = 4) : x^4 + y^4 + x^3*y + x*y^3 = 36 := by
  field_simp [pow_two] at h₂ ⊢
  nlinarith
theorem lean_workbook_1948_4 (x y : ℝ) (h₁ : x + y = 3) (h₂ : x^2 + y^2 - x*y = 4) : x^4 + y^4 + x^3*y + x*y^3 = 36 := by
  simp [pow_two, add_comm, add_left_comm, add_assoc, mul_add, mul_left_comm, mul_comm, h₁, h₂]
  nlinarith [h₁, h₂]
theorem lean_workbook_1948_5 (x y : ℝ) (h₁ : x + y = 3) (h₂ : x^2 + y^2 - x*y = 4) : x^4 + y^4 + x^3*y + x*y^3 = 36 := by
  simp [pow_two, add_comm] at h₂
  nlinarith
theorem lean_workbook_1948_6 (x y : ℝ) (h₁ : x + y = 3) (h₂ : x^2 + y^2 - x*y = 4) : x^4 + y^4 + x^3*y + x*y^3 = 36 := by
  simp only [pow_two, pow_one] at h₂
  nlinarith

theorem lean_workbook_1957_0 : 7 ^ 2003 ≡ 3 [MOD 10] := by
  exact (show 7 ^ 2003 % 10 = 3 from by norm_num)
theorem lean_workbook_1957_1 : 7 ^ 2003 ≡ 3 [MOD 10] := by
  simp only [ModEq, Int.ModEq]
  norm_num
theorem lean_workbook_1957_2 : 7 ^ 2003 ≡ 3 [MOD 10] := by
  exact (show 7 ^ 2003 % 10 = 3 by norm_num)
theorem lean_workbook_1957_3 : 7 ^ 2003 ≡ 3 [MOD 10] := by
  calc
    7 ^ 2003 ≡ 3 [MOD 10] := by norm_num [ModEq]
theorem lean_workbook_1957_4 : 7 ^ 2003 ≡ 3 [MOD 10] := by
  norm_num [pow_succ, Nat.ModEq]
theorem lean_workbook_1957_5 : 7 ^ 2003 ≡ 3 [MOD 10] := by
  change 7 ^ 2003 % 10 = 3
  norm_num [pow_succ, pow_mul]
theorem lean_workbook_1957_6 : 7 ^ 2003 ≡ 3 [MOD 10] := by
  simp [ModEq]
theorem lean_workbook_1957_7 : 7 ^ 2003 ≡ 3 [MOD 10] := by
  change 7 ^ 2003 % 10 = 3
  norm_num
theorem lean_workbook_1957_8 : 7 ^ 2003 ≡ 3 [MOD 10] := by
  conv => lhs; rw [← Nat.mod_add_div 7 10]
theorem lean_workbook_1957_9 : 7 ^ 2003 ≡ 3 [MOD 10] := by
  norm_num [Nat.modEq_of_dvd]
theorem lean_workbook_1957_10 : 7 ^ 2003 ≡ 3 [MOD 10] := by
  simp [Nat.modEq_iff_dvd, Nat.ModEq]
theorem lean_workbook_1957_11 : 7 ^ 2003 ≡ 3 [MOD 10] := by
  norm_num [pow_succ, pow_mul, Nat.ModEq]
theorem lean_workbook_1957_12 : 7 ^ 2003 ≡ 3 [MOD 10] := by
  rw [Nat.modEq_iff_dvd]
  norm_num
theorem lean_workbook_1957_13 : 7 ^ 2003 ≡ 3 [MOD 10] := by
  show 7 ^ 2003 % 10 = 3
  norm_num
theorem lean_workbook_1957_14 : 7 ^ 2003 ≡ 3 [MOD 10] := by
  conv => lhs; rw [← Nat.mod_add_div 2003 4]
theorem lean_workbook_1957_15 : 7 ^ 2003 ≡ 3 [MOD 10] := by
  norm_num [pow_succ, pow_mul, pow_one]
  decide
theorem lean_workbook_1957_16 : 7 ^ 2003 ≡ 3 [MOD 10] := by
  conv_lhs => rw [← pow_one 7]
theorem lean_workbook_1957_17 : 7 ^ 2003 ≡ 3 [MOD 10] := by
  calc
    7 ^ 2003 ≡ 3 [MOD 10] := by norm_num [Nat.ModEq]
theorem lean_workbook_1957_18 : 7 ^ 2003 ≡ 3 [MOD 10] := by
  norm_num [Nat.ModEq, Nat.mod_eq_of_lt]
theorem lean_workbook_1957_19 : 7 ^ 2003 ≡ 3 [MOD 10] := by
  norm_num [ModEq, pow_succ]
theorem lean_workbook_1957_20 : 7 ^ 2003 ≡ 3 [MOD 10] := by
  rw [ModEq]
  simp [Nat.pow_mod]
theorem lean_workbook_1957_21 : 7 ^ 2003 ≡ 3 [MOD 10] := by
  calc
   7 ^ 2003 ≡ 3 [MOD 10] := by norm_num [Nat.ModEq]
theorem lean_workbook_1957_22 : 7 ^ 2003 ≡ 3 [MOD 10] := by
  conv => lhs; rw [← Nat.mod_add_div 2003 10]

theorem lean_workbook_1992_0 (a b c : ℝ) (habc : a * b * c = 1) : a ^ 2 + b ^ 2 + c ^ 2 + 3 ≥ 2 * (a + b + c) := by
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), habc]
theorem lean_workbook_1992_1 (a b c : ℝ) (habc : a * b * c = 1) : a ^ 2 + b ^ 2 + c ^ 2 + 3 ≥ 2 * (a + b + c) := by
  have h1 := sq_nonneg (a - 1)
  have h2 := sq_nonneg (b - 1)
  have h3 := sq_nonneg (c - 1)
  linarith [habc, h1, h2, h3]
theorem lean_workbook_1992_2 (a b c : ℝ) (habc : a * b * c = 1) : a ^ 2 + b ^ 2 + c ^ 2 + 3 ≥ 2 * (a + b + c) := by
  have := sq_nonneg (a - 1)
  have := sq_nonneg (b - 1)
  have := sq_nonneg (c - 1)
  linarith [habc]
theorem lean_workbook_1992_3 (a b c : ℝ) (habc : a * b * c = 1) : a ^ 2 + b ^ 2 + c ^ 2 + 3 ≥ 2 * (a + b + c) := by
  have := sq_nonneg (a - 1)
  have := sq_nonneg (b - 1)
  have := sq_nonneg (c - 1)
  linarith
theorem lean_workbook_1992_4 (a b c : ℝ) (habc : a * b * c = 1) : a ^ 2 + b ^ 2 + c ^ 2 + 3 ≥ 2 * (a + b + c) := by
  nlinarith [sq_nonneg (1 - a), sq_nonneg (1 - b), sq_nonneg (1 - c), habc]
theorem lean_workbook_1992_5 (a b c : ℝ) (habc : a * b * c = 1) : a ^ 2 + b ^ 2 + c ^ 2 + 3 ≥ 2 * (a + b + c) := by
  have h1 : 0 ≤ (a - 1) ^ 2 + (b - 1) ^ 2 + (c - 1) ^ 2 := by nlinarith
  nlinarith [habc]
theorem lean_workbook_1992_6 (a b c : ℝ) (habc : a * b * c = 1) : a ^ 2 + b ^ 2 + c ^ 2 + 3 ≥ 2 * (a + b + c) := by
  have h₁ := sq_nonneg (a - 1)
  have h₂ := sq_nonneg (b - 1)
  have h₃ := sq_nonneg (c - 1)
  linarith [habc]
theorem lean_workbook_1992_7 (a b c : ℝ) (habc : a * b * c = 1) : a ^ 2 + b ^ 2 + c ^ 2 + 3 ≥ 2 * (a + b + c) := by
  have : 0 ≤ (a - 1)^2 + (b - 1)^2 + (c - 1)^2 := by positivity
  linarith

theorem lean_workbook_2010_0 (θ : ℝ) : Real.cos θ + Real.sqrt 3 * Real.sin θ = 2 * (1 / 2 * Real.cos θ + Real.sqrt 3 / 2 * Real.sin θ) := by
  rw [add_comm]
  ring_nf
theorem lean_workbook_2010_1 (θ : ℝ) : Real.cos θ + Real.sqrt 3 * Real.sin θ = 2 * (1 / 2 * Real.cos θ + Real.sqrt 3 / 2 * Real.sin θ) := by
  simp [two_mul, mul_add]
  ring
theorem lean_workbook_2010_2 (θ : ℝ) : Real.cos θ + Real.sqrt 3 * Real.sin θ = 2 * (1 / 2 * Real.cos θ + Real.sqrt 3 / 2 * Real.sin θ) := by
  field_simp [Real.sqrt_sq_eq_abs]
  ring
theorem lean_workbook_2010_3 (θ : ℝ) : Real.cos θ + Real.sqrt 3 * Real.sin θ = 2 * (1 / 2 * Real.cos θ + Real.sqrt 3 / 2 * Real.sin θ) := by
  linear_combination 2 * (1 / 2 * Real.cos θ + Real.sqrt 3 / 2 * Real.sin θ) - (Real.cos θ + Real.sqrt 3 * Real.sin θ)
theorem lean_workbook_2010_4 (θ : ℝ) : Real.cos θ + Real.sqrt 3 * Real.sin θ = 2 * (1 / 2 * Real.cos θ + Real.sqrt 3 / 2 * Real.sin θ) := by
  congr 1
  ring_nf
theorem lean_workbook_2010_5 (θ : ℝ) : Real.cos θ + Real.sqrt 3 * Real.sin θ = 2 * (1 / 2 * Real.cos θ + Real.sqrt 3 / 2 * Real.sin θ) := by
  simp [mul_add, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_2010_6 (θ : ℝ) : Real.cos θ + Real.sqrt 3 * Real.sin θ = 2 * (1 / 2 * Real.cos θ + Real.sqrt 3 / 2 * Real.sin θ) := by
  rw [mul_add]
  ring
theorem lean_workbook_2010_7 (θ : ℝ) : Real.cos θ + Real.sqrt 3 * Real.sin θ = 2 * (1 / 2 * Real.cos θ + Real.sqrt 3 / 2 * Real.sin θ) := by
  simp [add_mul, mul_assoc]
  ring_nf
theorem lean_workbook_2010_8 (θ : ℝ) : Real.cos θ + Real.sqrt 3 * Real.sin θ = 2 * (1 / 2 * Real.cos θ + Real.sqrt 3 / 2 * Real.sin θ) := by
  field_simp [_root_.mul_assoc]
  ring
theorem lean_workbook_2010_9 (θ : ℝ) : Real.cos θ + Real.sqrt 3 * Real.sin θ = 2 * (1 / 2 * Real.cos θ + Real.sqrt 3 / 2 * Real.sin θ) := by
  field_simp [add_comm]
  ring
theorem lean_workbook_2010_10 (θ : ℝ) : Real.cos θ + Real.sqrt 3 * Real.sin θ = 2 * (1 / 2 * Real.cos θ + Real.sqrt 3 / 2 * Real.sin θ) := by
  rw [mul_comm]
  simp [mul_add, mul_comm, mul_left_comm]
  ring
theorem lean_workbook_2010_11 (θ : ℝ) : Real.cos θ + Real.sqrt 3 * Real.sin θ = 2 * (1 / 2 * Real.cos θ + Real.sqrt 3 / 2 * Real.sin θ) := by
  field_simp [_root_.sq, Real.sqrt_sq_eq_abs]
  ring
theorem lean_workbook_2010_12 (θ : ℝ) : Real.cos θ + Real.sqrt 3 * Real.sin θ = 2 * (1 / 2 * Real.cos θ + Real.sqrt 3 / 2 * Real.sin θ) := by
  rw [← mul_right_inj' (two_ne_zero' ℝ)]
  ring
theorem lean_workbook_2010_13 (θ : ℝ) : Real.cos θ + Real.sqrt 3 * Real.sin θ = 2 * (1 / 2 * Real.cos θ + Real.sqrt 3 / 2 * Real.sin θ) := by
  field_simp [show (2 : ℝ) ≠ 0 by norm_num, add_comm]
  ring
theorem lean_workbook_2010_14 (θ : ℝ) : Real.cos θ + Real.sqrt 3 * Real.sin θ = 2 * (1 / 2 * Real.cos θ + Real.sqrt 3 / 2 * Real.sin θ) := by
  rw [mul_add]
  ring_nf
theorem lean_workbook_2010_15 (θ : ℝ) : Real.cos θ + Real.sqrt 3 * Real.sin θ = 2 * (1 / 2 * Real.cos θ + Real.sqrt 3 / 2 * Real.sin θ) := by
  field_simp [Real.sqrt_sq]
  ring
theorem lean_workbook_2010_16 (θ : ℝ) : Real.cos θ + Real.sqrt 3 * Real.sin θ = 2 * (1 / 2 * Real.cos θ + Real.sqrt 3 / 2 * Real.sin θ) := by
  field_simp [Real.sqrt_eq_iff_sq_eq]
  ring

theorem lean_workbook_2021_0 : ∀ x : ℝ, (Real.cos x)^2 = (1 + Real.cos (2 * x)) / 2 := by
  refine' fun x => Eq.symm _
  simp [Real.cos_two_mul]
  ring
theorem lean_workbook_2021_1 : ∀ x : ℝ, (Real.cos x)^2 = (1 + Real.cos (2 * x)) / 2 := by
  refine' fun x => Eq.symm _
  rw [add_comm]
  simp [cos_two_mul, mul_add, add_mul, add_assoc, add_left_comm]
  ring
theorem lean_workbook_2021_2 : ∀ x : ℝ, (Real.cos x)^2 = (1 + Real.cos (2 * x)) / 2 := by
  intro x
  field_simp [Real.cos_sq_add_sin_sq, Real.cos_two_mul]
  ring
theorem lean_workbook_2021_3 : ∀ x : ℝ, (Real.cos x)^2 = (1 + Real.cos (2 * x)) / 2 := by
  intro x
  rw [Real.cos_sq]
  ring
theorem lean_workbook_2021_4 : ∀ x : ℝ, (Real.cos x)^2 = (1 + Real.cos (2 * x)) / 2 := by
  intro x; rw [Real.cos_sq]; ring
theorem lean_workbook_2021_5 : ∀ x : ℝ, (Real.cos x)^2 = (1 + Real.cos (2 * x)) / 2 := by
  refine' fun x => by rw [cos_sq, cos_two_mul]; ring
theorem lean_workbook_2021_6 : ∀ x : ℝ, (Real.cos x)^2 = (1 + Real.cos (2 * x)) / 2 := by
  intro x
  rw [Real.cos_two_mul]
  ring
theorem lean_workbook_2021_7 : ∀ x : ℝ, (Real.cos x)^2 = (1 + Real.cos (2 * x)) / 2 := by
  refine' fun x => by rw [Real.cos_two_mul, add_comm]; ring
theorem lean_workbook_2021_8 : ∀ x : ℝ, (Real.cos x)^2 = (1 + Real.cos (2 * x)) / 2 := by
  intro x
  rw [cos_sq]
  ring_nf
theorem lean_workbook_2021_9 : ∀ x : ℝ, (Real.cos x)^2 = (1 + Real.cos (2 * x)) / 2 := by
  exact fun x ↦ by rw [Real.cos_sq, add_comm]; ring
theorem lean_workbook_2021_10 : ∀ x : ℝ, (Real.cos x)^2 = (1 + Real.cos (2 * x)) / 2 := by
  exact fun x ↦ by rw [Real.cos_two_mul, add_comm]; ring
theorem lean_workbook_2021_11 : ∀ x : ℝ, (Real.cos x)^2 = (1 + Real.cos (2 * x)) / 2 := by
  exact fun x ↦ by rw [cos_sq, add_comm]; ring
theorem lean_workbook_2021_12 : ∀ x : ℝ, (Real.cos x)^2 = (1 + Real.cos (2 * x)) / 2 := by
  intro x
  simp [cos_two_mul]
  ring
theorem lean_workbook_2021_13 : ∀ x : ℝ, (Real.cos x)^2 = (1 + Real.cos (2 * x)) / 2 := by
  refine' fun x => Eq.symm _
  rw [add_comm]
  simp [cos_two_mul, mul_div_cancel_left]
  linarith
theorem lean_workbook_2021_14 : ∀ x : ℝ, (Real.cos x)^2 = (1 + Real.cos (2 * x)) / 2 := by
  exact fun x ↦ by rw [cos_sq]; ring
theorem lean_workbook_2021_15 : ∀ x : ℝ, (Real.cos x)^2 = (1 + Real.cos (2 * x)) / 2 := by
  refine' fun x => eq_of_sub_eq_zero _
  rw [sub_eq_zero]
  rw [Real.cos_sq]
  ring
theorem lean_workbook_2021_16 : ∀ x : ℝ, (Real.cos x)^2 = (1 + Real.cos (2 * x)) / 2 := by
  intro x
  rw [cos_two_mul, add_comm]
  ring
theorem lean_workbook_2021_17 : ∀ x : ℝ, (Real.cos x)^2 = (1 + Real.cos (2 * x)) / 2 := by
  exact (λ x ↦ by linarith [cos_sq x])
theorem lean_workbook_2021_18 : ∀ x : ℝ, (Real.cos x)^2 = (1 + Real.cos (2 * x)) / 2 := by
  simp [Real.cos_two_mul]
  exact fun x ↦ by ring
theorem lean_workbook_2021_19 : ∀ x : ℝ, (Real.cos x)^2 = (1 + Real.cos (2 * x)) / 2 := by
  exact fun x ↦ by rw [Real.cos_two_mul]; ring
theorem lean_workbook_2021_20 : ∀ x : ℝ, (Real.cos x)^2 = (1 + Real.cos (2 * x)) / 2 := by
  intro x
  rw [cos_two_mul, add_comm]
  field_simp [cos_sq_add_sin_sq]
  ring
theorem lean_workbook_2021_21 : ∀ x : ℝ, (Real.cos x)^2 = (1 + Real.cos (2 * x)) / 2 := by
  intro x
  rw [Real.cos_two_mul, add_comm]
  ring
theorem lean_workbook_2021_22 : ∀ x : ℝ, (Real.cos x)^2 = (1 + Real.cos (2 * x)) / 2 := by
  exact fun x ↦ by rw [cos_two_mul, add_comm]; ring

theorem lean_workbook_2023_0 : 999 + 10 = 1009 := by
  simp only [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]
theorem lean_workbook_2023_1 : 999 + 10 = 1009 := by
  simp only [Nat.succ_pos', Nat.add_comm, Nat.add_left_comm]
theorem lean_workbook_2023_2 : 999 + 10 = 1009 := by
  simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
theorem lean_workbook_2023_3 : 999 + 10 = 1009 := by
  simp [show 999 + 10 = 1009 from rfl]
theorem lean_workbook_2023_4 : 999 + 10 = 1009 := by
  refine' rfl
theorem lean_workbook_2023_5 : 999 + 10 = 1009 := by
  exact Nat.add_comm 999 10
theorem lean_workbook_2023_6 : 999 + 10 = 1009 := by
  simp [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]
theorem lean_workbook_2023_7 : 999 + 10 = 1009 := by
  norm_num [add_comm, add_left_comm]
theorem lean_workbook_2023_8 : 999 + 10 = 1009 := by
  rw [show (999 + 10 : ℕ) = 1009 by rfl]
theorem lean_workbook_2023_9 : 999 + 10 = 1009 := by
  norm_num [Nat.add_comm 999 10, Nat.add_left_comm 999 10 9]
theorem lean_workbook_2023_10 : 999 + 10 = 1009 := by
  simp [add_comm]
theorem lean_workbook_2023_11 : 999 + 10 = 1009 := by
  simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
theorem lean_workbook_2023_12 : 999 + 10 = 1009 := by
  simp only [Nat.add_zero, Nat.add_comm, Nat.add_left_comm]
theorem lean_workbook_2023_13 : 999 + 10 = 1009 := by
  norm_num [show (999 : ℚ) + 10 = 1009 by norm_num]
theorem lean_workbook_2023_14 : 999 + 10 = 1009 := by
  norm_num [Nat.add_comm 10 999]
theorem lean_workbook_2023_15 : 999 + 10 = 1009 := by
  simp only [add_comm 10]
theorem lean_workbook_2023_16 : 999 + 10 = 1009 := by
  norm_num [Nat.sub_eq_iff_eq_add]
theorem lean_workbook_2023_17 : 999 + 10 = 1009 := by
  simp only [Int.add_comm]
theorem lean_workbook_2023_18 : 999 + 10 = 1009 := by
  norm_num [show 999 + 10 = 1009 by decide]
theorem lean_workbook_2023_19 : 999 + 10 = 1009 := by
  simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
theorem lean_workbook_2023_20 : 999 + 10 = 1009 := by
  exact rfl
theorem lean_workbook_2023_21 : 999 + 10 = 1009 := by
  norm_num [Nat.gcd]
theorem lean_workbook_2023_22 : 999 + 10 = 1009 := by
  norm_num [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm]
theorem lean_workbook_2023_23 : 999 + 10 = 1009 := by
  simp only [Nat.add_comm]
theorem lean_workbook_2023_24 : 999 + 10 = 1009 := by
  norm_num [add_comm]
theorem lean_workbook_2023_25 : 999 + 10 = 1009 := by
  simp only [eq_iff_true_of_subsingleton]
theorem lean_workbook_2023_26 : 999 + 10 = 1009 := by
  rw [add_comm]
theorem lean_workbook_2023_27 : 999 + 10 = 1009 := by
  norm_num [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
theorem lean_workbook_2023_28 : 999 + 10 = 1009 := by
  simp [Nat.add_comm, Nat.add_left_comm]
theorem lean_workbook_2023_29 : 999 + 10 = 1009 := by
  norm_num [add_comm 999 10]
theorem lean_workbook_2023_30 : 999 + 10 = 1009 := by
  norm_num [show 999 + 10 = 1009 by rfl]
theorem lean_workbook_2023_31 : 999 + 10 = 1009 := by
  simp only [add_comm, add_zero, add_one]
theorem lean_workbook_2023_32 : 999 + 10 = 1009 := by
  exact add_comm 999 10
theorem lean_workbook_2023_33 : 999 + 10 = 1009 := by
  simp only [add_comm]
theorem lean_workbook_2023_34 : 999 + 10 = 1009 := by
  norm_num [show 10 = 9 + 1 by norm_num, show 1009 = 999 + 10 by norm_num]
theorem lean_workbook_2023_35 : 999 + 10 = 1009 := by
  norm_num [show (9 : ℤ) = 10 - 1 by norm_num, show (10 : ℤ) = 11 - 1 by norm_num]
theorem lean_workbook_2023_36 : 999 + 10 = 1009 := by
  norm_num [Nat.add_comm]

theorem lean_workbook_2044_0 (a b c : ℝ) (habc : a * b * c = 1) (h : a + b + c >= 3) : a + b + c >= 3 * (a^5 * b^5 * c^5)^(1 / 27) := by
  simp [pow_one /-, mul_add, add_mul, mul_comm, mul_assoc, mul_left_comm -/] at *
  nlinarith [habc, h]
theorem lean_workbook_2044_1 (a b c : ℝ) (habc : a * b * c = 1) (h : a + b + c >= 3) : a + b + c >= 3 * (a^5 * b^5 * c^5)^(1 / 27) := by
  simp [Nat.cast_add, Nat.cast_mul, pow_one /-, mul_assoc, mul_left_comm, mul_comm -/] at *
  nlinarith [habc, h]
theorem lean_workbook_2044_2 (a b c : ℝ) (habc : a * b * c = 1) (h : a + b + c >= 3) : a + b + c >= 3 * (a^5 * b^5 * c^5)^(1 / 27) := by
  ring_nf at habc ⊢
  field_simp [habc]
  nlinarith
theorem lean_workbook_2044_3 (a b c : ℝ) (habc : a * b * c = 1) (h : a + b + c >= 3) : a + b + c >= 3 * (a^5 * b^5 * c^5)^(1 / 27) := by
  norm_num
  simp [pow_one /-, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc-/] at *
  nlinarith [habc, h]
theorem lean_workbook_2044_4 (a b c : ℝ) (habc : a * b * c = 1) (h : a + b + c >= 3) : a + b + c >= 3 * (a^5 * b^5 * c^5)^(1 / 27) := by
  ring_nf at habc ⊢
  field_simp [habc]
  nlinarith [h]
theorem lean_workbook_2044_5 (a b c : ℝ) (habc : a * b * c = 1) (h : a + b + c >= 3) : a + b + c >= 3 * (a^5 * b^5 * c^5)^(1 / 27) := by
  ring_nf at habc ⊢
  nlinarith
theorem lean_workbook_2044_6 (a b c : ℝ) (habc : a * b * c = 1) (h : a + b + c >= 3) : a + b + c >= 3 * (a^5 * b^5 * c^5)^(1 / 27) := by
  simp [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] at *
  nlinarith [habc, h]
theorem lean_workbook_2044_7 (a b c : ℝ) (habc : a * b * c = 1) (h : a + b + c >= 3) : a + b + c >= 3 * (a^5 * b^5 * c^5)^(1 / 27) := by
  norm_num at habc
  simp [habc, h]
theorem lean_workbook_2044_8 (a b c : ℝ) (habc : a * b * c = 1) (h : a + b + c >= 3) : a + b + c >= 3 * (a^5 * b^5 * c^5)^(1 / 27) := by
  simp at habc h ⊢
  nlinarith [habc, h]
theorem lean_workbook_2044_9 (a b c : ℝ) (habc : a * b * c = 1) (h : a + b + c >= 3) : a + b + c >= 3 * (a^5 * b^5 * c^5)^(1 / 27) := by
  simp [habc, h, le_refl]
theorem lean_workbook_2044_10 (a b c : ℝ) (habc : a * b * c = 1) (h : a + b + c >= 3) : a + b + c >= 3 * (a^5 * b^5 * c^5)^(1 / 27) := by
  simp [pow_one /-, mul_assoc, mul_left_comm, mul_comm -/] at *
  nlinarith [habc, h]
theorem lean_workbook_2044_11 (a b c : ℝ) (habc : a * b * c = 1) (h : a + b + c >= 3) : a + b + c >= 3 * (a^5 * b^5 * c^5)^(1 / 27) := by
  norm_num
  nlinarith [habc, h]
theorem lean_workbook_2044_12 (a b c : ℝ) (habc : a * b * c = 1) (h : a + b + c >= 3) : a + b + c >= 3 * (a^5 * b^5 * c^5)^(1 / 27) := by
  simp [habc] at *
  nlinarith
theorem lean_workbook_2044_13 (a b c : ℝ) (habc : a * b * c = 1) (h : a + b + c >= 3) : a + b + c >= 3 * (a^5 * b^5 * c^5)^(1 / 27) := by
  simp [add_comm, add_left_comm, mul_comm, mul_left_comm] at *
  nlinarith [habc, h]
theorem lean_workbook_2044_14 (a b c : ℝ) (habc : a * b * c = 1) (h : a + b + c >= 3) : a + b + c >= 3 * (a^5 * b^5 * c^5)^(1 / 27) := by
  norm_num at habc h ⊢
  nlinarith
theorem lean_workbook_2044_15 (a b c : ℝ) (habc : a * b * c = 1) (h : a + b + c >= 3) : a + b + c >= 3 * (a^5 * b^5 * c^5)^(1 / 27) := by
  simp [pow_one /-, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc-/] at *
  nlinarith [habc, h]
theorem lean_workbook_2044_16 (a b c : ℝ) (habc : a * b * c = 1) (h : a + b + c >= 3) : a + b + c >= 3 * (a^5 * b^5 * c^5)^(1 / 27) := by
  simp at habc ⊢
  simp [pow_two, pow_three] at *
  nlinarith
theorem lean_workbook_2044_17 (a b c : ℝ) (habc : a * b * c = 1) (h : a + b + c >= 3) : a + b + c >= 3 * (a^5 * b^5 * c^5)^(1 / 27) := by
  ring_nf at habc ⊢
  nlinarith [habc, h]
theorem lean_workbook_2044_18 (a b c : ℝ) (habc : a * b * c = 1) (h : a + b + c >= 3) : a + b + c >= 3 * (a^5 * b^5 * c^5)^(1 / 27) := by
  norm_num at habc ⊢
  nlinarith
theorem lean_workbook_2044_19 (a b c : ℝ) (habc : a * b * c = 1) (h : a + b + c >= 3) : a + b + c >= 3 * (a^5 * b^5 * c^5)^(1 / 27) := by
  ring_nf at habc ⊢
  simp [habc]
  nlinarith [habc, h]

theorem lean_workbook_2101_0 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x^3 + y^3 ≤ x - y) : x^2 + y^2 ≤ 1 := by
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), hx, hy]
theorem lean_workbook_2101_1 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x^3 + y^3 ≤ x - y) : x^2 + y^2 ≤ 1 := by
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), h]

theorem lean_workbook_2117_0 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  norm_num at h₀
  constructor
  nlinarith [h₀]
  nlinarith [h₀]
theorem lean_workbook_2117_1 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  rw [← sub_nonneg] at h₀
  norm_num at h₀
  constructor <;> nlinarith
theorem lean_workbook_2117_2 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  constructor <;> nlinarith [h₀]
theorem lean_workbook_2117_3 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  rw [← mul_le_mul_left (by norm_num : 0 < (2 : ℝ))]
  rw [mul_zero]
  norm_num
  constructor <;> nlinarith
theorem lean_workbook_2117_4 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  have h₁ : 3 * x^2 - 12 * x ≤ 0 := h₀
  norm_num at h₁
  refine' ⟨by nlinarith, by nlinarith⟩
theorem lean_workbook_2117_5 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  have h₁ : 3 * x^2 ≤ 12 * x := by linarith
  constructor
  nlinarith
  nlinarith
theorem lean_workbook_2117_6 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  refine ⟨?_,?_⟩
  nlinarith only [h₀]
  nlinarith only [h₀]
theorem lean_workbook_2117_7 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  apply And.intro
  nlinarith only [h₀]
  nlinarith only [h₀]
theorem lean_workbook_2117_8 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  field_simp [pow_two] at h₀ ⊢
  constructor <;> nlinarith
theorem lean_workbook_2117_9 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  apply And.intro
  nlinarith [h₀]
  nlinarith [h₀]
theorem lean_workbook_2117_10 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  have h₁ : 0 ≤ 3 * x^2 := by nlinarith
  constructor <;> nlinarith
theorem lean_workbook_2117_11 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  field_simp [pow_two] at h₀
  refine ⟨by nlinarith, by nlinarith⟩
theorem lean_workbook_2117_12 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  constructor
  nlinarith
  nlinarith only [h₀]
theorem lean_workbook_2117_13 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  have h₀ : 3 * x^2 - 12 * x ≤ 0 := by linarith
  constructor <;> nlinarith
theorem lean_workbook_2117_14 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  apply And.intro
  nlinarith
  nlinarith only [h₀]
theorem lean_workbook_2117_15 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  rw [mul_comm] at h₀
  apply And.intro
  nlinarith
  nlinarith
theorem lean_workbook_2117_16 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  field_simp [pow_two] at h₀
  constructor <;> nlinarith
theorem lean_workbook_2117_17 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  refine' ⟨_, _⟩
  nlinarith
  nlinarith [h₀]
theorem lean_workbook_2117_18 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  constructor <;> nlinarith only [h₀]
theorem lean_workbook_2117_19 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  refine' ⟨_, _⟩
  all_goals nlinarith [h₀]
theorem lean_workbook_2117_20 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  refine ⟨?_,?_⟩
  nlinarith [h₀]
  nlinarith [h₀]
theorem lean_workbook_2117_21 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  constructor
  nlinarith
  nlinarith [h₀]
theorem lean_workbook_2117_22 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  exact ⟨by nlinarith, by nlinarith⟩
theorem lean_workbook_2117_23 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  simp [sq, sub_nonpos] at h₀
  constructor <;> nlinarith
theorem lean_workbook_2117_24 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  refine ⟨?_,?_⟩
  nlinarith
  nlinarith only [h₀]
theorem lean_workbook_2117_25 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  refine' ⟨_, _⟩
  all_goals nlinarith
theorem lean_workbook_2117_26 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  constructor
  all_goals nlinarith [h₀]
theorem lean_workbook_2117_27 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  constructor
  nlinarith [h₀]
  nlinarith [h₀]
theorem lean_workbook_2117_28 (x : ℝ) (h₀ : 3 * x^2 - 12 * x ≤ 0) : 0 ≤ x ∧ x ≤ 4 := by
  have h : 3 * x^2 - 12 * x ≤ 0 := h₀
  constructor
  nlinarith
  nlinarith

theorem lean_workbook_2137_0 : ∃ l, ∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20)) = l := by
  refine' ⟨∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20)), _⟩
  simp only [eq_self_iff_true, exists_prop_of_true]
theorem lean_workbook_2137_1 : ∃ l, ∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20)) = l := by
  refine' ⟨∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20)), _⟩
  norm_num
theorem lean_workbook_2137_2 : ∃ l, ∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20)) = l := by
  use ∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20))
theorem lean_workbook_2137_3 : ∃ l, ∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20)) = l := by
  refine' ⟨∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20)), by norm_num⟩
theorem lean_workbook_2137_4 : ∃ l, ∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20)) = l := by
  refine ⟨∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20)),?_⟩
  simp only [eq_self_iff_true, heq_iff_eq, and_self_iff]
theorem lean_workbook_2137_5 : ∃ l, ∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20)) = l := by
  refine' ⟨∑' n : ℕ, Real.sqrt (n^5)/(n^4+20), _⟩
  trivial
theorem lean_workbook_2137_6 : ∃ l, ∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20)) = l := by
  refine' ⟨∑' n : ℕ, Real.sqrt (n^5)/(n^4+20), by norm_num⟩
theorem lean_workbook_2137_7 : ∃ l, ∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20)) = l := by
  refine ⟨∑' n : ℕ, Real.sqrt (n^5)/(n^4+20), by norm_num⟩
theorem lean_workbook_2137_8 : ∃ l, ∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20)) = l := by
  refine ⟨∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20)), by norm_num⟩
theorem lean_workbook_2137_9 : ∃ l, ∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20)) = l := by
  simp [Real.sqrt_sq_eq_abs, add_comm]
theorem lean_workbook_2137_10 : ∃ l, ∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20)) = l := by
  refine ⟨∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20)),?_⟩
  norm_num
theorem lean_workbook_2137_11 : ∃ l, ∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20)) = l := by
  refine' ⟨∑' n : ℕ, Real.sqrt (n^5)/(n^4+20), _⟩
  norm_num
theorem lean_workbook_2137_12 : ∃ l, ∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20)) = l := by
  refine' ⟨∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20)), _⟩
  simp
theorem lean_workbook_2137_13 : ∃ l, ∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20)) = l := by
  exact ⟨∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20)), by norm_num⟩
theorem lean_workbook_2137_14 : ∃ l, ∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20)) = l := by
  refine ⟨∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20)), rfl⟩
theorem lean_workbook_2137_15 : ∃ l, ∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20)) = l := by
  refine' ⟨∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20)), _⟩
  exact tsum_congr fun n => rfl
theorem lean_workbook_2137_16 : ∃ l, ∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20)) = l := by
  refine' ⟨∑' n : ℕ, Real.sqrt (n^5) / (n^4 + 20), _⟩
  trivial

theorem lean_workbook_2141_0 : 1^3 = 1^2 := by
  simp at *
theorem lean_workbook_2141_1 : 1^3 = 1^2 := by
  norm_num [pow_two, pow_three]
theorem lean_workbook_2141_2 : 1^3 = 1^2 := by
  simp [pow_succ]
theorem lean_workbook_2141_3 : 1^3 = 1^2 := by
  norm_num [pow_succ, pow_succ]
theorem lean_workbook_2141_4 : 1^3 = 1^2 := by
  field_simp [pow_two, pow_three]
theorem lean_workbook_2141_5 : 1^3 = 1^2 := by
  simp [sq, pow_succ]
theorem lean_workbook_2141_6 : 1^3 = 1^2 := by
  simp only [pow_one, pow_two, pow_three]
theorem lean_workbook_2141_7 : 1^3 = 1^2 := by
  simp [pow_succ, pow_zero, mul_one]
theorem lean_workbook_2141_8 : 1^3 = 1^2 := by
  norm_num [Nat.pow_succ, Nat.pow_zero, Nat.pow_one]
theorem lean_workbook_2141_9 : 1^3 = 1^2 := by
  simp [pow_succ, pow_zero, Nat.mul_one]
theorem lean_workbook_2141_10 : 1^3 = 1^2 := by
  norm_num [Nat.pow_succ, Nat.mul_succ, Nat.add_succ]
theorem lean_workbook_2141_11 : 1^3 = 1^2 := by
  exact (by norm_num : 1^3 = 1^2)
theorem lean_workbook_2141_12 : 1^3 = 1^2 := by
  simp only [pow_succ, pow_zero, one_mul]
theorem lean_workbook_2141_13 : 1^3 = 1^2 := by
  simp [one_pow]
theorem lean_workbook_2141_14 : 1^3 = 1^2 := by
  simp only [one_pow, eq_self_iff_true, and_self_iff]
theorem lean_workbook_2141_15 : 1^3 = 1^2 := by
  simp [Nat.pow_succ, Nat.pow_zero]
theorem lean_workbook_2141_16 : 1^3 = 1^2 := by
  simp only [one_pow]
theorem lean_workbook_2141_17 : 1^3 = 1^2 := by
  simp only [Nat.one_pow, Nat.cast_one]
theorem lean_workbook_2141_18 : 1^3 = 1^2 := by
  norm_num [pow_succ, pow_mul]
theorem lean_workbook_2141_19 : 1^3 = 1^2 := by
  simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
theorem lean_workbook_2141_20 : 1^3 = 1^2 := by
  norm_num [pow_succ, pow_two]
theorem lean_workbook_2141_21 : 1^3 = 1^2 := by
  norm_num [Nat.pow_succ, Nat.pow_zero, Nat.pow_one, Nat.mul_one]
theorem lean_workbook_2141_22 : 1^3 = 1^2 := by
  simp [pow_two, pow_three]
theorem lean_workbook_2141_23 : 1^3 = 1^2 := by
  norm_num [pow_one, pow_two]
theorem lean_workbook_2141_24 : 1^3 = 1^2 := by
  simp only [pow_two, pow_three, one_mul, mul_one]
theorem lean_workbook_2141_25 : 1^3 = 1^2 := by
  simp [pow_one, pow_two]

theorem lean_workbook_2156_0 : ∀ x : ℝ, x^4 - x^3 + x^2 - x + 1 > 0 := by
  rintro x
  nlinarith [sq_nonneg x, sq_nonneg (x - 1)]
theorem lean_workbook_2156_1 : ∀ x : ℝ, x^4 - x^3 + x^2 - x + 1 > 0 := by
  intro x
  nlinarith [pow_two_nonneg (x^2 - x), pow_two_nonneg (x^3 - x^2)]
theorem lean_workbook_2156_2 : ∀ x : ℝ, x^4 - x^3 + x^2 - x + 1 > 0 := by
  intro x
  nlinarith [sq_nonneg (2 : ℝ), sq_nonneg (x^2 - x)]
theorem lean_workbook_2156_3 : ∀ x : ℝ, x^4 - x^3 + x^2 - x + 1 > 0 := by
  simp [sq, add_assoc, add_comm, add_left_comm]
  intro x
  nlinarith [sq_nonneg (x ^ 2 - x)]
theorem lean_workbook_2156_4 : ∀ x : ℝ, x^4 - x^3 + x^2 - x + 1 > 0 := by
  intro x
  field_simp [sq]
  nlinarith [sq_nonneg (x ^ 2 - x)]
theorem lean_workbook_2156_5 : ∀ x : ℝ, x^4 - x^3 + x^2 - x + 1 > 0 := by
  simp [add_assoc]
  intro x
  nlinarith [sq_nonneg (x^2 - x)]
theorem lean_workbook_2156_6 : ∀ x : ℝ, x^4 - x^3 + x^2 - x + 1 > 0 := by
  intro x
  simp [sq]
  nlinarith [sq_nonneg x, sq_nonneg (x - 1)]
theorem lean_workbook_2156_7 : ∀ x : ℝ, x^4 - x^3 + x^2 - x + 1 > 0 := by
  intro x
  nlinarith [sq_nonneg (x^2 + -x)]
theorem lean_workbook_2156_8 : ∀ x : ℝ, x^4 - x^3 + x^2 - x + 1 > 0 := by
  intro x
  nlinarith [pow_two_nonneg x, pow_two_nonneg (x - 1)]
theorem lean_workbook_2156_9 : ∀ x : ℝ, x^4 - x^3 + x^2 - x + 1 > 0 := by
  intro x
  simp [add_assoc]
  nlinarith [sq_nonneg (x ^ 2 - x)]
theorem lean_workbook_2156_10 : ∀ x : ℝ, x^4 - x^3 + x^2 - x + 1 > 0 := by
  intro x
  simp [sq]
  nlinarith [sq_nonneg (x ^ 2 - x)]
theorem lean_workbook_2156_11 : ∀ x : ℝ, x^4 - x^3 + x^2 - x + 1 > 0 := by
  intro x
  simp only [add_pos_iff, add_comm]
  nlinarith [sq_nonneg (x ^ 2 - x)]
theorem lean_workbook_2156_12 : ∀ x : ℝ, x^4 - x^3 + x^2 - x + 1 > 0 := by
  simp [sq, pow_two]
  intro x
  nlinarith [sq_nonneg (x - 1), sq_nonneg x]
theorem lean_workbook_2156_13 : ∀ x : ℝ, x^4 - x^3 + x^2 - x + 1 > 0 := by
  refine' fun x => _
  nlinarith [sq_nonneg (x^2 - x)]
theorem lean_workbook_2156_14 : ∀ x : ℝ, x^4 - x^3 + x^2 - x + 1 > 0 := by
  intro x
  nlinarith [sq_nonneg (x^2 - x), sq_nonneg (x^2 + x + 1)]
theorem lean_workbook_2156_15 : ∀ x : ℝ, x^4 - x^3 + x^2 - x + 1 > 0 := by
  intro x
  simp [add_assoc]
  nlinarith [sq_nonneg (x^2 - x)]
theorem lean_workbook_2156_16 : ∀ x : ℝ, x^4 - x^3 + x^2 - x + 1 > 0 := by
  intro x
  nlinarith [pow_two_nonneg (x^2 - x), pow_two_nonneg x]
theorem lean_workbook_2156_17 : ∀ x : ℝ, x^4 - x^3 + x^2 - x + 1 > 0 := by
  intro x
  nlinarith [pow_two_nonneg (x ^ 2 - x)]
theorem lean_workbook_2156_18 : ∀ x : ℝ, x^4 - x^3 + x^2 - x + 1 > 0 := by
  simp only [add_pos_iff, add_comm, sub_eq_add_neg]
  intro x
  nlinarith [sq_nonneg (x^2 - x)]

theorem lean_workbook_2164_0 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3) : (a^2 * b^2 + b^2 * c^2)^(1/3) + (b^2 * c^2 + c^2 * a^2)^(1/3) + (c^2 * a^2 + a^2 * b^2)^(1/3) ≤ 3 * (2)^(1/3) := by
  simp [← hab]
  nlinarith
theorem lean_workbook_2164_1 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3) : (a^2 * b^2 + b^2 * c^2)^(1/3) + (b^2 * c^2 + c^2 * a^2)^(1/3) + (c^2 * a^2 + a^2 * b^2)^(1/3) ≤ 3 * (2)^(1/3) := by
  simp [add_comm, add_left_comm]
  nlinarith [ha, hb, hc, hab]
theorem lean_workbook_2164_2 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3) : (a^2 * b^2 + b^2 * c^2)^(1/3) + (b^2 * c^2 + c^2 * a^2)^(1/3) + (c^2 * a^2 + a^2 * b^2)^(1/3) ≤ 3 * (2)^(1/3) := by
  simp [← le_sub_iff_add_le', le_sub_comm]
  nlinarith [ha, hb, hc, hab]
theorem lean_workbook_2164_3 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3) : (a^2 * b^2 + b^2 * c^2)^(1/3) + (b^2 * c^2 + c^2 * a^2)^(1/3) + (c^2 * a^2 + a^2 * b^2)^(1/3) ≤ 3 * (2)^(1/3) := by
  simp [add_comm, add_left_comm, mul_comm, mul_left_comm, ha, hb, hc, pow_nonneg] at hab ⊢
  nlinarith
theorem lean_workbook_2164_4 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3) : (a^2 * b^2 + b^2 * c^2)^(1/3) + (b^2 * c^2 + c^2 * a^2)^(1/3) + (c^2 * a^2 + a^2 * b^2)^(1/3) ≤ 3 * (2)^(1/3) := by
  simp [ha, hb, hc, hab]
  norm_num
theorem lean_workbook_2164_5 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3) : (a^2 * b^2 + b^2 * c^2)^(1/3) + (b^2 * c^2 + c^2 * a^2)^(1/3) + (c^2 * a^2 + a^2 * b^2)^(1/3) ≤ 3 * (2)^(1/3) := by
  ring_nf
  nlinarith [ha, hb, hc, hab]
theorem lean_workbook_2164_6 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3) : (a^2 * b^2 + b^2 * c^2)^(1/3) + (b^2 * c^2 + c^2 * a^2)^(1/3) + (c^2 * a^2 + a^2 * b^2)^(1/3) ≤ 3 * (2)^(1/3) := by
  simp [_root_.pow_succ, add_assoc]
  nlinarith [ha, hb, hc, hab]
theorem lean_workbook_2164_7 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3) : (a^2 * b^2 + b^2 * c^2)^(1/3) + (b^2 * c^2 + c^2 * a^2)^(1/3) + (c^2 * a^2 + a^2 * b^2)^(1/3) ≤ 3 * (2)^(1/3) := by
  simp [pow_one]
  nlinarith [ha, hb, hc, hab]
theorem lean_workbook_2164_8 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3) : (a^2 * b^2 + b^2 * c^2)^(1/3) + (b^2 * c^2 + c^2 * a^2)^(1/3) + (c^2 * a^2 + a^2 * b^2)^(1/3) ≤ 3 * (2)^(1/3) := by
  simp [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
  nlinarith [ha, hb, hc, hab]
theorem lean_workbook_2164_9 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3) : (a^2 * b^2 + b^2 * c^2)^(1/3) + (b^2 * c^2 + c^2 * a^2)^(1/3) + (c^2 * a^2 + a^2 * b^2)^(1/3) ≤ 3 * (2)^(1/3) := by
  simp [← pow_mul, hab]
  nlinarith [ha, hb, hc, hab]
theorem lean_workbook_2164_10 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3) : (a^2 * b^2 + b^2 * c^2)^(1/3) + (b^2 * c^2 + c^2 * a^2)^(1/3) + (c^2 * a^2 + a^2 * b^2)^(1/3) ≤ 3 * (2)^(1/3) := by
  simp [ha, hb, hc]
  nlinarith [ha, hb, hc, hab]
theorem lean_workbook_2164_11 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3) : (a^2 * b^2 + b^2 * c^2)^(1/3) + (b^2 * c^2 + c^2 * a^2)^(1/3) + (c^2 * a^2 + a^2 * b^2)^(1/3) ≤ 3 * (2)^(1/3) := by
  simp [_root_.pow_succ, hab]
  nlinarith [ha, hb, hc, hab]

theorem lean_workbook_2174_0 : ∀ α β : ℝ, 2 * Real.sin ((α - β) / 2) * Real.cos ((α + β) / 2) = Real.sin α - Real.sin β := by
  intro α β
  rw [← Complex.ofReal_inj]
  simp [sin_sub]
  simp [Complex.sin_sub_sin]
theorem lean_workbook_2174_1 : ∀ α β : ℝ, 2 * Real.sin ((α - β) / 2) * Real.cos ((α + β) / 2) = Real.sin α - Real.sin β := by
  intros α β
  rw [← Complex.ofReal_inj]
  simp [sin_sub, Complex.sin_sub_sin]
theorem lean_workbook_2174_2 : ∀ α β : ℝ, 2 * Real.sin ((α - β) / 2) * Real.cos ((α + β) / 2) = Real.sin α - Real.sin β := by
  intro α β
  rw [← Complex.ofReal_inj]
  simp [Complex.sin_sub_sin]
theorem lean_workbook_2174_3 : ∀ α β : ℝ, 2 * Real.sin ((α - β) / 2) * Real.cos ((α + β) / 2) = Real.sin α - Real.sin β := by
  intro α β
  rw [← Complex.ofReal_inj]
  simp [sin_sub, Complex.sin_sub_sin]
theorem lean_workbook_2174_4 : ∀ α β : ℝ, 2 * Real.sin ((α - β) / 2) * Real.cos ((α + β) / 2) = Real.sin α - Real.sin β := by
  intro α β
  rw [← Complex.ofReal_inj]
  simp [sin_sub, mul_add, add_mul, Complex.sin_sub_sin]
theorem lean_workbook_2174_5 : ∀ α β : ℝ, 2 * Real.sin ((α - β) / 2) * Real.cos ((α + β) / 2) = Real.sin α - Real.sin β := by
  intro α β
  rw [← Complex.ofReal_inj]
  simp [Complex.sin_sub_sin, Complex.ofReal_sub]

theorem lean_workbook_2176_0 : ∀ n ≥ 1, 133 ∣ 11 ^ (n + 2) + 12 ^ (2 * n + 1) := by
  intros n hn
  simp [Nat.dvd_iff_mod_eq_zero]
  simp [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hn]
  omega
theorem lean_workbook_2176_1 : ∀ n ≥ 1, 133 ∣ 11 ^ (n + 2) + 12 ^ (2 * n + 1) := by
  intros n h
  rw [Nat.dvd_iff_mod_eq_zero]
  cases n
  contradiction
  simp [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, h]
  omega
theorem lean_workbook_2176_2 : ∀ n ≥ 1, 133 ∣ 11 ^ (n + 2) + 12 ^ (2 * n + 1) := by
  rintro n (hn : 1 ≤ n)
  rw [Nat.dvd_iff_mod_eq_zero]
  simp [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hn]
  omega
theorem lean_workbook_2176_3 : ∀ n ≥ 1, 133 ∣ 11 ^ (n + 2) + 12 ^ (2 * n + 1) := by
  intro n hn
  rw [Nat.dvd_iff_mod_eq_zero]
  cases' n with n
  exfalso
  linarith
  simp [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hn]
  omega
theorem lean_workbook_2176_4 : ∀ n ≥ 1, 133 ∣ 11 ^ (n + 2) + 12 ^ (2 * n + 1) := by
  intro n hn
  rw [Nat.dvd_iff_mod_eq_zero]
  simp [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hn]
  omega
theorem lean_workbook_2176_5 : ∀ n ≥ 1, 133 ∣ 11 ^ (n + 2) + 12 ^ (2 * n + 1) := by
  intros n hn
  rw [Nat.dvd_iff_mod_eq_zero]
  simp [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hn]
  omega
theorem lean_workbook_2176_6 : ∀ n ≥ 1, 133 ∣ 11 ^ (n + 2) + 12 ^ (2 * n + 1) := by
  intros n hn
  rw [Nat.dvd_iff_mod_eq_zero]
  simp [pow_add, pow_mul, pow_one, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hn]
  omega
theorem lean_workbook_2176_7 : ∀ n ≥ 1, 133 ∣ 11 ^ (n + 2) + 12 ^ (2 * n + 1) := by
  rintro n (hn : 1 ≤ n)
  rw [Nat.dvd_iff_mod_eq_zero]
  simp [pow_add, pow_mul, pow_one, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hn]
  omega
theorem lean_workbook_2176_8 : ∀ n ≥ 1, 133 ∣ 11 ^ (n + 2) + 12 ^ (2 * n + 1) := by
  intro n hn
  rw [Nat.dvd_iff_mod_eq_zero]
  simp [pow_add, pow_mul, pow_one, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hn]
  omega
theorem lean_workbook_2176_9 : ∀ n ≥ 1, 133 ∣ 11 ^ (n + 2) + 12 ^ (2 * n + 1) := by
  intro n hn
  simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod]
  simp [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hn]
  omega
theorem lean_workbook_2176_10 : ∀ n ≥ 1, 133 ∣ 11 ^ (n + 2) + 12 ^ (2 * n + 1) := by
  intro n hn
  rw [Nat.dvd_iff_mod_eq_zero]
  cases' n with n
  contradiction
  simp [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hn]
  omega

theorem lean_workbook_2182_0 (a b c : ℝ) : a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b ≤ a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c),  sq_nonneg (a - c)]
theorem lean_workbook_2182_1 (a b c : ℝ) : a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b ≤ a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 := by
  have h1 : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  have h2 : 0 ≤ (b - c) ^ 2 := sq_nonneg (b - c)
  have h3 : 0 ≤ (c - a) ^ 2 := sq_nonneg (c - a)
  nlinarith
theorem lean_workbook_2182_2 (a b c : ℝ) : a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b ≤ a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 := by
  rw [← sub_nonneg]
  ring_nf
  nlinarith [sq_nonneg (a * c - b * a), sq_nonneg (b * a - c * b), sq_nonneg (c * b - a * c)]
theorem lean_workbook_2182_3 (a b c : ℝ) : a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b ≤ a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 := by
  simp [mul_assoc]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
theorem lean_workbook_2182_4 (a b c : ℝ) : a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b ≤ a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 := by
  simp [mul_assoc]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_2182_5 (a b c : ℝ) : a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b ≤ a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 := by
  have h1 := sq_nonneg (a * b - b * c)
  have h2 := sq_nonneg (b * c - c * a)
  have h3 := sq_nonneg (c * a - a * b)
  linarith
theorem lean_workbook_2182_6 (a b c : ℝ) : a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b ≤ a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 := by
  have h1 := sq_nonneg (b - c)
  have h2 := sq_nonneg (c - a)
  have h3 := sq_nonneg (a - b)
  nlinarith
theorem lean_workbook_2182_7 (a b c : ℝ) : a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b ≤ a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 := by
  rw [← sub_nonneg]
  ring_nf
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_2182_8 (a b c : ℝ) : a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b ≤ a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 := by
  have h1 : 0 ≤ (a * b - b * c) ^ 2 + (b * c - c * a) ^ 2 + (c * a - a * b) ^ 2 := by positivity
  linarith
theorem lean_workbook_2182_9 (a b c : ℝ) : a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b ≤ a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 := by
  simp [sq]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_2182_10 (a b c : ℝ) : a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b ≤ a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 := by
  have h1 := sq_nonneg (a * c - b * c)
  have h2 := sq_nonneg (b * a - c * a)
  have h3 := sq_nonneg (c * b - a * b)
  linarith
theorem lean_workbook_2182_11 (a b c : ℝ) : a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b ≤ a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 := by
  ring_nf
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

theorem lean_workbook_2209_0 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : p * q^2 ≤ (p^3 + 2 * q^3) / 3 := by
  simp [mul_comm]
  nlinarith [sq_nonneg (p - q), sq_nonneg (p + 2 * q)]
theorem lean_workbook_2209_1 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : p * q^2 ≤ (p^3 + 2 * q^3) / 3 := by
  ring_nf
  have h1 : 0 ≤ (p - q)^2 := sq_nonneg (p - q)
  nlinarith
theorem lean_workbook_2209_2 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : p * q^2 ≤ (p^3 + 2 * q^3) / 3 := by
  rw [mul_comm]
  have := sq_nonneg (p - q)
  nlinarith [hp, hq]
theorem lean_workbook_2209_3 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : p * q^2 ≤ (p^3 + 2 * q^3) / 3 := by
  have h1 : 0 ≤ (p - q)^2 := sq_nonneg (p - q)
  nlinarith [h1]
theorem lean_workbook_2209_4 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : p * q^2 ≤ (p^3 + 2 * q^3) / 3 := by
  ring_nf
  have hpq : 0 < p * q := mul_pos hp hq
  nlinarith [sq_nonneg (p - q), sq_nonneg (p + 2 * q)]
theorem lean_workbook_2209_5 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : p * q^2 ≤ (p^3 + 2 * q^3) / 3 := by
  have : 0 ≤ (p - q)^2 := sq_nonneg (p - q)
  nlinarith [mul_nonneg hp.le (sq_nonneg q)]
theorem lean_workbook_2209_6 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : p * q^2 ≤ (p^3 + 2 * q^3) / 3 := by
  have h1 := sq_nonneg (p - q)
  have h2 := sq_nonneg (p + 2 * q)
  nlinarith [h1, h2]
theorem lean_workbook_2209_7 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : p * q^2 ≤ (p^3 + 2 * q^3) / 3 := by
  rw [mul_comm]
  have := sq_nonneg (p - q)
  nlinarith
theorem lean_workbook_2209_8 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : p * q^2 ≤ (p^3 + 2 * q^3) / 3 := by
  have hp3 : 0 < p^3 := pow_pos hp 3
  nlinarith [sq_nonneg (p - q)]
theorem lean_workbook_2209_9 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : p * q^2 ≤ (p^3 + 2 * q^3) / 3 := by
  have : 0 ≤ (p - q)^2 := sq_nonneg (p - q)
  nlinarith
theorem lean_workbook_2209_10 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : p * q^2 ≤ (p^3 + 2 * q^3) / 3 := by
  have : 0 ≤ (p - q)^2 := sq_nonneg (p - q)
  nlinarith [this]
theorem lean_workbook_2209_11 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : p * q^2 ≤ (p^3 + 2 * q^3) / 3 := by
  have hp3 : 0 < p^3 := by positivity
  nlinarith [sq_nonneg (p - q)]
theorem lean_workbook_2209_12 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : p * q^2 ≤ (p^3 + 2 * q^3) / 3 := by
  nlinarith [sq_nonneg (p - q)]
theorem lean_workbook_2209_13 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : p * q^2 ≤ (p^3 + 2 * q^3) / 3 := by
  ring_nf
  rw [add_comm]
  have hpq : 0 < p * q := mul_pos hp hq
  nlinarith [sq_nonneg (p - q)]
theorem lean_workbook_2209_14 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : p * q^2 ≤ (p^3 + 2 * q^3) / 3 := by
  have := sq_nonneg (p - q)
  nlinarith [hq, hp]
theorem lean_workbook_2209_15 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : p * q^2 ≤ (p^3 + 2 * q^3) / 3 := by
  have h1 := sq_nonneg (p - q)
  have h2 := sq_nonneg (p + 2 * q)
  nlinarith
theorem lean_workbook_2209_16 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : p * q^2 ≤ (p^3 + 2 * q^3) / 3 := by
  have := sq_nonneg (p - q)
  apply le_of_sub_nonneg
  field_simp [hp.ne', hq.ne']
  ring_nf
  nlinarith
theorem lean_workbook_2209_17 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : p * q^2 ≤ (p^3 + 2 * q^3) / 3 := by
  have hpq : 0 < p * q := mul_pos hp hq
  nlinarith [sq_nonneg (p - q)]
theorem lean_workbook_2209_18 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : p * q^2 ≤ (p^3 + 2 * q^3) / 3 := by
  have := sq_nonneg (p - q)
  nlinarith
theorem lean_workbook_2209_19 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : p * q^2 ≤ (p^3 + 2 * q^3) / 3 := by
  field_simp [mul_comm]
  nlinarith [sq_nonneg (p - q), sq_nonneg (p + 2 * q)]
theorem lean_workbook_2209_20 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : p * q^2 ≤ (p^3 + 2 * q^3) / 3 := by
  have hpq := sq_nonneg (p - q)
  nlinarith [hp, hq, hpq]
theorem lean_workbook_2209_21 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : p * q^2 ≤ (p^3 + 2 * q^3) / 3 := by
  have : 0 ≤ (p - q)^2 := sq_nonneg (p - q)
  nlinarith [hq, hp]

theorem lean_workbook_2216_0 : 9! ≡ -1 [ZMOD 71] := by
  conv_lhs => rw [← one_mul 9]
theorem lean_workbook_2216_1 : 9! ≡ -1 [ZMOD 71] := by
  norm_num [Nat.factorial_succ, Nat.factorial_zero]
  decide
theorem lean_workbook_2216_2 : 9! ≡ -1 [ZMOD 71] := by
  norm_num [Nat.factorial, Int.ModEq]
theorem lean_workbook_2216_3 : 9! ≡ -1 [ZMOD 71] := by
  norm_num [factorial_succ, Int.ModEq]
theorem lean_workbook_2216_4 : 9! ≡ -1 [ZMOD 71] := by
  conv_lhs => norm_num [Nat.factorial]
theorem lean_workbook_2216_5 : 9! ≡ -1 [ZMOD 71] := by
  conv_lhs => rw [← Nat.mod_add_div 9 71]
theorem lean_workbook_2216_6 : 9! ≡ -1 [ZMOD 71] := by
  simp only [Int.ModEq]
  decide
theorem lean_workbook_2216_7 : 9! ≡ -1 [ZMOD 71] := by
  simp only [Int.ModEq]
  rfl
theorem lean_workbook_2216_8 : 9! ≡ -1 [ZMOD 71] := by
  conv => lhs; rw [← Nat.mod_add_div 9 71]

theorem lean_workbook_2224_0 (a b c : ℝ) : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) := by
  linarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (a ^ 2 - c ^ 2)]
theorem lean_workbook_2224_1 (a b c : ℝ) : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) := by
  ring_nf
  linarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2)]
theorem lean_workbook_2224_2 (a b c : ℝ) : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) := by
  have := sq_nonneg (a^2 - b^2)
  have := sq_nonneg (b^2 - c^2)
  have := sq_nonneg (c^2 - a^2)
  linarith
theorem lean_workbook_2224_3 (a b c : ℝ) : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) := by
  ring_nf
  simp [sq]
  linarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2)]
theorem lean_workbook_2224_4 (a b c : ℝ) : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) := by
  have h0 := sq_nonneg (a^2 - b^2)
  have h1 := sq_nonneg (b^2 - c^2)
  have h2 := sq_nonneg (c^2 - a^2)
  linarith
theorem lean_workbook_2224_5 (a b c : ℝ) : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) := by
  ring_nf
  rw [add_assoc]
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2)]
theorem lean_workbook_2224_6 (a b c : ℝ) : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) := by
  ring_nf
  nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2)]
theorem lean_workbook_2224_7 (a b c : ℝ) : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) := by
  ring_nf
  simp only [sq, mul_add, mul_comm, mul_left_comm]
  linarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2)]
theorem lean_workbook_2224_8 (a b c : ℝ) : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) := by
  have h := sq_nonneg (a ^ 2 - b ^ 2)
  have h' := sq_nonneg (b ^ 2 - c ^ 2)
  have h'' := sq_nonneg (c ^ 2 - a ^ 2)
  linarith
theorem lean_workbook_2224_9 (a b c : ℝ) : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) := by
  linarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2)]
theorem lean_workbook_2224_10 (a b c : ℝ) : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) := by
  simp [sq]
  linarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2)]
theorem lean_workbook_2224_11 (a b c : ℝ) : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) := by
  simp only [sq]
  linarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2)]
theorem lean_workbook_2224_12 (a b c : ℝ) : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) := by
  ring_nf
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (a ^ 2 - c ^ 2)]
theorem lean_workbook_2224_13 (a b c : ℝ) : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) := by
  have h1 : 0 ≤ (a^2 - b^2)^2 + (b^2 - c^2)^2 + (c^2 - a^2)^2 := by positivity
  linarith

theorem lean_workbook_2260_0 : ∀ a b c : ℝ, (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  refine' fun a b c => _
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_2260_1 : ∀ a b c : ℝ, (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  rintro a b c
  ring_nf
  ring_nf
  ring_nf
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_2260_2 : ∀ a b c : ℝ, (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  rintro a b c
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_2260_3 : ∀ a b c : ℝ, (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  intro a b c
  simp [sq, add_assoc]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_2260_4 : ∀ a b c : ℝ, (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  intros a b c
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_2260_5 : ∀ a b c : ℝ, (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  intro a b c
  have := sq_nonneg (a - b)
  have := sq_nonneg (b - c)
  have := sq_nonneg (a - c)
  linarith
theorem lean_workbook_2260_6 : ∀ a b c : ℝ, (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  intro a b c
  ring_nf
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_2260_7 : ∀ a b c : ℝ, (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  intro a b c
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_2260_8 : ∀ a b c : ℝ, (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  rintro a b c
  ring_nf
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_2260_9 : ∀ a b c : ℝ, (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  intro a b c
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_2260_10 : ∀ a b c : ℝ, (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  intro a b c
  simp [add_assoc, add_left_comm, add_comm]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_2260_11 : ∀ a b c : ℝ, (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  simp [sq]
  intro a b c
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_2260_12 : ∀ a b c : ℝ, (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  intro a b c
  simp [add_sq]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_2260_13 : ∀ a b c : ℝ, (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  refine' fun a b c => _
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem lean_workbook_2260_14 : ∀ a b c : ℝ, (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  intro a b c
  simp [add_assoc, add_comm, add_left_comm]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
theorem lean_workbook_2260_15 : ∀ a b c : ℝ, (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  intro x y z
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_2260_16 : ∀ a b c : ℝ, (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  intros a b c
  simp [sq, add_assoc, add_left_comm, add_comm]
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

theorem lean_workbook_2271_0 (x y z : ℝ) : 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2 := by
  have h3 : 0 ≤ (x - y)^2 + (y - z)^2 + (z - x)^2 := by nlinarith
  linarith
theorem lean_workbook_2271_1 (x y z : ℝ) : 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2 := by
  have h₁ := sq_nonneg (x - y)
  have h₂ := sq_nonneg (y - z)
  have h₃ := sq_nonneg (z - x)
  linarith
theorem lean_workbook_2271_2 (x y z : ℝ) : 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2 := by
  rw [sq]
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_2271_3 (x y z : ℝ) : 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2 := by
  ring_nf
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_2271_4 (x y z : ℝ) : 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2 := by
  ring_nf
  linarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]
theorem lean_workbook_2271_5 (x y z : ℝ) : 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2 := by
  nlinarith only [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_2271_6 (x y z : ℝ) : 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2 := by
  simp [sq, mul_add, add_mul, mul_comm, mul_left_comm]
  linarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_2271_7 (x y z : ℝ) : 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2 := by
  have h1 := sq_nonneg (x - y)
  have h2 := sq_nonneg (y - z)
  have h3 := sq_nonneg (z - x)
  linarith
theorem lean_workbook_2271_8 (x y z : ℝ) : 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2 := by
  ring_nf
  simp only [sq]
  linarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_2271_9 (x y z : ℝ) : 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2 := by
  linarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_2271_10 (x y z : ℝ) : 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2 := by
  simp only [sq]
  linarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_2271_11 (x y z : ℝ) : 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2 := by
  ring_nf
  linarith only [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_2271_12 (x y z : ℝ) : 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2 := by
  simp [sq, add_mul, mul_add]
  linarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_2271_13 (x y z : ℝ) : 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2 := by
  ring_nf
  ring_nf
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_2271_14 (x y z : ℝ) : 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2 := by
  simp [sq, add_mul, mul_add, mul_comm, mul_left_comm]
  linarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_2271_15 (x y z : ℝ) : 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2 := by
  have := sq_nonneg (x - y)
  linarith [sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_2271_16 (x y z : ℝ) : 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2 := by
  have h1 : 0 ≤ (x - y)^2 + (y - z)^2 + (z - x)^2 := by nlinarith
  nlinarith
theorem lean_workbook_2271_17 (x y z : ℝ) : 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2 := by
  ring_nf
  ring_nf
  ring_nf
  linarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_2271_18 (x y z : ℝ) : 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2 := by
  rw [sq, add_assoc, add_comm]
  linarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_2271_19 (x y z : ℝ) : 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2 := by
  simp [sq, mul_add, add_mul]
  linarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_2271_20 (x y z : ℝ) : 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2 := by
  simp [mul_add, add_mul]
  linarith [mul_self_nonneg (x - y), mul_self_nonneg (y - z), mul_self_nonneg (z - x)]
theorem lean_workbook_2271_21 (x y z : ℝ) : 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2 := by
  have := sq_nonneg (x - y)
  have := sq_nonneg (y - z)
  have := sq_nonneg (z - x)
  linarith
theorem lean_workbook_2271_22 (x y z : ℝ) : 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2 := by
  simp [sq]
  linarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
theorem lean_workbook_2271_23 (x y z : ℝ) : 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2 := by
  have h1 : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
  have h2 : 0 ≤ (y - z) ^ 2 := sq_nonneg (y - z)
  have h3 : 0 ≤ (z - x) ^ 2 := sq_nonneg (z - x)
  linarith

theorem lean_workbook_2272_0 : ∀ a b : ℝ, (Real.sqrt a - 1 / 2)^2 + (Real.sqrt b - 1 / 2)^2 ≥ 0 := by
  exact fun a b => add_nonneg (sq_nonneg _) (sq_nonneg _)
theorem lean_workbook_2272_1 : ∀ a b : ℝ, (Real.sqrt a - 1 / 2)^2 + (Real.sqrt b - 1 / 2)^2 ≥ 0 := by
  intro a b
  exact add_nonneg (pow_two_nonneg _) (pow_two_nonneg _)
theorem lean_workbook_2272_2 : ∀ a b : ℝ, (Real.sqrt a - 1 / 2)^2 + (Real.sqrt b - 1 / 2)^2 ≥ 0 := by
  simp [add_nonneg]
  intro a b
  apply_rules [sq_nonneg, add_nonneg]
theorem lean_workbook_2272_3 : ∀ a b : ℝ, (Real.sqrt a - 1 / 2)^2 + (Real.sqrt b - 1 / 2)^2 ≥ 0 := by
  simp [sq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  intros a b
  nlinarith [sq_nonneg (Real.sqrt a), sq_nonneg (Real.sqrt b)]
theorem lean_workbook_2272_4 : ∀ a b : ℝ, (Real.sqrt a - 1 / 2)^2 + (Real.sqrt b - 1 / 2)^2 ≥ 0 := by
  exact fun a b ↦ add_nonneg (sq_nonneg _) (sq_nonneg _)
theorem lean_workbook_2272_5 : ∀ a b : ℝ, (Real.sqrt a - 1 / 2)^2 + (Real.sqrt b - 1 / 2)^2 ≥ 0 := by
  intro a b
  refine' add_nonneg (sq_nonneg (Real.sqrt a - 1 / 2)) (sq_nonneg (Real.sqrt b - 1 / 2))
theorem lean_workbook_2272_6 : ∀ a b : ℝ, (Real.sqrt a - 1 / 2)^2 + (Real.sqrt b - 1 / 2)^2 ≥ 0 := by
  intros a b
  refine' add_nonneg (sq_nonneg _) (sq_nonneg _)
theorem lean_workbook_2272_7 : ∀ a b : ℝ, (Real.sqrt a - 1 / 2)^2 + (Real.sqrt b - 1 / 2)^2 ≥ 0 := by
  exact fun a b => by positivity
theorem lean_workbook_2272_8 : ∀ a b : ℝ, (Real.sqrt a - 1 / 2)^2 + (Real.sqrt b - 1 / 2)^2 ≥ 0 := by
  intros a b
  nlinarith [sq_nonneg (Real.sqrt a), sq_nonneg (Real.sqrt b)]
theorem lean_workbook_2272_9 : ∀ a b : ℝ, (Real.sqrt a - 1 / 2)^2 + (Real.sqrt b - 1 / 2)^2 ≥ 0 := by
  exact fun a b ↦ by positivity
theorem lean_workbook_2272_10 : ∀ a b : ℝ, (Real.sqrt a - 1 / 2)^2 + (Real.sqrt b - 1 / 2)^2 ≥ 0 := by
  intro a b
  linarith only [sq_nonneg (Real.sqrt a - 1 / 2), sq_nonneg (Real.sqrt b - 1 / 2)]
theorem lean_workbook_2272_11 : ∀ a b : ℝ, (Real.sqrt a - 1 / 2)^2 + (Real.sqrt b - 1 / 2)^2 ≥ 0 := by
  exact fun a b => by nlinarith [sq_nonneg (Real.sqrt a), sq_nonneg (Real.sqrt b)]
theorem lean_workbook_2272_12 : ∀ a b : ℝ, (Real.sqrt a - 1 / 2)^2 + (Real.sqrt b - 1 / 2)^2 ≥ 0 := by
  intro a b
  simp [sq]
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
theorem lean_workbook_2272_13 : ∀ a b : ℝ, (Real.sqrt a - 1 / 2)^2 + (Real.sqrt b - 1 / 2)^2 ≥ 0 := by
  intro a b
  exact add_nonneg (sq_nonneg (Real.sqrt a - 1 / 2)) (sq_nonneg (Real.sqrt b - 1 / 2))
theorem lean_workbook_2272_14 : ∀ a b : ℝ, (Real.sqrt a - 1 / 2)^2 + (Real.sqrt b - 1 / 2)^2 ≥ 0 := by
  intros a b
  apply_rules [add_nonneg, sq_nonneg, sub_nonneg]
theorem lean_workbook_2272_15 : ∀ a b : ℝ, (Real.sqrt a - 1 / 2)^2 + (Real.sqrt b - 1 / 2)^2 ≥ 0 := by
  simp [sq]
  intro a b
  apply_rules [add_nonneg, mul_self_nonneg, sub_nonneg]
  all_goals nlinarith [sq_nonneg (Real.sqrt a), sq_nonneg (Real.sqrt b)]
theorem lean_workbook_2272_16 : ∀ a b : ℝ, (Real.sqrt a - 1 / 2)^2 + (Real.sqrt b - 1 / 2)^2 ≥ 0 := by
  simp [sq_nonneg, add_nonneg]
theorem lean_workbook_2272_17 : ∀ a b : ℝ, (Real.sqrt a - 1 / 2)^2 + (Real.sqrt b - 1 / 2)^2 ≥ 0 := by
  intro a b
  simp [sq_nonneg, add_nonneg]
theorem lean_workbook_2272_18 : ∀ a b : ℝ, (Real.sqrt a - 1 / 2)^2 + (Real.sqrt b - 1 / 2)^2 ≥ 0 := by
  exact fun a b ↦ add_nonneg (pow_two_nonneg _) (pow_two_nonneg _)
theorem lean_workbook_2272_19 : ∀ a b : ℝ, (Real.sqrt a - 1 / 2)^2 + (Real.sqrt b - 1 / 2)^2 ≥ 0 := by
  exact fun a b ↦ add_nonneg (sq_nonneg (Real.sqrt a - 1 / 2)) (sq_nonneg (Real.sqrt b - 1 / 2))
theorem lean_workbook_2272_20 : ∀ a b : ℝ, (Real.sqrt a - 1 / 2)^2 + (Real.sqrt b - 1 / 2)^2 ≥ 0 := by
  rintro a b
  nlinarith [sq_nonneg (Real.sqrt a), sq_nonneg (Real.sqrt b)]
theorem lean_workbook_2272_21 : ∀ a b : ℝ, (Real.sqrt a - 1 / 2)^2 + (Real.sqrt b - 1 / 2)^2 ≥ 0 := by
  intro a b
  nlinarith [sq_nonneg (Real.sqrt a), sq_nonneg (Real.sqrt b)]
theorem lean_workbook_2272_22 : ∀ a b : ℝ, (Real.sqrt a - 1 / 2)^2 + (Real.sqrt b - 1 / 2)^2 ≥ 0 := by
  intro a b
  nlinarith only [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
theorem lean_workbook_2272_23 : ∀ a b : ℝ, (Real.sqrt a - 1 / 2)^2 + (Real.sqrt b - 1 / 2)^2 ≥ 0 := by
  intro a b
  all_goals nlinarith [sqrt_nonneg a, sqrt_nonneg b]

theorem lean_workbook_2274_0 (x : ℝ) (hx : 0 < x): ¬ (x + 2022 = Int.floor x * (x - Int.floor x)) := by
  by_contra!
  have h₁ := Int.floor_le x
  have h₂ := Int.lt_floor_add_one x
  nlinarith
theorem lean_workbook_2274_1 (x : ℝ) (hx : 0 < x): ¬ (x + 2022 = Int.floor x * (x - Int.floor x)) := by
  by_contra h
  have h₁ := Int.floor_le x
  have h₂ := Int.lt_floor_add_one x
  nlinarith
theorem lean_workbook_2274_2 (x : ℝ) (hx : 0 < x): ¬ (x + 2022 = Int.floor x * (x - Int.floor x)) := by
  rw [← add_neg_eq_zero]
  intro h
  nlinarith [Int.floor_le x, Int.lt_floor_add_one x, h]
theorem lean_workbook_2274_3 (x : ℝ) (hx : 0 < x): ¬ (x + 2022 = Int.floor x * (x - Int.floor x)) := by
  contrapose!
  intro _
  nlinarith [Int.floor_le x, Int.lt_floor_add_one x]
theorem lean_workbook_2274_4 (x : ℝ) (hx : 0 < x): ¬ (x + 2022 = Int.floor x * (x - Int.floor x)) := by
  intro h
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  nlinarith [h1, h2, h]

theorem lean_workbook_2281_0 (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8) : -4 / 5 ≤ a ∧ a ≤ 4 := by
  refine' ⟨_, _⟩
  linarith
  linarith [h1.1, h2]
theorem lean_workbook_2281_1 (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8) : -4 / 5 ≤ a ∧ a ≤ 4 := by
  refine ⟨?_,?_⟩
  nlinarith
  linarith [h1.1, h2]
theorem lean_workbook_2281_2 (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8) : -4 / 5 ≤ a ∧ a ≤ 4 := by
  constructor
  linarith [h1.1]
  linarith [h1.2, h2]
theorem lean_workbook_2281_3 (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8) : -4 / 5 ≤ a ∧ a ≤ 4 := by
  refine' ⟨_, _⟩
  nlinarith [h1.1]
  nlinarith [h1.2, h2]
theorem lean_workbook_2281_4 (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8) : -4 / 5 ≤ a ∧ a ≤ 4 := by
  refine' ⟨by linarith [h1.1, h2], by linarith [h1.2, h2]⟩
theorem lean_workbook_2281_5 (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8) : -4 / 5 ≤ a ∧ a ≤ 4 := by
  refine ⟨?_,?_⟩
  linarith [h1.1, h2]
  linarith [h1.2, h2]
theorem lean_workbook_2281_6 (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8) : -4 / 5 ≤ a ∧ a ≤ 4 := by
  refine' ⟨by linarith, by linarith⟩
theorem lean_workbook_2281_7 (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8) : -4 / 5 ≤ a ∧ a ≤ 4 := by
  apply And.intro
  linarith [h1, h2]
  linarith [h1, h2]
theorem lean_workbook_2281_8 (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8) : -4 / 5 ≤ a ∧ a ≤ 4 := by
  exact ⟨by linarith [h1.1, h2], by linarith [h1.2, h2]⟩
theorem lean_workbook_2281_9 (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8) : -4 / 5 ≤ a ∧ a ≤ 4 := by
  refine' ⟨_, _⟩
  linarith
  linarith only [h1.1, h1.2, h2]
theorem lean_workbook_2281_10 (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8) : -4 / 5 ≤ a ∧ a ≤ 4 := by
  constructor
  linarith [h1.1, h2]
  linarith [h1.2, h2]
theorem lean_workbook_2281_11 (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8) : -4 / 5 ≤ a ∧ a ≤ 4 := by
  refine ⟨?_,?_⟩
  linarith [h1, h2]
  linarith [h1, h2]
theorem lean_workbook_2281_12 (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8) : -4 / 5 ≤ a ∧ a ≤ 4 := by
  apply And.intro
  linarith [h1.1, h2]
  linarith [h1.2, h2]
theorem lean_workbook_2281_13 (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8) : -4 / 5 ≤ a ∧ a ≤ 4 := by
  constructor <;> nlinarith
theorem lean_workbook_2281_14 (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8) : -4 / 5 ≤ a ∧ a ≤ 4 := by
  constructor
  linarith [h1, h2]
  linarith [h1, h2]
theorem lean_workbook_2281_15 (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8) : -4 / 5 ≤ a ∧ a ≤ 4 := by
  constructor
  linarith [h1.1]
  linarith [h1.2]
theorem lean_workbook_2281_16 (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8) : -4 / 5 ≤ a ∧ a ≤ 4 := by
  apply And.intro
  linarith [h2]
  linarith [h2]
theorem lean_workbook_2281_17 (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8) : -4 / 5 ≤ a ∧ a ≤ 4 := by
  constructor <;> linarith
theorem lean_workbook_2281_18 (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8) : -4 / 5 ≤ a ∧ a ≤ 4 := by
  refine' ⟨_, _⟩
  all_goals linarith
theorem lean_workbook_2281_19 (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8) : -4 / 5 ≤ a ∧ a ≤ 4 := by
  rw [← neg_le_neg_iff] at *
  constructor
  linarith [h1, h2]
  linarith [h1, h2]
theorem lean_workbook_2281_20 (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8) : -4 / 5 ≤ a ∧ a ≤ 4 := by
  apply And.intro
  linarith [h1.1, h1.2, h2]
  linarith [h1.1, h1.2, h2]
theorem lean_workbook_2281_21 (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8) : -4 / 5 ≤ a ∧ a ≤ 4 := by
  constructor
  nlinarith
  linarith [h1.2, h2]
theorem lean_workbook_2281_22 (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8) : -4 / 5 ≤ a ∧ a ≤ 4 := by
  refine ⟨?_,?_⟩
  linarith [h1.1, h1.2, h2]
  linarith [h1.1, h1.2, h2]
theorem lean_workbook_2281_23 (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8) : -4 / 5 ≤ a ∧ a ≤ 4 := by
  constructor
  nlinarith only [h1, h2]
  nlinarith only [h1, h2]
theorem lean_workbook_2281_24 (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8) : -4 / 5 ≤ a ∧ a ≤ 4 := by
  refine' ⟨_, _⟩
  linarith [h1.1]
  linarith [h1.2, h2]
theorem lean_workbook_2281_25 (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8) : -4 / 5 ≤ a ∧ a ≤ 4 := by
  constructor <;> linarith [h1, h2]
theorem lean_workbook_2281_26 (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8) : -4 / 5 ≤ a ∧ a ≤ 4 := by
  refine' ⟨_, _⟩
  linarith [h1.1, h2]
  linarith [h1.2, h2]

theorem lean_workbook_2305_0 : 7 ^ 25 ≡ 16 ^ 5 [MOD 29] := by
  change 7 ^ 25 % 29 = 16 ^ 5 % 29
  simp [Nat.mod_eq_of_lt]
theorem lean_workbook_2305_1 : 7 ^ 25 ≡ 16 ^ 5 [MOD 29] := by
  show 7 ^ 25 % 29 = 16 ^ 5 % 29
  norm_num
theorem lean_workbook_2305_2 : 7 ^ 25 ≡ 16 ^ 5 [MOD 29] := by
  conv => lhs; rw [← pow_one 7, ← pow_mul, mul_comm]
theorem lean_workbook_2305_3 : 7 ^ 25 ≡ 16 ^ 5 [MOD 29] := by
  conv_lhs => rw [← pow_one 7, ← pow_mul, mul_comm]
theorem lean_workbook_2305_4 : 7 ^ 25 ≡ 16 ^ 5 [MOD 29] := by
  simp only [Nat.ModEq]
  norm_cast
theorem lean_workbook_2305_5 : 7 ^ 25 ≡ 16 ^ 5 [MOD 29] := by
  exact (show 7 ^ 25 % 29 = 16 ^ 5 % 29 from by norm_num)
theorem lean_workbook_2305_6 : 7 ^ 25 ≡ 16 ^ 5 [MOD 29] := by
  conv => lhs; rw [← pow_one 7]
theorem lean_workbook_2305_7 : 7 ^ 25 ≡ 16 ^ 5 [MOD 29] := by
  conv => lhs; rw [← Nat.mod_add_div 25 4]
theorem lean_workbook_2305_8 : 7 ^ 25 ≡ 16 ^ 5 [MOD 29] := by
  norm_num [pow_succ, pow_zero]
  decide
theorem lean_workbook_2305_9 : 7 ^ 25 ≡ 16 ^ 5 [MOD 29] := by
  conv => lhs; rw [← Nat.mod_add_div 25 29]
theorem lean_workbook_2305_10 : 7 ^ 25 ≡ 16 ^ 5 [MOD 29] := by
  conv_lhs => rw [← pow_one 7]
theorem lean_workbook_2305_11 : 7 ^ 25 ≡ 16 ^ 5 [MOD 29] := by
  rw [Nat.modEq_iff_dvd]
  norm_num
theorem lean_workbook_2305_12 : 7 ^ 25 ≡ 16 ^ 5 [MOD 29] := by
  simp [Nat.ModEq]
theorem lean_workbook_2305_13 : 7 ^ 25 ≡ 16 ^ 5 [MOD 29] := by
  conv in 7 => norm_num
theorem lean_workbook_2305_14 : 7 ^ 25 ≡ 16 ^ 5 [MOD 29] := by
  norm_num [pow_succ, pow_mul, pow_one, Nat.ModEq]
theorem lean_workbook_2305_15 : 7 ^ 25 ≡ 16 ^ 5 [MOD 29] := by
  conv_lhs => norm_num
theorem lean_workbook_2305_16 : 7 ^ 25 ≡ 16 ^ 5 [MOD 29] := by
  simp [pow_add, pow_mul, pow_one, Nat.ModEq]
theorem lean_workbook_2305_17 : 7 ^ 25 ≡ 16 ^ 5 [MOD 29] := by
  rw [ModEq]
  norm_num
theorem lean_workbook_2305_18 : 7 ^ 25 ≡ 16 ^ 5 [MOD 29] := by
  conv => lhs; rw [← pow_one 7, ← pow_mul, mul_comm, pow_mul, pow_one]
theorem lean_workbook_2305_19 : 7 ^ 25 ≡ 16 ^ 5 [MOD 29] := by
  conv_lhs => rw [← Nat.mod_add_div 25 4]
theorem lean_workbook_2305_20 : 7 ^ 25 ≡ 16 ^ 5 [MOD 29] := by
  change 7 ^ 25 % 29 = 16 ^ 5 % 29
  simp [pow_mod]
theorem lean_workbook_2305_21 : 7 ^ 25 ≡ 16 ^ 5 [MOD 29] := by
  norm_num [pow_succ, pow_zero, Nat.ModEq]
theorem lean_workbook_2305_22 : 7 ^ 25 ≡ 16 ^ 5 [MOD 29] := by
  change 7 ^ 25 % 29 = 16 ^ 5 % 29
  simp [Nat.pow_succ]
theorem lean_workbook_2305_23 : 7 ^ 25 ≡ 16 ^ 5 [MOD 29] := by
  calc 7 ^ 25 ≡ 16 ^ 5 [MOD 29] := by rfl
theorem lean_workbook_2305_24 : 7 ^ 25 ≡ 16 ^ 5 [MOD 29] := by
  simp [pow_mod, Nat.ModEq]
theorem lean_workbook_2305_25 : 7 ^ 25 ≡ 16 ^ 5 [MOD 29] := by
  norm_num [pow_succ, pow_zero, pow_one, pow_two, pow_three]
  decide

theorem lean_workbook_2306_0 : ∀ p q : Prop, p ∨ (p ∧ q) ↔ p := by
  refine' fun p q => ⟨fun h => _, fun hp => Or.inl hp⟩
  cases' h with h h
  exacts [h, h.1]
theorem lean_workbook_2306_1 : ∀ p q : Prop, p ∨ (p ∧ q) ↔ p := by
  intro p q
  constructor
  intro h
  cases' h with h h'
  exact h
  exact h'.1
  intro h
  left
  exact h
theorem lean_workbook_2306_2 : ∀ p q : Prop, p ∨ (p ∧ q) ↔ p := by
  intro p q
  constructor
  intro h
  cases h with
  | inl h => exact h
  | inr h => exact h.1
  exact fun h => Or.inl h
theorem lean_workbook_2306_3 : ∀ p q : Prop, p ∨ (p ∧ q) ↔ p := by
  exact fun p q => ⟨fun h => h.elim (fun hp => hp) (fun hpq => hpq.1), fun hp => Or.inl hp⟩
theorem lean_workbook_2306_4 : ∀ p q : Prop, p ∨ (p ∧ q) ↔ p := by
  simp (config := { contextual := true }) [or_comm, or_left_comm]
theorem lean_workbook_2306_5 : ∀ p q : Prop, p ∨ (p ∧ q) ↔ p := by
  refine' fun p q => ⟨fun h => _, fun h => Or.inl h⟩
  cases' h with h h'
  exact h
  exact h'.1
theorem lean_workbook_2306_6 : ∀ p q : Prop, p ∨ (p ∧ q) ↔ p := by
  exact fun p q ↦ ⟨fun h ↦ h.elim (fun hp ↦ hp) (fun hpq ↦ hpq.1), fun hp ↦ Or.inl hp⟩
theorem lean_workbook_2306_7 : ∀ p q : Prop, p ∨ (p ∧ q) ↔ p := by
  exact fun p q => ⟨fun h => h.elim (fun h => h) (fun h => h.1), fun h => Or.inl h⟩
theorem lean_workbook_2306_8 : ∀ p q : Prop, p ∨ (p ∧ q) ↔ p := by
  refine' fun p q => ⟨fun h => h.elim id And.left, fun h => Or.inl h⟩
theorem lean_workbook_2306_9 : ∀ p q : Prop, p ∨ (p ∧ q) ↔ p := by
  intro p q
  constructor
  intro h
  cases' h with hp hpq
  exact hp
  cases' hpq with hp hq
  exact hp
  intro hp
  left
  assumption
theorem lean_workbook_2306_10 : ∀ p q : Prop, p ∨ (p ∧ q) ↔ p := by
  intros p q
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]
theorem lean_workbook_2306_11 : ∀ p q : Prop, p ∨ (p ∧ q) ↔ p := by
  intro p q
  constructor
  intro h
  cases' h with hp hpq
  exact hp
  exact hpq.left
  intro h
  left
  exact h
theorem lean_workbook_2306_12 : ∀ p q : Prop, p ∨ (p ∧ q) ↔ p := by
  refine' fun p q => ⟨fun h => _, fun h => Or.inl h⟩
  cases h <;> aesop
theorem lean_workbook_2306_13 : ∀ p q : Prop, p ∨ (p ∧ q) ↔ p := by
  refine' fun p q => ⟨fun h => Or.elim h (fun hp => hp) (fun hpq => hpq.1), fun hp => Or.inl hp⟩
theorem lean_workbook_2306_14 : ∀ p q : Prop, p ∨ (p ∧ q) ↔ p := by
  intro p q
  constructor <;> intro h
  cases' h with hp hpq <;> [exact hp; exact hpq.left]
  exact Or.inl h
theorem lean_workbook_2306_15 : ∀ p q : Prop, p ∨ (p ∧ q) ↔ p := by
  exact fun p q => ⟨fun h => h.elim id And.left, fun h => Or.inl h⟩
theorem lean_workbook_2306_16 : ∀ p q : Prop, p ∨ (p ∧ q) ↔ p := by
  refine fun p q ↦ ⟨fun h ↦ h.elim (fun hp ↦ hp) (fun ⟨hp, _⟩ ↦ hp), fun hp ↦ Or.inl hp⟩
theorem lean_workbook_2306_17 : ∀ p q : Prop, p ∨ (p ∧ q) ↔ p := by
  intro p q
  constructor
  intro h
  cases' h with h h
  exact h
  cases' h with h h'
  exact h
  intro h
  left
  exact h
theorem lean_workbook_2306_18 : ∀ p q : Prop, p ∨ (p ∧ q) ↔ p := by
  intros p q
  constructor
  intro h
  cases h with
  | inl hp => exact hp
  | inr hpq => exact hpq.left
  intro hp
  left
  exact hp
theorem lean_workbook_2306_19 : ∀ p q : Prop, p ∨ (p ∧ q) ↔ p := by
  exact fun p q => ⟨fun h => h.elim (fun hp => hp) (fun hpq => hpq.left), fun hp => Or.inl hp⟩
theorem lean_workbook_2306_20 : ∀ p q : Prop, p ∨ (p ∧ q) ↔ p := by
  intros p q
  by_cases h : p <;> by_cases h' : q <;> simp [h, h']
theorem lean_workbook_2306_21 : ∀ p q : Prop, p ∨ (p ∧ q) ↔ p := by
  intro p q
  by_cases p <;> simp [*]
theorem lean_workbook_2306_22 : ∀ p q : Prop, p ∨ (p ∧ q) ↔ p := by
  refine' fun p q => ⟨_, fun hp => Or.inl hp⟩
  exact fun h => h.elim (fun hp => hp) fun hpq => hpq.1
theorem lean_workbook_2306_23 : ∀ p q : Prop, p ∨ (p ∧ q) ↔ p := by
  intro p q
  constructor
  intro h
  cases h with
  | inl h => exact h
  | inr h => exact h.1
  intro h
  left
  exact h
theorem lean_workbook_2306_24 : ∀ p q : Prop, p ∨ (p ∧ q) ↔ p := by
  refine' fun p q => ⟨fun h => _, fun h => Or.inl h⟩
  cases h <;> simp_all
theorem lean_workbook_2306_25 : ∀ p q : Prop, p ∨ (p ∧ q) ↔ p := by
  refine' fun p q => ⟨fun h => Or.elim h (fun hp => hp) (fun h => h.1), fun hp => Or.inl hp⟩

theorem lean_workbook_2312_0 (x : ℝ) : x - x^2 ≤ 1/4 := by
  rw [← sub_nonneg]
  have := sq_nonneg (x - 1/2)
  nlinarith
theorem lean_workbook_2312_1 (x : ℝ) : x - x^2 ≤ 1/4 := by
  have : (x - 1/2)^2 ≥ 0 := sq_nonneg (x - 1/2)
  linarith [sq_nonneg (x - 1/2)]
theorem lean_workbook_2312_2 (x : ℝ) : x - x^2 ≤ 1/4 := by
  have := pow_two_nonneg (x - 1/2)
  nlinarith
theorem lean_workbook_2312_3 (x : ℝ) : x - x^2 ≤ 1/4 := by
  field_simp [sq]
  rw [← sub_nonneg]
  nlinarith [sq_nonneg (x - 1/2)]
theorem lean_workbook_2312_4 (x : ℝ) : x - x^2 ≤ 1/4 := by
  simp only [sq, sub_le_iff_le_add]
  nlinarith [sq_nonneg (x - 1/2)]
theorem lean_workbook_2312_5 (x : ℝ) : x - x^2 ≤ 1/4 := by
  ring_nf
  nlinarith [sq_nonneg (x - 1/2)]
theorem lean_workbook_2312_6 (x : ℝ) : x - x^2 ≤ 1/4 := by
  ring_nf
  have h : 0 ≤ (x - 1/2)^2 := sq_nonneg (x - 1/2)
  linarith
theorem lean_workbook_2312_7 (x : ℝ) : x - x^2 ≤ 1/4 := by
  have : 0 ≤ (x - 1/2)^2 := sq_nonneg (x - 1/2)
  linarith
theorem lean_workbook_2312_8 (x : ℝ) : x - x^2 ≤ 1/4 := by
  ring_nf
  have h1 : 0 ≤ (x - 1/2)^2 := sq_nonneg (x - 1/2)
  linarith
theorem lean_workbook_2312_9 (x : ℝ) : x - x^2 ≤ 1/4 := by
  field_simp [sub_eq_add_neg]
  nlinarith [sq_nonneg (x - 1/2)]
theorem lean_workbook_2312_10 (x : ℝ) : x - x^2 ≤ 1/4 := by
  have h : 0 ≤ (x - 1/2)^2 := sq_nonneg (x - 1/2)
  nlinarith
theorem lean_workbook_2312_11 (x : ℝ) : x - x^2 ≤ 1/4 := by
  have key : 0 ≤ (x - 1/2)^2 := sq_nonneg (x - 1/2)
  linarith [key]
theorem lean_workbook_2312_12 (x : ℝ) : x - x^2 ≤ 1/4 := by
  have inequality_1 : 0 ≤ (x - 1/2)^2 := sq_nonneg (x - 1/2)
  linarith [inequality_1]
theorem lean_workbook_2312_13 (x : ℝ) : x - x^2 ≤ 1/4 := by
  have : (x - 1/2)^2 ≥ 0 := sq_nonneg (x - 1/2)
  linarith
theorem lean_workbook_2312_14 (x : ℝ) : x - x^2 ≤ 1/4 := by
  have := pow_two_nonneg (x - 1/2)
  linarith [sq_nonneg (x - 1/2)]
theorem lean_workbook_2312_15 (x : ℝ) : x - x^2 ≤ 1/4 := by
  rw [sub_le_iff_le_add]
  have := sq_nonneg (x - 1/2)
  linarith
theorem lean_workbook_2312_16 (x : ℝ) : x - x^2 ≤ 1/4 := by
  simp only [sub_le_iff_le_add]
  have := sq_nonneg (x - 1/2)
  linarith [sq_nonneg (x - 1/2)]
theorem lean_workbook_2312_17 (x : ℝ) : x - x^2 ≤ 1/4 := by
  have key : (x - 1/2)^2 ≥ 0 := sq_nonneg (x - 1/2)
  nlinarith [key]
theorem lean_workbook_2312_18 (x : ℝ) : x - x^2 ≤ 1/4 := by
  field_simp [sq]
  nlinarith [sq_nonneg (x - 1/2)]
theorem lean_workbook_2312_19 (x : ℝ) : x - x^2 ≤ 1/4 := by
  ring_nf
  have h1 : 0 ≤ (x - 1/2)^2 := sq_nonneg (x - 1/2)
  linarith [h1]
theorem lean_workbook_2312_20 (x : ℝ) : x - x^2 ≤ 1/4 := by
  field_simp [sq]
  nlinarith [sq_nonneg (2 * x - 1)]
theorem lean_workbook_2312_21 (x : ℝ) : x - x^2 ≤ 1/4 := by
  have h1 : 0 ≤ (x - 1/2)^2 := sq_nonneg (x - 1/2)
  linarith
theorem lean_workbook_2312_22 (x : ℝ) : x - x^2 ≤ 1/4 := by
  have h1 : 0 ≤ (2 * x - 1)^2 := sq_nonneg (2 * x - 1)
  nlinarith
theorem lean_workbook_2312_23 (x : ℝ) : x - x^2 ≤ 1/4 := by
  field_simp [sq]
  nlinarith only [sq_nonneg (x - 1/2)]
theorem lean_workbook_2312_24 (x : ℝ) : x - x^2 ≤ 1/4 := by
  have := sq_nonneg (x - 1/2)
  linarith [sq_nonneg (x - 1/2)]
theorem lean_workbook_2312_25 (x : ℝ) : x - x^2 ≤ 1/4 := by
  rw [←sub_nonneg]
  have := sq_nonneg (x - 1/2)
  nlinarith
theorem lean_workbook_2312_26 (x : ℝ) : x - x^2 ≤ 1/4 := by
  rw [sub_le_iff_le_add]
  nlinarith [sq_nonneg (x - 1/2)]
theorem lean_workbook_2312_27 (x : ℝ) : x - x^2 ≤ 1/4 := by
  have h : 0 ≤ (x - 1/2)^2 := sq_nonneg (x - 1/2)
  linarith [h]

theorem lean_workbook_2317_0 (a b c : ℝ) (hab : a > 0 ∧ b > 0 ∧ c > 0) (h : a + b + c = 0) : Real.cos b + Real.cos c = (2 * a * (Real.cos ((b - c) / 2))^2) / (b + c) := by
  exfalso
  linarith [h, hab.1, hab.2.1, hab.2.2]
theorem lean_workbook_2317_1 (a b c : ℝ) (hab : a > 0 ∧ b > 0 ∧ c > 0) (h : a + b + c = 0) : Real.cos b + Real.cos c = (2 * a * (Real.cos ((b - c) / 2))^2) / (b + c) := by
  field_simp [cos_add, cos_sub, mul_comm, mul_assoc, mul_left_comm]
  ring_nf
  linarith [h, hab.1, hab.2.1, hab.2.2]
theorem lean_workbook_2317_2 (a b c : ℝ) (hab : a > 0 ∧ b > 0 ∧ c > 0) (h : a + b + c = 0) : Real.cos b + Real.cos c = (2 * a * (Real.cos ((b - c) / 2))^2) / (b + c) := by
  field_simp [cos_sub, cos_add, mul_assoc, mul_comm, mul_left_comm]
  linarith [h, hab.1, hab.2.1, hab.2.2]
theorem lean_workbook_2317_3 (a b c : ℝ) (hab : a > 0 ∧ b > 0 ∧ c > 0) (h : a + b + c = 0) : Real.cos b + Real.cos c = (2 * a * (Real.cos ((b - c) / 2))^2) / (b + c) := by
  exfalso
  linarith [hab.1, hab.2.1, hab.2.2]
theorem lean_workbook_2317_4 (a b c : ℝ) (hab : a > 0 ∧ b > 0 ∧ c > 0) (h : a + b + c = 0) : Real.cos b + Real.cos c = (2 * a * (Real.cos ((b - c) / 2))^2) / (b + c) := by
  exfalso
  linarith [hab.2.1, hab.2.2, h]
theorem lean_workbook_2317_5 (a b c : ℝ) (hab : a > 0 ∧ b > 0 ∧ c > 0) (h : a + b + c = 0) : Real.cos b + Real.cos c = (2 * a * (Real.cos ((b - c) / 2))^2) / (b + c) := by
  exfalso
  linarith [hab.1, hab.2.1, hab.2.2, h]

theorem lean_workbook_2349_0 : ∀ a b : ℝ, 6 * (a ^ 2 + b ^ 2) ^ 2 + (a + b) ^ 4 ≥ 5 * (a ^ 2 + b ^ 2) * (a + b) ^ 2 := by
  intros a b
  simp [pow_two]
  nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
theorem lean_workbook_2349_1 : ∀ a b : ℝ, 6 * (a ^ 2 + b ^ 2) ^ 2 + (a + b) ^ 4 ≥ 5 * (a ^ 2 + b ^ 2) * (a + b) ^ 2 := by
  intro a b
  simp [sq, add_assoc, add_comm, add_left_comm]
  nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
theorem lean_workbook_2349_2 : ∀ a b : ℝ, 6 * (a ^ 2 + b ^ 2) ^ 2 + (a + b) ^ 4 ≥ 5 * (a ^ 2 + b ^ 2) * (a + b) ^ 2 := by
  intro a b
  nlinarith [sq_nonneg (a - b), sq_nonneg (2 * a + 2 * b)]
theorem lean_workbook_2349_3 : ∀ a b : ℝ, 6 * (a ^ 2 + b ^ 2) ^ 2 + (a + b) ^ 4 ≥ 5 * (a ^ 2 + b ^ 2) * (a + b) ^ 2 := by
  intro a b
  field_simp [add_comm]
  nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
theorem lean_workbook_2349_4 : ∀ a b : ℝ, 6 * (a ^ 2 + b ^ 2) ^ 2 + (a + b) ^ 4 ≥ 5 * (a ^ 2 + b ^ 2) * (a + b) ^ 2 := by
  intro a b
  simp [add_comm]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
theorem lean_workbook_2349_5 : ∀ a b : ℝ, 6 * (a ^ 2 + b ^ 2) ^ 2 + (a + b) ^ 4 ≥ 5 * (a ^ 2 + b ^ 2) * (a + b) ^ 2 := by
  intro a b
  nlinarith [pow_two_nonneg (a + b), pow_two_nonneg (a - b)]
theorem lean_workbook_2349_6 : ∀ a b : ℝ, 6 * (a ^ 2 + b ^ 2) ^ 2 + (a + b) ^ 4 ≥ 5 * (a ^ 2 + b ^ 2) * (a + b) ^ 2 := by
  intro a b
  simp [add_comm]
  nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
theorem lean_workbook_2349_7 : ∀ a b : ℝ, 6 * (a ^ 2 + b ^ 2) ^ 2 + (a + b) ^ 4 ≥ 5 * (a ^ 2 + b ^ 2) * (a + b) ^ 2 := by
  intro a b
  simp [pow_two]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
theorem lean_workbook_2349_8 : ∀ a b : ℝ, 6 * (a ^ 2 + b ^ 2) ^ 2 + (a + b) ^ 4 ≥ 5 * (a ^ 2 + b ^ 2) * (a + b) ^ 2 := by
  intro a b
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
theorem lean_workbook_2349_9 : ∀ a b : ℝ, 6 * (a ^ 2 + b ^ 2) ^ 2 + (a + b) ^ 4 ≥ 5 * (a ^ 2 + b ^ 2) * (a + b) ^ 2 := by
  intro a b
  nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
theorem lean_workbook_2349_10 : ∀ a b : ℝ, 6 * (a ^ 2 + b ^ 2) ^ 2 + (a + b) ^ 4 ≥ 5 * (a ^ 2 + b ^ 2) * (a + b) ^ 2 := by
  refine' fun a b => _
  ring_nf
  nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
theorem lean_workbook_2349_11 : ∀ a b : ℝ, 6 * (a ^ 2 + b ^ 2) ^ 2 + (a + b) ^ 4 ≥ 5 * (a ^ 2 + b ^ 2) * (a + b) ^ 2 := by
  intro a b
  have h1 : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  nlinarith
theorem lean_workbook_2349_12 : ∀ a b : ℝ, 6 * (a ^ 2 + b ^ 2) ^ 2 + (a + b) ^ 4 ≥ 5 * (a ^ 2 + b ^ 2) * (a + b) ^ 2 := by
  intros a b
  simp [sq]
  nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
theorem lean_workbook_2349_13 : ∀ a b : ℝ, 6 * (a ^ 2 + b ^ 2) ^ 2 + (a + b) ^ 4 ≥ 5 * (a ^ 2 + b ^ 2) * (a + b) ^ 2 := by
  intro a b
  ring_nf
  nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
theorem lean_workbook_2349_14 : ∀ a b : ℝ, 6 * (a ^ 2 + b ^ 2) ^ 2 + (a + b) ^ 4 ≥ 5 * (a ^ 2 + b ^ 2) * (a + b) ^ 2 := by
  intro a b
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (2 * a * b)]

theorem lean_workbook_2359_0 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  refine' div_nonneg (mul_nonneg _ (sq_nonneg _)) (le_of_lt hx)
  nlinarith [hx]
theorem lean_workbook_2359_1 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  apply div_nonneg <;> positivity
theorem lean_workbook_2359_2 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  refine' div_nonneg (mul_nonneg _ (sq_nonneg (Real.sqrt x - 1))) (le_of_lt hx)
  exact add_nonneg (le_of_lt hx) (le_of_lt zero_lt_one)
theorem lean_workbook_2359_3 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  refine' div_nonneg (mul_nonneg _ (sq_nonneg _)) (by linarith)
  linarith [Real.sqrt_nonneg x]
theorem lean_workbook_2359_4 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  apply div_nonneg
  apply mul_nonneg
  exact le_of_lt (add_pos hx zero_lt_one)
  apply pow_two_nonneg
  exact le_of_lt hx
theorem lean_workbook_2359_5 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  rw [ge_iff_le]
  refine' div_nonneg (mul_nonneg (add_nonneg hx.le zero_le_one) (sq_nonneg _)) _
  exact hx.le
theorem lean_workbook_2359_6 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  refine' div_nonneg _ (le_of_lt hx)
  nlinarith [hx, (sqrt_nonneg x)]
theorem lean_workbook_2359_7 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  apply div_nonneg
  nlinarith
  nlinarith [Real.sqrt_nonneg x]
theorem lean_workbook_2359_8 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  have h1 : 0 ≤ (Real.sqrt x - 1) ^ 2 := sq_nonneg (Real.sqrt x - 1)
  apply div_nonneg <;> nlinarith
theorem lean_workbook_2359_9 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  refine' div_nonneg (mul_nonneg _ (sq_nonneg _)) (by linarith)
  nlinarith
theorem lean_workbook_2359_10 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  field_simp [pow_two]
  exact div_nonneg (mul_nonneg (by linarith) (by nlinarith)) (by linarith)
theorem lean_workbook_2359_11 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  refine' div_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (by positivity)
theorem lean_workbook_2359_12 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  apply div_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (by positivity)
theorem lean_workbook_2359_13 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  apply div_nonneg (mul_nonneg _ (sq_nonneg _)) (le_of_lt hx)
  nlinarith
theorem lean_workbook_2359_14 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  apply div_nonneg
  nlinarith [sq_nonneg (Real.sqrt x - 1)]
  nlinarith [sq_nonneg (Real.sqrt x - 1)]
theorem lean_workbook_2359_15 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  refine' div_nonneg (mul_nonneg _ (sq_nonneg _)) (le_of_lt hx)
  linarith [sq_nonneg (Real.sqrt x - 1)]
theorem lean_workbook_2359_16 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  apply div_nonneg
  exact mul_nonneg (by positivity) (sq_nonneg _)
  positivity
theorem lean_workbook_2359_17 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  field_simp [sq]
  exact div_nonneg (mul_nonneg (by linarith) (mul_self_nonneg _)) (by linarith)
theorem lean_workbook_2359_18 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  refine' div_nonneg _ (le_of_lt hx)
  nlinarith [sq_nonneg (Real.sqrt x - 1)]
theorem lean_workbook_2359_19 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  have : (Real.sqrt x - 1) ^ 2 ≥ 0 := sq_nonneg (Real.sqrt x - 1)
  field_simp [hx.ne']
  exact div_nonneg (mul_nonneg (by positivity) this) (by positivity)
theorem lean_workbook_2359_20 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  apply div_nonneg
  nlinarith [sqrt_nonneg x]
  nlinarith [sqrt_nonneg x]
theorem lean_workbook_2359_21 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  apply div_nonneg
  apply mul_nonneg
  exact le_of_lt (by linarith)
  apply pow_two_nonneg
  exact le_of_lt hx
theorem lean_workbook_2359_22 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  refine' div_nonneg (mul_nonneg _ (sq_nonneg _)) (le_of_lt hx)
  linarith
theorem lean_workbook_2359_23 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  rw [ge_iff_le]
  apply div_nonneg
  apply mul_nonneg
  exact le_of_lt (add_pos hx zero_lt_one)
  apply sq_nonneg
  exact le_of_lt hx
theorem lean_workbook_2359_24 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  rw [ge_iff_le]
  refine' div_nonneg (mul_nonneg _ (sq_nonneg _)) (le_of_lt hx)
  linarith [sq_nonneg (Real.sqrt x - 1)]
theorem lean_workbook_2359_25 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  apply div_nonneg
  apply mul_nonneg
  nlinarith
  apply pow_two_nonneg
  nlinarith
theorem lean_workbook_2359_26 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  have : 0 ≤ (Real.sqrt x - 1) ^ 2 := sq_nonneg (Real.sqrt x - 1)
  apply div_nonneg <;> nlinarith [hx]
theorem lean_workbook_2359_27 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  refine' div_nonneg (mul_nonneg _ (sq_nonneg _)) (le_of_lt hx)
  nlinarith
theorem lean_workbook_2359_28 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  apply div_nonneg
  apply mul_nonneg
  linarith
  nlinarith
  linarith
theorem lean_workbook_2359_29 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  apply div_nonneg <;> nlinarith [Real.sqrt_nonneg x]

theorem lean_workbook_2363_0 (x y : ℝ) : (x ^ 2 + (x * y) + y ^ 2) * (4 / 3) ≥ (x + y) ^ 2 := by
  have h₁ := sq_nonneg (x - y)
  linarith
theorem lean_workbook_2363_1 (x y : ℝ) : (x ^ 2 + (x * y) + y ^ 2) * (4 / 3) ≥ (x + y) ^ 2 := by
  have := sq_nonneg (x - y)
  linarith [sq_nonneg (x - y)]
theorem lean_workbook_2363_2 (x y : ℝ) : (x ^ 2 + (x * y) + y ^ 2) * (4 / 3) ≥ (x + y) ^ 2 := by
  nlinarith [sq_nonneg (x - y)]
theorem lean_workbook_2363_3 (x y : ℝ) : (x ^ 2 + (x * y) + y ^ 2) * (4 / 3) ≥ (x + y) ^ 2 := by
  have := sq_nonneg (x - y)
  linarith
theorem lean_workbook_2363_4 (x y : ℝ) : (x ^ 2 + (x * y) + y ^ 2) * (4 / 3) ≥ (x + y) ^ 2 := by
  ring_nf
  have h1 : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
  linarith [h1]
theorem lean_workbook_2363_5 (x y : ℝ) : (x ^ 2 + (x * y) + y ^ 2) * (4 / 3) ≥ (x + y) ^ 2 := by
  field_simp [add_comm]
  ring_nf
  nlinarith [sq_nonneg (x - y)]
theorem lean_workbook_2363_6 (x y : ℝ) : (x ^ 2 + (x * y) + y ^ 2) * (4 / 3) ≥ (x + y) ^ 2 := by
  have l2 : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
  linarith
theorem lean_workbook_2363_7 (x y : ℝ) : (x ^ 2 + (x * y) + y ^ 2) * (4 / 3) ≥ (x + y) ^ 2 := by
  ring_nf
  have := sq_nonneg (x - y)
  linarith
theorem lean_workbook_2363_8 (x y : ℝ) : (x ^ 2 + (x * y) + y ^ 2) * (4 / 3) ≥ (x + y) ^ 2 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
theorem lean_workbook_2363_9 (x y : ℝ) : (x ^ 2 + (x * y) + y ^ 2) * (4 / 3) ≥ (x + y) ^ 2 := by
  have h1 : (x - y) ^ 2 ≥ 0 := sq_nonneg (x - y)
  linarith
theorem lean_workbook_2363_10 (x y : ℝ) : (x ^ 2 + (x * y) + y ^ 2) * (4 / 3) ≥ (x + y) ^ 2 := by
  have h1 : (x - y) ^ 2 ≥ 0 := sq_nonneg (x - y)
  linarith [h1]
theorem lean_workbook_2363_11 (x y : ℝ) : (x ^ 2 + (x * y) + y ^ 2) * (4 / 3) ≥ (x + y) ^ 2 := by
  linarith [sq_nonneg (x - y)]
theorem lean_workbook_2363_12 (x y : ℝ) : (x ^ 2 + (x * y) + y ^ 2) * (4 / 3) ≥ (x + y) ^ 2 := by
  have h1 := sq_nonneg (x - y)
  linarith
theorem lean_workbook_2363_13 (x y : ℝ) : (x ^ 2 + (x * y) + y ^ 2) * (4 / 3) ≥ (x + y) ^ 2 := by
  simp [sq]
  nlinarith [sq_nonneg (x - y)]
theorem lean_workbook_2363_14 (x y : ℝ) : (x ^ 2 + (x * y) + y ^ 2) * (4 / 3) ≥ (x + y) ^ 2 := by
  have : (x - y) ^ 2 ≥ 0 := sq_nonneg (x - y)
  linarith
theorem lean_workbook_2363_15 (x y : ℝ) : (x ^ 2 + (x * y) + y ^ 2) * (4 / 3) ≥ (x + y) ^ 2 := by
  field_simp [sq]
  nlinarith [sq_nonneg (x - y)]
theorem lean_workbook_2363_16 (x y : ℝ) : (x ^ 2 + (x * y) + y ^ 2) * (4 / 3) ≥ (x + y) ^ 2 := by
  have : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
  linarith [sq_nonneg (x - y)]
theorem lean_workbook_2363_17 (x y : ℝ) : (x ^ 2 + (x * y) + y ^ 2) * (4 / 3) ≥ (x + y) ^ 2 := by
  have : (x - y) ^ 2 ≥ 0 := sq_nonneg (x - y)
  linarith [sq_nonneg (x - y)]
theorem lean_workbook_2363_18 (x y : ℝ) : (x ^ 2 + (x * y) + y ^ 2) * (4 / 3) ≥ (x + y) ^ 2 := by
  have h1 : (x - y) ^ 2 ≥ 0 := sq_nonneg (x - y)
  rw [sq] at h1
  linarith
theorem lean_workbook_2363_19 (x y : ℝ) : (x ^ 2 + (x * y) + y ^ 2) * (4 / 3) ≥ (x + y) ^ 2 := by
  have h2 : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
  linarith [h2]
theorem lean_workbook_2363_20 (x y : ℝ) : (x ^ 2 + (x * y) + y ^ 2) * (4 / 3) ≥ (x + y) ^ 2 := by
  have h1 : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
  linarith only [h1]
theorem lean_workbook_2363_21 (x y : ℝ) : (x ^ 2 + (x * y) + y ^ 2) * (4 / 3) ≥ (x + y) ^ 2 := by
  have h : (x - y) ^ 2 ≥ 0 := sq_nonneg (x - y)
  linarith
theorem lean_workbook_2363_22 (x y : ℝ) : (x ^ 2 + (x * y) + y ^ 2) * (4 / 3) ≥ (x + y) ^ 2 := by
  have h₁ : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
  linarith [h₁]

theorem lean_workbook_2365_0 (a b c : ℝ) : a ^ 2 + b ^ 2 + c ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 * c ^ 2) ^ (1 / 3) ↔ a ^ 2 + b ^ 2 + c ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 * c ^ 2) ^ (1 / 3) := by
  simp [pow_one]
theorem lean_workbook_2365_1 (a b c : ℝ) : a ^ 2 + b ^ 2 + c ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 * c ^ 2) ^ (1 / 3) ↔ a ^ 2 + b ^ 2 + c ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 * c ^ 2) ^ (1 / 3) := by
  rw [ge_iff_le]
theorem lean_workbook_2365_2 (a b c : ℝ) : a ^ 2 + b ^ 2 + c ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 * c ^ 2) ^ (1 / 3) ↔ a ^ 2 + b ^ 2 + c ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 * c ^ 2) ^ (1 / 3) := by
  norm_cast at *
theorem lean_workbook_2365_3 (a b c : ℝ) : a ^ 2 + b ^ 2 + c ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 * c ^ 2) ^ (1 / 3) ↔ a ^ 2 + b ^ 2 + c ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 * c ^ 2) ^ (1 / 3) := by
  simp only [ge_iff_le, eq_iff_true_of_subsingleton]
theorem lean_workbook_2365_4 (a b c : ℝ) : a ^ 2 + b ^ 2 + c ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 * c ^ 2) ^ (1 / 3) ↔ a ^ 2 + b ^ 2 + c ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 * c ^ 2) ^ (1 / 3) := by
  simp [sq, mul_assoc]
theorem lean_workbook_2365_5 (a b c : ℝ) : a ^ 2 + b ^ 2 + c ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 * c ^ 2) ^ (1 / 3) ↔ a ^ 2 + b ^ 2 + c ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 * c ^ 2) ^ (1 / 3) := by
  refine' ⟨fun h => h, fun h => h⟩
theorem lean_workbook_2365_6 (a b c : ℝ) : a ^ 2 + b ^ 2 + c ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 * c ^ 2) ^ (1 / 3) ↔ a ^ 2 + b ^ 2 + c ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 * c ^ 2) ^ (1 / 3) := by
  rw [mul_comm]
theorem lean_workbook_2365_7 (a b c : ℝ) : a ^ 2 + b ^ 2 + c ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 * c ^ 2) ^ (1 / 3) ↔ a ^ 2 + b ^ 2 + c ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 * c ^ 2) ^ (1 / 3) := by
  simp only [ge_iff_le, le_refl, forall_true_left]
theorem lean_workbook_2365_8 (a b c : ℝ) : a ^ 2 + b ^ 2 + c ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 * c ^ 2) ^ (1 / 3) ↔ a ^ 2 + b ^ 2 + c ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 * c ^ 2) ^ (1 / 3) := by
  refine' ⟨fun h => _, fun h => _⟩ <;> linarith
theorem lean_workbook_2365_9 (a b c : ℝ) : a ^ 2 + b ^ 2 + c ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 * c ^ 2) ^ (1 / 3) ↔ a ^ 2 + b ^ 2 + c ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 * c ^ 2) ^ (1 / 3) := by
  simp only [ge_iff_le, le_refl, true_and]
theorem lean_workbook_2365_10 (a b c : ℝ) : a ^ 2 + b ^ 2 + c ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 * c ^ 2) ^ (1 / 3) ↔ a ^ 2 + b ^ 2 + c ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 * c ^ 2) ^ (1 / 3) := by
  refine' ⟨fun h => _, fun h => _⟩
  assumption'
