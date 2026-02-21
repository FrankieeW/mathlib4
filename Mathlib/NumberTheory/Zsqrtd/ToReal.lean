/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Data.Real.Sqrt
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.NumberTheory.Zsqrtd.Basic

/-!
# Image of `Zsqrtd` in `ℝ`

This file defines `Zsqrtd.toReal` and related lemmas.
It is in a separate file to avoid pulling in all of `Data.Real` into `Data.Zsqrtd`.
-/

@[expose] public section


namespace Zsqrtd

/-- The image of `Zsqrtd` in `ℝ`, using `Real.sqrt` which takes the positive root of `d`.

If the negative root is desired, use `toReal h (star a)`. -/
@[simps!]
noncomputable def toReal {d : ℤ} (h : 0 ≤ d) : ℤ√d →+* ℝ :=
  lift ⟨√↑d, Real.mul_self_sqrt (Int.cast_nonneg h)⟩

theorem toReal_injective {d : ℤ} (h0d : 0 ≤ d) (hd : ∀ n : ℤ, d ≠ n * n) :
    Function.Injective (toReal h0d) :=
  lift_injective _ hd

section

variable {d : ℕ} [Nonsquare d]

private lemma sqLe_y_sqrt_le_x {x y d : ℕ} (h : SqLe y d x 1) :
    (y : ℝ) * Real.sqrt d ≤ x := by
  have hy : (0 : ℝ) ≤ y := by exact_mod_cast Nat.zero_le y
  have hd : (0 : ℝ) ≤ d := by exact_mod_cast Nat.zero_le d
  have hcast : (d : ℝ) * y * y ≤ x * x := by
    have h' : d * y * y ≤ x * x := by simpa [SqLe] using h
    exact_mod_cast h'
  have hsq : ((y : ℝ) * Real.sqrt d)^2 ≤ (x : ℝ)^2 := by
    calc
      ((y : ℝ) * Real.sqrt d)^2 = (d : ℝ) * y * y := by
        ring_nf
        rw [Real.sq_sqrt hd]
      _ ≤ x * x := hcast
      _ = (x : ℝ)^2 := by ring
  have hx : (0 : ℝ) ≤ x := by exact_mod_cast Nat.zero_le x
  have hy' : (0 : ℝ) ≤ (y : ℝ) * Real.sqrt d := mul_nonneg hy (Real.sqrt_nonneg _)
  nlinarith [hsq, hx, hy']

private lemma sqLe_x_le_y_sqrt {x y d : ℕ} (h : SqLe x 1 y d) :
    (x : ℝ) ≤ (y : ℝ) * Real.sqrt d := by
  have hy : (0 : ℝ) ≤ y := by exact_mod_cast Nat.zero_le y
  have hd : (0 : ℝ) ≤ d := by exact_mod_cast Nat.zero_le d
  have hx : (0 : ℝ) ≤ x := by exact_mod_cast Nat.zero_le x
  have hcast : (x : ℝ) * x ≤ (d : ℝ) * y * y := by
    have h' : x * x ≤ d * y * y := by simpa [SqLe] using h
    exact_mod_cast h'
  have hsq : (x : ℝ)^2 ≤ ((y : ℝ) * Real.sqrt d)^2 := by
    calc
      (x : ℝ)^2 = x * x := by ring
      _ ≤ (d : ℝ) * y * y := hcast
      _ = ((y : ℝ) * Real.sqrt d)^2 := by
        ring_nf
        rw [Real.sq_sqrt hd]
        ring
  have hy' : (0 : ℝ) ≤ (y : ℝ) * Real.sqrt d := mul_nonneg hy (Real.sqrt_nonneg _)
  nlinarith [hsq, hx, hy']

omit [Nonsquare d] in
private lemma toReal_nonneg_nat {a : ℤ√d} (ha : 0 ≤ a) :
    0 ≤ toReal (d := (d : ℤ)) (by exact_mod_cast Nat.zero_le d) a := by
  have ha' := ha
  change Nonneg (a - 0) at ha'
  have ha0 : Nonneg a := by simpa using ha'
  rcases nonneg_cases (d := d) ha0 with ⟨x, y, hxy⟩
  rcases hxy with rfl | rfl | rfl
  · have hx : (0 : ℝ) ≤ x := by exact_mod_cast Nat.zero_le x
    have hy : (0 : ℝ) ≤ y := by exact_mod_cast Nat.zero_le y
    exact add_nonneg hx (mul_nonneg hy (Real.sqrt_nonneg _))
  · have hnonnegg : Nonnegg d 1 x (-y) := by simpa [Nonneg] using ha'
    have hsq : SqLe y d x 1 := (nonnegg_pos_neg (c := d) (d := 1) (a := x) (b := y)).1 hnonnegg
    have hxy' : (y : ℝ) * Real.sqrt d ≤ x := sqLe_y_sqrt_le_x hsq
    have : 0 ≤ (x : ℝ) - (y : ℝ) * Real.sqrt d := sub_nonneg.mpr hxy'
    simpa [toReal, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using this
  · have hnonnegg : Nonnegg d 1 (-x) y := by simpa [Nonneg] using ha'
    have hsq : SqLe x 1 y d := (nonnegg_neg_pos (c := d) (d := 1) (a := x) (b := y)).1 hnonnegg
    have hxy' : (x : ℝ) ≤ (y : ℝ) * Real.sqrt d := sqLe_x_le_y_sqrt hsq
    have : 0 ≤ (y : ℝ) * Real.sqrt d - x := sub_nonneg.mpr hxy'
    simpa [toReal, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm,
      add_comm] using this

instance : Archimedean (ℤ√d) :=
  let h0 : (0 : ℤ) ≤ d := by exact_mod_cast Nat.zero_le d
  let hd : ∀ n : ℤ, (d : ℤ) ≠ n * n := by
    intro n hsq
    have hsq' : (d : ℤ) = (n.natAbs : ℤ) * n.natAbs := by
      simpa [Int.natAbs_mul_self] using hsq
    have hnat : d = n.natAbs * n.natAbs := by
      exact_mod_cast hsq'
    exact Nonsquare.ns d n.natAbs hnat
  let f := toReal (d := (d : ℤ)) h0
  have hmono : Monotone f := by
    intro a b hab
    have hba : 0 ≤ f (b - a) := toReal_nonneg_nat (d := d) (a := b - a) (sub_nonneg.mpr hab)
    have : 0 ≤ f b - f a := by simpa [map_sub] using hba
    exact sub_nonneg.mp this
  Archimedean.comap f.toAddMonoidHom (hmono.strictMono_of_injective (toReal_injective h0 hd))

end

end Zsqrtd
