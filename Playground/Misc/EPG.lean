import Mathlib.Init.Set
import Playground.Data.GeneralDotNotation

class Euclidean_Plane_Data (point : Type) where
  has_same_length_as : point × point → point × point → Prop
  is_between : point → point × point → Prop
  p1 : point
  p2 : point
  p3 : point

open Euclidean_Plane_Data in
class Euclidean_Plane_Axioms (point : Type) [Euclidean_Plane_Data point] where
  congr_sym : ∀ x y : point, (x, y)·has_same_length_as (y, x)
  congr_id : ∀ {x y z : point}, (x, y)·has_same_length_as (z, z) → x = y
  congr_trans : ∀ {x₁ y₁ x₂ y₂ x₃ y₃ : point}, (x₁, y₁)·has_same_length_as (x₂, y₂)
    → (x₁, y₁)·has_same_length_as (x₃, y₃)
    → (x₂, y₂)·has_same_length_as (x₃, y₃)
  between_id : ∀ {x y : point}, y·is_between (x, x) → x = y
  pasch_axiom : ∀ x y u v : point, Σ' a, a·is_between (u, y) ∧ a·is_between (v, x)
  continuity_schema {X Y : point·Set} :
    (∃ a, ∀ x ∈ X, ∀ y ∈ Y, x·is_between (a, y)) 
    → (∃ b, ∀ x ∈ X, ∀ y ∈ Y, b·is_between (x, y))
  lower_dim : ¬(p2 : point)·is_between (p1, p3)
    ∧ ¬(p3 : point)·is_between (p2, p1) ∧ ¬(p1 : point)·is_between (p3, p2)
  upper_dim : ∀ {x y z u v : point}, u ≠ v
    ∧ (x, u)·has_same_length_as (x, v)
    ∧ (y, u)·has_same_length_as (y, v)
    ∧ (z, u)·has_same_length_as (z, v)
    → y·is_between (x, z) ∨ z·is_between (y, x) ∨ x·is_between (z, y)
  euclid : ∀ {x y z u v w : point},
    ((y·is_between (x, w) ∧ (x, y)·has_same_length_as (y, w)) 
    ∧ (u·is_between (x, v) ∧ (x, u)·has_same_length_as (u, v)) 
    ∧ (u·is_between (y, z) ∧ (y, u)·has_same_length_as (u, z)))
    → (y, z)·has_same_length_as (v, w)
  five_seg : ∀ {x y z x' y' z' u u' : point},
    (x ≠ y ∧ y·is_between (x, z) ∧ y'·is_between (x', z')
    ∧ (x, y)·has_same_length_as (x', y') ∧ (y, z)·has_same_length_as (y', z')
    ∧ (x, u)·has_same_length_as (x', u') ∧ (y, u)·has_same_length_as (y', u')
    ) → (z, u)·has_same_length_as (z', u')
  seg_cons : ∀ x y a b : point, Σ' z, y·is_between (x, z) ∧ (y, z)·has_same_length_as (a, b)
