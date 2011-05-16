
{-# OPTIONS --universe-polymorphism #-}

module Functor where

open import Level
open import Function
open import Relation.Binary

open import Map
open import Category

-- Functor

record Functor {a b} (A : Category {a}) (B : Category {b}) : Set (a ⊔ suc (a ⊔ b)) where
    field
      FObj : Category.Obj A -> Category.Obj B
      FMap : (x y : Category.Obj A) -> Map (Category.Hom A x y) (Category.Hom B (FObj x) (FObj y))
      PrfFComp : (x y z : Category.Obj A) -> (f : Setoid.Carrier $ Category.Hom A x y) -> (g : Setoid.Carrier $ Category.Hom A y z)
        -> Setoid._≈_ (Category.Hom B (FObj x) (FObj z)) (Map.Ap (FMap x z) (Category._o_ A f g)) (Category._o_ B (Map.Ap (FMap x y) f) (Map.Ap (FMap y z) g))
      PrfFId : (x : Category.Obj A) -> Setoid._≈_ (Category.Hom B (FObj x) (FObj x)) (Map.Ap (FMap x x) (Category.Id A {x})) (Category.Id B {FObj x})
