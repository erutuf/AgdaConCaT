
{-# OPTIONS --universe-polymorphism #-}

module Category where

open import Level
open import Function
open import Relation.Binary
open import Relation.Binary.Core

open import Map

-----------------------------------------------------------
-- Category

record Category {a} : Set (suc (suc a)) where
    field
      Obj    : Set a
      Hom    : Obj -> Obj -> Setoid a a
      Comp   : {x y z : Obj} -> Map2 (Hom x y) (Hom y z) (Hom x z)
      Id     : {x : Obj} -> Setoid.Carrier $ Hom x x
      PrfAss : {x y z w : Obj} -> (f : Setoid.Carrier $ Hom x y) -> (g : Setoid.Carrier $ Hom y z) -> (h : Setoid.Carrier $ Hom z w)
        -> Setoid._≈_ (Hom x w) (Map.Ap (Map.Ap Comp $ Map.Ap (Map.Ap Comp f) g) h) (Map.Ap (Map.Ap Comp f) (Map.Ap (Map.Ap Comp g) h))
      PrfIdl : {x y : Obj} -> (f : Setoid.Carrier $ Hom x y) -> Setoid._≈_ (Hom x y) (Map.Ap (Map.Ap Comp Id) f) f
      PrfIdr : {x y : Obj} -> (f : Setoid.Carrier $ Hom x y) -> Setoid._≈_ (Hom x y) (Map.Ap (Map.Ap Comp f) Id) f

    _o_ : {x y z : Obj} -> Setoid.Carrier $ Hom x y -> Setoid.Carrier $ Hom y z -> Setoid.Carrier $ Hom x z
    f o g = Map.Ap (Map.Ap Comp f) g

eqCompr : ∀{a} (C : Category {a}) -> (x y z : Category.Obj C) -> (f g : Setoid.Carrier $ (Category.Hom C) x y) -> (h : Setoid.Carrier $ (Category.Hom C) y z)
  -> Setoid._≈_ ((Category.Hom C) x y) f g -> Setoid._≈_ ((Category.Hom C) x z) ((Category._o_ C) f h) ((Category._o_ C) g h)
eqCompr C x y z f g h f=g = map2Congr ((Category.Hom C) x y) ((Category.Hom C) y z) ((Category.Hom C) x z) (Category.Comp C) f g h f=g

eqCompl : ∀{a} (C : Category {a}) -> (x y z : Category.Obj C) -> (f g : Setoid.Carrier $ (Category.Hom C) y z) -> (h : Setoid.Carrier $ (Category.Hom C) x y)
  -> Setoid._≈_ ((Category.Hom C) y z) f g -> Setoid._≈_ ((Category.Hom C) x z) ((Category._o_ C) h f) ((Category._o_ C) h g)
eqCompl C x y z f g h f=g = map2Congl ((Category.Hom C) x y) ((Category.Hom C) y z) ((Category.Hom C) x z) (Category.Comp C) h f g f=g

eqComp : ∀{a} (C : Category {a}) -> (x y z : Category.Obj C) -> (f g : Setoid.Carrier $ (Category.Hom C) x y) -> (h k : Setoid.Carrier $ (Category.Hom C) y z)
  -> Setoid._≈_ ((Category.Hom C) x y) f g -> Setoid._≈_ ((Category.Hom C) y z) h k -> Setoid._≈_ ((Category.Hom C) x z) ((Category._o_ C) f h) ((Category._o_ C) g k)
eqComp C x y z f g h k f=g h=k = map2Cong ((Category.Hom C) x y) ((Category.Hom C) y z) ((Category.Hom C) x z) (Category.Comp C) f g h k f=g h=k

-- Dual Category

--Dual : ∀{a} -> Category {a} -> Category {a}
--Dual C = record
--    { Obj = Category.Obj C
--    ; Hom = flip $ Category.Hom C
--    ; Comp = record
--        { Ap = \f -> record
--            { Ap = \g -> Map.Ap (Map.Ap (Category.Comp C) g) f
--            ; Press = \x y p -> Map.Press (Category.Comp C) x y p f
--            }
--        ; Press = \x y p -> \f -> Map.Press (Map.Ap (Category.Comp C) f) x y p
--        }
--    ; Id = Category.Id C
--    ; PrfAss = \f g h -> Category.PrfAss C h g f
--    ; PrfIdl = \f -> Category.PrfIdr C f
--    ; PrfIdr = \f -> Category.PrfIdl C f
--    }


