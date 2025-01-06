------------------------------------------------------------------------
-- The Agda standard library
--
-- Possibly-infinite transitive closures.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --sized-types #-}

module Relation.Binary.Construct.Closure.InfiniteTransitive.Sized where

open import Level using (Level; _⊔_)
open import Size
open import Codata.Sized.Thunk
open import Function.Base
open import Relation.Binary.Core using (Rel; _=[_]⇒_; _⇒_)
open import Relation.Binary.Bundles using (Preorder)
open import Relation.Binary.Structures using (IsPreorder)
open import Relation.Binary.Definitions
  using (Transitive; Trans; Sym; TransFlip; Reflexive)

private
  variable
    a ℓ : Level
    i j : Size
    A B : Set a

------------------------------------------------------------------------
-- Definition

infixr 5 _◅_

data Omega⁺ {A : Set a} (_~_ : Rel A ℓ) (i : Size) : Rel A (a ⊔ ℓ)
∞Omega⁺ : {A : Set a} (_~_ : Rel A ℓ) (i : Size) → Rel A (a ⊔ ℓ)

data Omega⁺ {A} _~_ i where
  [_] : ∀ {x y} (x~y : x ~ y) → Omega⁺ _~_ i x y
  _◅_ : ∀ {x y z} (x~y : x ~ y) (y~∞z : ∞Omega⁺ _~_ i y z) → Omega⁺ _~_ i x z

∞Omega⁺ _~_ i x y = Thunk (λ j → Omega⁺ _~_ j x y) i

------------------------------------------------------------------------
-- Operations

module _ {_~_ : Rel A ℓ} where

  infixr 5 _◅◅_

  _◅◅_ : Transitive (Omega⁺ _~_ i)
  [ x~y ]      ◅◅ y~∞z = x~y ◅ λ where .force → y~∞z
  (x~y ◅ y~∞z) ◅◅ z~∞u = x~y ◅ λ where .force → y~∞z .force ◅◅ z~∞u

------------------------------------------------------------------------
-- Properties

module _ (_~_ : Rel A ℓ) where

  reflexive : Reflexive _~_ → Reflexive (Omega⁺ _~_ i)
  reflexive refl = [ refl ]

  trans : Transitive (Omega⁺ _~_ i)
  trans = _◅◅_
