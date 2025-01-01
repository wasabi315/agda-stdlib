------------------------------------------------------------------------
-- The Agda standard library
--
-- Possibly-infinite reflexive transitive closures.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --sized-types #-}

module Relation.Binary.Construct.Closure.InfiniteReflexiveTransitive.Sized where

open import Level using (Level; _⊔_)
open import Size
open import Codata.Sized.Thunk
open import Function.Base
open import Relation.Binary.Core using (Rel; _=[_]⇒_; _⇒_)
open import Relation.Binary.Bundles using (Preorder)
open import Relation.Binary.Structures using (IsPreorder)
open import Relation.Binary.Definitions
  using (Transitive; Trans; Sym; TransFlip; Reflexive)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_; refl; sym; cong; cong₂)
import Relation.Binary.PropositionalEquality.Properties as ≡

private
  variable
    a ℓ : Level
    i j : Size
    A B : Set a

------------------------------------------------------------------------
-- Definition

infixr 5 _◅_

data Omega {A : Set a} (_~_ : Rel A ℓ) (i : Size) : Rel A (a ⊔ ℓ)
∞Omega : {A : Set a} (_~_ : Rel A ℓ) (i : Size) → Rel A (a ⊔ ℓ)

data Omega {A} _~_ i where
  ε   : Reflexive (Omega _~_ i)
  _◅_ : ∀ {x y z} (x~y : x ~ y) (y~∞z : ∞Omega _~_ i y z) → Omega _~_ i x z

∞Omega _~_ i x y = Thunk (λ j → Omega _~_ j x y) i

------------------------------------------------------------------------
-- Operations

module _ {_~_ : Rel A ℓ} where

  repeat : ∀ {x} → x ~ x → Omega _~_ i x x
  repeat x~x = x~x ◅ λ where .force → repeat x~x

  infixr 5 _◅◅_

  _◅◅_ : Transitive (Omega _~_ i)
  ε            ◅◅ y~∞z = y~∞z
  (x~y ◅ y~∞z) ◅◅ z~∞u = x~y ◅ λ where .force → y~∞z .force ◅◅ z~∞u

------------------------------------------------------------------------
-- Properties

module _ (_~_ : Rel A ℓ) where

  reflexive : _≡_ ⇒ Omega _~_ i
  reflexive refl = ε

  trans : Transitive (Omega _~_ i)
  trans = _◅◅_

  isPreorder : IsPreorder _≡_ (Omega _~_ i)
  isPreorder = record
    { isEquivalence = ≡.isEquivalence
    ; reflexive     = reflexive
    ; trans         = trans
    }

  preorder : ∀ i → Preorder _ _ _
  preorder i = record
    { _≈_        = _≡_
    ; _≲_        = Omega _~_ i
    ; isPreorder = isPreorder
    }
