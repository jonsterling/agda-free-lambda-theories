{-# OPTIONS --type-in-type #-}
module CCC where

open import Operads
open import Prelude.List
open import Prelude.Path

record Sig : Set where
  no-eta-equality
  constructor ▸sig
  field
    ●₀ : Set
    ●₁ : List ●₀ → ●₀ → Set
open Sig public

module _ (𝔏 : Sig) where
  infixr 0 _⊕_
  infixr 0 _⊗_
  infixr 0 _⇒_
  infix  0 _≈_
  infixr 1 _⟓_
  infix  2 «_»

  𝔉 : Operad
  𝔉 = Free[ ●₁ 𝔏 ]

  𝔓 : PRO
  𝔓 = Planar.pro 𝔉

  data obj : Set where
    «_»
      : ●₀ 𝔏
      → obj
    𝟘
      : obj
    𝟙
      : obj
    _⊕_
      : (A B : obj)
      → obj
    _⊗_
      : (A B : obj)
      → obj
    _⇒_
      : (A B : obj)
      → obj

  ⟦_⟧₀ : List (●₀ 𝔏) → obj
  ⟦ [] ⟧₀ = 𝟙
  ⟦ A ∷ [] ⟧₀ = « A »
  ⟦ A ∷ A* ⟧₀ = « A » ⊗ ⟦ A* ⟧₀

  data hom : (A B : obj) → Set where
    «_»
      : {A* B* : List (●₀ 𝔏)}
      → (f* : PRO.hom 𝔓 A* B*)
      → hom ⟦ A* ⟧₀ ⟦ B* ⟧₀
    ↻
      : {A : obj}
      → hom A A
    _⟓_
      : {A B C : obj}
      → (f : hom A B)
      → (g : hom B C)
      → hom A C
    ¡ : {A : obj}
      → hom 𝟘 A
    ! : {A : obj}
      → hom A 𝟙
    inl
      : {A B : obj}
      → hom A (A ⊕ B)
    inr
      : {A B : obj}
      → hom B (A ⊕ B)
    fst
      : {A B : obj}
      → hom (A ⊗ B) A
    snd
      : {A B : obj}
      → hom (A ⊗ B) B
    [_,_]
      : {A B X : obj}
      → (f : hom A X)
      → (g : hom B X)
      → hom (A ⊕ B) X
    ⟨_,_⟩
      : {X A B : obj}
      → (f : hom X A)
      → (g : hom X B)
      → hom X (A ⊗ B)
    λ↗[_]
      : {A B C : obj}
      → (f : hom (A ⊗ B) C)
      → hom A (B ⇒ C)
    ap
      : {A B : obj}
      → hom ((A ⇒ B) ⊗ A) B

  [_⊕_]
    : {X Y A B : obj}
    → (f : hom A X)
    → (g : hom B Y)
    → hom (A ⊕ B) (X ⊕ Y)
  [ f ⊕ g ] = [ f ⟓ inl , g ⟓ inr ]

  ⟨_⊗_⟩
    : {X Y A B : obj}
    → (f : hom X A)
    → (g : hom Y B)
    → hom (X ⊗ Y) (A ⊗ B)
  ⟨ f ⊗ g ⟩ = ⟨ fst ⟓ f , snd ⟓ g ⟩

  λ↙[_]
    : {A B C : obj}
    → (f : hom A (B ⇒ C))
    → hom (A ⊗ B) C
  λ↙[ f ] = ⟨ fst ⟓ f , snd ⟩ ⟓ ap

  ⊕α⇒
    : {A B C : obj}
    → hom ((A ⊕ B) ⊕ C) (A ⊕ (B ⊕ C))
  ⊕α⇒ = [ [ inl , inl ⟓ inr ] , inr ⟓ inr ]

  ⊕α⇐
    : {A B C : obj}
    → hom (A ⊕ (B ⊕ C)) ((A ⊕ B) ⊕ C)
  ⊕α⇐ = [ inl ⟓ inl , [ inr ⟓ inl , inr ] ]

  ⊗α⇒
    : {A B C : obj}
    → hom ((A ⊗ B) ⊗ C) (A ⊗ (B ⊗ C))
  ⊗α⇒ = ⟨ fst ⟓ fst , ⟨ fst ⟓ snd , snd ⟩ ⟩

  ⊗α⇐
    : {A B C : obj}
    → hom (A ⊗ (B ⊗ C)) ((A ⊗ B) ⊗ C)
  ⊗α⇐ = ⟨ ⟨ fst , snd ⟓ fst ⟩ , snd ⟓ snd ⟩

  ⊕λ⇒
    : {A : obj}
    → hom (𝟘 ⊕ A) A
  ⊕λ⇒ = [ ¡ , ↻ ]

  ⊕λ⇐
    : {A : obj}
    → hom A (𝟘 ⊕ A)
  ⊕λ⇐ = inr

  ⊗λ⇒
    : {A : obj}
    → hom (𝟙 ⊗ A) A
  ⊗λ⇒ = snd

  ⊗λ⇐
    : {A : obj}
    → hom A (𝟙 ⊗ A)
  ⊗λ⇐ = ⟨ ! , ↻ ⟩

  ⊕ρ⇒
    : {A : obj}
    → hom (A ⊕ 𝟘) A
  ⊕ρ⇒ = [ ↻ , ¡ ]

  ⊕ρ⇐
    : {A : obj}
    → hom A (A ⊕ 𝟘)
  ⊕ρ⇐ = inl

  ⊗ρ⇒
    : {A : obj}
    → hom (A ⊗ 𝟙) A
  ⊗ρ⇒ = fst

  ⊗ρ⇐
    : {A : obj}
    → hom A (A ⊗ 𝟙)
  ⊗ρ⇐ = ⟨ ↻ , ! ⟩

  ⊕xch
    : {A B C D : obj}
    → hom ((A ⊕ B) ⊕ (C ⊕ D)) ((A ⊕ C) ⊕ (B ⊕ D))
  ⊕xch = [ [ inl ⊕ inl ] , [ inr ⊕ inr ] ]

  ⊗xch
    : {A B C D : obj}
    → hom ((A ⊗ B) ⊗ (C ⊗ D)) ((A ⊗ C) ⊗ (B ⊗ D))
  ⊗xch = ⟨ ⟨ fst ⊗ fst ⟩ , ⟨ snd ⊗ snd ⟩ ⟩

  ⊕δ
    : {A : obj}
    → hom (A ⊕ A) A
  ⊕δ = [ ↻ , ↻ ]

  ⊗δ
    : {A : obj}
    → hom A (A ⊗ A)
  ⊗δ = ⟨ ↻ , ↻ ⟩

  ⊕swp
    : {A B : obj}
    → hom (A ⊕ B) (B ⊕ A)
  ⊕swp = [ inr , inl ]

  ⊗swp
    : {A B : obj}
    → hom (A ⊗ B) (B ⊗ A)
  ⊗swp = ⟨ snd , fst ⟩

  const
    : {A B : obj}
    → (a : hom 𝟙 A)
    → hom B A
  const a = ! ⟓ a

  data _≈_ : {A B : obj} (f g : hom A B) → Set where
    ↻
      : {A B : obj}
      → {f : hom A B}
      → f ≈ f
    _⟓_
      : {A B : obj}
      → {f g h : hom A B}
      → (α : f ≈ g)
      → (β : g ≈ h)
      → f ≈ h
    _⁻¹
      : {A B : obj}
      → {f g : hom A B}
      → (α : f ≈ g)
      → g ≈ f
    _*_
      : {A B C : obj}
      → {f₀ f₁ : hom A B}
      → {g₀ g₁ : hom B C}
      → (α : f₀ ≈ f₁)
      → (β : g₀ ≈ g₁)
      → f₀ ⟓ g₀ ≈ f₁ ⟓ g₁
    [_,_]
      : {A B X : obj}
      → {f₀ f₁ : hom A X}
      → {g₀ g₁ : hom B X}
      → f₀ ≈ f₁
      → g₀ ≈ g₁
      → [ f₀ , g₀ ] ≈ [ f₁ , g₁ ]
    ⟨_,_⟩
      : {X A B : obj}
      → {f₀ f₁ : hom X A}
      → {g₀ g₁ : hom X B}
      → f₀ ≈ f₁
      → g₀ ≈ g₁
      → ⟨ f₀ , g₀ ⟩ ≈ ⟨ f₁ , g₁ ⟩
    λ↗
      : {A B C : obj}
      → {f₀ f₁ : hom (A ⊗ B) C}
      → λ↗[ f₀ ] ≈ λ↗[ f₁ ]
    ⊕-η
      : {A B X : obj}
      → {f : hom (A ⊕ B) X}
      → [ inl ⟓ f , inr ⟓ f ] ≈ f
    ⊗-η
      : {X A B : obj}
      → {f : hom X (A ⊗ B)}
      → ⟨ f ⟓ fst , f ⟓ snd ⟩ ≈ f
    λ-η
      : {A B C : obj}
      → {f : hom A (B ⇒ C)}
      → λ↗[ ⟨ fst ⟓ f , snd ⟩ ⟓ ap ] ≈ f
    inl-β
      : {A B X : obj}
      → {f : hom A X}
      → {g : hom B X}
      → inl ⟓ [ f , g ] ≈ f
    inr-β
      : {A B X : obj}
      → {f : hom A X}
      → {g : hom B X}
      → inr ⟓ [ f , g ] ≈ g
    fst-β
      : {X A B : obj}
      → {f : hom X A}
      → {g : hom X B}
      → ⟨ f , g ⟩ ⟓ fst ≈ f
    snd-β
      : {X A B : obj}
      → {f : hom X A}
      → {g : hom X B}
      → ⟨ f , g ⟩ ⟓ snd ≈ g
    ap-β
      : {A B C : obj}
      → {f : hom (A ⊗ B) C}
      → ⟨ fst ⟓ λ↗[ f ] , snd ⟩ ⟓ ap ≈ f

module Example where
  pattern · = stop
  pattern ψ g fs = step g fs

  data 𝔏₀ : Set where
    nat : 𝔏₀

  data 𝔏₁ : (m* : List 𝔏₀) (n : 𝔏₀) → Set where
    ze
      : 𝔏₁ [] nat
    su
      : 𝔏₁ (nat ∷ []) nat
    add
      : 𝔏₁ (nat ∷ nat ∷ []) nat
    mul
      : 𝔏₁ (nat ∷ nat ∷ []) nat

  𝔏 : Sig
  𝔏 = ▸sig 𝔏₀ 𝔏₁

  two : hom 𝔏 𝟙 « nat »
  two =
    «
    PRO.seq (𝔓 𝔏)
      (ψ ze [] ∷ [])
      (ψ su (· ∷ []) ∷ [])
    »

  three : hom 𝔏 𝟙 « nat »
  three =
    «
    PRO.seq (𝔓 𝔏)
      (ψ ze [] ∷ [])
      (PRO.seq (𝔓 𝔏)
        (ψ su (· ∷ []) ∷ [])
        (ψ su (· ∷ []) ∷ []))
    »

  five : hom 𝔏 𝟙 « nat »
  five = ⟨ two , three ⟩ ⟓ « ψ add (· ∷ · ∷ []) ∷ [] »

  add↗ : hom 𝔏 𝟙 (« nat » ⇒ « nat » ⇒ « nat »)
  add↗ = λ↗[ snd ⟓ λ↗[ « ψ add (· ∷ · ∷ []) ∷ [] » ] ]

  five′ : hom 𝔏 𝟙 « nat »
  five′
    = ⟨ two , three ⟩
    ⟓ ⟨ ! ⟓ add↗ , ↻ ⟩
    ⟓ ⊗α⇐ 𝔏
    ⟓ ⟨ fst ⟓ ap , snd ⟩
    ⟓ ap
