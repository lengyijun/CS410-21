module NowYouTry.Kleisli where


open import Data.Nat hiding (_≤_)
open import Data.Product
open import Data.Sum
open import Data.List as List
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality
open import Function hiding (_∘_; id)

open import Lectures.FunctorsAndNatTransformations
open import Lectures.Categories

open import Common.Category hiding (Monad)

open import Lectures.Monads

---------------------------------------------------------------------------
-- Using the categories solver
---------------------------------------------------------------------------

open import Common.Category.Solver

module _ {C : Category} where

  open Category C
  open Functor

{-

      F (id ∘ f)
  F X ----------> F X
   |  \          ^ |
   |   ---------/  |
 g |     F f       | g
   |               |
   v     F h       v      F k
  F Y ----------> F Y ----------> F Z
   |                               ^
   \------------------------------/
           F (h ∘ k)
-}


  example : {X Y Z : Obj}(F : Functor C C) ->
            (f : Hom X X)(g : Hom (act F X) (act F Y))(h : Hom Y Y)(k : Hom Y Z) ->
            (assumption : g ∘ fmap F f ≡ fmap F h ∘ g) ->
            fmap F k ∘ (g ∘ fmap F (id ∘ f)) ≡ fmap F (k ∘ h) ∘ g
  example F f g h k p = C ⊧begin
    fmapSyn F < k > ∘Syn (< g > ∘Syn fmapSyn F (idSyn ∘Syn < f >))
      ≡⟦ solveCat refl ⟧
    fmapSyn F < k > ∘Syn -[ < g > ∘Syn fmapSyn F < f > ]-
      ≡⟦ reduced (rd , rq p) ⟧
    fmapSyn F < k > ∘Syn -[ fmapSyn F < h > ∘Syn < g > ]-
      ≡⟦ solveCat refl ⟧
    fmapSyn F (< k > ∘Syn < h >) ∘Syn < g >
      ⟦∎⟧


---------------------------------------------------------------------------
-- Kleisli categories
---------------------------------------------------------------------------

module _ {C : Category} where

  open Monad
  open NaturalTransformation

  Kleisli : Monad C -> Category
  Category.Obj (Kleisli M) = Obj where open Category C
  Category.Hom (Kleisli M) X Y = Hom X (act M Y) where open Category C
  Category.id (Kleisli M) {X} = return M X
  Category.comp (Kleisli M) {D} {E} {F} de ef = join M F ∘ fmap M ef ∘ de where open Category C
  Category.assoc (Kleisli M) {D} {E} {F} {G} {de} {ef} {fg} = 
    ≡-Reasoning.begin
      (join M G ) ∘ ( (Functor.fmap (functor M) ( join M G ∘ ( Functor.fmap (functor M) fg ∘ ef) )) ∘ de ) 
    ≡-Reasoning.≡⟨ cong₂ (Category._∘_ C) refl ( cong₂ (Category._∘_ C) (homomorphism M )  refl)  ⟩
      (join M G ) ∘ ( ( Functor.fmap (functor M) (join M G) ∘ Functor.fmap (functor M) (Functor.fmap (functor M) fg ∘ ef) ) ∘ de ) 
    ≡-Reasoning.≡⟨ sym  ( Category.assoc C ) ⟩
      ( join M G ∘  ( Functor.fmap (functor M) (join M G) ∘ Functor.fmap (functor M) (Functor.fmap (functor M) fg ∘ ef) )) ∘ de
    ≡-Reasoning.≡⟨ cong₂ (Category._∘_ C) (sym (Category.assoc C) ) refl ⟩
      (( join M G ∘  Functor.fmap (functor M) (join M G) ) ∘ Functor.fmap (functor M) (Functor.fmap (functor M) fg ∘ ef) ) ∘ de
    ≡-Reasoning.≡⟨ cong₂ (Category._∘_ C) (cong₂ (Category._∘_ C) ( sym ( joinJoin  M ) ) refl) refl ⟩
       ((join M G ∘ join M (act M G) ) ∘
       Functor.fmap (functor M) (Functor.fmap (functor M) fg ∘ ef))
      ∘ de
    ≡-Reasoning.≡⟨ cong₂ (Category._∘_ C) ( cong₂ (Category._∘_ C) refl (homomorphism M) ) refl ⟩
       ((join M G ∘ join M (act M G) ) ∘
       ( Functor.fmap (functor M) (Functor.fmap (functor M) fg ) ∘ Functor.fmap (functor M) ef) )
      ∘ de
    ≡-Reasoning.≡⟨ cong₂ (Category._∘_ C) (  sym (Category.assoc C) ) refl ⟩
      ( ( ((join M G ∘ join M (act M G) ) ∘ Functor.fmap (functor M) (Functor.fmap (functor M) fg ) )∘ Functor.fmap (functor M) ef ) )
      ∘ de
    ≡-Reasoning.≡⟨ cong₂ (Category._∘_ C) ( cong₂ (Category._∘_ C) (Category.assoc C) refl) refl ⟩
      ( ( join M G ∘  join M (act M G) ∘  Functor.fmap (functor M) (Functor.fmap (functor M) fg )  )  ∘ Functor.fmap (functor M) ef )
      ∘ de
    ≡-Reasoning.≡⟨ cong₂ (Category._∘_ C) ( cong₂ (Category._∘_ C) ( cong₂ (Category._∘_ C) refl ( natural (joinNT M) _ _ fg ) )  refl) refl ⟩
      ( ( join M G ∘ Functor.fmap (functor M ) fg ∘ join M F  )  ∘ Functor.fmap (functor M) ef )
      ∘ de
    ≡-Reasoning.≡⟨ Category.assoc C ⟩
      ( join M G ∘ Functor.fmap (functor M ) fg ∘ join M F  )
      ∘ Functor.fmap (functor M) ef 
      ∘ de
    ≡-Reasoning.≡⟨ Category.assoc C ⟩
        join M G ∘ ( Functor.fmap (functor M ) fg ∘ join M F  )
      ∘ Functor.fmap (functor M) ef 
      ∘ de
    ≡-Reasoning.≡⟨ cong₂ (Category._∘_ C) refl (Category.assoc C)  ⟩
      (join M G ) ∘ ( Functor.fmap (functor M) fg ∘ ( join M F ∘ ( Functor.fmap (functor M) ef ∘ de )) )
    ≡-Reasoning.∎ where open Category C
  
    
    
  Category.identityˡ (Kleisli M) {A} {B} {f = f} = 
    ≡-Reasoning.begin
      (C Category.∘ join M B)
      ((C Category.∘
        Functor.fmap (functor M) (return M B))
       f) 
    ≡-Reasoning.≡⟨ sym (Category.assoc C) ⟩
      (C Category.∘ ((C Category.∘ join M B ) (Functor.fmap (functor M) (return M B)) ) ) f
    ≡-Reasoning.≡⟨ cong₂ ((Category._∘_ C)) (mapReturnJoin M) refl ⟩
     ( C Category.∘ ( Category.id C ) ) f
    ≡-Reasoning.≡⟨ Category.identityˡ C ⟩
      f
   ≡-Reasoning.∎

  
  Category.identityʳ (Kleisli M) {A} {B} {f = f} =
    ≡-Reasoning.begin
      (C Category.∘ join M B) ((C Category.∘ Functor.fmap (functor M) f) (return M A))
    ≡-Reasoning.≡⟨ cong (C Category.∘ join M B)  ( sym (natural (returnNT M) _ _ f  ) )  ⟩
      (C Category.∘ join M B) ((C Category.∘ return M (act M B) ) (f ))
    ≡-Reasoning.≡⟨ sym (Category.assoc C) ⟩
      (C Category.∘ (( C Category.∘ join M B ) (return M (act M B)) ) ) f
    ≡-Reasoning.≡⟨ cong₂ (Category._∘_ C) (returnJoin M ) refl  ⟩
      ( C Category.∘ ( Category.id C ) ) f
    ≡-Reasoning.≡⟨ Category.identityˡ C ⟩
      f
    ≡-Reasoning.∎
  
---------------------------------------------------------------------------
-- Now you try
---------------------------------------------------------------------------

  EmbedKleisli : (M : Monad C) -> Functor C (Kleisli M)
  Functor.act (EmbedKleisli M) X = X
  Functor.fmap (EmbedKleisli M) f = return M _ ∘ f where open Category C
  Functor.identity (EmbedKleisli M) {A} =
    ≡-Reasoning.begin
      return M A ∘ Category.id C
    ≡-Reasoning.≡⟨ Category.identityʳ C   ⟩
      return M A
    ≡-Reasoning.∎ where open Category C
    
  Functor.homomorphism (EmbedKleisli M) {X} {Y} {Z} {xy} {yz} =
    ≡-Reasoning.begin
      return M Z ∘ yz ∘ xy
    ≡-Reasoning.≡⟨ sym (Category.assoc C) ⟩
      ( return M Z ∘ yz ) ∘ xy
    ≡-Reasoning.≡⟨ cong₂ (Category._∘_ C) ( natural (returnNT M) _ _ yz ) refl ⟩
      ( fmap  M yz  ∘ return M Y ) ∘ xy
    ≡-Reasoning.≡⟨ Category.assoc C ⟩
      fmap  M yz  ∘ return M Y ∘ xy 
    ≡-Reasoning.≡⟨ cong₂ (Category._∘_ C) ( sym (Category.identityˡ C) ) refl ⟩
      ( ( Category.id C) ∘ fmap  M yz  )
      ∘ return M Y ∘ xy 
    ≡-Reasoning.≡⟨ cong₂ (Category._∘_ C) ( cong₂ (Category._∘_ C) (sym (mapReturnJoin M)) refl ) refl ⟩
      ( ( join M Z ∘ fmap M (return M Z) ) ∘ fmap  M yz  )
      ∘ return M Y ∘ xy 
    ≡-Reasoning.≡⟨ cong₂ (Category._∘_ C) (Category.assoc C) refl ⟩   
     ( join M Z ∘ (fmap M (return M Z) ∘ fmap  M yz ) )
      ∘ return M Y ∘ xy
     ≡-Reasoning.≡⟨ Category.assoc C ⟩  
      join M Z  ∘ ( fmap M (return M Z ) ∘ fmap M yz ) ∘ return M Y ∘ xy
    ≡-Reasoning.≡⟨ cong₂ (Category._∘_ C) refl ( cong₂ (Category._∘_ C) (sym (homomorphism M) ) refl ) ⟩
      join M Z  ∘ fmap M (return M Z ∘ yz) ∘ return M Y ∘ xy
    ≡-Reasoning.∎ where open Category C
