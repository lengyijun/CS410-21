{-# OPTIONS --type-in-type #-}
module NowYouTry.Adjunctions where

open import Axiom.UniquenessOfIdentityProofs.WithK
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Sum
open import Data.Unit hiding (_≤_)
open import Function using (_∘′_)

open import Lectures.Categories
open import Lectures.Kleisli
open import Lectures.Monads

open import Common.Category hiding (Monad)
open import Common.Category.Solver

---------------------------------------------------------------------------
-- Adjunctions
---------------------------------------------------------------------------

record Adjunction {C D : Category}
                  (F : Functor C D)
                  (G : Functor D C) : Set where

-- Notation: F ⊣ G, "F is left adjoint to G" or eq. "G is right adjoint to F"

  open Category
  open Functor
  open NaturalTransformation

  field
    to   : {X : Obj C}{B : Obj D} -> Hom D (act F X)        B  -> Hom C X         (act G B)         -- IMPORTANT
    from : {X : Obj C}{B : Obj D} -> Hom C X         (act G B) -> Hom D (act F X)        B          -- IMPORTANT
    left-inverse-of : ∀ {X B} →  (h : Hom D (act F X) B) -> from (to h) ≡ h                         -- (IMPORTANT)
    right-inverse-of : ∀ {X B} → (k : Hom C X (act G B)) -> to (from k) ≡ k                         -- (IMPORTANT)

--    for all X : Obj C, B : Obj D.
--
--            F X  -->   B      |         ^
--            ============      | to      | from
--              X  --> G B      v         |

    to-natural : {X X' : Obj C}{B B' : Obj D} (f : Hom C X' X)(g : Hom D B B') ->                   -- not so important
                   comp SET (to {X} {B}) (λ h → comp C f (comp C h (fmap G g)))
                     ≡
                   comp SET (λ k → comp D (fmap F f) (comp D k g)) (to {X'} {B'})


{-       for all f : X' -> X, g : B -> B'.

                            to {X} {B}
            Hom (F X) B   --------------> Hom X (G B)
                 |                            |
                 |                            |
    g ∘ _ ∘ F f  |                            | G g ∘ _ ∘ f
                 |                            |
                 |                            |
                 v                            v
                            to {X'} {B'}
            Hom (F X') B' --------------> Hom X' (G B')
-}

  from-natural : {X X' : Obj C}{B B' : Obj D} (f : Hom C X' X)(g : Hom D B B') ->
                 comp SET (from {X} {B}) (λ k → comp D (fmap F f) (comp D k g))
                   ≡
                 comp SET (λ h → comp C f (comp C h (fmap G g))) (from {X'} {B'})
  from-natural f g = ext λ x -> 
    ≡-Reasoning.begin
       ((λ k → comp D (fmap F f) (comp D k g)) ∘′ from) x
    ≡-Reasoning.≡⟨ sym ( left-inverse-of _ ) ⟩
      from (to (((λ k → comp D (fmap F f) (comp D k g) ) ∘′ from) x))
    ≡-Reasoning.≡⟨ refl ⟩
      from (to ((λ k → comp D (fmap F f) (comp D k g) ) (from x) ))
    ≡-Reasoning.≡⟨ cong from ( cong-app (sym ( to-natural _ _ )) (from x) ) ⟩
     from (comp SET to (λ h → comp C f (comp C h (fmap G g))) (from x))
    ≡-Reasoning.≡⟨ refl ⟩
      (from ∘′ (λ h → comp C f (comp C h (fmap G g)))) (to (from x))
    ≡-Reasoning.≡⟨ cong ( (from ∘′ (λ h → comp C f (comp C h (fmap G g))))) (right-inverse-of x) ⟩
       (from ∘′ (λ h → comp C f (comp C h (fmap G g)))) x
    ≡-Reasoning.∎

---------------------------------------------------------------------------
-- Adjoints to the forgetful functor PREORDER -> SET
---------------------------------------------------------------------------

open Category
open Functor
open Adjunction

open Preorder
open MonotoneMap

forget : Functor PREORDER SET
act forget X = Carrier X
fmap forget f = fun f
identity forget = refl
homomorphism forget = refl

-- A right adjoint to forget

chaoticPreorder : Functor SET PREORDER
Carrier (act chaoticPreorder B) = B
_≤_ (act chaoticPreorder B) b b' = ⊤
reflexive (act chaoticPreorder B) = tt
transitive (act chaoticPreorder B) _ _ = tt
propositional (act chaoticPreorder B) p q = refl
fun (fmap chaoticPreorder f) = f
monotone (fmap chaoticPreorder f) x y p = tt
identity chaoticPreorder = eqMonotoneMap refl
homomorphism chaoticPreorder = eqMonotoneMap refl

forget⊣chaotic : Adjunction forget chaoticPreorder
fun (to forget⊣chaotic h) = h
monotone (to forget⊣chaotic h) x y p = tt
from forget⊣chaotic k = fun k
left-inverse-of forget⊣chaotic h = refl
right-inverse-of forget⊣chaotic k = eqMonotoneMap refl
to-natural forget⊣chaotic f g = ext (λ x → eqMonotoneMap refl)

discretePreorder : Functor SET PREORDER
Carrier (act discretePreorder A) = A
_≤_ (act discretePreorder A) = _≡_
reflexive (act discretePreorder A) = refl
transitive (act discretePreorder A) = trans
propositional (act discretePreorder A) = uip
fun (fmap discretePreorder f) = f
monotone (fmap discretePreorder f) x y = cong f
identity discretePreorder = eqMonotoneMap refl
homomorphism discretePreorder = eqMonotoneMap refl

discrete⊣forget : Adjunction discretePreorder forget
to discrete⊣forget h = fun h
fun (from discrete⊣forget k) = k
monotone (from discrete⊣forget {B = B} k) x .x refl = reflexive B
left-inverse-of discrete⊣forget h = eqMonotoneMap refl
right-inverse-of discrete⊣forget k = refl
to-natural discrete⊣forget f g = refl









---------------------------------------------------------------------------
-- Binary coproducts as a left adjoint
---------------------------------------------------------------------------

PAIR : Category -> Category -> Category
Obj (PAIR C D) = Obj C × Obj D
Hom (PAIR C D) (A , X) (A' , X') = Hom C A A' × Hom D X X'
id (PAIR C D) = (id C , id D)
comp (PAIR C D) (f , g) (f' , g') = (comp C f f' , comp D g g')
assoc (PAIR C D) = cong₂ _,_ (assoc C) (assoc D)
identityˡ (PAIR C D) = cong₂ _,_ (identityˡ C) (identityˡ D)
identityʳ (PAIR C D) = cong₂ _,_ (identityʳ C) (identityʳ D)


diag : {C : Category} -> Functor C (PAIR C C)
act diag X = (X , X)
fmap diag f = (f , f)
identity diag = refl
homomorphism diag = refl

Either : Functor (PAIR SET SET) SET
act Either (A , B) = A ⊎ B
fmap Either (f , g) (inj₁ x) = inj₁ (f x)
fmap Either (f , g) (inj₂ y) = inj₂ (g y)
identity Either = ext (λ { (inj₁ x) → refl ; (inj₂ y) → refl})
homomorphism Either = ext (λ { (inj₁ x) → refl ; (inj₂ y) → refl })

Either⊣diag : Adjunction Either (diag {SET})
to Either⊣diag {X = (A , B)} {B = C} h = h ∘′ inj₁ , h ∘′ inj₂
from Either⊣diag {X = A , B} {B = C} (f , g) (inj₁ x) = f x
from Either⊣diag {X = A , B} {B = C} (f , g) (inj₂ y) = g y
left-inverse-of Either⊣diag h = ext (λ { (inj₁ x) → refl ; (inj₂ y) → refl })
right-inverse-of Either⊣diag (f , g) = refl
to-natural Either⊣diag f g = refl


---------------------------------------------------------------------------
-- Special cases of naturality (not very insightful)
---------------------------------------------------------------------------

to-natural₁ : {C D : Category}{F : Functor C D}{G : Functor D C} -> (adj : Adjunction F G) ->
              {X X' : Obj C}(f : Hom C X' X) ->
             comp C f (to adj (id D)) ≡ to adj (fmap F f)
to-natural₁ {C} {D} {F} {G} adj f =
 ≡-Reasoning.begin
   comp C f (to adj (id D))
 ≡-Reasoning.≡⟨ cong (comp C f) (sym (identityˡ C) ) ⟩
   comp C f (comp C (to adj (id D)) (id C) )
 ≡-Reasoning.≡⟨ cong₂ (comp C) refl (cong (comp C (to adj (id D)) ) (sym (identity G)) ) ⟩
  comp C f (comp C (to adj (id D)) (fmap G (id D)))
 ≡-Reasoning.≡⟨ cong-app (to-natural adj f (id D) ) (id D) ⟩
   comp SET (λ k → comp D (fmap F f) (comp D k (id D))) (to adj)
     (id D)
 ≡-Reasoning.≡⟨ cong (to adj) (cong (comp D (fmap F f)) (identityˡ D)) ⟩
   to adj (comp D (fmap F f) (id D ))
 ≡-Reasoning.≡⟨ cong (to adj) (identityˡ D) ⟩
   to adj (fmap F f)
 ≡-Reasoning.∎

to-natural₂ : {C D : Category}{F : Functor C D}{G : Functor D C} -> (adj : Adjunction F G) ->
                 {X : Obj C}{B' : Obj D}(g : Hom D (act F X) B') ->
                   comp C (to adj (id D)) (fmap G g) ≡ to adj g
to-natural₂ {C} {D} {F} {G} adj g =
  ≡-Reasoning.begin
    comp C (to adj (id D)) (fmap G g)
  ≡-Reasoning.≡⟨ sym (identityʳ C)  ⟩
    comp C (id C) (comp C (to adj (id D)) (fmap G g))
  ≡-Reasoning.≡⟨ cong-app ( to-natural adj (id C) g ) (id D) ⟩
    to adj ( comp D (fmap F (id C)) (comp D (id D) g) )
  ≡-Reasoning.≡⟨ cong (to adj) (cong₂ (comp D) (identity F)  refl ) ⟩
   to adj ( comp D (id D) (comp D (id D) g) )
  ≡-Reasoning.≡⟨ cong (to adj) (identityʳ D) ⟩
    to adj  (comp D (id D) g) 
  ≡-Reasoning.≡⟨ cong (to adj) (identityʳ D) ⟩  
   to adj g
  ≡-Reasoning.∎

from-natural₁ : {C D : Category}{F : Functor C D}{G : Functor D C} -> (adj : Adjunction F G) ->
                {X : Obj C}{B' : Obj D}(f : Hom C X (act G B')) ->
                 comp D (fmap F f) (from adj (id C)) ≡ from adj f
from-natural₁ {C} {D} {F} {G} adj f =
 ≡-Reasoning.begin
   comp D (fmap F f) (from adj (id C))
 ≡-Reasoning.≡⟨ cong₂ (comp D) refl ( sym (identityˡ  D)) ⟩
   comp D (fmap F f) (comp D  (from adj (id C))  (id D) )
 ≡-Reasoning.≡⟨ cong-app ( from-natural adj f (id D) ) (id C) ⟩
   comp SET (λ h → comp C f (comp C h (fmap G (id D)))) (from adj)
     (id C)
 ≡-Reasoning.≡⟨ refl ⟩
   from adj  ( comp C f ( comp C (id C) (fmap G (id D)) ))
 ≡-Reasoning.≡⟨ cong (from adj) ( cong₂  (comp C) refl (identityʳ  C) ) ⟩
   from adj  ( comp C f  (fmap G (id D)) )
 ≡-Reasoning.≡⟨ cong (from adj) (cong (comp C f) (identity G) ) ⟩
   from adj (comp C f (id C))
 ≡-Reasoning.≡⟨ cong (from adj) (identityˡ  C ) ⟩
   from adj f
 ≡-Reasoning.∎

from-natural₂ : {C D : Category}{F : Functor C D}{G : Functor D C} -> (adj : Adjunction F G) ->
                {B B' : Obj D}(g : Hom D B B') ->
                 comp D (from adj (id C)) g ≡ from adj (fmap G g)
from-natural₂ {C} {D} {F} {G} adj g =
 ≡-Reasoning.begin
   comp D (from adj (id C)) g
  ≡-Reasoning.≡⟨ sym (identityʳ D) ⟩
     comp D  (id D) (comp D (from adj (id C)) g )
  ≡-Reasoning.≡⟨ cong₂ (comp D) (sym (identity F)) refl ⟩
    comp D  (fmap F (id C)) (comp D (from adj (id C)) g )
  ≡-Reasoning.≡⟨ cong-app (from-natural adj (id C) g ) (id C) ⟩
    comp SET (λ h → comp C (id C) (comp C h (fmap G g))) (from adj)
      (id C)
  ≡-Reasoning.≡⟨ cong (from adj) (cong (comp C (id C)) (identityʳ C) ) ⟩
    from adj ((comp C (id C) (fmap G g)) )
  ≡-Reasoning.≡⟨ cong (from adj) (identityʳ C) ⟩
   from adj (fmap G g)
  ≡-Reasoning.∎


---------------------------------------------------------------------------
-- Monads from adjunctions
---------------------------------------------------------------------------

open Monad
open NaturalTransformation


monadFromAdj : (C D : Category)(F : Functor C D)(G : Functor D C) ->
               Adjunction F G -> Monad C
functor (monadFromAdj C D F G adj) = compFunctor F G
transform (returnNT (monadFromAdj C D F G adj)) c = to adj (id D)
natural (returnNT (monadFromAdj C D F G adj)) X Y cxy =
  ≡-Reasoning.begin
    (C ∘ to adj (id D)) cxy
  ≡-Reasoning.≡⟨ to-natural₁ adj cxy ⟩
    to adj (fmap F cxy)
  ≡-Reasoning.≡⟨ sym (to-natural₂ adj (fmap F cxy))⟩
    (C ∘ fmap G (fmap F cxy)) (to adj (id D))
  ≡-Reasoning.∎
transform (joinNT (monadFromAdj C D F G adj)) X = fmap G (from adj (id C))
natural (joinNT (monadFromAdj C D F G adj)) X Y f =
    ≡-Reasoning.begin
       (C ∘ fmap G (from adj (id C)))
      (fmap
       (compFunctor
        (compFunctor F G) (compFunctor F G))
       f)
    ≡-Reasoning.≡⟨ sym (homomorphism G) ⟩
      fmap G ( comp D (fmap F (fmap (compFunctor F G) f)) (from adj (id C)) )
    ≡-Reasoning.≡⟨ cong (fmap G) (from-natural₁ adj _)  ⟩
      fmap G (from adj (fmap G (fmap F f)))
    ≡-Reasoning.≡⟨ cong (fmap G) ( sym ( from-natural₂ adj _) ) ⟩
      fmap G ( comp D (from adj (id C))  (fmap F f) )
    ≡-Reasoning.≡⟨ homomorphism G ⟩
       (C ∘ fmap G (fmap F f)) (fmap G (from adj (id C)))
    ≡-Reasoning.∎
returnJoin (monadFromAdj C D F G adj) {X} =
   ≡-Reasoning.begin
      (C ∘ fmap G (from adj (id C))) (to adj (id D))
   ≡-Reasoning.≡⟨ sym (identityʳ C) ⟩
      comp C (id C) (comp C (to adj (id D)) (fmap G (from adj (id C))))
   ≡-Reasoning.≡⟨ cong-app ( to-natural adj (id C) (from adj (id C)) ) (id D)  ⟩
     to adj (comp D (fmap F (id C)) (comp D (id D) (from adj (id C))) )
   ≡-Reasoning.≡⟨ cong (to adj) ( cong₂ (comp D) (identity F) refl) ⟩
      to adj (comp D (id D) (comp D (id D) (from adj (id C))) )
   ≡-Reasoning.≡⟨ cong (to adj) (identityʳ D) ⟩
     to adj (comp D (id D) (from adj (id C)) )
   ≡-Reasoning.≡⟨ cong (to adj) (identityʳ D) ⟩
     to adj (from adj (id C))
   ≡-Reasoning.≡⟨ right-inverse-of adj (id C) ⟩
      id C
   ≡-Reasoning.∎
mapReturnJoin (monadFromAdj C D F G adj) {X} =
   ≡-Reasoning.begin
  (C ∘ fmap G (from adj (id C)))
      (fmap G (fmap F (to adj (id D))))
   ≡-Reasoning.≡⟨ sym (homomorphism G) ⟩
     fmap G (comp D (fmap F (to adj (id D))) (from adj (id C)) )
   ≡-Reasoning.≡⟨ cong (fmap G) jiting ⟩
     fmap G (id D)
   ≡-Reasoning.≡⟨ identity G ⟩
     id C
   ≡-Reasoning.∎ where
   jiting :  comp D (fmap F (to adj (id D))) (from adj (id C)) ≡ id D
   jiting =
     ≡-Reasoning.begin
       comp D (fmap F (to adj (id D))) (from adj (id C))
     ≡-Reasoning.≡⟨ cong (comp D (fmap F (to adj (id D)))) ( sym (identityˡ D) ) ⟩
      comp D (fmap F (to adj (id D))) (comp D (from adj (id C)) (id D))
     ≡-Reasoning.≡⟨ cong-app ( from-natural adj (to adj (id D)) (id D) ) (id C) ⟩
       from adj (comp C (to adj (id D)) (comp C (id C) (fmap G (id D))) )
     ≡-Reasoning.≡⟨ cong (from adj) ( cong (comp C (to adj (id D))) (identityʳ C) ) ⟩
       from adj (comp C (to adj (id D)) (fmap G (id D)))
     ≡-Reasoning.≡⟨ cong (from adj) ( cong (comp C (to adj (id D))) (identity G)) ⟩
       from adj (comp C (to adj (id D)) (id C))
     ≡-Reasoning.≡⟨ cong (from adj)  (identityˡ C) ⟩
       from adj (to adj (id D))
     ≡-Reasoning.≡⟨ left-inverse-of adj (id D) ⟩
       id D
     ≡-Reasoning.∎
 
joinJoin (monadFromAdj C D F G adj) {X} =
     ≡-Reasoning.begin
       (C ∘ fmap G (from adj (id C))) (fmap G (from adj (id C)))
     ≡-Reasoning.≡⟨ sym (homomorphism G) ⟩
       fmap G ( comp D (from adj (id C)) (from adj (id C)) )
     ≡-Reasoning.≡⟨ cong (fmap G) (from-natural₂ adj _) ⟩
       fmap G (from adj (fmap G (from adj (id C))))
     ≡-Reasoning.≡⟨ cong (fmap G) (sym ( from-natural₁ adj _ )) ⟩
       fmap G ( comp D (fmap F (fmap G (from adj (id C)))) (from adj (id C)) )
     ≡-Reasoning.≡⟨ homomorphism G ⟩
        (C ∘ fmap G (from adj (id C)))
      (fmap G (fmap F (fmap G (from adj (id C)))))
     ≡-Reasoning.∎
---------------------------------------------------------------------------
-- Every monad arises from an adjunction
---------------------------------------------------------------------------

ForgetKleisli : {C : Category}(M : Monad C) -> Functor (Kleisli M) C
act (ForgetKleisli M) X = Monad.act M X
fmap (ForgetKleisli M) f = bind M f
identity (ForgetKleisli M) = bindReturn M
homomorphism (ForgetKleisli {C} M) {Z = Z} {f = f} {g} =
  trans (cong (λ z → comp C (fmap (functor M) z) (join M Z)) (sym (assoc C))) (bindBind M {f = f} {g})

kleisliAdjunction : {C : Category}(M : Monad C) -> Adjunction (EmbedKleisli M) (ForgetKleisli M)
to (kleisliAdjunction M) x = x
from (kleisliAdjunction M) x = x
left-inverse-of (kleisliAdjunction M) h = refl
right-inverse-of (kleisliAdjunction M) k = refl
to-natural (kleisliAdjunction {C} M) {X} {X'} {B} {B'} f g = ext λ x →
  ≡-Reasoning.begin
    ((λ h → comp C f (comp C h (bind M g))) ∘′ (λ x₁ → x₁)) x
  ≡-Reasoning.≡⟨ refl ⟩
     (λ h → comp C f (comp C h (bind M g)) ) x
  ≡-Reasoning.≡⟨ refl ⟩
    comp C f (comp C x (bind M g))
  ≡-Reasoning.≡⟨ {!!} ⟩
    comp (Kleisli M)  (fmap (EmbedKleisli M) f) (comp (Kleisli M) (to (kleisliAdjunction M) x) g)
  ≡-Reasoning.∎


-- Theorem: monadFromAdj (kleisliAdjunction M) ≅ M

---------------------------------------------------------------------------
-- Now you try: binary products as a right adjoint
---------------------------------------------------------------------------

Both : Functor (PAIR SET SET) SET
act Both (A , B) = A × B
fmap Both = {!!}
identity Both = {!!}
homomorphism Both = {!!}

⊢diag : Adjunction (diag {SET}) Both
⊢diag = {!!}
