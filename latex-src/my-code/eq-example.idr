module eq

{-
data Nat = Z 
         | S Nat

data List : Type -> Type where
  Nil  : List elem
  (::) : elem -> List elem -> List elem 
-}
data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a

-- exactLength' : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)

-- data EqNat' : (num1 : Nat) -> (num2 : Nat) -> Type where

-- checkEqNat' : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)

{- ATTEMPT 1
We should expect to be able to implement exactLength by comparing the length of
input with the desired length, len.
If they’re equal, then input has length len, so its
type should be considered equivalent to Vect len a,
and you can return it directly. Otherwise, you return Nothing


exactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength len input {m}  = case (len == m) of
                             False => Nothing
                             True => Just (Input)


this one cant type check because the compiler cannot infer on its own that m and len are equal 
ie: he type of == isn’t informative enough to guarantee that m and len are equal, even if it returns True.
A variable’s type tells Idris what possible values a variable can have,
but it says nothing about where the value comes from.
If a variable has type Bool, Idris knows that 
it can have either of the values True or False,
but it knows nothing about the computation that
has produced the value.
-}

{-
We need a a more precise type for the equality test, where the
type guarantees that a comparison between two inputs can only be successful if the
inputs really are identical.
-}                                                                                                                                                                                                 
data EqNat : (num1 : Nat) -> (num2 : Nat) -> Type where
  SameNat : (num : Nat) -> EqNat num num

--sameS1 : (k : Nat) ->  (j: Nat) -> (eq_prf : EqNat k j) -> EqNat (S k) (S j)


--checkEqNat1 : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)


{-
It has two numbers as arguments, num1 and num2.
If you have a value of type EqNat num1 num2 , you know that num1 and num2 must
be the same number because the only constructor, Same , can only build something
with a type of the form EqNat num num , where the two arguments are the same.         

!!!) EqNat num1 num2 is essentially a proof that num1 must be equal to num2


you can have a type EqNat 3 4 but it cannot be inhabitated

λΠ> the (EqNat 3 4) (SameNat _)
(input):1:1-27:When checking argument value to function Prelude.Basics.the:
        Type mismatch between
                EqNat num num (Type of SameNat num)
        and
                EqNat 3 4 (Expected type)
        
        Specifically:
                Type mismatch between
                        0
                and
                        1
-}

{-
checkEqNat function either returns a proof that its
inputs are the same, in the form of EqNat,
or Nothing if the inputs are different.
checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)

-}

{-
  extracted while writing checkEqNat
  it takes an instance of EqNat as an input and manipulate
  it deduce additional information about equalities.
-}
sameS : (k : Nat) ->  (j: Nat) -> (eq_prf : EqNat k j) -> EqNat (S k) (S j)
-- sameS k j eq_prf = ?hole1 -- C-c c on eq_prf
sameS j j (SameNat j) = SameNat (S j)
-- sameS k j eq_prf = ?hole1
{-
by expressing a relationship between k and j using eq in the type of sameS ,
and you’ve case-split on eq , Idris has noticed that both Nat inputs must be the
same. Not only that, if you try to give a different value, it will report an error. If,
instead, you write this
-}

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
checkEqNat Z Z = Just (SameNat Z)
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) = case (checkEqNat k j) of -- i've proved EqNat k j, now propagate to successors
                              Nothing => Nothing
                              (Just eq_prf) => Just (sameS _ _ eq_prf)
                              --(Just eq_prf) => Just (cong S eq_prf)

exactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength {m} len input = case checkEqNat len m of
                             Nothing            => Nothing
                             Just (SameNat len) => Just (input)

{-
Rather than defining a specific equality type and function for every possible type
you’ll need to compare, such as Nat with EqNat and checkEqNat here, Idris provides a
generic equality type. This is built into Idris’s syntax, so you can’t define this yourself
(because = is a reserved symbol), but conceptually it would be defined as follows.

data (=) : a -> b -> Type where
  Refl : x = x
  
  
checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (num1 = num2)
checkEqNat Z     Z     = Just Refl
checkEqNat Z     (S k) = Nothing
checkEqNat (S k) Z     = Nothing
checkEqNat (S k) (S j) = case checkEqNat k j of
                             Nothing            => Nothing
                             Just (prf) => Just (cong prf)



cong is a generic version of sameS defined in the prelude as:

cong : {func : a -> b} -> x = y -> func x = func y
cong Refl = Refl


-}

-- ===========================================================================
-- ===========================================================================

{-
-- it is enough to know that the functions typecheck
-- Exercise 1 p.219
same_cons : {xs : List a} -> {ys : List a} -> xs = ys -> x :: xs = x :: ys
same_cons prf = cong prf
 
-- Exercise 2 p.219
same_lists : {xs : List a} -> {ys : List a} -> x = y -> xs = ys -> x :: xs = y :: ys
same_lists Refl = same_cons

data ThreeEq : a -> b -> c -> Type where
  Refl3 : ThreeEq a a a

allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS a a a Refl3 = Refl3
-}
