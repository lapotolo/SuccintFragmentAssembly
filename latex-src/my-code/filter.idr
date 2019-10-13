filter : (a -> Bool) -> Vect n a -> (k ** Vect k a)
filter p [] = ( _ ** [] )
filter p (x :: xs) with (filter p xs)
  filter p (x :: xs) | ( _ ** xs' ) = 
                     if (p x) then ( _ ** x :: xs' )
                              else ( _ ** xs' )
