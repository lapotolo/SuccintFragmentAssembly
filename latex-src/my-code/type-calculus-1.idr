StringOrInt : Bool -> Type -- simple example of
StringOrInt False = String -- type level function
StringOrInt True = Int
