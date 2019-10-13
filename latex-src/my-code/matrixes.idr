Matrix : Nat -> Nat -> Type -> Type
Matrix n m a = Vect n (Vect m a)

transpose_mat : Matrix n m a -> Matrix m n a
transpose_mat []            = replicate _ []
transpose_mat (row :: rows) = zipWith (::) row (transpose_mat rows)

add_matrix : Num a => Matrix n m a -> Matrix n m a -> Matrix n m a
add_matrix []        []        = []
add_matrix (x :: xs) (y :: ys) = zipWith (+) x y :: add_matrix xs ys

mul_matrix : Num a => Matrix n m a -> Matrix m p a -> Matrix n p a
mul_matrix []            _  = []
mul_matrix (row :: rows) m2 = map (sum . zipWith (*) row) (transpose_mat m2) :: mul_matrix rows m2
  
