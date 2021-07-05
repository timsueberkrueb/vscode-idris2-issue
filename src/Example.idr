module Example

import Data.Nat

import PreorderReasoning

%default total

example : (x : Nat) -> (x + 1) + 0 = 1 + x
example x =
  Calc $
   |~ (x + 1) + 0
   ~~ x+1  ...( plusZeroRightNeutral $ x + 1 )
   ~~ 1+x  ...( plusCommutative x 1          )
