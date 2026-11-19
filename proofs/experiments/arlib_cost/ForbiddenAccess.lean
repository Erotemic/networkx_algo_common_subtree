import Arlib.Computation.Queue
import Arlib.Computation.Dict
import Arlib.Computation.Charged
open Arlib.Computation
-- Each declaration must fail: these are specification-only projections.
def badQueue (q : Queue Nat) : List Nat := q.toList
def badDictionary (d : Dict Nat Nat) (k : Nat) : Option Nat := d.lookup k
def badEraseCost (p : Charged Unit Unit Nat) : Charged Unit Unit Nat := pure p.val
