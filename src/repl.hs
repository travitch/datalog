
import Database.Datalog.REPL.REPL

main :: IO ()
main = replMain

{-

Example use


*Main> :main
% parentOf(bob,mary).
% parentOf(sue,mary).
% parentOf(mary,john).
% parentOf(joe,john).
% 
% ancestorOf(X,Y) :- parentOf(X,Y).
% ancestorOf(X,Y) :- parentOf(X,Z),ancestorOf(Z,Y).
% 
% :facts
parentOf(bob, mary).
parentOf(sue, mary).
parentOf(mary, john).
parentOf(joe, john).
% :rules
ancestorOf(X, Y) :- parentOf(X, Y).
ancestorOf(X, Y) :- parentOf(X, Z), ancestorOf(Z, Y).
% ?ancestorOf(X,john).
Query result:
ancestorOf(bob, john).
ancestorOf(sue, john).
ancestorOf(mary, john).
ancestorOf(joe, john).
% :last
ancestorOf(X, john)  :  ancestorOf(bob, john).
                        ancestorOf(sue, john).
                        ancestorOf(mary, john).
                        ancestorOf(joe, john).
% :q
*Main>
-}
