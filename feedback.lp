%Written by z5222191 for COMP4418 Assignment 2
%const value
#const size = 15.
%encoding
%choice rule of selecting edge set of given size
size { select(X,Y) : edge(X,Y)} size.
%ne is a set of all edges that is not selected - complement of selected set.
ne(X,Y) :- edge(X,Y), not select(X,Y).
%check rule checked if there exists a path from every vertex to the next vertex in the new edge set
check(X) :- vertex(X), check(Y):ne(X,Y).
%if there exists a path from a vertex to itself then it is a cycle
cycle :- check(X):vertex(X).
%we select only the models that are acyclic using not of cycle rule.
:- not cycle.
#show select/2.
