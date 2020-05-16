%Written by z5222191 for COMP4418 Assignment 2
#const size = 4.
% encoding
%selecting vertex set of given size  which is a constant value
size {select(X) : vertex(X) } size.
% checking if there exists an edge for all selected vertices
:- select(X), select(Y), edge(X,Y).
#show select/1.
