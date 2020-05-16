vertex(1..10).
edge(1,2). edge(2,3). edge(3,4). edge(4,5). edge(5,1).
edge(6,8). edge(8,10). edge(10,7). edge(7,9). edge(9,6).
edge(1,6). edge(2,7). edge(3,8). edge(4,9). edge(5,10).
edge(U, V) :- edge(V, U).
