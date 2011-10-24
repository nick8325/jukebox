tff(foo, type, list : $tType).
tff(foo, type, nil : list).
tff(foo, type, cons : $i * list > list).
tff(foo, type, head : list > $i).
tff(foo, type, tail : list > list).

tff(foo, axiom, ![X:$i,Xs:list]: nil != cons(X, Xs)).
tff(foo, axiom, ![Xs:list]: (Xs != nil | ?[Y:$i,Ys:list]: (Xs = cons(Y, Ys)))).
tff(foo, axiom, ![X:$i,Xs:list]: head(cons(X,Xs)) = X).
tff(foo, axiom, ![X:$i,Xs:list]: tail(cons(X,Xs)) = Xs).
