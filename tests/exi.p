%% Make sure there are two types, otherwise monotonox won't encode any types
tff(foo, type, a : $tType).
tff(foo, type, c : a).
cnf(foo, axiom, c = c).

%% Non-monotone type $i
cnf(foo, axiom, X = Y).
%% Existentially-quantified variables should not be guarded
cnf(foo, conjecture, X = Y).
fof(foo, axiom, ?[X,Y]: X = Y).
fof(foo, axiom, ~![X,Y]: X = Y).
%% Nor negative variables
fof(foo, axiom, ![X,Y]: ~(X = Y)).
fof(foo, axiom, ?[X,Y]: ~(X = Y)).

