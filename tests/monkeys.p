tff(foo, type, monkey : $tType).
tff(foo, type, banana : $tType).
tff(foo, type, banana1 : monkey > banana).
tff(foo, type, banana2 : monkey > banana).
tff(foo, type, has : (monkey * banana) > $o).

tff(foo, axiom, ![M:monkey]:has(M,banana1(M))).
tff(foo, axiom, ![M:monkey]:has(M,banana2(M))).
tff(foo, axiom, ![M:monkey]:banana1(M) != banana2(M)).
tff(foo, axiom, ![M1:monkey,M2:monkey,B:banana]:((has(M1,B) & has(M2, B)) => M1=M2)).
