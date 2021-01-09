————————————————————————————————————————————————————————————
MAGMA SCRIPTS FOR FINDING MINIMAL MISSING TRACE GROUPS OF GL2-LEVEL IN THE CUMMINS-PAULI LIST (M \LEQ 96)
————————————————————————————————————————————————————————————

for m < 48 do:

1.  Lm := CumminsPauliGL2Groups(m,0);
2.  SDLm := ThinDownToSurjectiveDet(Lm,m);
3.  MTLm := ThinDownToMinimalMissingTraceGroups(SDLm,m);
4.  MMTLm := ThinDownByMaximality(MTLm,m);

5.  NMLm := ThinDownToNonMissingTraceGroups(SDLm,m);
6.  ADLm := ThinDownToAdmissibleGroups(NMLm,m);
7.  HLm := FormingHigherLevelMTGroups(ADLm,m);

if 2m \notin CumminsPauliList, then also do:

8.  ThinLm := ThinDownToContainsMinusIdentity(NMLm,m);
9.  L2m := TwoTimesMComputation(ThinLm,m);
10.  SDL2m := ThinDownToSurjectiveDet(L2m,2m);
11.   MTL2m := ThinDownToMinimalMissingTraceGroups(SDL2m,2m);
12.  MMTL2m := ThinDownByMaximality(MMTL2m,2m);

13.  NML2m := ThinDownToNonMissingTraceGroups(SDL2m,2m);
14.  ADL2m := ThinDownToAdmissibleGroups(NML2m,2m);
15.  HL2m := FormingHigherLevelMTGroups(ADL2m,2m);
