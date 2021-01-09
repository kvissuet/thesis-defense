RTI:= function(x)
	for a in [0..1000] do
		if a eq x then
			return a;
			break a;
		end if;
	end for;
end function;

SizeOfSL2Kernel := function(d,m)
	answer := 1;
	q := Floor(d/m);	
	for n := 1 to #Factorization(q) do
		p := Factorization(q)[n,1];
		e := Factorization(q)[n,2];
		if IsDivisibleBy(m,p) then
			pfactor := p^(3*e);
		end if;
		if not IsDivisibleBy(m,p) then
			pfactor := p^(3*(e-1))*p*(p-1)*(p+1);
		end if;
		answer := answer*pfactor;
	end for;
	return answer;
end function;

SizeOfGL2Kernel := function(d,m)
	answer := 1;
	q := Floor(d/m);	
	for n := 1 to #Factorization(q) do
		p := Factorization(q)[n,1];
		e := Factorization(q)[n,2];
		if IsDivisibleBy(m,p) then
			pfactor := p^(4*e);
		end if;
		if not IsDivisibleBy(m,p) then
			pfactor := p^(4*(e-1))*p*(p-1)^2*(p+1);
		end if;
		answer := answer*pfactor;
	end for;
	return answer;
end function;

SL2Level := function(G,m)
	S := G meet SL(2,Integers(m));
	setoflevels := {};
	if #S eq #SL(2,Integers(m)) then 
		setoflevels := { 1 };
	end if;
	for d in Divisors(m) do
		if d gt 1 then
			Smodd := MatrixGroup<2, Integers(d) | Generators(S) >;
			if Floor(#S/#Smodd) eq SizeOfSL2Kernel(m,d) then
				setoflevels := setoflevels join { d };
			end if;
		end if;
	end for;
	return Min(setoflevels);
end function;

GL2Level := function(G,m)
	setoflevels := {};
	if #G eq #GL(2,Integers(m)) then 
		setoflevels := { 1 };
	end if;
	for d in Divisors(m) do
		if d gt 1 then
			Gmodd := MatrixGroup<2, Integers(d) | Generators(G) >;
			if Floor(#G/#Gmodd) eq SizeOfGL2Kernel(m,d) then
				setoflevels := setoflevels join { d };
			end if;
		end if;
	end for;
	return Min(setoflevels);
end function;

DetOfGroup := function(G,m)
	D := MatrixGroup<1, IntegerRing(m) | [1] >;
	for X in Generators(G) do
		D := MatrixGroup<1, IntegerRing(m) | Generators(D), [Determinant(X)] >;
	end for;
	return D;
end function;

Genus := function(H,m)
	G := GL(2,IntegerRing(m));
	S := SL(2,IntegerRing(m));
	f, GPerm := PermutationRepresentation(G);
	gi := f([0,-1,1,0]);
	gp := f([1,1,-1,0]);
	Si := Set(Class(f(S),gi)); 
	Sp := Set(Class(f(S),gp));
	Gamma := MatrixGroup<2, IntegerRing(m) | [1,1,0,1] >;
	negI := Matrix(IntegerRing(m),2,2,[-1,0,0,-1]);
	Xenl := MatrixGroup<2, IntegerRing(m) | H, [-1,0,0,-1] >;
	XS := Xenl meet S;
	Ni := Si meet Set(f(XS));
	Np := Sp meet Set(f(XS));
	ri := #Ni / #Si;
	rp := #Np / #Sp;
	rinf := #DoubleCosetRepresentatives(f(S),f(Gamma),f(XS))*#XS/#S;
	genus := 1 + #S/12/#XS*(1 - 3*ri - 4*rp - 6*rinf);
	return <ri, rp, rinf, genus>;
end function;

CumminsPauliGL2Groups := function(m,g)
	List := [];		
	G := GL(2,Integers(m));
	S := SL(2,Integers(m));
	for H in Subgroups(G) do
		if Genus(H`subgroup,m)[4] eq g then
			Append(~List,<H`subgroup,H`subgroup meet S,Genus(H`subgroup,m),m>);	
		end if;
	end for;
	return List;
end function;

Level48Calculation := function(L16,L3,m16,m3,genus)
	List := [];
	for x := 1 to #L3 do
		for y := 1 to #L16 do
			print <x,y>;
			for H3 in NormalSubgroups(L3[x,1]) do
				N3 := H3`subgroup;
				Q3, pi3 := L3[x,1]/N3;
				for H16 in NormalSubgroups(L16[y,1] : IndexEqual := #Q3) do
					N16 := H16`subgroup;
					Q16, pi16 := L16[y,1]/N16;
					dummy, psi := IsIsomorphic(Q3,Q16);
					if dummy eq true then
						for ga in OuterAutomorphismRepresentatives(AutomorphismGroup(Q16)) do
							Fib := FiberedProductWithTwisting(L3[x,1],m3,L16[y,1],m16,N3,pi3,pi16,psi,ga);
							if Genus(Fib,m3*m16)[4] eq genus then
								Append(~List,<Fib,Fib meet SL(2,Integers(m3*m16)),Genus(Fib,m3*m16),m3*m16>);
							end if;
						end for;
					end if;
				end for;
			end for;
		end for;
	end for;
	return List;
end function;

DetOfGroup := function(G,m)
	D := MatrixGroup<1, IntegerRing(m) | [1] >;
	for X in Generators(G) do
		D := MatrixGroup<1, IntegerRing(m) | Generators(D), [Determinant(X)] >;
	end for;
	return D;
end function;

ThinDownToSurjectiveDet := function(L,m)
	List := [];
	for x := 1 to #L do
		if #DetOfGroup(L[x,1],m) eq EulerPhi(m) then
			Append(~List,L[x]);
		end if;
	end for;
	return List;
end function;

TraceOfGroup := function(G,m)
	Traces := {};
	for g in G do
		Traces := Traces join { Trace(g) };
		if #Traces eq m then
			break g;
		end if;
	end for;
	return Traces;
end function;

IsMinimalMissingTraceGroup := function(G,m)
	hasmissingtrace := false;
	if #TraceOfGroup(G,m) lt m then 
		hasmissingtrace := true;
	end if;
	isminimalmissingtracegroup := true;
	for p in PrimeDivisors(m) do
		if p lt m then
			Gmodmoverp := MatrixGroup<2, Integers(Floor(m/p))	| Generators(G) >;
			if #TraceOfGroup(Gmodmoverp,Floor(m/p)) lt Floor(m/p) then
				isminimalmissingtracegroup := false;
				break p;
			end if;
		end if;
	end for;
	answer := hasmissingtrace and isminimalmissingtracegroup;
	return answer;
end function;

ThinDownToMinimalMissingTraceGroups := function(L,m)
	List := [];
	for x := 1 to #L do
		if IsMinimalMissingTraceGroup(L[x,1],m) then
			Append(~List,L[x]);
		end if;
	end for;
	return List;
end function;

ThinDownToNonMissingTraceGroups := function(L,m)
	List := [];
	for x := 1 to #L do
		print x;
		if #TraceOfGroup(L[x,1],m) eq m then
			Gm := L[x,1];
			Sm := Gm meet SL(2,Integers(m));
			Qm := Floor(#Sm/#CommutatorSubgroup(Gm,Gm));
			Append(~List,<L[x,1],L[x,2],L[x,3],L[x,4],Qm>);
		end if;
	end for;
	return List;
end function;


IsConjugateToSubgroup := function(G1,G2,m)
	answer := false;
	for H2 in Subgroups(G2 : OrderEqual := #G1) do
		if IsConjugate(GL(2,Integers(m)),G1,H2`subgroup) then
			answer := true;
			break H2;
		end if;
	end for;
	return answer;
end function;

ThinDownByMaximality := function(L,m);
	List := [];
	for x := 1 to #L do
		ismaximal := true;
		for y := 1 to #L do
			if y ne x then
				if IsConjugateToSubgroup(L[x,1],L[y,1],m) then
					ismaximal := false;
					break y;
				end if;
			end if;
		end for;
		if ismaximal eq true then
			Append(~List,L[x]);
		end if;
	end for;
	return List;
end function;


SupportedOnPrimesDividing := function(d,m)
	answer := true;
	for p in PrimeDivisors(d) do
		if not IsDivisibleBy(m,p) then
			answer := false;
			break p;
		end if;
	end for;
	return answer;
end function;

IsCongruentToImod := function(g,d)
	iscongruent := false;
	if (RTI(g[1,1]) - RTI(g[2,2])) mod d eq 0 mod d and RTI(g[1,2]) mod d eq 0 mod d and RTI(g[2,1]) mod d eq 0 mod d then
		iscongruent := true;
	end if;
	return iscongruent;
end function;


IsAdmissible := function(G,m,d)
	isadmissible := false;
	for t := 1 to m do
		tSet := {};
		for g in G do
			ngSet := {};
			if RTI(Trace(g)) mod m eq t mod m then
				for p in PrimeDivisors(d) do
 					if IsCongruentToImod(g,p) then
						tSet := tSet join {p};
					end if;
					if not IsCongruentToImod(g,p) then
						ngSet := ngSet join {p};
					end if;
				end for;
			end if;
			if #ngSet eq #PrimeDivisors(d) then
				continue t;
			end if;
		end for;
		if #tSet eq #PrimeDivisors(d) then
			isadmissible := true;
			break t;
		end if;
	end for;
	return isadmissible;
end function;


ThinDownToAdmissibleGroups := function(L,m)
	List := [];
	SetOfIndexDivisors := {};
	for x := 1 to #L do
		Gm := L[x,1];
		Sm := Gm meet SL(2,Integers(m));
		Cm := CommutatorSubgroup(Gm,Gm);
		index := Floor(#Sm/#Cm);
		for d in Divisors(index) do
			if SupportedOnPrimesDividing(d,m) then
				SetOfIndexDivisors := SetOfIndexDivisors join {d};
			end if;
		end for;
	end for;
	SeqOfIndexDivisors := SetToSequence(SetOfIndexDivisors);
	for j := 1 to #SeqOfIndexDivisors do
		d := SeqOfIndexDivisors[j];
		dList := [];
		for x := 1 to #L do
			if IsDivisibleBy(L[x,5],d) then
				if IsAdmissible(L[x,1],m,d) then
					Append(~dList,<L[x,1],L[x,2],L[x,3],L[x,4],L[x,5],d>);
				end if;
			end if;
		end for;
		if #dList gt 0 then
			Append(~List,dList);
		end if;
	end for;
	return List;
end function;


ModuloM1D := function(d,m)
	Answer := RTI(d[1,1]) mod m;
	return Answer;
end function;

IsCoherentDelta := function(delta,pimodH,G,m)
	iscoherent := true;
	for g in Generators(G) do
		if not ModuloM1D(delta(pimodH(g)),m) eq Determinant(g) then
			iscoherent := false;
			break g;
		end if;
	end for;
	return iscoherent;
end function;

IsCoherentAlpha := function(alpha,m,d)
	iscoherent := true;
	for g in Generators(GL(1,Integers(d*m))) do
		if not ModuloM1D(alpha(g),m) eq ModuloM1D(g,m) then
			iscoherent := false;
			break g;
		end if;
	end for;
	return iscoherent;
end function;

CoherentAlphaList := function(L,m,d)
	List := [];
	for x := 1 to #L do
		if IsCoherentAlpha(L[x],m,d) then
			Append(~List,L[x]);
		end if;
	end for;
	return List;
end function;

OuterAutomorphismRepresentatives := function(A)
	List := [];
	f,G := PermutationRepresentation(A);
	for N in Reverse(NormalSubgroups(G)) do
		if #N`subgroup eq #A/OuterOrder(A) then
			dummy := true;
			for x in SetToSequence(Set(N`subgroup)) do
				if IsInnerAutomorphism(x@@f) eq false then
					dummy := false;
				end if;
			end for;
			if dummy eq true then
				Ans := N`subgroup;
			break N;
			end if;
		end if;
	end for;
	Triv := NormalSubgroups(G)[1]`subgroup;
	L := DoubleCosetRepresentatives(G,Ans,Triv);
	for x in L do
		Append(~List,x@@f);
	end for;
	return List;
end function;

FullPreImagepk := function(G,m,p,k)
	if IsDivisibleBy(m,p) then
		PreG := G;
		level := m;
		for j := 1 to k do
			PreG := MatrixGroup<2, IntegerRing(level*p) | Generators(PreG), [1+level,0,0,1], [1,level,0,1], [1,0,level,1], [1,0,0,1+level] >;
			level := p*level;
		end for;
	end if;
	if not IsDivisibleBy(m,p) then
		Gen := {};
		for X1 in Generators(G) do
			a11 := CRT([RTI(X1[1,1]),1],[m,p]);
			a12 := CRT([RTI(X1[1,2]),0],[m,p]);
			a21 := CRT([RTI(X1[2,1]),0],[m,p]);
			a22 := CRT([RTI(X1[2,2]),1],[m,p]);
			A := Matrix(IntegerRing(m*p),2,2,[a11,a12,a21,a22]);
			Gen := Gen join { A };
		end for;
		for X2 in Generators(GL(2,Integers(p))) do
			a11 := CRT([RTI(X2[1,1]),1],[p,m]);
			a12 := CRT([RTI(X2[1,2]),0],[p,m]);
			a21 := CRT([RTI(X2[2,1]),0],[p,m]);
			a22 := CRT([RTI(X2[2,2]),1],[p,m]);
			A := Matrix(IntegerRing(m*p),2,2,[a11,a12,a21,a22]);
			Gen := Gen join { A };
		end for;
		PreG := MatrixGroup<2, IntegerRing(m*p) | Gen >;
		level := m*p;
		for j := 1 to k-1 do
			PreG := MatrixGroup<2, IntegerRing(level*p) | Generators(PreG), [1+level,0,0,1], [1,level,0,1], [1,0,level,1], [1,0,0,1+level] >;
			level := p*level;
		end for;
	end if;
	return PreG;
end function;

FullPreImage := function(G,m,d)
	PreG := G;
	level := m;
	w := #Factorization(d);
	for x := 1 to w do
		p := Factorization(d)[x,1];
		k := Factorization(d)[x,2];
		PreG := FullPreImagepk(PreG,level,p,k);
		level := level*p^k;
	end for;
	return PreG;
end function;

ModuloM := function(g,m)
	a11 := RTI(g[1,1]) mod m;
	a12 := RTI(g[1,2]) mod m;
	a21 := RTI(g[2,1]) mod m;
	a22 := RTI(g[2,2]) mod m;
	answer := Matrix(Integers(m),2,2,[a11,a12,a21,a22]);
	Answer := GL(2,Integers(m))!answer;
	return Answer;
end function;

FormingHigherLevelMTGroups := function(L,m)
	List := [];
	for x := 1 to #L do
		d := L[x,1,6];
		for y := 1 to #L[x] do
			print <x,y>;
			Gm := L[x,y,1];
			Sm := Gm meet SL(2,Integers(m));
			CoherentOuterAutomorphismList := CoherentAlphaList(OuterAutomorphismRepresentatives(AutomorphismGroup(GL(1,Integers(d*m)))),m,d);
			Gdm := FullPreImage(Gm,m,d);
			for H in Subgroups(Gm : IndexEqual := EulerPhi(d*m)) do
				if IsNormal(Gm,H`subgroup) and H`subgroup subset Sm and IsAbelian(Gm/H`subgroup) then
					print 17;
					GmmodHfromGm, pimodH := Gm/H`subgroup;
					isrightquotient, delta := IsIsomorphic(Gm/H`subgroup,GL(1,Integers(d*m)));
					if isrightquotient eq true then
						for beta in OuterAutomorphismRepresentatives(AutomorphismGroup(GL(1,Integers(d*m)))) do
							if IsCoherentDelta(delta*beta,pimodH,Gm,m) then
								delta := delta*beta;
								print 19;
								break beta;
							end if;
						end for;
						for alpha in CoherentOuterAutomorphismList do
							if IsCoherentAlpha(alpha,m,d) then
 								print 23;
								Groupdm := MatrixGroup<2, Integers(d*m) | [1,0,0,1] >;
								TraceOfGroupdm := TraceOfGroup(Groupdm,d*m);
								for g in Gdm do
									if not g in Groupdm then 
										det := Matrix(Integers(d*m),1,1,[Determinant(g)]);	
										if alpha(det) eq delta(pimodH(Gm!ModuloM(g,m))) then
											Groupdm := MatrixGroup<2, Integers(d*m) | Generators(Groupdm), g >;
											TraceOfGroupdm := TraceOfGroup(Groupdm,d*m);
											if #TraceOfGroupdm eq d*m then
												print 24;
												continue alpha;
											end if;
										end if;
									end if;
								end for;
								print 29;
								if IsMinimalMissingTraceGroup(Groupdm,d*m) and #DetOfGroup(Groupdm,d*m) eq EulerPhi(d*m) then
									print 101;
									if Genus(Groupdm,d*m)[4] eq 0 then
										print 2357;
										Append(~List,<Groupdm, Groupdm meet SL(2,Integers(d*m)),H`subgroup,L[x,y,1],L[x,y,2],L[x,y,3],L[x,y,4],L[x,y,5],L[x,y,6],d*m>);
									end if;
								end if;
							end if;
						end for;
					end if;
				end if;
			end for;
		end for;
	end for;
	return List;
end function;

ThinDownToContainsMinusIdentity := function(L,m)
	List := [];
	negI := Matrix(Integers(m),2,2,[-1,0,0,-1]);
	for x := 1 to #L do
		print x;
		if negI in L[x,1] then
			Append(~List,L[x]);
		end if;
	end for;
	return List;
end function;

TwoTimesMComputation := function(L,m)
	List := [];
	negI := Matrix(Integers(2*m),2,2,[-1,0,0,-1]);
	for x := 1 to #L do
		print x;
		FPreG := FullPreImage(L[x,1],m,2);
		for H in Subgroups(FPreG : IndexEqual := 2) do
			if not negI in H`subgroup then
				Hmodm := MatrixGroup<2, Integers(m) | Generators(H`subgroup) >;
				if #Hmodm eq #L[x,1] then
					Append(~List,<H`subgroup,L[x,2]>);
				end if;
			end if;
		end for;
	end for;
	return List;
end function;


