/*
// Example 1:
Attach("heigs.m");
Attach("polredabs.m");
G := DirichletGroup(55, CyclotomicField(4));
chi := G.1*G.2;  
assert Order(chi) eq 4;
Snew := NewSubspace(CuspidalSubspace(ModularSymbols(chi,6,-1)));
Vfs := NewformDecomposition(Snew);
Vf := Vfs[1];
ExactHeckeEigenvalues(Vf);
*/

/* 
// Example 2:
Attach("heigs.m");
Attach("polredabs.m");
Snew := NewSubspace(CuspidalSubspace(ModularSymbols(2,130,-1)));
Vfs := NewformDecomposition(Snew);
Vf := Vfs[1];
ExactHeckeEigenvalues(Vf);
*/

function PolredbestifyWithRoot(f)
  K0 := NumberField(f);
  iota := hom<K0 -> K0 | K0.1>; // start with identity
  cnt := 0;
  Kfront := K0;
  ffront := f;
  while true and cnt lt 10 do
    fbest, fbestroot := PolredbestWithRoot(ffront);
    if fbest eq ffront then 
      return ffront, Eltseq(iota(K0.1)), cnt;
    end if;
    cnt +:= 1;
    Kbest := NumberField(fbest);
    fbestroot := fbestroot cat [0 : i in [1..Degree(fbest)-#fbestroot]];
  	iota := iota*hom<Kfront -> Kbest | fbestroot>;
    Kfront := Kbest;
    ffront := fbest; 
  end while;
end function;

// input is a Hecke irreducible space Vf;
// output is:
//    KbestSeq, a sequence [...,1] of integers giving the minimal polynomial of the Hecke field 
//    HeckeRingZZBasisSeq, a sequence of sequences of integers whose entries are a
//         ZZ-basis for the Hecke ring, written in a power basis (specified by KbestSeq)
//    Oind, a divisor of the index of the Hecke ring in the maximal order
//    foundmax, a boolean saying if we can certify the index
//    ZOE, a sequence of sequences of integers whose nth entry is the Hecke operator
//        T_n written in the basis Oind.
intrinsic ExactHeckeEigenvalues(Vf::ModSym : Tnbnd := 0) -> 
  SeqEnum[RngInt], SeqEnum[SeqEnum[RngInt]], RngIntElt, BoolElt, SeqEnum[SeqEnum[RngInt]]
  {Computes exact Hecke data}
  
	chi := DirichletCharacter(Vf);
	QQchi := BaseRing(chi);  // cyclotomic field; required to be the field
	dchi := Degree(QQchi);
	ZZchi := Integers(QQchi);

  if Tnbnd eq 0 then
  	upsturmbnd := Max(HeckeBound(Vf)+20,100);
  else
    upsturmbnd := Tnbnd;
  end if;

	assert BaseField(Vf) eq QQchi;  // to avoid degree problems

	d := Dimension(Vf);
	Tns := [HeckeOperator(Vf,n) : n in [1..upsturmbnd]];   // sequence of dxd matrices

	M := Matrix([Eltseq(Tn) : Tn in Tns]); 
		// matrix with upsturmbnd rows and d^2 columns, 
		// entries in QQchi, but its rank is only d
	MZZ := Matrix([[Trace(e) : e in Eltseq(Tn)] : Tn in Tns]);  
		// matrix with upsturmbnd rows and d^2 columns over ZZ

/*
  // small linear combinations doesn't really work for CM forms, better to just iterate
	// find small linear combination which generates the Hecke field
	_, E := LLL(MZZ);
	Tref := &+[E[2][i]*Tns[i] : i in [1..#Tns]];  // usually the second works
	Trefpol := CharacteristicPolynomial(Tref);
	cnt := 0;
	
	while not IsIrreducible(Trefpol) do  
		cnt +:= 1;
		j := Random(1,Nrows(E));
		Tref +:= (-1)^(Random(1))*&+[E[j][i]*Tns[i] : i in [1..#Tns]];
			 // add random vector; probabilistic, but we will throw this away soon anyway
		Trefpol := CharacteristicPolynomial(Tref);
		assert cnt lt 100;  // if this loop gets called more than 10 times, something is wrong
	end while;
*/
  
	Tref := 0;
	foundirr := false;
	for n := 2 to upsturmbnd do
	  Tref +:= (n-1)*Tns[n];
  	Trefpol := CharacteristicPolynomial(Tref);
	  if IsIrreducible(Trefpol) then 
	    foundirr := true;
	    break;
	  end if;
	end for;
  assert foundirr;
  
	Trefpows := [Tref^i : i in [0..d-1]];  // QQ(chi)-power basis for the Hecke algebra
	Mrefpows := Matrix([Eltseq(Ti) : Ti in Trefpows]);  
		// d x d^2 (flattened) matrix with rows the QQ(chi)-power basis

	// write Tns in this basis
	Z_rel := Solution(Mrefpows,Matrix([Eltseq(Tn) : Tn in Tns]));  
	// Z_rel is now upsturmbnd x d, the nth row writes Tn as a linear combination of Trefpows, so we can coerce

	K_notbest_rel := ext<QQchi | Trefpol>;   // define Hecke field
	K_notbest := AbsoluteField(K_notbest_rel);

  if Degree(Trefpol) eq 1 then
  	Z := Matrix([Eltseq(K_notbest!K_notbest_rel!Z_rel[i][1]) : i in [1..Nrows(Z_rel)]]);
  else
  	Z := Matrix([Eltseq(K_notbest!K_notbest_rel!Eltseq(Z_rel[i])) : i in [1..Nrows(Z_rel)]]);
  end if;

	// Make best field
	Trefpolbest, fbestroot := PolredbestifyWithRoot(MinimalPolynomial(K_notbest.1));  // iotaK is the isomorphism from Kabs_notbest to Kabs
	Kbest := NumberField(Trefpolbest);
	fbestroot := fbestroot cat [0 : i in [1..Degree(Trefpolbest)-#fbestroot]];
	iotabest := hom<K_notbest -> Kbest | fbestroot>;
	// <======= when polredabs is given, find an isomorphism to the given field
	KbestSeq := Eltseq(MinimalPolynomial(Kbest.1));  // seq defining Hecke field polynomial

	// Change of power basis from K_notbest to Kbest (so d*dchi x d*dchi)
	Pbest := Matrix([Eltseq(iotabest(K_notbest.1^i)) : i in [0..Degree(K_notbest)-1]]);
	Pbestinv := Pbest^-1;
	Zbest := Z*Pbest;  // Z is still upsturmbnd x d
	assert &and[K_notbest!Eltseq(Z[m]) eq (iotabest^-1)(Kbest!Eltseq(Zbest[m])) : m in [1..Nrows(Z)]];

	// make order over ZZ generated by T_n's
	O := Order([Kbest | Kbest!Eltseq(Zbest[i]) : i in [1..Nrows(Zbest)]]);
	OBasis := Basis(O);  
	assert #OBasis eq d*dchi;

	// Improve O as much as possible to get a divisor of the index
	Oma := O;  // Initialize "almost max" order to O
	discO := Discriminant(O);
	ps, foo := TrialDivision(discO);
	for pdat in ps do  // make p-maximal
		Oma := pMaximalOrder(Oma, pdat[1]);
	end for;
	_, Oind := IsSquare(discO/Discriminant(Oma));
	foundmax := foo cmpeq [] or (#foo eq 1 and IsPrime(foo[1]));

	PO := Matrix([Eltseq(Kbest!b) : b in OBasis]);
	// PO is the change of basis matrix from Magma's integral basis to the power basis
	POinv := PO^-1;

	ZO := ChangeRing(Zbest*POinv,Integers());  
	// upsturmbnd x (d*dchi), the nth row write Tn as a linear combination of the chosen ZZ-basis for O

	// Now compute a small basis
	_, E := LLL(MinkowskiLattice(O));   // E is the ZZ-change of basis to an LLL-reduced basis
	Einv := E^-1;
	OLLLBasis := [&+[ E[i][j]*OBasis[j] : j in [1..d*dchi]] : i in [1..d*dchi]];
	ZOE := ZO*Einv;   // still upsturmbnd x (d*dchi), now linear combo of LLL-reduced basis

	// check that seqs match originally computed
	assert &and[Kbest!Eltseq(Zbest[m]) eq Kbest!&+[ZOE[m][i]*OLLLBasis[i] : i in [1..d*dchi]] : m in [1..Nrows(Z)]];

	// Sequence of d*dchi elements giving an LLL-reduced basis for the Hecke ring
	HeckeRingZZBasisSeq := [Eltseq(c) : c in OLLLBasis];   // bam

	return KbestSeq, HeckeRingZZBasisSeq, Oind, foundmax, ZOE;
end intrinsic;