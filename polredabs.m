intrinsic Polredabs(f::RngUPolElt) -> RngUPolElt
  { A smallest generating polynomial of the number field, using pari. }
  cmd := Sprintf(
           "{print(Vecrev(Vec(polredabs(Pol(Vecrev(%o))))))}",
           Coefficients(f));
  s := Pipe("gp -q", cmd);
  ss := [ StringToInteger(x)
        : x in Split(s, ", []\n") | x ne "" ];
  return Parent(f) ! ss;
end intrinsic;

intrinsic Polredbest(f::RngUPolElt) -> RngUPolElt
  { A smallest generating polynomial of the number field, using pari. }
  cmd := Sprintf(
           "{print(Vecrev(Vec(polredbest(Pol(Vecrev(%o))))))}",
           Coefficients(f));
  s := Pipe("gp -q", cmd);
  ss := [ StringToInteger(x)
        : x in Split(s, ", []\n") | x ne "" ];
  return Parent(f) ! ss;
end intrinsic;

intrinsic PolredbestWithRoot(f::RngUPolElt) -> RngUPolElt, SeqEnum
  { A smallest generating polynomial of the number field, using pari. }
  cmd := Sprintf(
     "{u = polredbest(Pol(Vecrev(%o)),1); print(Vecrev(Vec(u[1])),Vecrev(Vec(lift(u[2]))))}", 
     Coefficients(f));
  s := Pipe("gp -q", cmd);
  c := Index(s,"][");
  spol := s[1..c];
  sroot := s[c+1..#s-1];
  sspol := [ StringToInteger(x) : x in Split(spol, ", []\n") | x ne "" ];
  ssroot := [ StringToRational(x) : x in Split(sroot, ", []\n") | x ne "" ];
  return Parent(f) ! sspol, ssroot;
end intrinsic;

