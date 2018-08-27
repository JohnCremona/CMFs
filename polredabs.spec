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
