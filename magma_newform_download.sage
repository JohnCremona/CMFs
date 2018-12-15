def magma_newform_code_string(r):
    """Given a row r from mf_newforms containing columns level,weight,char_orbit_label,char_values,cutters returns a string containing magma code to create the newform in magma."""
    N = r["level"]
    k = r["weight"]
    o = r["char_orbit_label"]
    cv =r["char_values"]
    cutters = "[" + ",".join(["<%d,R!%s"%(c[0],c[1])+">" for c in r["hecke_cutters"]]) + "]"
    s = "function make_character_%d_%s()\n"%(N,o)
    s += "    N := %d; n := %d; u := %s; v := %s;\n"%(cv[0],cv[1],cv[2],cv[3])
    s += "    assert UnitGenerators(DirichletGroup(N)) eq u;\n"
    s += "    F := CyclotomicField(n);\n"
    s += "    return DirichletCharacterFromValuesOnUnitGenerators(DirichletGroup(N,F),[F|F.1^n:n in v]);\n"
    s += "end function;\n\n"
    s += "function make_newform_%s()\n"%(r["label"].replace(".","_"))
    s += "    return Kernel(%s,NewSubspace(CuspidalSubspace(ModularSymbols(make_character_%d_%s(),%d,-1))));\n"%(cutters,N,o,k)
    s += "end function;\n\n"
    return s
