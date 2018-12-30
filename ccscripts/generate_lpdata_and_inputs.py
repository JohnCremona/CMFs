from sage.all import ComplexBallField, primes_first_n, ZZ
from dirichlet_conrey import DirichletGroup_conrey, DirichletCharacter_conrey
import sys, os
# 265 = 80 digits
default_prec = 265

def line_count(filename):
    i = 0
    with open(filename, 'r') as F:
        for _ in F:
            i += 1
    return i

def generate_lpdata_and_inputs(filename, prec=default_prec, check_for_lpdata = True, check_for_lfunction = True, chunk = 100):

    linecount = line_count(filename)

    CCC = ComplexBallField(prec)
    def print_RRR(elt):
        if elt.contains_integer():
            return "%d" % ZZ(elt)
        else:
            return elt.mid().str(truncate=False)

    def print_CCC(elt):
        elt = CCC(elt)
        return "[ %s, %s]" % tuple(map(print_RRR, [elt.real(), elt.imag()]))

    def self_dual(char, aps):
        if char.is_trivial():
            return True
        if (char*char).is_trivial():
            for _, z in aps:
                if not z.imag().contains_zero():
                    return False
            return True
        else:
            return False
    base_dir = os.path.dirname(os.path.abspath(filename))
    real_filename = os.path.abspath(filename).split('/')[-1]
    lfun_dir = os.path.join(base_dir, 'lfun')
    inputs_dir = os.path.join(base_dir, 'inputs')
    print inputs_dir
    for d in [inputs_dir, lfun_dir]:
        if not os.path.exists(d):
            os.mkdir(d)
    inputs = {}
    k = 0
    with open(filename, 'r') as F:
        for line in F:
            linesplit = line[:-1].split(':')
            hoc, label, conrey_label, embedding_index, embedding_m, ap_txt = linesplit
            lpfilename = os.path.join(lfun_dir, label + ".lpdata")
            lfunctionfilename = os.path.join(lfun_dir, label + ".lpdata.lfunction")
            
            level, weight, char_orbit, hecke_orbit, conrey_label_again, embedding = label.split('.')
            assert conrey_label_again == conrey_label
            level = int(level)
            weight = int(weight)
            conrey_label = int(conrey_label)
            ap_list = [ CCC(*elt.split(',')) for elt in ap_txt[2:-2].split('],[')]
            ap_list = zip(primes_first_n(len(ap_list)),ap_list)
            G = DirichletGroup_conrey(level, CCC)
            char = DirichletCharacter_conrey(G, conrey_label)
            def euler_factor(p, ap):
                if p.divides(level):
                    return [1, -ap]
                charval = CCC(2*char.logvalue(p)).exppii()
                if charval.contains_exact(ZZ(1)):
                    charval = 1
                elif charval.contains_exact(ZZ(-1)):
                    charval = -1
                return [1, -ap, (p**(weight-1))*charval]
            euler_factors = [[elt[0], euler_factor(*elt)] for elt in ap_list]
            if not os.path.exists(lpfilename) or not check_for_lpdata:
                with open(lpfilename, 'w') as LPDATA:
                    for p, ep in euler_factors:
                        LPDATA.write("%d, [ %s ]\n" % (p, ", ".join(map(print_CCC, ep))))
            if not os.path.exists(lfunctionfilename) or not check_for_lfunction:
                if weight not in inputs:
                    inputs[weight] = []
                inputs[weight].append("%d %d %d %s %s" % (weight, self_dual(char, ap_list) , level, label, lpfilename))
            k += 1
            if (k % (linecount//10)) == 0:
                print "%.2f%% done" % (k*100./linecount)
    for weight, lines in inputs.iteritems():
        if chunk is None:
            chunked_lines = [lines]
        else:
            chunked_lines = [ lines[i:i+chunk] for i in range(0, len(lines), chunk)]
        assert sum(map(len, chunked_lines)) == len(lines), "%d != %d" % (sum(map(len, chunked_lines)), len(lines))
        for i, line_block in enumerate(chunked_lines):
            inputsfilename = os.path.join(inputs_dir, real_filename + '_wt%d_%d.input' % (weight, i))
            with open(inputsfilename , 'w') as W:
                W.write('\n'.join(line_block) + '\n')
                print "wrote %d lines to %s" % (len(line_block), inputsfilename)


generate_lpdata_and_inputs(sys.argv[1])


