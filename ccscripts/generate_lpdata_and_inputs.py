from sage.all import ComplexBallField, primes_first_n, ZZ, RealIntervalField
from dirichlet_conrey import DirichletGroup_conrey, DirichletCharacter_conrey
import sys, os
# 265 = 80 digits
default_prec = 300
CCC = ComplexBallField(default_prec)
RRR = RealIntervalField(default_prec)
def toRRR(elt):
    if "." in elt and len(elt) > 70:
        # drop the last digit and convert it to an unkown
        if 'E' in elt:
            begin, end = elt.split("E")
        elif 'e' in elt:
            begin, end = elt.split("E")
        else:
            begin = elt
            end = "0"
        begin = begin[:-1] # drop the last digit
        return RRR(begin + "0e" + end, begin + "9e" + end)
    else:
        return RRR(elt)
        
def toCCC(r, i):
    return CCC(toRRR(r)) + CCC.gens()[0]*CCC(toRRR(i))

def line_count(filename):
    i = 0
    with open(filename, 'r') as F:
        for _ in F:
            i += 1
    return i
def euler_factor(level, weight, char, p, ap, normalized = False):
    if normalized:
        ap *= p**(-ZZ(weight-1)/2)
        ppower = 1
    else:
        ppower = p**(weight-1)
    if p.divides(level):
        return [1, -ap]
    charval = CCC(2*char.logvalue(p)).exppii()
    if charval.contains_exact(ZZ(1)):
        charval = 1
    elif charval.contains_exact(ZZ(-1)):
        charval = -1
    return [1, -ap, ppower * charval]

weight_boundary_normalization = 201
def generate_lpdata_and_inputs(filename, check_for_lpdata = True, check_for_lfunction = True, chunk = 100):

    linecount = line_count(filename)

    def print_RRR(elt):
        if elt.contains_integer():
            try:
                return "%d" % ZZ(elt)
            except ValueError:
                pass
        return RRR(elt).str(style="question").replace('?', '')

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
            weight_normalized = weight if weight < weight_boundary_normalization else 1
            normalized = weight >= weight_boundary_normalization
            conrey_label = int(conrey_label)
            ap_list = [ toCCC(*elt.split(',')) for elt in ap_txt[2:-2].split('],[')]
            ap_list = zip(primes_first_n(len(ap_list)),ap_list)
            G = DirichletGroup_conrey(level, CCC)
            char = DirichletCharacter_conrey(G, conrey_label)
            euler_factors = [[elt[0], euler_factor(level, weight, char, elt[0], elt[1], normalized = normalized)] for elt in ap_list]
            if not os.path.exists(lpfilename) or not check_for_lpdata:
                with open(lpfilename, 'w') as LPDATA:
                    for p, ep in euler_factors:
                        LPDATA.write("%d, [ %s ]\n" % (p, ", ".join(map(print_CCC, ep))))
            if not os.path.exists(lfunctionfilename) or not check_for_lfunction:
                if weight not in inputs:
                    inputs[weight] = []
                inputs[weight].append("%d %d %d %s %s" % (weight_normalized, self_dual(char, ap_list), level, label, lpfilename))
            k += 1
            if linecount > 10:
                if (k % (linecount//10)) == 0:
                    print "generate_lpdata_and_inputs %.2f%% done" % (k*100./linecount)
    parallel_inputs = os.path.join(base_dir, real_filename + '.tsv')
    with open(parallel_inputs, 'w') as I:
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
                    #print "wrote %d lines to %s" % (len(line_block), inputsfilename)
                I.write("%d\t%s\n" % (weight_normalized, inputsfilename))

    print "now set LFUNCTIONS and run:"
    print r"""parallel -a %s  --colsep '\t' --progress ${LFUNCTIONS}/euler_factors 11 200  ${LFUNCTIONS}/gamma_files/mf.{1} {2} 100""" % (parallel_inputs,)


generate_lpdata_and_inputs(sys.argv[1])


