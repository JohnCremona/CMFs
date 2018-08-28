from sage.all import PolynomialRing, gp, QQ
import sys
QQx = PolynomialRing(QQ, "x")
def polredbestabs(f):
    fnew = QQx(f)
    fold = None
    while fold != fnew:
        fold = fnew
        fnew = QQx(str(gp.polredbest(fold)))
    return f, QQx(str(gp.polredabs(fnew))).list()

def polredmap(inputstr):
    f, redf = map(eval, inputstr.split(":"))
    if redf is None:
        print ("%s:%s" % polredbestabs(f)).replace(" ","")
    else:
        return inputstr

if __name__ == '__main__':
    polredmap(sys.argv[1])
