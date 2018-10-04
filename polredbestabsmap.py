from sage.all import PolynomialRing, gp, QQ, ZZ
import sys
import signal


def sigterm_handler(_signo, _stack_frame):
    print sys.argv[1]
    sys.exit(1)

signal.signal(signal.SIGTERM, sigterm_handler)

QQx = PolynomialRing(QQ, "x")
def polredbestabs(f):
    fnew = QQx(f)
    fold = None
    while fold != fnew:
        fold = fnew
        fnew = QQx(str(gp.polredbest(fold)))
    return map(ZZ, list(f)), map(ZZ, QQx(str(gp.polredabs(fnew))).list())

def polredmap(inputstr):
    f, redf = map(eval, inputstr.split(":"))
    if redf is None:
        print ("%s:%s" % polredbestabs(f)).replace(" ","")
    else:
        return inputstr

if __name__ == '__main__':
    try:
        gp.allocatemem(900000000)
        print polredmap(sys.argv[1])
    except:
        print sys.argv[1]