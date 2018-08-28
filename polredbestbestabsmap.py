from sage.all import PolynomialRing, gp, QQ, ZZ
import sys
import signal


def sigterm_handler(_signo, _stack_frame):
    print sys.argv[1]
    sys.exit(1)

signal.signal(signal.SIGTERM, sigterm_handler)

QQx = PolynomialRing(QQ, "x")
def polredbestbestabs(g, f):
    return map(ZZ, list(f)),map(ZZ, QQx(f)), map(ZZ, QQx(str(gp.polredabs(QQx(f)))).list())

def polredmap(inputstr):
    g, f, redf = map(eval, inputstr.split(":"))
    if redf is None:
        return ("%s:%s:%s" % polredbestbestabs(g, f)).replace(" ","")
    else:
        return inputstr

if __name__ == '__main__':
    try:
        gp.allocatemem(9000000000)
        print polredmap(sys.argv[1])
    except:
        print sys.argv[1]
