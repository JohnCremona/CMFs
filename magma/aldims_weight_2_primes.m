// usage: magma -b N_min:={} N_max:={} aldims_weight_2_primes.m
// This is for N <= 10^6 prime, k = 2
import "magma/aldims.m" : write_ALdims_upto;

write_ALdims_upto(eval(N_min), eval(N_max), 2 : OnlyPrimes);

exit;